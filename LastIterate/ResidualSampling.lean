module

public import LastIterate.FrozenSampling
public import LastIterate.ResidualGeometry

@[expose] public section

/-! # Tail residuals and their correlation with the observed history -/

namespace LastIterate

open Finset
open scoped Fin.NatCast RealInnerProductSpace

variable {Ω Z E : Type*} {m : ℕ} [Fintype Ω] [NeZero m]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace HistoryLaw

noncomputable def residual (L : HistoryLaw Ω Z m) (ζ : Z → E) (i : Fin m) :
    HistorySpace Ω E := WithLp.toLp 2 (fun ω ↦ ζ (L.label ω i))

def FutureInvariant (L : HistoryLaw Ω Z m) (U : HistorySpace Ω E) (k : ℕ) : Prop :=
  ∀ i j : Fin m, k ≤ i.val → k ≤ j.val → ∀ ω,
    U (L.reindex (Equiv.swap i j) ω) = U ω

theorem futureInvariant_current (L : HistoryLaw Ω Z m) (step : Z → E → E)
    (x0 : Ω → E) (h0 : L.StartInvariant x0) {t k : ℕ} (ht : t ≤ k) :
    L.FutureInvariant (L.current step x0 t) k := by
  intro i j hi hj ω
  exact L.current_swap step x0 h0 i j (by omega) (by omega) ω

theorem futureInvariant_sub (L : HistoryLaw Ω Z m) {U V : HistorySpace Ω E} {k : ℕ}
    (hU : L.FutureInvariant U k) (hV : L.FutureInvariant V k) :
    L.FutureInvariant (U - V) k := by
  intro i j hi hj ω
  change U _ - V _ = U _ - V _
  rw [hU i j hi hj ω, hV i j hi hj ω]

theorem shift_to_current (L : HistoryLaw Ω Z m) (step : Z → E → E)
    (x0 : Ω → E) (h0 : L.StartInvariant x0) (k : ℕ) :
    L.shift (k : Fin m) (L.past step x0 0 k) = L.current step x0 k := by
  rw [L.shift_past step x0 h0, zero_add]
  ext ω
  exact suffix_forward step (x0 ω) (L.label ω) k

theorem past_current_distance (L : HistoryLaw Ω Z m) (step : Z → E → E)
    (x0 : Ω → E) (h0 : L.StartInvariant x0) (k : ℕ) :
    ‖L.past step x0 0 k - L.past step x0 0 0‖ =
      ‖L.current step x0 k - L.current step x0 0‖ := by
  have he : L.shift (k : Fin m) (L.past step x0 0 0) = L.current step x0 0 := by
    rw [L.shift_past step x0 h0]
    ext ω
    rfl
  rw [← L.shift_to_current step x0 h0 k, ← he, ← map_sub]
  exact ((L.shift (k : Fin m)).norm_map _).symm

theorem queriedGradient_forward (L : HistoryLaw Ω Z m) (g : Z → E → E)
    (x0 : Ω → E) (h0 : L.StartInvariant x0) (k : ℕ) :
    ‖L.queriedGradient g x0 k‖ ^ 2 =
      ‖liftGradient (fun ω ↦ g (L.label ω (k : Fin m)))
        (L.current (fun z x ↦ x - g z x) x0 k)‖ ^ 2 := by
  rw [history_norm_sq, history_norm_sq]
  exact L.queriedLoss_forward (fun z x ↦ ‖g z x‖ ^ 2)
    (fun z x ↦ x - g z x) x0 h0 k

theorem queriedGradient_sq_loss (L : HistoryLaw Ω Z m) (g : Z → E → E)
    (x0 : Ω → E) (k : ℕ) :
    ‖L.queriedGradient g x0 k‖ ^ 2 =
      L.queriedLoss (fun z x ↦ ‖g z x‖ ^ 2) (fun z x ↦ x - g z x) x0 k := by
  rw [history_norm_sq]
  rfl

theorem current_succ (L : HistoryLaw Ω Z m) (g : Z → E → E)
    (x0 : Ω → E) (k : ℕ) :
    L.current (fun z x ↦ x - g z x) x0 (k + 1) =
      L.current (fun z x ↦ x - g z x) x0 k -
        liftGradient (fun ω ↦ g (L.label ω (k : Fin m)))
          (L.current (fun z x ↦ x - g z x) x0 k) := by
  ext ω
  rfl

theorem residual_current_inner (L : HistoryLaw Ω Z m) (ζ : Z → E)
    (step : Z → E → E) (x0 : Ω → E) (h0 : L.StartInvariant x0)
    {k : ℕ} (i j : Fin m) (hi : k ≤ i.val) (hj : k ≤ j.val) :
    ⟪L.residual ζ i, L.current step x0 k⟫ =
      ⟪L.residual ζ j, L.current step x0 k⟫ := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  exact L.sum_future_query step x0 h0 (fun z x ↦ ⟪ζ z, x⟫) i j hi hj

theorem residual_displacement_inner (L : HistoryLaw Ω Z m) (ζ : Z → E)
    (step : Z → E → E) (x0 : Ω → E) (h0 : L.StartInvariant x0)
    {k : ℕ} (i j : Fin m) (hi : k ≤ i.val) (hj : k ≤ j.val) :
    ⟪L.residual ζ i, L.current step x0 k - L.current step x0 0⟫ =
      ⟪L.residual ζ j, L.current step x0 k - L.current step x0 0⟫ := by
  simp only [inner_sub_right]
  rw [L.residual_current_inner ζ step x0 h0 i j hi hj,
    L.residual_current_inner ζ step x0 h0 (k := 0) i j (by omega) (by omega)]

/-- Average all still unobserved residuals, retaining their pairwise geometry. -/
noncomputable def remainingResidual (L : HistoryLaw Ω Z m) (ζ : Z → E) (k : ℕ) :
    HistorySpace Ω E :=
  ((m - k : ℕ) : ℝ)⁻¹ • ∑ j ∈ range (m - k), L.residual ζ ((k + j : ℕ) : Fin m)

theorem remainingResidual_norm (L : HistoryLaw Ω Z m) (ζ : Z → E)
    {v : ℝ} (hdiag : ∀ i, ‖L.residual ζ i‖ ^ 2 ≤ v)
    (hpair : ∀ i j, i ≠ j → ⟪L.residual ζ i, L.residual ζ j⟫ ≤ 0)
    {k : ℕ} (hk : k < m) :
    ‖L.remainingResidual ζ k‖ ^ 2 ≤ v / (m - k : ℕ) := by
  have hh := norm_average_sq_le_of_nonpos (range (m - k))
    (fun j ↦ L.residual ζ ((k + j : ℕ) : Fin m))
    (by simpa only [card_range] using (show 0 < m - k by omega))
    (fun j _ ↦ hdiag _) (fun i hi j hj hij ↦ hpair _ _ (by
      intro he
      have hv := congrArg Fin.val he
      have hi' := mem_range.mp hi
      have hj' := mem_range.mp hj
      simp only [Fin.val_natCast, Nat.mod_eq_of_lt (show k + i < m by omega),
        Nat.mod_eq_of_lt (show k + j < m by omega)] at hv
      omega))
  simpa only [remainingResidual, card_range] using hh

theorem remainingResidual_current (L : HistoryLaw Ω Z m) (ζ : Z → E)
    (step : Z → E → E) (x0 : Ω → E) (h0 : L.StartInvariant x0)
    {k : ℕ} (hk : k < m) :
    ⟪L.remainingResidual ζ k, L.current step x0 k⟫ =
      ⟪L.residual ζ (k : Fin m), L.current step x0 k⟫ := by
  have hn : ((m - k : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show m - k ≠ 0 by omega)
  unfold remainingResidual
  rw [real_inner_smul_left, sum_inner]
  have he : (∑ j ∈ range (m - k),
      ⟪L.residual ζ ((k + j : ℕ) : Fin m), L.current step x0 k⟫) =
      (m - k : ℕ) * ⟪L.residual ζ (k : Fin m), L.current step x0 k⟫ := by
    calc
      _ = ∑ _j ∈ range (m - k), ⟪L.residual ζ (k : Fin m), L.current step x0 k⟫ := by
        apply sum_congr rfl
        intro j hj
        have hj' := mem_range.mp hj
        apply L.residual_current_inner ζ step x0 h0
        · simp only [Fin.val_natCast, Nat.mod_eq_of_lt (show k + j < m by omega)]
          omega
        · simp only [Fin.val_natCast, Nat.mod_eq_of_lt hk]
          exact le_rfl
      _ = _ := by simp
  rw [he, ← mul_assoc, inv_mul_cancel₀ hn, one_mul]

theorem remainingResidual_inner (L : HistoryLaw Ω Z m) (ζ : Z → E)
    (U : HistorySpace Ω E) {k : ℕ} (hk : k < m) (hU : L.FutureInvariant U k) :
    ⟪L.remainingResidual ζ k, U⟫ = ⟪L.residual ζ (k : Fin m), U⟫ := by
  have hn : ((m - k : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show m - k ≠ 0 by omega)
  have hinner (j : ℕ) (hj : j < m - k) :
      ⟪L.residual ζ ((k + j : ℕ) : Fin m), U⟫ = ⟪L.residual ζ (k : Fin m), U⟫ := by
    let i : Fin m := (k + j : ℕ)
    let q : Fin m := k
    have hi : k ≤ i.val := by
      simp only [i, Fin.val_natCast, Nat.mod_eq_of_lt (show k + j < m by omega)]
      omega
    have hq : k ≤ q.val := by simp [q, Fin.val_natCast, Nat.mod_eq_of_lt hk]
    have hh := L.sum_invariant (Equiv.swap i q) (fun ω ↦ ⟪ζ (L.label ω i), U ω⟫)
    have he := hU i q hi hq
    simp only [L.label_reindex, Equiv.swap_apply_left, he] at hh
    rw [PiLp.inner_apply, PiLp.inner_apply]
    exact hh.symm
  unfold remainingResidual
  rw [real_inner_smul_left, sum_inner]
  have he : (∑ j ∈ range (m - k), ⟪L.residual ζ ((k + j : ℕ) : Fin m), U⟫) =
      (m - k : ℕ) * ⟪L.residual ζ (k : Fin m), U⟫ := by
    calc
      _ = ∑ _j ∈ range (m - k), ⟪L.residual ζ (k : Fin m), U⟫ :=
        sum_congr rfl (fun j hj ↦ hinner j (mem_range.mp hj))
      _ = _ := by simp
  rw [he, ← mul_assoc, inv_mul_cancel₀ hn, one_mul]

/-- The noise/history correlation, with its precise remaining-history weight. -/
theorem residual_correlation (L : HistoryLaw Ω Z m) (ζ : Z → E)
    {v : ℝ} (hv : 0 ≤ v) (hdiag : ∀ i, ‖L.residual ζ i‖ ^ 2 ≤ v)
    (hpair : ∀ i j, i ≠ j → ⟪L.residual ζ i, L.residual ζ j⟫ ≤ 0)
    (U : HistorySpace Ω E) {k : ℕ} (hk : k < m) (hU : L.FutureInvariant U k) :
    |⟪L.residual ζ (k : Fin m), U⟫| ≤
      Real.sqrt v * ‖U‖ / Real.sqrt (m - k : ℕ) := by
  rw [← L.remainingResidual_inner ζ U hk hU]
  have hn := Real.sqrt_le_sqrt (L.remainingResidual_norm ζ hdiag hpair hk)
  rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_div hv] at hn
  have hh := mul_le_mul_of_nonneg_right hn (norm_nonneg U)
  have hc := (abs_real_inner_le_norm (L.remainingResidual ζ k) U).trans hh
  convert! hc using 1 <;> ring

end HistoryLaw

end LastIterate
