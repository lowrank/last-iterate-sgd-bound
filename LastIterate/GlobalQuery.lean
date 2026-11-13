module

public import LastIterate.NoiseAmplification
public import LastIterate.Restart

@[expose] public section

/-! # Averaging all actual restarts: the improved queried-loss bound -/

namespace LastIterate

open Finset
open scoped Fin.NatCast RealInnerProductSpace

variable {Ω Z E : Type*} {m : ℕ} [Fintype Ω] [NeZero m]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace NoiseModel

noncomputable def restartBudget (p : NoiseModel Z E) (L : HistoryLaw Ω Z m)
    (x0 : Ω → E) (v : ℝ) (r : ℕ) : ℝ :=
  16 * L.queriedLoss p.h p.step x0 r / p.δ + (34 + 8 * p.α / p.δ) * v

noncomputable def linearQuery (p : NoiseModel Z E) (L : HistoryLaw Ω Z m)
    (x0 : Ω → E) (r : ℕ) : ℝ :=
  L.queriedLoss (fun z x ↦ ⟪p.ζ z, x - p.star⟫) p.step x0 r

theorem linearQuery_inner (p : NoiseModel Z E) (L : HistoryLaw Ω Z m)
    (x0 : Ω → E) (h0 : L.StartInvariant x0) (r : ℕ) :
    p.linearQuery L x0 r = ⟪L.residual p.ζ (r : Fin m), L.current p.step x0 r - p.starField⟫ := by
  rw [linearQuery, L.queriedLoss_forward _ p.step x0 h0, PiLp.inner_apply]
  rfl

theorem linearQuery_average (p : NoiseModel Z E) (L : HistoryLaw Ω Z m)
    (v : ResidualControl p L) (x0 : Ω → E) (h0 : L.StartInvariant x0) :
    mean (p.linearQuery L x0) m ≤
      ‖L.current p.step x0 0 - p.starField‖ ^ 2 / m + 13 * v.variance / p.δ := by
  let R := ‖L.current p.step x0 0 - p.starField‖ ^ 2
  let B := 2 * R + 26 * m * v.variance / p.δ
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hB : 0 ≤ B := by
    have := v.nonneg
    have := p.delta_pos
    dsimp [B, R]
    positivity
  have hbound (r : ℕ) (hr : r < m) :
      p.linearQuery L x0 r ≤ Real.sqrt v.variance * Real.sqrt B / Real.sqrt (m - r : ℕ) := by
    have he := p.radius_budget L v x0 h0 (Nat.le_of_lt hr)
    have hn : 0 ≤ p.δ * ∑ j ∈ range r, p.lossAt L (j : Fin m) (L.current p.step x0 j) :=
      mul_nonneg p.delta_pos.le (sum_nonneg (fun _ _ ↦ p.lossAt_nonneg L _ _))
    have hmul := mul_le_mul_of_nonneg_right
      (show (r : ℝ) ≤ m by exact_mod_cast (Nat.le_of_lt hr))
      (show 0 ≤ 26 * v.variance / p.δ by
        exact div_nonneg (mul_nonneg (by norm_num) v.nonneg) p.delta_pos.le)
    have hd : ‖L.current p.step x0 r - p.starField‖ ^ 2 ≤ B := by
      dsimp [B, R]
      linear_combination he + hmul + hn
    have hroot := Real.sqrt_le_sqrt hd
    rw [Real.sqrt_sq (norm_nonneg _)] at hroot
    have hi := L.futureInvariant_current p.step x0 h0 (le_refl r)
    have ht : L.FutureInvariant (p.starField : HistorySpace Ω E) r := fun _ _ _ _ _ ↦ rfl
    have hc := p.correlation L v _ hr le_rfl (L.futureInvariant_sub hi ht)
    have hmul' := mul_le_mul_of_nonneg_left hroot (Real.sqrt_nonneg v.variance)
    have hdiv := div_le_div_of_nonneg_right hmul' (Real.sqrt_nonneg (m - r : ℕ))
    rw [p.linearQuery_inner L x0 h0]
    exact (le_abs_self _).trans (hc.trans hdiv)
  have hs := sum_le_sum (s := range m) (fun r hr ↦ hbound r (mem_range.mp hr))
  have he : (∑ r ∈ range m, Real.sqrt v.variance * Real.sqrt B / Real.sqrt (m - r : ℕ)) =
      (Real.sqrt v.variance * Real.sqrt B) * ∑ r ∈ range m, 1 / Real.sqrt (m - r : ℕ) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro _ _
    ring
  rw [he] at hs
  have ht := mul_le_mul_of_nonneg_left (sum_inv_sqrt_remaining (le_refl m))
    (mul_nonneg (Real.sqrt_nonneg v.variance) (Real.sqrt_nonneg B))
  have hd := div_le_div_of_nonneg_right (hs.trans ht) hm0.le
  have hc := averaged_correlation_constant (sq_nonneg ‖L.current p.step x0 0 - p.starField‖)
    v.nonneg p.delta_pos p.delta_le_one hm
  unfold mean
  apply le_trans hd
  convert! hc using 1 <;> dsimp [B, R] <;> ring

theorem restartBudget_average (p : NoiseModel Z E) (L : HistoryLaw Ω Z m)
    (v : ResidualControl p L) (x0 : Ω → E) (h0 : L.StartInvariant x0) :
    mean (p.restartBudget L x0 v.variance) m ≤
      32 * ‖L.current p.step x0 0 - p.starField‖ ^ 2 / (m * p.δ ^ 2) +
        474 * v.variance / p.δ ^ 3 := by
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne m)
  apply averaged_restart_budget hm p.delta_pos p.delta_le_one p.alpha_lt_two.le
    (sq_nonneg _) v.nonneg (L.queriedLoss p.h p.step x0)
  · have he := p.radius_budget L v x0 h0 (le_refl m)
    have hh : (∑ j ∈ range m, L.queriedLoss p.h p.step x0 j) =
        ∑ j ∈ range m, p.lossAt L (j : Fin m) (L.current p.step x0 j) := by
      apply sum_congr rfl
      intro j _
      exact L.queriedLoss_forward p.h p.step x0 h0 j
    rw [hh]
    nlinarith only [he, sq_nonneg ‖L.current p.step x0 m - p.starField‖]
  · have he : mean (p.restartBudget L x0 v.variance) m =
        16 / p.δ * mean (L.queriedLoss p.h p.step x0) m +
          (34 + 8 * p.α / p.δ) * v.variance := by
      unfold mean restartBudget
      simp only [sum_add_distrib, ← sum_div, ← mul_sum, sum_const, card_range, nsmul_eq_mul]
      field_simp
    rw [he]
    linear_combination 8 * v.nonneg

theorem queried_loss_bound (p : NoiseModel Z E) (L : HistoryLaw Ω Z m)
    (v : ResidualControl p L) (x0 : Ω → E) (h0 : L.StartInvariant x0)
    {M : ℕ} (hmM : m ≤ M) :
    L.queriedLoss p.loss p.step x0 (m - 1) ≤ 35000 * polylog M *
      (‖L.current p.step x0 0 - p.starField‖ ^ 2 / (m * p.δ ^ 3) + v.variance / p.δ ^ 4) := by
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  apply noisy_query_bound (p.linearQuery L x0) (p.restartBudget L x0 v.variance) hm hmM
    p.delta_pos p.delta_le_one (sq_nonneg _) v.nonneg
  · intro r hr
    let : NeZero (m - r) := ⟨by omega⟩
    let Lr := L.restart r
    let vr : ResidualControl p Lr := v.restrict (HistoryLaw.tailEmbedding r m)
    let xr := fun ω ↦ L.current p.step x0 r ω
    have hxr : Lr.StartInvariant xr := L.restart_start p.step x0 h0 (Nat.le_of_lt hr)
    have hh := p.history_amplification Lr vr xr hxr (show m - r ≤ M by omega)
    change (L.restart r).queriedLoss p.loss p.step xr (m - r - 1) ≤
      p.initialLinear (L.restart r) xr +
        73 * polylog M * (p.budget (L.restart r) xr v.variance / p.δ) at hh
    unfold initialLinear budget at hh
    dsimp only [xr] at hh
    rw [L.restart_query p.loss p.step x0 h0 (r := r) (s := m - r - 1)
        (Nat.le_of_lt hr) (by omega),
      L.restart_query (fun z x ↦ ⟪p.ζ z, x - p.star⟫) p.step x0 h0
        (r := r) (s := 0) (Nat.le_of_lt hr) (by omega),
      L.restart_query p.h p.step x0 h0 (r := r) (s := 0) (Nat.le_of_lt hr) (by omega)] at hh
    have hi : r + (m - r - 1) = m - 1 := by omega
    rw [hi, Nat.add_zero] at hh
    dsimp [linearQuery, restartBudget]
    convert! hh using 1 <;> ring
  · exact p.linearQuery_average L v x0 h0
  · exact p.restartBudget_average L v x0 h0

theorem queried_gradient_bound (p : NoiseModel Z E) (L : HistoryLaw Ω Z m)
    (v : ResidualControl p L) (x0 : Ω → E) (h0 : L.StartInvariant x0)
    {M : ℕ} (hmM : m ≤ M) :
    ‖L.queriedGradient p.g x0 (m - 1)‖ ^ 2 ≤ 21000 * ell M ^ 2 *
      (‖L.current p.step x0 0 - p.starField‖ ^ 2 / (m * p.δ ^ 3) + v.variance / p.δ ^ 4) := by
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hcoeff : 0 ≤ 44 * ell M ^ 2 / p.δ :=
    div_nonneg (by positivity) p.delta_pos.le
  have hrestart (r : ℕ) (hr : r < m) : ‖L.queriedGradient p.g x0 (m - 1)‖ ^ 2 ≤
      (0 : ℝ) + (44 * ell M ^ 2 / p.δ) * p.restartBudget L x0 v.variance r := by
    let : NeZero (m - r) := ⟨by omega⟩
    let Lr := L.restart r
    let vr : ResidualControl p Lr := v.restrict (HistoryLaw.tailEmbedding r m)
    let xr := fun ω ↦ L.current p.step x0 r ω
    have hxr : Lr.StartInvariant xr := L.restart_start p.step x0 h0 (Nat.le_of_lt hr)
    have hh := p.gradient_uniform Lr vr xr hxr (show m - r ≤ M by omega)
      (show m - r - 1 < m - r by omega)
    change ‖(L.restart r).queriedGradient p.g xr (m - r - 1)‖ ^ 2 ≤
      44 * ell M ^ 2 * (p.budget (L.restart r) xr v.variance / p.δ) at hh
    unfold budget at hh
    dsimp only [xr] at hh
    have hg : ‖(L.restart r).queriedGradient p.g
        (fun ω ↦ L.current p.step x0 r ω) (m - r - 1)‖ ^ 2 =
        ‖L.queriedGradient p.g x0 (r + (m - r - 1))‖ ^ 2 :=
      L.restart_gradient p.g x0 h0 (Nat.le_of_lt hr) (by omega)
    rw [hg,
      L.restart_query p.h p.step x0 h0 (r := r) (s := 0) (Nat.le_of_lt hr) (by omega)] at hh
    have hi : r + (m - r - 1) = m - 1 := by omega
    rw [hi, Nat.add_zero] at hh
    dsimp [restartBudget]
    convert! hh using 1 <;> ring
  have hh := restart_average (fun _ ↦ (0 : ℝ)) (p.restartBudget L x0 v.variance) hm hrestart
  simp only [mean, sum_const_zero, zero_div, zero_add] at hh
  have hb := mul_le_mul_of_nonneg_left (p.restartBudget_average L v x0 h0) hcoeff
  have he : (44 * ell M ^ 2 / p.δ) *
      (32 * ‖L.current p.step x0 0 - p.starField‖ ^ 2 / (m * p.δ ^ 2) +
        474 * v.variance / p.δ ^ 3) =
      1408 * ell M ^ 2 * (‖L.current p.step x0 0 - p.starField‖ ^ 2 / (m * p.δ ^ 3)) +
        20856 * ell M ^ 2 * (v.variance / p.δ ^ 4) := by field_simp; ring
  rw [he] at hb
  have hR : 0 ≤ ell M ^ 2 * (‖L.current p.step x0 0 - p.starField‖ ^ 2 / (m * p.δ ^ 3)) := by
    have := p.delta_pos
    positivity
  have hV : 0 ≤ ell M ^ 2 * (v.variance / p.δ ^ 4) :=
    mul_nonneg (sq_nonneg _) (div_nonneg v.nonneg (pow_nonneg p.delta_pos.le _))
  change _ ≤ _ at hh
  unfold mean at hb
  nlinarith only [hh, hb, hR, hV]

theorem gradient_energy (p : NoiseModel Z E) (L : HistoryLaw Ω Z m)
    (v : ResidualControl p L) (x0 : Ω → E) (h0 : L.StartInvariant x0) :
    (∑ j ∈ range m, ‖L.queriedGradient p.g x0 j‖ ^ 2) ≤
      8 * p.α * ‖L.current p.step x0 0 - p.starField‖ ^ 2 / p.δ +
        (104 * p.α / p.δ ^ 2 + 2) * m * v.variance := by
  have he := p.radius_budget L v x0 h0 (le_refl m)
  have hl : (∑ j ∈ range m, p.lossAt L (j : Fin m) (L.current p.step x0 j)) ≤
      (2 * ‖L.current p.step x0 0 - p.starField‖ ^ 2 + 26 * m * v.variance / p.δ) / p.δ := by
    apply (le_div_iff₀ p.delta_pos).mpr
    nlinarith only [he, sq_nonneg ‖L.current p.step x0 m - p.starField‖]
  have hg := sum_le_sum (s := range m) (fun j _ ↦ p.gradient_step_bound L v x0 h0 j)
  simp only [sum_add_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul] at hg
  have hc := mul_le_mul_of_nonneg_left hl (show 0 ≤ 4 * p.α by linarith [p.alpha_pos])
  linear_combination hg + hc

end NoiseModel

end LastIterate
