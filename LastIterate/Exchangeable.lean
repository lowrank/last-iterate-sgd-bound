module

public import LastIterate.Trajectory

@[expose] public section

/-! # The cyclic-history construction on an actual exchangeable sampling space -/

namespace LastIterate

open Finset
open scoped Fin.NatCast RealInnerProductSpace

variable {Ω Z E : Type*} {m : ℕ} [Fintype Ω] [NeZero m]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace HistoryLaw

def StartInvariant (L : HistoryLaw Ω Z m) (x0 : Ω → E) : Prop :=
  ∀ e ω, x0 (L.reindex e ω) = x0 ω

theorem startInvariant_const (L : HistoryLaw Ω Z m) (x0 : E) :
    L.StartInvariant (fun _ ↦ x0) := fun _ _ ↦ rfl

theorem label_reindex_fun (L : HistoryLaw Ω Z m) (e : Equiv.Perm (Fin m)) (ω : Ω) :
    L.label (L.reindex e ω) = fun i ↦ L.label ω (e i) := by
  funext i
  exact L.label_reindex e ω i

theorem sum_invariant (L : HistoryLaw Ω Z m) (e : Equiv.Perm (Fin m)) (f : Ω → ℝ) :
    (∑ ω, f (L.reindex e ω)) = ∑ ω, f ω := Equiv.sum_comp (L.reindex e) f

noncomputable def past (L : HistoryLaw Ω Z m) (step : Z → E → E)
    (x0 : Ω → E) (a : Fin m) (k : ℕ) : HistorySpace Ω E :=
  WithLp.toLp 2 (fun ω ↦ suffix step (x0 ω) (rotateWord (L.label ω) a) k)

noncomputable def current (L : HistoryLaw Ω Z m) (step : Z → E → E)
    (x0 : Ω → E) (k : ℕ) : HistorySpace Ω E :=
  WithLp.toLp 2 (fun ω ↦ forward step (x0 ω) (fun i ↦ L.label ω (i : Fin m)) k)

noncomputable def shift (L : HistoryLaw Ω Z m) (a : Fin m) :
    HistorySpace Ω E ≃ₗᵢ[ℝ] HistorySpace Ω E :=
  historyShift (L.reindex (Equiv.addRight a))

@[simp] theorem past_apply (L : HistoryLaw Ω Z m) (step : Z → E → E)
    (x0 : Ω → E) (a : Fin m) (k : ℕ) (ω : Ω) :
    L.past step x0 a k ω = suffix step (x0 ω) (rotateWord (L.label ω) a) k := rfl

@[simp] theorem current_apply (L : HistoryLaw Ω Z m) (step : Z → E → E)
    (x0 : Ω → E) (k : ℕ) (ω : Ω) :
    L.current step x0 k ω = forward step (x0 ω) (fun i ↦ L.label ω (i : Fin m)) k := rfl

theorem shift_past (L : HistoryLaw Ω Z m) (step : Z → E → E)
    (x0 : Ω → E) (h0 : L.StartInvariant x0) (a b : Fin m) (k : ℕ) :
    L.shift a (L.past step x0 b k) = L.past step x0 (b + a) k := by
  change ∀ e ω, x0 (L.reindex e ω) = x0 ω at h0
  ext ω
  change suffix step (x0 (L.reindex (Equiv.addRight a) ω))
    (rotateWord (L.label (L.reindex (Equiv.addRight a) ω)) b) k =
      suffix step (x0 ω) (rotateWord (L.label ω) (b + a)) k
  rw [h0, label_reindex_fun]
  have he : rotateWord (fun i ↦ L.label ω ((Equiv.addRight a) i)) b =
      rotateWord (L.label ω) (b + a) := by
    funext i
    simp only [rotateWord, Equiv.coe_addRight, add_assoc]
  rw [he]

theorem past_succ (L : HistoryLaw Ω Z m) (g : Z → E → E)
    (x0 : Ω → E) (h0 : L.StartInvariant x0) (k : ℕ) :
    L.past (fun z x ↦ x - g z x) x0 0 (k + 1) =
      L.shift (-1) (L.past (fun z x ↦ x - g z x) x0 0 k) -
        liftGradient (fun ω ↦ g (L.label ω (-1)))
          (L.shift (-1) (L.past (fun z x ↦ x - g z x) x0 0 k)) := by
  rw [shift_past L _ x0 h0, zero_add]
  ext ω
  change suffix (fun z x ↦ x - g z x) (x0 ω) (rotateWord (L.label ω) 0) (k + 1) =
    suffix (fun z x ↦ x - g z x) (x0 ω) (rotateWord (L.label ω) (-1)) k -
      g (L.label ω (-1))
        (suffix (fun z x ↦ x - g z x) (x0 ω) (rotateWord (L.label ω) (-1)) k)
  rw [rotateWord_zero, suffix_succ]

/-- A shifted suffix query has the same law as the corresponding forward query. -/
theorem sum_past_query (L : HistoryLaw Ω Z m) (step : Z → E → E)
    (x0 : Ω → E) (h0 : L.StartInvariant x0) (f : Z → E → ℝ)
    (a b : Fin m) (k : ℕ) :
    (∑ ω, f (L.label ω a) (L.past step x0 b k ω)) =
      ∑ ω, f (L.label ω (a + (k : Fin m) - b)) (L.current step x0 k ω) := by
  change ∀ e ω, x0 (L.reindex e ω) = x0 ω at h0
  have hh := L.sum_invariant (Equiv.addRight ((k : Fin m) - b))
    (fun ω ↦ f (L.label ω a) (L.past step x0 b k ω))
  rw [← hh]
  apply sum_congr rfl
  intro ω _
  rw [L.label_reindex, past_apply, h0, L.label_reindex_fun]
  simp only [Equiv.coe_addRight]
  have he : rotateWord (fun i ↦ L.label ω (i + ((k : Fin m) - b))) b =
      rotateWord (L.label ω) (k : Fin m) := by
    funext i
    unfold rotateWord
    congr 1
    abel
  rw [he, suffix_forward]
  congr 2
  abel

theorem current_swap (L : HistoryLaw Ω Z m) (step : Z → E → E)
    (x0 : Ω → E) (h0 : L.StartInvariant x0) {k : ℕ} (i j : Fin m)
    (hi : k ≤ i.val) (hj : k ≤ j.val) (ω : Ω) :
    L.current step x0 k (L.reindex (Equiv.swap i j) ω) = L.current step x0 k ω := by
  change ∀ e ω, x0 (L.reindex e ω) = x0 ω at h0
  simp only [current_apply, h0, label_reindex]
  apply forward_congr
  intro q hq
  have hqm : q < m := lt_of_lt_of_le hq (le_trans hi (Nat.le_of_lt i.isLt))
  have hqi : (q : Fin m) ≠ i := by
    intro he
    have hv := congrArg Fin.val he
    simp only [Fin.val_natCast, Nat.mod_eq_of_lt hqm] at hv
    omega
  have hqj : (q : Fin m) ≠ j := by
    intro he
    have hv := congrArg Fin.val he
    simp only [Fin.val_natCast, Nat.mod_eq_of_lt hqm] at hv
    omega
  rw [Equiv.swap_apply_of_ne_of_ne hqi hqj]

/-- All query coordinates after a fixed prefix give the same expected loss. -/
theorem sum_future_query (L : HistoryLaw Ω Z m) (step : Z → E → E)
    (x0 : Ω → E) (h0 : L.StartInvariant x0) (f : Z → E → ℝ)
    {k : ℕ} (i j : Fin m) (hi : k ≤ i.val) (hj : k ≤ j.val) :
    (∑ ω, f (L.label ω i) (L.current step x0 k ω)) =
      ∑ ω, f (L.label ω j) (L.current step x0 k ω) := by
  have hh := L.sum_invariant (Equiv.swap i j)
    (fun ω ↦ f (L.label ω i) (L.current step x0 k ω))
  simpa only [L.label_reindex, Equiv.swap_apply_left,
    L.current_swap step x0 h0 i j hi hj] using hh.symm

theorem past_distance (L : HistoryLaw Ω Z m) (step : Z → E → E)
    (x0 : Ω → E) (h0 : L.StartInvariant x0)
    (hs : ∀ z x y, ‖step z x - step z y‖ ^ 2 ≤ ‖x - y‖ ^ 2) (s r : ℕ) :
    ‖L.past step x0 0 (s + r) - L.past step x0 0 r‖ ^ 2 ≤
      ‖L.past step x0 0 s - L.past step x0 0 0‖ ^ 2 := by
  change ∀ e ω, x0 (L.reindex e ω) = x0 ω at h0
  rw [history_norm_sq, history_norm_sq]
  have hh := sum_le_sum (s := univ) (fun ω _ ↦
    suffix_nonexpansive step hs (x0 ω) (L.label ω) s r)
  have he : (∑ ω, ‖suffix step (x0 ω)
      (rotateWord (L.label ω) (-(r : Fin m))) s - x0 ω‖ ^ 2) =
      ∑ ω, ‖suffix step (x0 ω) (L.label ω) s - x0 ω‖ ^ 2 := by
    have hp := L.sum_invariant (Equiv.addRight (-(r : Fin m)))
      (fun ω ↦ ‖suffix step (x0 ω) (L.label ω) s - x0 ω‖ ^ 2)
    simp only [h0, L.label_reindex_fun, Equiv.coe_addRight] at hp
    exact hp
  rw [he] at hh
  simpa only [PiLp.sub_apply, past_apply, rotateWord_zero, suffix_zero] using hh

end HistoryLaw

end LastIterate
