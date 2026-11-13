module

public import LastIterate.Exchangeable

@[expose] public section

/-! # Frozen-history inequalities derived from the concrete sampling symmetry -/

namespace LastIterate

open Finset
open scoped Fin.NatCast RealInnerProductSpace

variable {Ω Z E : Type*} {m : ℕ} [Fintype Ω] [NeZero m]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace HistoryLaw

noncomputable def queriedLoss (L : HistoryLaw Ω Z m) (f : Z → E → ℝ)
    (step : Z → E → E) (x0 : Ω → E) (k : ℕ) : ℝ :=
  liftLoss (fun ω ↦ f (L.label ω (-1))) (L.shift (-1) (L.past step x0 0 k))

noncomputable def queriedGradient (L : HistoryLaw Ω Z m) (g : Z → E → E)
    (x0 : Ω → E) (k : ℕ) : HistorySpace Ω E :=
  liftGradient (fun ω ↦ g (L.label ω (-1)))
    (L.shift (-1) (L.past (fun z x ↦ x - g z x) x0 0 k))

theorem queriedLoss_forward (L : HistoryLaw Ω Z m) (f : Z → E → ℝ)
    (step : Z → E → E) (x0 : Ω → E) (h0 : L.StartInvariant x0) (k : ℕ) :
    L.queriedLoss f step x0 k = ∑ ω, f (L.label ω (k : Fin m))
      (L.current step x0 k ω) := by
  unfold queriedLoss liftLoss
  rw [L.shift_past step x0 h0, zero_add, L.sum_past_query step x0 h0]
  congr 1
  funext ω
  congr 2
  abel

theorem frozen_query (L : HistoryLaw Ω Z m) (f : Z → E → ℝ)
    (step : Z → E → E) (x0 : Ω → E) (h0 : L.StartInvariant x0)
    {r u : ℕ} (hu : 0 < u) (hrum : r + u ≤ m) :
    liftLoss (fun ω ↦ f (L.label ω (-1)))
      (L.past step x0 (-(u : Fin m)) r) = L.queriedLoss f step x0 r := by
  unfold liftLoss
  rw [L.sum_past_query step x0 h0, L.queriedLoss_forward f step x0 h0]
  have hrm : r < m := by omega
  have him : r + u - 1 < m := by omega
  have hi : (-1 : Fin m) + (r : Fin m) - -(u : Fin m) =
      ((r + u - 1 : ℕ) : Fin m) := by
    have he := congrArg (fun q : ℕ ↦ (q : Fin m))
      (show r + u - 1 + 1 = r + u by omega)
    simp only [Nat.cast_add, Nat.cast_one] at he
    rw [eq_sub_of_add_eq he]
    abel
  rw [hi]
  apply L.sum_future_query step x0 h0 f
  · simp only [Fin.val_natCast, Nat.mod_eq_of_lt him]
    omega
  · simp only [Fin.val_natCast, Nat.mod_eq_of_lt hrm]
    exact le_rfl

set_option maxHeartbeats 1000000 in
/-- The actual WR/WOR histories satisfy the frozen comparison; it is not assumed. -/
theorem frozen_comparison (L : HistoryLaw Ω Z m) (f : Z → E → ℝ)
    (g : Z → E → E) (x0 : Ω → E) (h0 : L.StartInvariant x0)
    {α : ℝ} (hα : 0 < α) (hf : ∀ z, SmoothInterpolation (f z) (g z) α)
    {r s l : ℕ} (hrs : r ≤ s) (hsl : s + l ≤ m) :
    (∑ j ∈ range l, (L.queriedLoss f (fun z x ↦ x - g z x) x0 (s + j) -
      ‖L.queriedGradient g x0 (s + j)‖ ^ 2 / 2)) ≤
        l * L.queriedLoss f (fun z x ↦ x - g z x) x0 r +
          ‖L.past (fun z x ↦ x - g z x) x0 0 s -
            L.past (fun z x ↦ x - g z x) x0 0 r‖ ^ 2 / 2 := by
  let step := fun z x ↦ x - g z x
  let X := L.past step x0 0
  let Y := fun t ↦ L.past step x0 (-((t - s : ℕ) : Fin m)) r
  let G := L.queriedGradient g x0
  let R : HistorySpace Ω E → HistorySpace Ω E := L.shift (-1)
  let a := L.queriedLoss f step x0
  have hsmooth := lift_interpolation (fun ω ↦ f (L.label ω (-1)))
    (fun ω ↦ g (L.label ω (-1))) (fun ω ↦ hf (L.label ω (-1)))
  have hX (j : ℕ) (_ : j < l) : X (s + j + 1) = R (X (s + j)) - G (s + j) :=
    L.past_succ g x0 h0 (s + j)
  have hY (j : ℕ) (_ : j < l) : Y (s + j + 1) = R (Y (s + j)) := by
    dsimp [Y, R]
    rw [L.shift_past step x0 h0]
    have h1 : s + j + 1 - s = j + 1 := by omega
    have h2 : s + j - s = j := by omega
    rw [h1, h2]
    congr 1
    push_cast
    abel
  have hc (j : ℕ) (hj : j < l) :
      a (s + j) - a r ≤ ⟪G (s + j), R (X (s + j)) - R (Y (s + j))⟫ := by
    have hh := hsmooth (R (X (s + j))) (R (Y (s + j)))
    have hc : liftLoss (fun ω ↦ f (L.label ω (-1))) (R (Y (s + j))) = a r := by
      dsimp [R, Y]
      rw [L.shift_past step x0 h0]
      have he : -((s + j - s : ℕ) : Fin m) + (-1) = -((j + 1 : ℕ) : Fin m) := by
        rw [Nat.add_sub_cancel_left]
        push_cast
        abel
      rw [he]
      exact L.frozen_query f step x0 h0 (by omega) (by omega)
    have hn : 0 ≤
        ‖liftGradient (fun ω ↦ g (L.label ω (-1))) (R (Y (s + j))) -
          liftGradient (fun ω ↦ g (L.label ω (-1))) (R (X (s + j)))‖ ^ 2 /
            (2 * α) := by positivity
    rw [hc] at hh
    change a (s + j) + ⟪G (s + j), R (Y (s + j)) - R (X (s + j))⟫ + _ ≤ a r at hh
    simp only [inner_sub_right] at hh ⊢
    linarith
  have hh := frozen_history X Y G R a (a r)
    (fun U V ↦ by simpa only [dist_eq_norm] using (L.shift (-1)).dist_map U V)
    hX hY hc
  have hy : Y s = L.past step x0 0 r := by simp [Y]
  rw [hy] at hh
  exact hh

end HistoryLaw

end LastIterate
