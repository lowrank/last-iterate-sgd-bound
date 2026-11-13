module

public import LastIterate.Geometry
public import Mathlib.Algebra.BigOperators.Intervals

@[expose] public section

/-!
# From frozen histories to geometric suffix comparisons

This file handles the reversal of indices between the forward SGD loss sequence and
the suffix-average rate engine. It also proves the deterministic deletion contraction.
-/

namespace LastIterate

open Finset

theorem reverse_suffix_sum (a : ℕ → ℝ) {m l : ℕ} (hlm : l ≤ m) :
    (∑ i ∈ range l, a (m - 1 - i)) = ∑ i ∈ range l, a (m - l + i) := by
  calc
    (∑ i ∈ range l, a (m - 1 - i)) =
        ∑ i ∈ range l, a (m - l + (l - 1 - i)) := by
      apply sum_congr rfl
      intro i hi
      have hi' := mem_range.mp hi
      congr 1
      omega
    _ = _ := sum_range_reflect (fun i ↦ a (m - l + i)) l

theorem window_of_frozen (a k : ℕ → ℝ) {m : ℕ} {B D : ℝ}
    (hgrad : ∀ i < m, k i ≤ B)
    (hfrozen : ∀ r s l : ℕ, r ≤ s → 0 < l → s + l ≤ m →
      (∑ i ∈ range l, (a (s + i) - k (s + i) / 2)) ≤
        l * a r + (s - r : ℕ) * D / 2) :
    WindowComparison (fun i ↦ a (m - 1 - i)) m (B / 2) (D / 2) := by
  intro l j hl hj
  have hlm : l ≤ m := by omega
  have hf := hfrozen (m - 1 - (l + j)) (m - l) l (by omega) hl (by omega)
  have hg : (∑ i ∈ range l, k (m - l + i)) ≤ (l : ℝ) * B := by
    have hs := sum_le_sum (s := range l) (fun i hi ↦ hgrad (m - l + i) (by
      have hi' := mem_range.mp hi
      omega))
    simpa only [sum_const, card_range, nsmul_eq_mul] using hs
  have hdist : m - l - (m - 1 - (l + j)) = j + 1 := by omega
  rw [hdist, sum_sub_distrib] at hf
  have hsum : (∑ i ∈ range l, k (m - l + i) / 2) =
      (∑ i ∈ range l, k (m - l + i)) / 2 := by
    simp only [div_eq_mul_inv, sum_mul]
  rw [hsum] at hf
  rw [reverse_suffix_sum a hlm]
  push_cast at hf
  linarith

variable {E Z : Type*} [NormedAddCommGroup E]

/-- Any common sequence of nonexpansive updates preserves the initial distance bound. -/
theorem foldl_nonexpansive_sq (step : Z → E → E)
    (hstep : ∀ z x y, ‖step z x - step z y‖ ^ 2 ≤ ‖x - y‖ ^ 2)
    (labels : List Z) (x y : E) :
    ‖labels.foldl (fun u z ↦ step z u) x - labels.foldl (fun u z ↦ step z u) y‖ ^ 2 ≤
      ‖x - y‖ ^ 2 := by
  induction labels generalizing x y with
  | nil => simp
  | cons z labels ih =>
    simpa only [List.foldl_cons] using (ih (step z x) (step z y)).trans (hstep z x y)

/-- Deleting one update costs at most the squared norm of that update. -/
theorem deletion_distance (g : Z → E → E)
    (hstep : ∀ z x y, ‖(x - g z x) - (y - g z y)‖ ^ 2 ≤ ‖x - y‖ ^ 2)
    (pre suffix : List Z) (z : Z) (x0 : E) :
    let run := fun labels ↦ labels.foldl (fun x z ↦ x - g z x) x0
    ‖run (pre ++ z :: suffix) - run (pre ++ suffix)‖ ^ 2 ≤ ‖g z (run pre)‖ ^ 2 := by
  dsimp only
  rw [List.foldl_append, List.foldl_append, List.foldl_cons]
  have hh := foldl_nonexpansive_sq (fun z x ↦ x - g z x) hstep suffix
    (pre.foldl (fun x z ↦ x - g z x) x0 - g z (pre.foldl (fun x z ↦ x - g z x) x0))
    (pre.foldl (fun x z ↦ x - g z x) x0)
  simpa only [sub_sub_cancel_left, norm_neg] using hh

end LastIterate
