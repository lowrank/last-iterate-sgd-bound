module

public import LastIterate.Dyadic

@[expose] public section

/-!
# Local geometry and frozen-history telescoping

The smooth convex interpolation inequality is kept explicitly in the local lemmas.
The frozen comparator is allowed to move by the same isometry as the lifted histories.
-/

namespace LastIterate

open Finset
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The exact first-order interpolation inequality for convex, `α`-smooth losses. -/
def SmoothInterpolation (f : E → ℝ) (g : E → E) (α : ℝ) : Prop :=
  ∀ x y, f y ≥ f x + ⟪g x, y - x⟫ + ‖g y - g x‖ ^ 2 / (2 * α)

theorem cocoercive_of_interpolation {f : E → ℝ} {g : E → E} {α : ℝ}
    (h : SmoothInterpolation f g α) (x y : E) :
    ‖g x - g y‖ ^ 2 / α ≤ ⟪g x - g y, x - y⟫ := by
  have hxy := h x y
  have hyx := h y x
  rw [norm_sub_rev (g y) (g x)] at hxy
  simp only [inner_sub_left, inner_sub_right] at *
  have he : ‖g x - g y‖ ^ 2 / α = 2 * (‖g x - g y‖ ^ 2 / (2 * α)) := by ring
  rw [he]
  linarith

/-- Nonexpansiveness with the gradient-difference term retained. -/
theorem firm_step {f : E → ℝ} {g : E → E} {α : ℝ}
    (h : SmoothInterpolation f g α) (hα : 0 < α) (x y : E) :
    ‖(x - g x) - (y - g y)‖ ^ 2 + ((2 - α) / α) * ‖g x - g y‖ ^ 2 ≤
      ‖x - y‖ ^ 2 := by
  have hc := cocoercive_of_interpolation h x y
  rw [show (x - g x) - (y - g y) = (x - y) - (g x - g y) by abel,
    norm_sub_sq_real, ← real_inner_comm (x - y) (g x - g y)]
  have hid : ((2 - α) / α) * ‖g x - g y‖ ^ 2 =
      2 * (‖g x - g y‖ ^ 2 / α) - ‖g x - g y‖ ^ 2 := by field_simp
  rw [hid]
  linarith

theorem nonexpansive_step {f : E → ℝ} {g : E → E} {α : ℝ}
    (h : SmoothInterpolation f g α) (hα : 0 < α) (hα2 : α ≤ 2) (x y : E) :
    ‖(x - g x) - (y - g y)‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
  have hh := firm_step h hα x y
  have hc : 0 ≤ ((2 - α) / α) * ‖g x - g y‖ ^ 2 := by positivity
  linarith

/-- Convexity is the only loss assumption needed by the frozen comparator. -/
theorem frozen_step (u v g : E) {a c : ℝ} (h : a - c ≤ ⟪g, u - v⟫) :
    ‖(u - g) - v‖ ^ 2 + 2 * a - ‖g‖ ^ 2 ≤ ‖u - v‖ ^ 2 + 2 * c := by
  rw [show (u - g) - v = (u - v) - g by abel, norm_sub_sq_real,
    ← real_inner_comm (u - v) g]
  linarith

omit [InnerProductSpace ℝ E] [NormedAddCommGroup E] in
theorem telescope (D a k : ℕ → ℝ) (c : ℝ) {s l : ℕ}
    (h : ∀ j < l, D (s + j + 1) + 2 * a (s + j) - k (s + j) ≤
      D (s + j) + 2 * c) :
    D (s + l) + 2 * (∑ j ∈ range l, (a (s + j) - k (s + j) / 2)) ≤
      D s + 2 * l * c := by
  induction l with
  | zero => simp
  | succ l ih =>
    have hi := ih (fun j hj ↦ h j (by omega))
    have hs := h l (by omega)
    rw [sum_range_succ]
    push_cast
    have he : s + (l + 1) = s + l + 1 := by omega
    rw [he]
    linarith

/-- The frozen-history estimate in the invariant Hilbert space. -/
theorem frozen_history (X Y G : ℕ → E) (R : E → E) (a : ℕ → ℝ) (c : ℝ)
    {s l : ℕ}
    (hR : ∀ x y, ‖R x - R y‖ = ‖x - y‖)
    (hX : ∀ j < l, X (s + j + 1) = R (X (s + j)) - G (s + j))
    (hY : ∀ j < l, Y (s + j + 1) = R (Y (s + j)))
    (hc : ∀ j < l, a (s + j) - c ≤
      ⟪G (s + j), R (X (s + j)) - R (Y (s + j))⟫) :
    (∑ j ∈ range l, (a (s + j) - ‖G (s + j)‖ ^ 2 / 2)) ≤
      l * c + ‖X s - Y s‖ ^ 2 / 2 := by
  have hs := telescope (fun j ↦ ‖X j - Y j‖ ^ 2) a (fun j ↦ ‖G j‖ ^ 2) c
    (s := s) (l := l) (fun j hj ↦ by
      have hh := frozen_step (R (X (s + j))) (R (Y (s + j))) (G (s + j)) (hc j hj)
      rw [hX j hj, hY j hj, ← hR (X (s + j)) (Y (s + j))]
      exact hh)
  nlinarith [sq_nonneg ‖X (s + l) - Y (s + l)‖]

/-- The lag-energy sum, retaining the terminal distance instead of dropping it. -/
theorem lag_energy (X G : ℕ → E) (R : E → E) (f : E → ℝ) (g : E → E)
    {α : ℝ} (hα : 0 < α) (h : SmoothInterpolation f g α)
    (hR : ∀ x y, ‖R x - R y‖ = ‖x - y‖)
    (hX : ∀ k, X (k + 1) = R (X k) - G k)
    (hG : ∀ k, G k = g (R (X k))) (s l : ℕ) :
    ‖X (s + l) - X l‖ ^ 2 + ((2 - α) / α) *
      (∑ j ∈ range l, ‖G (s + j) - G j‖ ^ 2) ≤ ‖X s - X 0‖ ^ 2 := by
  induction l with
  | zero => simp
  | succ l ih =>
    have hh := firm_step h hα (R (X (s + l))) (R (X l))
    rw [← hG (s + l), ← hG l, ← hX (s + l), ← hX l, hR] at hh
    rw [sum_range_succ]
    have he : s + (l + 1) = s + l + 1 := by omega
    rw [he]
    linarith

theorem interpolation_energy (f : ℕ → E → ℝ) (g : ℕ → E → E) (x : ℕ → E)
    (xstar : E) (hsmooth : ∀ j, SmoothInterpolation (f j) (g j) 1)
    (hzero : ∀ j, f j xstar = 0) (hgzero : ∀ j, g j xstar = 0)
    (hupdate : ∀ j, x (j + 1) = x j - g j (x j)) (m : ℕ) :
    ‖x m - xstar‖ ^ 2 + 2 * (∑ j ∈ range m, f j (x j)) ≤ ‖x 0 - xstar‖ ^ 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hc := hsmooth m (x m) xstar
    rw [hzero m, hgzero m, zero_sub, norm_neg] at hc
    have hi : ⟪g m (x m), xstar - x m⟫ = -⟪x m - xstar, g m (x m)⟫ := by
      rw [inner_sub_right, inner_sub_left]
      rw [real_inner_comm (x m) (g m (x m)), real_inner_comm xstar (g m (x m))]
      ring
    rw [hi] at hc
    rw [sum_range_succ, hupdate m,
      show (x m - g m (x m)) - xstar = (x m - xstar) - g m (x m) by abel,
      norm_sub_sq_real]
    norm_num at hc
    linarith

end LastIterate
