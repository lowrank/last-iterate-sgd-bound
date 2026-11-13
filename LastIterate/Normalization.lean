module

public import LastIterate.Geometry

@[expose] public section

/-! # Scaling and centering smooth convex losses -/

namespace LastIterate

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem scale_interpolation {f : E → ℝ} {g : E → E} {α η : ℝ}
    (hη : 0 < η) (h : SmoothInterpolation f g α) :
    SmoothInterpolation (fun x ↦ η * f x) (fun x ↦ η • g x) (η * α) := by
  intro x y
  have hh := mul_le_mul_of_nonneg_left (h x y) hη.le
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hη, real_inner_smul_left]
  have he : (η * ‖g y - g x‖) ^ 2 / (2 * (η * α)) =
      η * (‖g y - g x‖ ^ 2 / (2 * α)) := by field_simp
  rw [he]
  nlinarith only [hh]

theorem center_interpolation {f : E → ℝ} {g : E → E} {α : ℝ}
    (h : SmoothInterpolation f g α) (xstar : E) :
    SmoothInterpolation
      (fun x ↦ f x - f xstar - ⟪g xstar, x - xstar⟫)
      (fun x ↦ g x - g xstar) α := by
  intro x y
  have hh := h x y
  rw [show (g y - g xstar) - (g x - g xstar) = g y - g x by abel,
    inner_sub_left]
  simp only [inner_sub_right] at *
  linarith

theorem centered_nonnegative {f : E → ℝ} {g : E → E} {α : ℝ}
    (hα : 0 < α) (h : SmoothInterpolation f g α) (xstar x : E) :
    0 ≤ f x - f xstar - ⟪g xstar, x - xstar⟫ := by
  have hh := h xstar x
  have hp : 0 ≤ ‖g x - g xstar‖ ^ 2 / (2 * α) := by positivity
  linarith

end LastIterate
