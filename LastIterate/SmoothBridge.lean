module

public import LastIterate.Geometry
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Comp

@[expose] public section

/-!
# From the manuscript's analytic assumptions to first-order interpolation

The original hypotheses are `HasGradientAt`, convexity, and a Lipschitz gradient.
The strong interpolation inequality used by the history estimates is derived here,
not postulated as an additional assumption on the losses.
-/

namespace LastIterate

open Set
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem hasDerivAt_line {f : E → ℝ} {g : E → E}
    (hg : ∀ x, HasGradientAt f (g x) x) (x d : E) (t : ℝ) :
    HasDerivAt (fun t : ℝ ↦ f (x + t • d)) ⟪g (x + t • d), d⟫ t := by
  have hd : HasDerivAt (fun t : ℝ ↦ x + t • d) d t := by
    simpa only [one_smul, id_eq] using ((hasDerivAt_id t).smul_const d).const_add x
  exact (hg (x + t • d)).hasFDerivAt.comp_hasDerivAt t hd

theorem convex_first_order {f : E → ℝ} {g : E → E}
    (hg : ∀ x, HasGradientAt f (g x) x) (hf : ConvexOn ℝ univ f) (x y : E) :
    f x + ⟪g x, y - x⟫ ≤ f y := by
  let d := y - x
  have hline : ConvexOn ℝ univ (fun t : ℝ ↦ f (x + t • d)) := by
    refine ⟨convex_univ, ?_⟩
    intro t _ u _ a b ha hb hab
    have hh := hf.2 (mem_univ (x + t • d)) (mem_univ (x + u • d)) ha hb hab
    have he : a • (x + t • d) + b • (x + u • d) = x + (a * t + b * u) • d := by
      calc
        _ = (a + b) • x + (a * t + b * u) • d := by module
        _ = _ := by rw [hab, one_smul]
    rw [he] at hh
    exact hh
  have hh := hline.le_slope_of_hasDerivAt (mem_univ (0 : ℝ)) (mem_univ (1 : ℝ))
    (by norm_num) (hasDerivAt_line hg x d 0)
  simp only [slope, zero_smul, add_zero, one_smul, sub_zero, inv_one, one_smul] at hh
  dsimp [d] at hh
  simp only [add_sub_cancel] at hh
  linarith

theorem smooth_upper {f : E → ℝ} {g : E → E} {α : ℝ}
    (hg : ∀ x, HasGradientAt f (g x) x)
    (hs : ∀ x y, ‖g x - g y‖ ≤ α * ‖x - y‖) (x y : E) :
    f y ≤ f x + ⟪g x, y - x⟫ + (α / 2) * ‖y - x‖ ^ 2 := by
  let d := y - x
  let u : ℝ → ℝ := fun t ↦ f (x + t • d) - t * ⟪g x, d⟫ - (α / 2) * t ^ 2 * ‖d‖ ^ 2
  have hder (t : ℝ) : HasDerivAt u
      (⟪g (x + t • d), d⟫ - ⟪g x, d⟫ - α * t * ‖d‖ ^ 2) t := by
    have hh := ((hasDerivAt_line hg x d t).sub
      ((hasDerivAt_id t).mul_const ⟪g x, d⟫)).sub
      ((((hasDerivAt_id t).pow 2).const_mul (α / 2)).mul_const (‖d‖ ^ 2))
    convert! hh using 1
    norm_num only [id_eq, pow_one, Nat.reduceSub, Nat.cast_ofNat, one_mul, mul_one]
    ring
  have hder_nonpos (t : ℝ) (ht : 0 ≤ t) :
      ⟪g (x + t • d), d⟫ - ⟪g x, d⟫ - α * t * ‖d‖ ^ 2 ≤ 0 := by
    have hg' := hs (x + t • d) x
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht] at hg'
    have hi := real_inner_le_norm (g (x + t • d) - g x) d
    rw [inner_sub_left] at hi
    have hh := mul_le_mul_of_nonneg_right hg' (norm_nonneg d)
    nlinarith
  have hanti : AntitoneOn u (Icc 0 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
    · exact (continuous_iff_continuousAt.mpr (fun t ↦ (hder t).continuousAt)).continuousOn
    · exact fun t _ ↦ (hder t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hder t).deriv]
      exact hder_nonpos t (interior_subset ht).1
  have hh := hanti (show (0 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num)
    (show (1 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num) (by norm_num)
  dsimp [u, d] at hh
  simp only [zero_smul, add_zero, one_smul, add_sub_cancel, one_pow, mul_one,
    zero_mul, zero_pow (by omega : (2 : ℕ) ≠ 0), sub_zero] at hh
  linarith

/-- Strong convex-smooth interpolation follows from the original analytic assumptions. -/
theorem smoothInterpolation_of_convex_smooth {f : E → ℝ} {g : E → E} {α : ℝ}
    (hα : 0 < α) (hg : ∀ x, HasGradientAt f (g x) x)
    (hf : ConvexOn ℝ univ f) (hs : ∀ x y, ‖g x - g y‖ ≤ α * ‖x - y‖) :
    SmoothInterpolation f g α := by
  intro x y
  let p := g y - g x
  let v := y - α⁻¹ • p
  have hc := convex_first_order hg hf x v
  have hu := smooth_upper hg hs y v
  have hvy : v - y = -(α⁻¹ • p) := by dsimp [v]; abel
  have hvx : v - x = (y - x) - α⁻¹ • p := by dsimp [v]; abel
  rw [hvy, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hα),
    inner_neg_right, inner_smul_right] at hu
  rw [hvx, inner_sub_right, inner_smul_right] at hc
  have hp : ⟪g y, p⟫ - ⟪g x, p⟫ = ‖p‖ ^ 2 := by
    rw [← inner_sub_left]
    exact real_inner_self_eq_norm_sq p
  have hid : α⁻¹ * (⟪g y, p⟫ - ⟪g x, p⟫) -
      (α / 2) * (α⁻¹ * ‖p‖) ^ 2 = ‖p‖ ^ 2 / (2 * α) := by
    rw [hp]
    field_simp
    ring
  change f x + ⟪g x, y - x⟫ + ‖p‖ ^ 2 / (2 * α) ≤ f y
  rw [← hid]
  nlinarith only [hc, hu]

end LastIterate
