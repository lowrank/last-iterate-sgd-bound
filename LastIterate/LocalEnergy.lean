module

public import LastIterate.Geometry

@[expose] public section

/-! # Deterministic local energy estimates underlying both stochastic regimes -/

namespace LastIterate

open Finset
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem self_bound_at_common_zero {f : E → ℝ} {g : E → E} {α : ℝ}
    (hα : 0 < α) (h : SmoothInterpolation f g α) {xstar : E}
    (hf : f xstar = 0) (hg : g xstar = 0) (x : E) :
    ‖g x‖ ^ 2 ≤ 2 * α * f x := by
  have hh := h xstar x
  rw [hf, hg, inner_zero_left, sub_zero, zero_add, zero_add] at hh
  have hh' := (div_le_iff₀ (show 0 < 2 * α by positivity)).mp hh
  nlinarith only [hh']

/-- Weighted Young's inequality in a real inner product space. -/
theorem inner_young (q z : E) {a : ℝ} (ha : 0 < a) :
    2 * ⟪q, z⟫ ≤ a * ‖q‖ ^ 2 + ‖z‖ ^ 2 / a := by
  have hh := sq_nonneg ‖a • q - z‖
  rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, abs_of_pos ha,
    real_inner_smul_left] at hh
  have he := div_mul_cancel₀ (‖z‖ ^ 2) (ne_of_gt ha)
  nlinarith

theorem initial_distance_step (p q r : E) {H H₀ : ℝ}
    (hinterp : H₀ ≥ H - ⟪q, p⟫ + ‖q - r‖ ^ 2 / 2)
    (hq : ‖q‖ ^ 2 ≤ 2 * H) (hr : ‖r‖ ^ 2 ≤ 2 * H₀) :
    ‖p - q‖ ^ 2 + H ≤ ‖p‖ ^ 2 + 4 * H₀ := by
  have hs := sq_nonneg ‖q - (2 : ℝ) • r‖
  rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num),
    inner_smul_right] at hs
  rw [norm_sub_sq_real] at hinterp
  rw [norm_sub_sq_real, ← real_inner_comm p q]
  nlinarith

/-- The displacement and loss estimates are proved together, before either term is dropped. -/
theorem initial_distance_energy (f : ℕ → E → ℝ) (g : ℕ → E → E) (x : ℕ → E)
    (xstar : E) (hsmooth : ∀ j, SmoothInterpolation (f j) (g j) 1)
    (hzero : ∀ j, f j xstar = 0) (hgzero : ∀ j, g j xstar = 0)
    (hupdate : ∀ j, x (j + 1) = x j - g j (x j)) (m : ℕ) :
    ‖x m - x 0‖ ^ 2 + (∑ j ∈ range m, f j (x j)) ≤ 4 * ∑ j ∈ range m, f j (x 0) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hc := hsmooth m (x m) (x 0)
    have hinner : ⟪g m (x m), x 0 - x m⟫ = -⟪g m (x m), x m - x 0⟫ := by
      simp only [inner_sub_right]
      ring
    rw [hinner, norm_sub_rev (g m (x 0)) (g m (x m))] at hc
    norm_num at hc
    have hq := self_bound_at_common_zero (by norm_num : (0 : ℝ) < 1)
      (hsmooth m) (hzero m) (hgzero m) (x m)
    have hr := self_bound_at_common_zero (by norm_num : (0 : ℝ) < 1)
      (hsmooth m) (hzero m) (hgzero m) (x 0)
    norm_num at hq hr
    have hh := initial_distance_step (x m - x 0) (g m (x m)) (g m (x 0))
      (by linarith only [hc]) hq hr
    rw [sum_range_succ, sum_range_succ, hupdate m,
      show (x m - g m (x m)) - x 0 = (x m - x 0) - g m (x m) by abel]
    linarith

theorem interpolation_gradient_energy (f : ℕ → E → ℝ) (g : ℕ → E → E) (x : ℕ → E)
    (xstar : E) (hsmooth : ∀ j, SmoothInterpolation (f j) (g j) 1)
    (hzero : ∀ j, f j xstar = 0) (hgzero : ∀ j, g j xstar = 0)
    (hupdate : ∀ j, x (j + 1) = x j - g j (x j)) (m : ℕ) :
    (∑ j ∈ range m, ‖g j (x j)‖ ^ 2) ≤ ‖x 0 - xstar‖ ^ 2 := by
  have he := interpolation_energy f g x xstar hsmooth hzero hgzero hupdate m
  have hg := sum_le_sum (s := range m) (fun j _ ↦
    self_bound_at_common_zero (by norm_num : (0 : ℝ) < 1) (hsmooth j)
      (hzero j) (hgzero j) (x j))
  simp only [mul_one, ← mul_sum] at hg
  nlinarith [sq_nonneg ‖x m - xstar‖]

/-- The noisy one-step radius estimate, with the residual/history correlation retained. -/
theorem noisy_distance_step (p q z : E) {H α δ : ℝ}
    (hα : 0 < α) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδα : δ ≤ 2 - α)
    (hH : 0 ≤ H) (hq : ‖q‖ ^ 2 ≤ 2 * α * H)
    (hinterp : 2 * H + ‖q‖ ^ 2 / α ≤ 2 * ⟪p, q⟫) :
    ‖p - q - z‖ ^ 2 - ‖p‖ ^ 2 + δ * H ≤
      (1 + 2 * α / δ) * ‖z‖ ^ 2 - 2 * ⟪p, z⟫ := by
  have hcurv : (1 - α⁻¹) * ‖q‖ ^ 2 ≤ 2 * (1 - δ) * H := by
    by_cases ha1 : α ≤ 1
    · have hia : 1 ≤ α⁻¹ := (one_le_inv₀ hα).mpr ha1
      have hn := mul_nonpos_of_nonpos_of_nonneg (show 1 - α⁻¹ ≤ 0 by linarith)
        (sq_nonneg ‖q‖)
      have hp : 0 ≤ 2 * (1 - δ) * H := by positivity
      linarith
    · have hα1 : 1 ≤ α := by linarith
      have hmul := mul_le_mul_of_nonneg_left hq (show 0 ≤ α - 1 by linarith)
      have hh : (α - 1) * ‖q‖ ^ 2 ≤ α * (2 * (1 - δ) * H) := by
        have hHα : 0 ≤ α * H := mul_nonneg hα.le hH
        nlinarith [mul_nonneg (show 0 ≤ 2 - α - δ by linarith) hHα]
      have he : (1 - α⁻¹) * ‖q‖ ^ 2 = ((α - 1) * ‖q‖ ^ 2) / α := by
        field_simp
      rw [he]
      apply (div_le_iff₀ hα).mpr
      nlinarith only [hh]
  have hy := inner_young q z (show 0 < δ / (2 * α) by positivity)
  have hself := mul_le_mul_of_nonneg_left hq (show 0 ≤ δ / (2 * α) by positivity)
  have hself' : δ / (2 * α) * ‖q‖ ^ 2 ≤ δ * H := by
    have he : δ / (2 * α) * (2 * α * H) = δ * H := by field_simp
    rwa [he] at hself
  have hy' : 2 * ⟪q, z⟫ ≤ δ * H + (2 * α / δ) * ‖z‖ ^ 2 := by
    have he : ‖z‖ ^ 2 / (δ / (2 * α)) = (2 * α / δ) * ‖z‖ ^ 2 := by
      simp only [div_div_eq_mul_div]
      ring
    rw [he] at hy
    linarith
  rw [norm_sub_sq_real, norm_sub_sq_real, inner_sub_left]
  have he : (1 - α⁻¹) * ‖q‖ ^ 2 = ‖q‖ ^ 2 - ‖q‖ ^ 2 / α := by ring
  rw [he] at hcurv
  nlinarith only [hinterp, hcurv, hy']

end LastIterate
