module

public import LastIterate.LocalEnergy
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section

/-! # Residual-gradient geometry, before any correlation is discarded -/

namespace LastIterate

open Finset
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Pairwise nonpositive residual correlations give a variance bound for every sub-sum. -/
theorem norm_sum_sq_le_of_nonpos {ι : Type*} (s : Finset ι) (z : ι → E)
    (hpair : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ⟪z i, z j⟫ ≤ 0) :
    ‖∑ i ∈ s, z i‖ ^ 2 ≤ ∑ i ∈ s, ‖z i‖ ^ 2 := by
  classical
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  apply sum_le_sum
  intro i hi
  rw [inner_sum]
  calc
    ∑ j ∈ s, ⟪z i, z j⟫ ≤ ∑ j ∈ s, if j = i then ‖z i‖ ^ 2 else 0 := by
      apply sum_le_sum
      intro j hj
      by_cases he : j = i
      · subst j
        simp only [if_pos rfl, real_inner_self_eq_norm_sq]
        exact le_rfl
      · rw [if_neg he]
        exact hpair i hi j hj (Ne.symm he)
    _ = ‖z i‖ ^ 2 := by simp [hi]

theorem norm_average_sq_le_of_nonpos {ι : Type*} (s : Finset ι) (z : ι → E)
    {v : ℝ} (hs : 0 < s.card) (hdiag : ∀ i ∈ s, ‖z i‖ ^ 2 ≤ v)
    (hpair : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ⟪z i, z j⟫ ≤ 0) :
    ‖(s.card : ℝ)⁻¹ • ∑ i ∈ s, z i‖ ^ 2 ≤ v / s.card := by
  have hn : (0 : ℝ) < s.card := by exact_mod_cast hs
  have hh := (norm_sum_sq_le_of_nonpos s z hpair).trans
    (sum_le_sum (fun i hi ↦ hdiag i hi))
  simp only [sum_const, nsmul_eq_mul] at hh
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn), mul_pow]
  have hc := mul_le_mul_of_nonneg_left hh (sq_nonneg (s.card : ℝ)⁻¹)
  convert! hc using 1
  field_simp

/-- The curvature term is paid from loss before the residual Young inequality is applied. -/
theorem curvature_budget {q H α δ : ℝ} (hq0 : 0 ≤ q) (hH : 0 ≤ H)
    (hα : 0 < α) (hδ1 : δ ≤ 1) (hδα : δ ≤ 2 - α) (hq : q ≤ 2 * α * H) :
    (1 - α⁻¹) * q ≤ 2 * (1 - δ) * H := by
  by_cases ha1 : α ≤ 1
  · have hia : 1 ≤ α⁻¹ := (one_le_inv₀ hα).mpr ha1
    have hn := mul_nonpos_of_nonpos_of_nonneg (show 1 - α⁻¹ ≤ 0 by linarith) hq0
    have hp : 0 ≤ 2 * (1 - δ) * H := by positivity
    linarith
  · have hmul := mul_le_mul_of_nonneg_left hq (show 0 ≤ α - 1 by linarith)
    have hh : (α - 1) * q ≤ α * (2 * (1 - δ) * H) := by
      have hHα : 0 ≤ α * H := mul_nonneg hα.le hH
      nlinarith [mul_nonneg (show 0 ≤ 2 - α - δ by linarith) hHα]
    have he : (1 - α⁻¹) * q = ((α - 1) * q) / α := by field_simp
    rw [he]
    apply (div_le_iff₀ hα).mpr
    nlinarith only [hh]

/-- Noisy displacement from an arbitrary initial point, retaining the residual correlation. -/
theorem noisy_initial_step (p q r z : E) {H H₀ α δ : ℝ}
    (hα : 0 < α) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδα : δ ≤ 2 - α)
    (hH : 0 ≤ H) (hH₀ : 0 ≤ H₀)
    (hq : ‖q‖ ^ 2 ≤ 2 * α * H) (hr : ‖r‖ ^ 2 ≤ 2 * α * H₀)
    (hinterp : H - ⟪q, p⟫ + ‖q - r‖ ^ 2 / (2 * α) ≤ H₀) :
    ‖p - q - z‖ ^ 2 - ‖p‖ ^ 2 + δ * H ≤
      8 * H₀ / δ + (1 + 4 * α / δ) * ‖z‖ ^ 2 - 2 * ⟪p, z⟫ := by
  have hc := curvature_budget (sq_nonneg ‖q‖) hH hα hδ1 hδα hq
  have hqr := inner_young q r (show 0 < δ / 4 by positivity)
  have hqz := inner_young q z (show 0 < δ / (4 * α) by positivity)
  have hq' := mul_le_mul_of_nonneg_left hq (show 0 ≤ δ / (2 * α) by positivity)
  have hqr' := div_le_div_of_nonneg_right hqr hα.le
  have hr' := mul_le_mul_of_nonneg_left hr
    (show 0 ≤ 4 / (α * δ) - 1 / α by
      apply sub_nonneg.mpr
      rw [div_le_div_iff₀ hα (mul_pos hα hδ)]
      nlinarith)
  rw [norm_sub_sq_real] at hinterp
  rw [norm_sub_sq_real, norm_sub_sq_real, inner_sub_left, ← real_inner_comm p q]
  have he1 : (δ / (2 * α)) * (2 * α * H) = δ * H := by field_simp
  have he2 : (4 / (α * δ) - 1 / α) * (2 * α * H₀) = 8 * H₀ / δ - 2 * H₀ := by
    field_simp
    ring
  rw [he1] at hq'
  rw [he2] at hr'
  have he4 : ‖z‖ ^ 2 / (δ / (4 * α)) = 4 * α / δ * ‖z‖ ^ 2 := by
    field_simp
  rw [he4] at hqz
  simp only [add_div, div_div] at hqr'
  have he5 : (δ / 4 * ‖q‖ ^ 2) / α = δ / (4 * α) * ‖q‖ ^ 2 := by ring
  have he6 : ‖r‖ ^ 2 / (δ / 4 * α) = 4 / (α * δ) * ‖r‖ ^ 2 := by
    field_simp
  rw [he5, he6] at hqr'
  have hinterp' : 2 * H - 2 * ⟪q, p⟫ + ‖q‖ ^ 2 / α -
      2 * ⟪q, r⟫ / α + ‖r‖ ^ 2 / α ≤ 2 * H₀ := by
    linear_combination 2 * hinterp
  have hq'' : δ / (4 * α) * ‖q‖ ^ 2 + δ / (4 * α) * ‖q‖ ^ 2 ≤ δ * H := by
    linear_combination hq'
  have hc' : ‖q‖ ^ 2 - ‖q‖ ^ 2 / α ≤ 2 * (1 - δ) * H := by
    simpa only [sub_mul, one_mul, inv_mul_eq_div] using hc
  linear_combination hinterp' + hc' + hqr' + hqz + hq'' + hr'

end LastIterate
