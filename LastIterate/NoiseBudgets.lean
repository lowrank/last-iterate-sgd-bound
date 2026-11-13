module

public import LastIterate.NoiseModel

@[expose] public section

/-! # Noisy energy budgets with the sampling correlations proved explicitly -/

namespace LastIterate

open Finset
open scoped Fin.NatCast RealInnerProductSpace

variable {Ω Z E : Type*} {m : ℕ} [Fintype Ω] [NeZero m]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

structure ResidualControl (p : NoiseModel Z E) (L : HistoryLaw Ω Z m) where
  variance : ℝ
  nonneg : 0 ≤ variance
  diagonal : ∀ i, ‖L.residual p.ζ i‖ ^ 2 ≤ variance
  cross : ∀ i j, i ≠ j → ⟪L.residual p.ζ i, L.residual p.ζ j⟫ ≤ 0

namespace NoiseModel

theorem correlation (p : NoiseModel Z E) (L : HistoryLaw Ω Z m) (v : ResidualControl p L)
    (U : HistorySpace Ω E) {j s : ℕ} (hjs : j < s) (hsm : s ≤ m)
    (hU : L.FutureInvariant U j) :
    |⟪L.residual p.ζ (j : Fin m), U⟫| ≤
      Real.sqrt v.variance * ‖U‖ / Real.sqrt (s - j : ℕ) := by
  have hh := L.residual_correlation p.ζ v.nonneg v.diagonal v.cross U (by omega) hU
  apply hh.trans
  apply div_le_div_of_nonneg_left (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
  · apply Real.sqrt_pos.mpr
    exact_mod_cast (show 0 < s - j by omega)
  · apply Real.sqrt_le_sqrt
    exact_mod_cast (show s - j ≤ m - j by omega)

theorem radius_budget (p : NoiseModel Z E) (L : HistoryLaw Ω Z m) (v : ResidualControl p L)
    (x0 : Ω → E) (h0 : L.StartInvariant x0) {s : ℕ} (hsm : s ≤ m) :
    ‖L.current p.step x0 s - p.starField‖ ^ 2 +
      p.δ * (∑ j ∈ range s, p.lossAt L (j : Fin m) (L.current p.step x0 j)) ≤
        2 * ‖L.current p.step x0 0 - p.starField‖ ^ 2 + 26 * s * v.variance / p.δ := by
  let D := fun j ↦ ‖L.current p.step x0 j - p.starField‖
  let H : ℕ → ℝ := fun j ↦ p.lossAt L (j : Fin m) (L.current p.step x0 j)
  let C := (1 + 2 * p.α / p.δ) * v.variance
  have hcoef : 0 ≤ 1 + 2 * p.α / p.δ := by
    have := p.alpha_pos
    have := p.delta_pos
    positivity
  have hstep (j : ℕ) (hj : j < s) : D (j + 1) ^ 2 - D j ^ 2 + p.δ * H j ≤
      C + 2 * Real.sqrt v.variance * D j / Real.sqrt (s - j : ℕ) := by
    have hs := p.radius_step L x0 j
    have hi := L.futureInvariant_current p.step x0 h0 (le_refl j)
    have ht : L.FutureInvariant (p.starField : HistorySpace Ω E) j := fun _ _ _ _ _ ↦ rfl
    have hc := p.correlation L v _ hj hsm (L.futureInvariant_sub hi ht)
    have hd := mul_le_mul_of_nonneg_left (v.diagonal (j : Fin m)) hcoef
    rw [← real_inner_comm (L.current p.step x0 j - p.starField)
      (L.residual p.ζ (j : Fin m))] at hs
    dsimp [D, H, C]
    have ha := neg_le_abs ⟪L.residual p.ζ (j : Fin m), L.current p.step x0 j - p.starField⟫
    linear_combination hs + hd + 2 * hc + 2 * ha
  have hh := radius_drift D H p.delta_pos.le (mul_nonneg hcoef v.nonneg)
    (Real.sqrt_nonneg _) (fun _ _ ↦ norm_nonneg _)
    (fun j _ ↦ p.lossAt_nonneg L _ _) hstep
  rw [Real.sq_sqrt v.nonneg] at hh
  have hconst : 2 * C + 16 * v.variance ≤ 26 * v.variance / p.δ := by
    apply (le_div_iff₀ p.delta_pos).mpr
    have he : (2 * C + 16 * v.variance) * p.δ =
        (18 * p.δ + 4 * p.α) * v.variance := by
      dsimp [C]
      field_simp [ne_of_gt p.delta_pos]
      ring
    rw [he]
    exact mul_le_mul_of_nonneg_right (by linarith [p.delta_le_one, p.alpha_lt_two]) v.nonneg
  have hc := mul_le_mul_of_nonneg_left hconst (Nat.cast_nonneg (α := ℝ) s)
  dsimp [D, H] at hh
  linear_combination hh + hc

noncomputable def budget (p : NoiseModel Z E) (L : HistoryLaw Ω Z m)
    (x0 : Ω → E) (v : ℝ) : ℝ :=
  16 * L.queriedLoss p.h p.step x0 0 / p.δ + (34 + 8 * p.α / p.δ) * v

theorem initial_nonneg (p : NoiseModel Z E) (L : HistoryLaw Ω Z m)
    (x0 : Ω → E) : 0 ≤ L.queriedLoss p.h p.step x0 0 :=
  sum_nonneg (fun ω _ ↦ p.nonneg _ _)

theorem budget_nonneg (p : NoiseModel Z E) (L : HistoryLaw Ω Z m)
    (x0 : Ω → E) {v : ℝ} (hv : 0 ≤ v) : 0 ≤ p.budget L x0 v := by
  have := p.initial_nonneg L x0
  have := p.alpha_pos
  have := p.delta_pos
  unfold budget
  positivity

theorem variance_le_budget (p : NoiseModel Z E) (L : HistoryLaw Ω Z m)
    (x0 : Ω → E) {v : ℝ} (hv : 0 ≤ v) : 34 * v ≤ p.budget L x0 v := by
  have h1 : 0 ≤ 16 * L.queriedLoss p.h p.step x0 0 / p.δ :=
    div_nonneg (mul_nonneg (by norm_num) (p.initial_nonneg L x0)) p.delta_pos.le
  have h2 : 0 ≤ 8 * p.α / p.δ * v := by
    have := p.alpha_pos
    have := p.delta_pos
    positivity
  dsimp [budget]
  nlinarith

/-- The restart point may depend on the fixed prefix; all remaining permutations preserve it. -/
theorem initial_budget (p : NoiseModel Z E) (L : HistoryLaw Ω Z m) (v : ResidualControl p L)
    (x0 : Ω → E) (h0 : L.StartInvariant x0) {s : ℕ} (hsm : s ≤ m) :
    ‖L.current p.step x0 s - L.current p.step x0 0‖ ^ 2 +
      p.δ * (∑ j ∈ range s, p.lossAt L (j : Fin m) (L.current p.step x0 j)) ≤
        s * p.budget L x0 v.variance := by
  let D := fun j ↦ ‖L.current p.step x0 j - L.current p.step x0 0‖
  let H : ℕ → ℝ := fun j ↦ p.lossAt L (j : Fin m) (L.current p.step x0 j)
  let C := 8 * L.queriedLoss p.h p.step x0 0 / p.δ + (1 + 4 * p.α / p.δ) * v.variance
  have hcoef : 0 ≤ 1 + 4 * p.α / p.δ := by
    have := p.alpha_pos
    have := p.delta_pos
    positivity
  have hC : 0 ≤ C := by
    dsimp [C]
    exact add_nonneg
      (div_nonneg (mul_nonneg (by norm_num) (p.initial_nonneg L x0)) p.delta_pos.le)
      (mul_nonneg hcoef v.nonneg)
  have hstep (j : ℕ) (hj : j < s) : D (j + 1) ^ 2 - D j ^ 2 + p.δ * H j ≤
      C + 2 * Real.sqrt v.variance * D j / Real.sqrt (m - j : ℕ) := by
    have hs := p.initial_step L x0 h0 j
    have hi := L.futureInvariant_current p.step x0 h0 (le_refl j)
    have ht := L.futureInvariant_current p.step x0 h0 (Nat.zero_le j)
    have hc := p.correlation L v _ (show j < m by omega) le_rfl (L.futureInvariant_sub hi ht)
    have hd := mul_le_mul_of_nonneg_left (v.diagonal (j : Fin m)) hcoef
    rw [← real_inner_comm (L.current p.step x0 j - L.current p.step x0 0)
      (L.residual p.ζ (j : Fin m))] at hs
    dsimp [D, H, C]
    have ha := neg_le_abs
      ⟪L.residual p.ζ (j : Fin m), L.current p.step x0 j - L.current p.step x0 0⟫
    linear_combination hs + hd + 2 * hc + 2 * ha
  have hh := displacement_drift D H hsm p.delta_pos.le hC (Real.sqrt_nonneg _)
    (by simp [D]) (fun _ _ ↦ norm_nonneg _) (fun _ _ ↦ p.lossAt_nonneg L _ _) hstep
  rw [Real.sq_sqrt v.nonneg] at hh
  have hconst : 2 * C + 16 * v.variance ≤ p.budget L x0 v.variance := by
    dsimp [C, budget]
    linear_combination 16 * v.nonneg
  have hc := mul_le_mul_of_nonneg_left hconst (Nat.cast_nonneg (α := ℝ) s)
  exact hh.trans hc

theorem displacement_budget (p : NoiseModel Z E) (L : HistoryLaw Ω Z m)
    (v : ResidualControl p L) (x0 : Ω → E) (h0 : L.StartInvariant x0)
    {s : ℕ} (hsm : s ≤ m) :
    ‖L.past p.step x0 0 s - L.past p.step x0 0 0‖ ^ 2 ≤ s * p.budget L x0 v.variance := by
  rw [L.past_current_distance p.step x0 h0]
  have hh := p.initial_budget L v x0 h0 hsm
  have hn : 0 ≤ p.δ * ∑ j ∈ range s, p.lossAt L (j : Fin m) (L.current p.step x0 j) :=
    mul_nonneg p.delta_pos.le (sum_nonneg (fun j _ ↦ p.lossAt_nonneg L _ _))
  linarith

theorem gradient_step_bound (p : NoiseModel Z E) (L : HistoryLaw Ω Z m)
    (v : ResidualControl p L) (x0 : Ω → E) (h0 : L.StartInvariant x0) (j : ℕ) :
    ‖L.queriedGradient p.g x0 j‖ ^ 2 ≤
      4 * p.α * p.lossAt L (j : Fin m) (L.current p.step x0 j) + 2 * v.variance := by
  rw [L.queriedGradient_forward p.g x0 h0]
  have he : liftGradient (fun ω ↦ p.g (L.label ω (j : Fin m))) (L.current p.step x0 j) =
      p.gradientAt L (j : Fin m) (L.current p.step x0 j) + L.residual p.ζ (j : Fin m) := by
    ext ω
    rfl
  change ‖liftGradient (fun ω ↦ p.g (L.label ω (j : Fin m)))
    (L.current p.step x0 j)‖ ^ 2 ≤ _
  rw [he, norm_add_sq_real]
  have hq := p.gradientAt_self_bound L (j : Fin m) (L.current p.step x0 j)
  have hz := v.diagonal (j : Fin m)
  have hi := inner_young (p.gradientAt L (j : Fin m) (L.current p.step x0 j))
    (L.residual p.ζ (j : Fin m)) (by norm_num : (0 : ℝ) < 1)
  norm_num only [one_mul, div_one] at hi
  linarith

theorem gradient_budget (p : NoiseModel Z E) (L : HistoryLaw Ω Z m)
    (v : ResidualControl p L) (x0 : Ω → E) (h0 : L.StartInvariant x0)
    {s : ℕ} (hsm : s ≤ m) :
    (∑ j ∈ range s, ‖L.queriedGradient p.g x0 j‖ ^ 2) ≤
      s * (4 * p.α * p.budget L x0 v.variance / p.δ + 2 * v.variance) := by
  have hh := p.initial_budget L v x0 h0 hsm
  have hsum : (∑ j ∈ range s, p.lossAt L (j : Fin m) (L.current p.step x0 j)) ≤
      s * p.budget L x0 v.variance / p.δ := by
    apply (le_div_iff₀ p.delta_pos).mpr
    nlinarith only [hh, sq_nonneg ‖L.current p.step x0 s - L.current p.step x0 0‖]
  have hg := sum_le_sum (s := range s) (fun j _ ↦ p.gradient_step_bound L v x0 h0 j)
  simp only [sum_add_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul] at hg
  have hc := mul_le_mul_of_nonneg_left hsum (show 0 ≤ 4 * p.α by linarith [p.alpha_pos])
  linear_combination hg + hc

end NoiseModel

end LastIterate
