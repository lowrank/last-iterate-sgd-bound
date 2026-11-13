module

public import LastIterate.FiniteRisk

@[expose] public section

/-!
# End-to-end last-iterate bounds

The hypotheses below are only the original differentiable, smooth convex finite-sum
problem and the stated step-size and horizon restrictions. The histories, noise
budgets, gradient estimates, deletion law, and population expectations are constructed
in the imported proofs. No history estimate is assumed by these final theorems.
-/

namespace LastIterate

open Finset

namespace SGDProblem

variable {d n : ℕ} (p : SGDProblem d n) (η : ℝ) (hη : 0 < η) (hηβ : η * p.beta < 2)

theorem normalized_wordRun {T : ℕ} (ω : Fin T → Fin n) :
    wordRun (p.normalized η hη hηβ).step p.x0 ω = p.run η (List.ofFn ω) := by
  simp only [wordRun, run, p.normalized_step η hη hηβ]

theorem normalized_population (x : State d) :
    uniformMean (fun z ↦ (p.normalized η hη hηβ).loss z x) =
      η * (p.population x - p.population p.xstar) := by
  simp only [p.normalized_loss η hη hηβ, uniformMean_mul, uniformMean_sub, population]

include hη hηβ

/-- WR, every positive horizon, with the complete step-size dependence. -/
theorem wr_noisy_bound {T : ℕ} (hT : 0 < T) :
    p.wrRisk η T ≤ 280000 * polylog T *
      (p.radiusSq / (delta η p.beta ^ 3 * η * T) + η * p.noiseSq / delta η p.beta ^ 4) := by
  have hh := (p.normalized η hη hηβ).wr_population_bound p.population_nonempty
    (p.normalized_residual_sum η hη hηβ) p.x0 hT
  simp only [p.normalized_wordRun η hη hηβ,
    p.normalized_population η hη hηβ, uniformMean_mul,
    p.normalized_noise η hη hηβ] at hh
  apply restore_stepsize hη
  exact hh

/-- WOR, every positive horizon up to and including one complete pass. -/
theorem wor_noisy_bound {T : ℕ} (hT : 0 < T) (hTn : T ≤ n) :
    p.worRisk η T ≤ 280000 * polylog T *
      (p.radiusSq / (delta η p.beta ^ 3 * η * T) + η * p.noiseSq / delta η p.beta ^ 4) := by
  have hh := (p.normalized η hη hηβ).wor_population_bound p.population_nonempty
    (p.normalized_residual_sum η hη hηβ) p.x0 hT hTn
  simp only [p.normalized_wordRun η hη hηβ,
    p.normalized_population η hη hηβ, uniformMean_mul,
    p.normalized_noise η hη hηβ] at hh
  apply restore_stepsize hη
  exact hh

end SGDProblem

/-- Explicit interpolation corollary, with the same universal constant. -/
theorem SGDProblem.interpolation_bound {d n : ℕ} (p : SGDProblem d n)
    (hnoise : p.noiseSq = 0) {T : ℕ} (hT : 0 < T) :
    p.wrRisk p.beta⁻¹ T ≤ 280000 * p.beta * p.radiusSq * polylog T / T ∧
      (T ≤ n → p.worRisk p.beta⁻¹ T ≤ 280000 * p.beta * p.radiusSq * polylog T / T) := by
  have he : p.beta⁻¹ * p.beta = 1 := inv_mul_cancel₀ (ne_of_gt p.beta_pos)
  have hstep : p.beta⁻¹ * p.beta < 2 := by rw [he]; norm_num
  have hd : delta p.beta⁻¹ p.beta = 1 := by norm_num [delta, he]
  have hid : 280000 * polylog T *
      (p.radiusSq / (delta p.beta⁻¹ p.beta ^ 3 * p.beta⁻¹ * T) +
        p.beta⁻¹ * p.noiseSq / delta p.beta⁻¹ p.beta ^ 4) =
      280000 * p.beta * p.radiusSq * polylog T / T := by
    rw [hd, hnoise]
    simp only [one_pow, one_mul, mul_zero, zero_div, add_zero]
    field_simp
  constructor
  · simpa only [hid] using p.wr_noisy_bound p.beta⁻¹ (inv_pos.mpr p.beta_pos) hstep hT
  · intro hTn
    simpa only [hid] using p.wor_noisy_bound p.beta⁻¹ (inv_pos.mpr p.beta_pos) hstep hT hTn

/-- The manuscript's noisy WR/WOR target, proved with one explicit universal constant. -/
theorem noisyClaim : NoisyClaim := by
  refine ⟨280000, by norm_num, ?_⟩
  intro d n p η hη hηβ T hT
  exact ⟨p.wr_noisy_bound η hη hηβ hT, fun hTn ↦ p.wor_noisy_bound η hη hηβ hT hTn⟩

/-- The interpolation target follows from the proved noisy theorem at `η = 1/β`. -/
theorem interpolationClaim : InterpolationClaim :=
  noisyClaim_implies_interpolationClaim noisyClaim

end LastIterate
