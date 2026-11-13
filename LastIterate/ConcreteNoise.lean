module

public import LastIterate.NoiseBudgets
public import LastIterate.SamplingMoments
public import LastIterate.Population

@[expose] public section

/-! # Constructing the analytic and sampling hypotheses from the original SGD problem -/

namespace LastIterate

open Finset
open scoped RealInnerProductSpace

theorem sum_eq_card_mul_mean {Ω : Type*} [Fintype Ω] [Nonempty Ω] (f : Ω → ℝ) :
    (∑ ω, f ω) = (Fintype.card Ω : ℝ) * uniformMean f := by
  have hn : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  unfold uniformMean
  field_simp

namespace NoiseModel

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def wrControl {n m : ℕ} [NeZero m] (p : NoiseModel (Fin n) E)
    (hn : 0 < n) (hzero : ∑ z, p.ζ z = 0) : ResidualControl p (wrHistoryLaw n m) := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  refine ⟨Fintype.card (WR n m) * uniformMean (fun z ↦ ‖p.ζ z‖ ^ 2),
    mul_nonneg (Nat.cast_nonneg _) (uniformMean_nonneg _ (fun _ ↦ sq_nonneg _)), ?_, ?_⟩
  · intro i
    rw [history_norm_sq]
    change (∑ ω : WR n m, ‖p.ζ (ω i)‖ ^ 2) ≤ _
    rw [sum_eq_card_mul_mean, wr_coordinate hn i (fun z ↦ ‖p.ζ z‖ ^ 2)]
  · intro i j hij
    rw [PiLp.inner_apply]
    change (∑ ω : WR n m, ⟪p.ζ (ω i), p.ζ (ω j)⟫) ≤ 0
    rw [sum_eq_card_mul_mean, wr_cross_moment hn p.ζ hzero i j hij, mul_zero]

noncomputable def worControl {n m : ℕ} [NeZero m] (p : NoiseModel (Fin n) E)
    (hn : m ≤ n) (hzero : ∑ z, p.ζ z = 0) : ResidualControl p (worHistoryLaw n m) := by
  let : Nonempty (WOR n m) := ⟨⟨Fin.castLE hn, Fin.castLE_injective hn⟩⟩
  refine ⟨Fintype.card (WOR n m) * uniformMean (fun z ↦ ‖p.ζ z‖ ^ 2),
    mul_nonneg (Nat.cast_nonneg _) (uniformMean_nonneg _ (fun _ ↦ sq_nonneg _)), ?_, ?_⟩
  · intro i
    rw [history_norm_sq]
    change (∑ ω : WOR n m, ‖p.ζ (ω i)‖ ^ 2) ≤ _
    rw [sum_eq_card_mul_mean, wor_coordinate hn i (fun z ↦ ‖p.ζ z‖ ^ 2)]
  · intro i j hij
    rw [PiLp.inner_apply]
    change (∑ ω : WOR n m, ⟪p.ζ (ω i), p.ζ (ω j)⟫) ≤ 0
    rw [sum_eq_card_mul_mean]
    exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _)
      (wor_cross_moment hn p.ζ hzero i j hij)

end NoiseModel

namespace SGDProblem

noncomputable def normalized {d n : ℕ} (p : SGDProblem d n) (η : ℝ)
    (hη : 0 < η) (hηβ : η * p.beta < 2) : NoiseModel (Fin n) (State d) where
  h z x := η * p.loss z x - η * p.loss z p.xstar - ⟪η • p.grad z p.xstar, x - p.xstar⟫
  q z x := η • p.grad z x - η • p.grad z p.xstar
  ζ z := η • p.grad z p.xstar
  star := p.xstar
  α := η * p.beta
  δ := delta η p.beta
  alpha_pos := mul_pos hη p.beta_pos
  delta_pos := LastIterate.delta_pos hηβ
  delta_le_one := LastIterate.delta_le_one η p.beta
  delta_le := min_le_right _ _
  smooth z := center_interpolation (scale_interpolation hη (p.strongInterpolation z)) p.xstar
  zero_loss z := by simp
  zero_grad z := by simp

theorem normalized_step {d n : ℕ} (p : SGDProblem d n) (η : ℝ)
    (hη : 0 < η) (hηβ : η * p.beta < 2) (z : Fin n) (x : State d) :
    (p.normalized η hη hηβ).step z x = x - η • p.grad z x := by
  simp only [NoiseModel.step, NoiseModel.g, normalized, sub_add_cancel]

theorem normalized_loss {d n : ℕ} (p : SGDProblem d n) (η : ℝ)
    (hη : 0 < η) (hηβ : η * p.beta < 2) (z : Fin n) (x : State d) :
    (p.normalized η hη hηβ).loss z x = η * (p.loss z x - p.loss z p.xstar) := by
  simp only [NoiseModel.loss, normalized]
  ring

theorem normalized_residual_sum {d n : ℕ} (p : SGDProblem d n) (η : ℝ)
    (hη : 0 < η) (hηβ : η * p.beta < 2) :
    (∑ z, (p.normalized η hη hηβ).ζ z) = 0 := by
  simp only [normalized, ← smul_sum, p.gradient_sum_zero, smul_zero]

theorem normalized_noise {d n : ℕ} (p : SGDProblem d n) (η : ℝ)
    (hη : 0 < η) (hηβ : η * p.beta < 2) :
    uniformMean (fun z ↦ ‖(p.normalized η hη hηβ).ζ z‖ ^ 2) = η ^ 2 * p.noiseSq := by
  simp only [uniformMean, normalized, norm_smul, Real.norm_eq_abs, abs_of_pos hη,
    mul_pow, ← mul_sum, noiseSq]
  ring

end SGDProblem

end LastIterate
