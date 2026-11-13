module

public import LastIterate.Conditional
public import LastIterate.FiniteSampling
public import LastIterate.SmoothBridge
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

/-!
# Exact SGD targets

`NoisyClaim` and `InterpolationClaim` pin the original assumptions and the actual
finite WR/WOR expectations. No history estimate is included in `SGDProblem`.
Their proofs are `noisyClaim` and `interpolationClaim` in `Main.lean`.
-/

namespace LastIterate

abbrev State (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The original smooth convex problem, with the actual gradient and population minimizer. -/
structure SGDProblem (d n : ℕ) where
  loss : Fin n → State d → ℝ
  grad : Fin n → State d → State d
  beta : ℝ
  x0 : State d
  xstar : State d
  population_nonempty : 0 < n
  beta_pos : 0 < beta
  hasGradient : ∀ z x, HasGradientAt (loss z) (grad z x) x
  convex : ∀ z, ConvexOn ℝ Set.univ (loss z)
  smooth : ∀ z x y, ‖grad z x - grad z y‖ ≤ beta * ‖x - y‖
  minimizes : ∀ x, uniformMean (fun z ↦ loss z xstar) ≤ uniformMean (fun z ↦ loss z x)

namespace SGDProblem

theorem strongInterpolation {d n : ℕ} (p : SGDProblem d n) (z : Fin n) :
    SmoothInterpolation (p.loss z) (p.grad z) p.beta :=
  smoothInterpolation_of_convex_smooth p.beta_pos (p.hasGradient z) (p.convex z) (p.smooth z)

noncomputable def population {d n : ℕ} (p : SGDProblem d n) (x : State d) : ℝ :=
  uniformMean (fun z ↦ p.loss z x)

noncomputable def radiusSq {d n : ℕ} (p : SGDProblem d n) : ℝ := ‖p.x0 - p.xstar‖ ^ 2

noncomputable def noiseSq {d n : ℕ} (p : SGDProblem d n) : ℝ :=
  uniformMean (fun z ↦ ‖p.grad z p.xstar‖ ^ 2)

theorem noiseSq_zero_iff {d n : ℕ} (p : SGDProblem d n) :
    p.noiseSq = 0 ↔ ∀ z, p.grad z p.xstar = 0 := by
  constructor
  · intro h z
    have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt p.population_nonempty)
    simp only [noiseSq, uniformMean, Fintype.card_fin] at h
    have hs : (∑ i : Fin n, ‖p.grad i p.xstar‖ ^ 2) = 0 :=
      (div_eq_zero_iff.mp h).resolve_right hn
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ ↦ sq_nonneg ‖p.grad i p.xstar‖)).mp
      hs z (Finset.mem_univ z)
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hz)
  · intro h
    simp [noiseSq, uniformMean, h]

theorem common_minimizer_of_noiseSq_zero {d n : ℕ} (p : SGDProblem d n)
    (h : p.noiseSq = 0) (z : Fin n) (x : State d) : p.loss z p.xstar ≤ p.loss z x := by
  have hg := p.noiseSq_zero_iff.mp h z
  have hh := convex_first_order (p.hasGradient z) (p.convex z) p.xstar x
  simpa [hg] using hh

/-- Start at `x₀`; apply one update for every label in list order. -/
noncomputable def run {d n : ℕ} (p : SGDProblem d n) (η : ℝ) (labels : List (Fin n)) :
    State d := labels.foldl (fun x z ↦ x - η • p.grad z x) p.x0

noncomputable def wrRisk {d n : ℕ} (p : SGDProblem d n) (η : ℝ) (T : ℕ) : ℝ :=
  uniformMean (fun ω : WR n T ↦
    p.population (p.run η (List.ofFn ω)) - p.population p.xstar)

noncomputable def worRisk {d n : ℕ} (p : SGDProblem d n) (η : ℝ) (T : ℕ) : ℝ :=
  uniformMean (fun ω : WOR n T ↦
    p.population (p.run η (List.ofFn (fun i ↦ ω i))) - p.population p.xstar)

end SGDProblem

/-- Main theorem target, including all `0 < η < 2/β`, and one-pass WOR including `T = n`. -/
def NoisyClaim : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (d n : ℕ) (p : SGDProblem d n) (η : ℝ),
    0 < η → η * p.beta < 2 → ∀ T : ℕ, 0 < T →
    let bound := C * polylog T *
      (p.radiusSq / (delta η p.beta ^ 3 * η * T) + η * p.noiseSq / delta η p.beta ^ 4)
    p.wrRisk η T ≤ bound ∧ (T ≤ n → p.worRisk η T ≤ bound)

/-- Interpolation target at the greedy step, with no additional history assumptions. -/
def InterpolationClaim : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (d n : ℕ) (p : SGDProblem d n), p.noiseSq = 0 →
    ∀ T : ℕ, 0 < T →
    p.wrRisk p.beta⁻¹ T ≤ C * p.beta * p.radiusSq * polylog T / T ∧
      (T ≤ n → p.worRisk p.beta⁻¹ T ≤ C * p.beta * p.radiusSq * polylog T / T)

/-- The interpolation loss bound is a consequence of the full noisy target. -/
theorem noisyClaim_implies_interpolationClaim (h : NoisyClaim) : InterpolationClaim := by
  rcases h with ⟨C, hC, h⟩
  refine ⟨C, hC, ?_⟩
  intro d n p hnoise T hT
  have hp := p.beta_pos
  have he : p.beta⁻¹ * p.beta = 1 := inv_mul_cancel₀ (ne_of_gt hp)
  have hd : delta p.beta⁻¹ p.beta = 1 := by norm_num [delta, he]
  have hh := h d n p p.beta⁻¹ (inv_pos.mpr hp) (by rw [he]; norm_num) T hT
  dsimp only at hh
  have hid : C * polylog T *
      (p.radiusSq / (delta p.beta⁻¹ p.beta ^ 3 * p.beta⁻¹ * T) +
        p.beta⁻¹ * p.noiseSq / delta p.beta⁻¹ p.beta ^ 4) =
      C * p.beta * p.radiusSq * polylog T / T := by
    rw [hd, hnoise]
    simp only [one_pow, one_mul, mul_zero, zero_div, add_zero]
    field_simp
  rwa [hid] at hh

end LastIterate
