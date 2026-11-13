module

public import LastIterate
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.List.OfFn

@[expose] public section

namespace SGDLastIterate

/-- The real Euclidean state space in arbitrary finite dimension. -/
abbrev State (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Uniform expectation on a finite sample space, implemented as the sum divided by cardinality. -/
noncomputable def mean {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) : ℝ :=
  (∑ ω, f ω) / Fintype.card Ω

/-- The finite population objective, with each of the `n` labels given equal weight. -/
noncomputable def population {d n : ℕ} (f : Fin n → State d → ℝ) (x : State d) : ℝ :=
  mean (fun z ↦ f z x)

/-- SGD starts at `x0` and applies one update for each label, in list order. -/
noncomputable def run {d n : ℕ} (g : Fin n → State d → State d)
    (η : ℝ) (x0 : State d) (labels : List (Fin n)) : State d :=
  labels.foldl (fun x z ↦ x - η • g z x) x0

/-- Expected excess population loss after `T` independent uniform updates with replacement. -/
noncomputable def wrRisk {d n : ℕ} (f : Fin n → State d → ℝ)
    (g : Fin n → State d → State d) (η : ℝ) (x0 xstar : State d) (T : ℕ) : ℝ :=
  mean (fun ω : Fin T → Fin n ↦
    population f (run g η x0 (List.ofFn ω)) - population f xstar)

/-- Expected excess population loss under a uniform ordered injective sample of `T` labels.
For `T ≤ n` this is the first `T` updates of a uniform random permutation of all labels. -/
noncomputable def worRisk {d n : ℕ} (f : Fin n → State d → ℝ)
    (g : Fin n → State d → State d) (η : ℝ) (x0 xstar : State d) (T : ℕ) : ℝ :=
  mean (fun ω : Fin T ↪ Fin n ↦
    population f (run g η x0 (List.ofFn (fun i ↦ ω i))) - population f xstar)

/-- Squared gradient noise at the population minimizer. -/
noncomputable def noiseSq {d n : ℕ} (g : Fin n → State d → State d)
    (xstar : State d) : ℝ := mean (fun z ↦ ‖g z xstar‖ ^ 2)

/-- The explicit logarithmic factor, defined also at small horizons. -/
noncomputable def polylog (T : ℕ) : ℝ :=
  Real.log ((T : ℝ) + 2) ^ 3 / Real.log (Real.log ((T : ℝ) + 2) + 2)

/-- Step-size margin for the full stable range `0 < ηβ < 2`. -/
noncomputable def delta (η β : ℝ) : ℝ := min 1 (2 - η * β)

/-- For every smooth convex finite-sum problem and `0 < ηβ < 2`, the expected last-iterate
loss is at most the explicit log-log rate plus a noise term. WR permits any positive horizon;
WOR permits every horizon through the end of the first pass, including `T = n`.
No trajectory, gradient-energy, or history-comparison estimate is assumed. -/
theorem noisy_wr_wor {d n : ℕ} (f : Fin n → State d → ℝ)
    (g : Fin n → State d → State d) (β : ℝ) (x0 xstar : State d)
    (hn : 0 < n) (hβ : 0 < β)
    (hgrad : ∀ z x, HasGradientAt (f z) (g z x) x)
    (hconv : ∀ z, ConvexOn ℝ Set.univ (f z))
    (hsmooth : ∀ z x y, ‖g z x - g z y‖ ≤ β * ‖x - y‖)
    (hmin : ∀ x, population f xstar ≤ population f x)
    (η : ℝ) (hη : 0 < η) (hηβ : η * β < 2) (T : ℕ) (hT : 0 < T) :
    let B := 280000 * polylog T *
      (‖x0 - xstar‖ ^ 2 / (delta η β ^ 3 * η * T) + η * noiseSq g xstar / delta η β ^ 4)
    wrRisk f g η x0 xstar T ≤ B ∧ (T ≤ n → worRisk f g η x0 xstar T ≤ B) := by
  let p : LastIterate.SGDProblem d n :=
    ⟨f, g, β, x0, xstar, hn, hβ, hgrad, hconv, hsmooth, hmin⟩
  exact ⟨p.wr_noisy_bound η hη hηβ hT,
    fun hTn ↦ p.wor_noisy_bound η hη hηβ hT hTn⟩

/-- In interpolation (`noiseSq = 0`) at `η = 1/β`, both sampling schemes have last-iterate
expected loss bounded by `280000 β ‖x0-xstar‖² polylog(T)/T`.
This is the loss conclusion; no separate population-gradient conclusion is asserted here. -/
theorem interpolation_wr_wor {d n : ℕ} (f : Fin n → State d → ℝ)
    (g : Fin n → State d → State d) (β : ℝ) (x0 xstar : State d)
    (hn : 0 < n) (hβ : 0 < β)
    (hgrad : ∀ z x, HasGradientAt (f z) (g z x) x)
    (hconv : ∀ z, ConvexOn ℝ Set.univ (f z))
    (hsmooth : ∀ z x y, ‖g z x - g z y‖ ≤ β * ‖x - y‖)
    (hmin : ∀ x, population f xstar ≤ population f x)
    (hnoise : noiseSq g xstar = 0) (T : ℕ) (hT : 0 < T) :
    let B := 280000 * β * ‖x0 - xstar‖ ^ 2 * polylog T / T
    wrRisk f g β⁻¹ x0 xstar T ≤ B ∧ (T ≤ n → worRisk f g β⁻¹ x0 xstar T ≤ B) := by
  let p : LastIterate.SGDProblem d n :=
    ⟨f, g, β, x0, xstar, hn, hβ, hgrad, hconv, hsmooth, hmin⟩
  exact p.interpolation_bound hnoise hT

end SGDLastIterate
