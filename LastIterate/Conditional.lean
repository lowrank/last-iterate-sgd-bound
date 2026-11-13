module

public import LastIterate.Noise

@[expose] public section

/-!
# Conditional rate theorems

These theorems assume the precise local history estimates listed in their signatures.
They do not assume a logarithmic rate. They prove the rate from geometric comparison,
average energy and the noisy restart budgets. Instantiating their hypotheses for the
concrete sampling models is separate work, not an axiom of this development.
-/

namespace LastIterate

open Finset

theorem interpolation_from_history_bounds {m M : ℕ} {A R₂ : ℝ}
    (a : ℕ → ℕ → ℝ) (initial : ℕ → ℝ)
    (hm : 0 < m) (hmM : m ≤ M)
    (hinit : ∀ r < m, 0 ≤ initial r)
    (hterminal : ∀ r < m, a r 0 = A)
    (hwindow : ∀ r < m, WindowComparison (a r) (m - r)
      (20 * ell M ^ 2 * initial r) (2 * initial r))
    (haverage : ∀ r < m, mean (a r) (m - r) ≤ 4 * initial r)
    (henergy : (∑ r ∈ range m, initial r) ≤ R₂ / 2) :
    A ≤ 40 * polylog M * R₂ / m := by
  have hM : 0 < M := lt_of_lt_of_le hm hmM
  have hP : 0 ≤ polylog M := by have := one_le_two_polylog hM; linarith
  have hre (r : ℕ) (hr : r < m) : A ≤ 0 + (80 * polylog M) * initial r := by
    have hr0 := hinit r hr
    have hh := interpolation_amplification (a r) (show 0 < m - r by omega)
      (show m - r ≤ M by omega) (hinit r hr) (hwindow r hr)
      (by positivity) (by positivity) (haverage r hr) le_rfl le_rfl
    simpa only [hterminal r hr, zero_add] using hh
  have hh := restart_average (fun _ ↦ 0) initial hm hre
  simp only [mean, sum_const_zero, zero_div, zero_add] at hh
  have hav := div_le_div_of_nonneg_right henergy (show (0 : ℝ) ≤ m by positivity)
  have hh' := mul_le_mul_of_nonneg_left hav (show 0 ≤ 80 * polylog M by positivity)
  calc
    A ≤ (80 * polylog M) * ((∑ r ∈ range m, initial r) / m) := hh
    _ ≤ (80 * polylog M) * ((R₂ / 2) / m) := hh'
    _ = _ := by ring

theorem noisy_from_history_bounds {m M : ℕ} {A δ R₂ σ₂ : ℝ}
    (a : ℕ → ℕ → ℝ) (μ K : ℕ → ℝ)
    (hm : 0 < m) (hmM : m ≤ M) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hR : 0 ≤ R₂) (hσ : 0 ≤ σ₂)
    (hK : ∀ r < m, 0 ≤ K r)
    (hterminal : ∀ r < m, a r 0 = A)
    (hwindow : ∀ r < m, WindowComparison (a r) (m - r)
      (22 * ell M ^ 2 * (K r / δ)) ((1 / 2) * (K r / δ)))
    (haverage : ∀ r < m, mean (a r) (m - r) ≤ μ r + 2 * (K r / δ))
    (hmean : mean μ m ≤ R₂ / m + 13 * σ₂ / δ)
    (hbudget : mean K m ≤ 32 * R₂ / (m * δ ^ 2) + 474 * σ₂ / δ ^ 3) :
    A ≤ 35000 * polylog M * (R₂ / (m * δ ^ 3) + σ₂ / δ ^ 4) := by
  apply noisy_query_bound μ K hm hmM hδ hδ1 hR hσ _ hmean hbudget
  intro r hr
  have hKr := hK r hr
  have hh := noisy_amplification (a r) (show 0 < m - r by omega)
    (show m - r ≤ M by omega) hKr hδ (hwindow r hr)
    (by positivity) (by positivity) (haverage r hr) le_rfl le_rfl
  rw [hterminal r hr] at hh
  convert hh using 1
  ring

noncomputable def delta (η β : ℝ) : ℝ := min 1 (2 - η * β)

theorem delta_pos {η β : ℝ} (h : η * β < 2) : 0 < delta η β := by
  exact lt_min (by norm_num) (by linarith)

theorem delta_le_one (η β : ℝ) : delta η β ≤ 1 := min_le_left _ _

/-- Undo the manuscript's scaling: normalized noise is `η² σ_*²`. -/
theorem restore_stepsize {risk C P R₂ σ₂ η δ : ℝ} {T : ℕ} (hη : 0 < η)
    (h : η * risk ≤ C * P * (R₂ / (T * δ ^ 3) + (η ^ 2 * σ₂) / δ ^ 4)) :
    risk ≤ C * P * (R₂ / (δ ^ 3 * η * T) + η * σ₂ / δ ^ 4) := by
  have hh : risk ≤ (C * P * (R₂ / (T * δ ^ 3) + (η ^ 2 * σ₂) / δ ^ 4)) / η :=
    (le_div_iff₀ hη).mpr (by nlinarith only [h])
  have he : (C * P * (R₂ / (T * δ ^ 3) + (η ^ 2 * σ₂) / δ ^ 4)) / η =
      C * P * (R₂ / (δ ^ 3 * η * T) + η * σ₂ / δ ^ 4) := by
    field_simp
  rw [← he]
  exact hh

end LastIterate
