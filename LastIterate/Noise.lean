module

public import LastIterate.RateEngine

@[expose] public section

/-!
# Noise bootstrap and restart budgets

These scalar lemmas retain the loss sum when closing the quadratic radius estimate.
They are used for both the whole run and a conditionally restarted run in Section 4.
-/

namespace LastIterate

open Finset

theorem quadratic_bootstrap {D a b H : ℝ}
    (hD : D ^ 2 ≤ a + b * D) (hH : H ≤ a + b * D) :
    D ^ 2 ≤ 2 * a + b ^ 2 ∧ H ≤ 2 * a + b ^ 2 := by
  constructor <;> nlinarith [sq_nonneg (D - b)]

theorem inv_sqrt_succ (k : ℕ) :
    1 / Real.sqrt ((k : ℝ) + 1) ≤ 2 * (Real.sqrt ((k : ℝ) + 1) - Real.sqrt k) := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hp : 0 < Real.sqrt ((k : ℝ) + 1) := Real.sqrt_pos.mpr (by linarith)
  have ha := Real.sq_sqrt hk
  have hb := Real.sq_sqrt (show 0 ≤ (k : ℝ) + 1 by positivity)
  apply (div_le_iff₀ hp).mpr
  nlinarith [sq_nonneg (Real.sqrt ((k : ℝ) + 1) - Real.sqrt k)]

theorem sum_inv_sqrt (m : ℕ) :
    (∑ k ∈ range m, 1 / Real.sqrt ((k : ℝ) + 1)) ≤ 2 * Real.sqrt m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ]
    push_cast
    linarith [inv_sqrt_succ m]

/-- The averaged restarted budget in Lemma `lem: n bd`, before its constants are rounded. -/
theorem averaged_restart_budget {δ α R₂ σ₂ : ℝ} {m : ℕ}
    (hm : 0 < m) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hα : α ≤ 2)
    (_hR : 0 ≤ R₂) (hσ : 0 ≤ σ₂) (φ K : ℕ → ℝ)
    (henergy : δ * (∑ r ∈ range m, φ r) ≤ 2 * R₂ + 26 * m * σ₂ / δ)
    (hK : mean K m ≤ (16 / δ) * mean φ m + (42 + 8 * α / δ) * σ₂) :
    mean K m ≤ 32 * R₂ / (m * δ ^ 2) + 474 * σ₂ / δ ^ 3 := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hφ : mean φ m ≤ (2 * R₂ + 26 * m * σ₂ / δ) / (m * δ) := by
    unfold mean
    apply (div_le_iff₀ hm0).mpr
    have he : (2 * R₂ + 26 * m * σ₂ / δ) / (m * δ) * m =
        (2 * R₂ + 26 * m * σ₂ / δ) / δ := by field_simp
    rw [he]
    apply (le_div_iff₀ hδ).mpr
    nlinarith only [henergy]
  have hh := mul_le_mul_of_nonneg_left hφ (show 0 ≤ 16 / δ by positivity)
  have hd2 : δ ^ 2 ≤ 1 := by nlinarith
  have hd3 : δ ^ 3 ≤ 1 := by nlinarith
  have hαδ : α * δ ^ 2 ≤ 2 := by nlinarith [sq_nonneg δ]
  have hrem : (42 + 8 * α / δ) * σ₂ ≤ 58 * σ₂ / δ ^ 3 := by
    apply (le_div_iff₀ (pow_pos hδ 3)).mpr
    have he : (42 + 8 * α / δ) * σ₂ * δ ^ 3 = (42 * δ ^ 3 + 8 * α * δ ^ 2) * σ₂ := by
      field_simp
    rw [he]
    exact mul_le_mul_of_nonneg_right (by nlinarith) hσ
  have hid : (16 / δ) * ((2 * R₂ + 26 * m * σ₂ / δ) / (m * δ)) =
      32 * R₂ / (m * δ ^ 2) + 416 * σ₂ / δ ^ 3 := by field_simp; ring
  rw [hid] at hh
  calc
    mean K m ≤ (16 / δ) * mean φ m + (42 + 8 * α / δ) * σ₂ := hK
    _ ≤ (32 * R₂ / (m * δ ^ 2) + 416 * σ₂ / δ ^ 3) + 58 * σ₂ / δ ^ 3 :=
      add_le_add hh hrem
    _ = _ := by ring

/-- Combination of restart amplification with the noisy global energy budgets. -/
theorem noisy_query_bound {m M : ℕ} {δ R₂ σ₂ A : ℝ} (μ K : ℕ → ℝ)
    (hm : 0 < m) (hmM : m ≤ M) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hR : 0 ≤ R₂) (hσ : 0 ≤ σ₂)
    (hrestart : ∀ r < m, A ≤ μ r + (73 * polylog M / δ) * K r)
    (hmean : mean μ m ≤ R₂ / m + 13 * σ₂ / δ)
    (hbudget : mean K m ≤ 32 * R₂ / (m * δ ^ 2) + 474 * σ₂ / δ ^ 3) :
    A ≤ 35000 * polylog M * (R₂ / (m * δ ^ 3) + σ₂ / δ ^ 4) := by
  have hM : 0 < M := lt_of_lt_of_le hm hmM
  have hP := one_le_two_polylog hM
  have hP0 : 0 ≤ polylog M := by linarith
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hh := restart_average μ K hm hrestart
  have hk := mul_le_mul_of_nonneg_left hbudget (show 0 ≤ 73 * polylog M / δ by positivity)
  have hd3 : δ ^ 3 ≤ 1 := pow_le_one₀ hδ.le hδ1
  have hd4 : δ ^ 4 ≤ δ := by nlinarith [mul_le_mul_of_nonneg_left hd3 hδ.le]
  have hr : R₂ / m ≤ 2 * polylog M * (R₂ / (m * δ ^ 3)) := by
    have hh1 : R₂ / m ≤ R₂ / (m * δ ^ 3) :=
      div_le_div_of_nonneg_left hR (by positivity) (by nlinarith)
    have hh2 := mul_le_mul_of_nonneg_right hP
      (show 0 ≤ R₂ / (m * δ ^ 3) by positivity)
    linarith
  have hn : 13 * σ₂ / δ ≤ 26 * polylog M * (σ₂ / δ ^ 4) := by
    have hh1 : σ₂ / δ ≤ σ₂ / δ ^ 4 :=
      div_le_div_of_nonneg_left hσ (by positivity) hd4
    have hh2 := mul_le_mul_of_nonneg_right hP (show 0 ≤ σ₂ / δ ^ 4 by positivity)
    have hh3 := mul_le_mul_of_nonneg_left
      (hh1.trans (by simpa only [one_mul] using hh2)) (show (0 : ℝ) ≤ 13 by norm_num)
    calc
      13 * σ₂ / δ = 13 * (σ₂ / δ) := by ring
      _ ≤ 13 * (2 * polylog M * (σ₂ / δ ^ 4)) := hh3
      _ = _ := by ring
  have hid : (73 * polylog M / δ) *
      (32 * R₂ / (m * δ ^ 2) + 474 * σ₂ / δ ^ 3) =
      2336 * polylog M * (R₂ / (m * δ ^ 3)) +
      34602 * polylog M * (σ₂ / δ ^ 4) := by field_simp; ring
  rw [hid] at hk
  nlinarith [mul_nonneg hP0 (show 0 ≤ R₂ / (m * δ ^ 3) by positivity),
    mul_nonneg hP0 (show 0 ≤ σ₂ / δ ^ 4 by positivity)]

end LastIterate
