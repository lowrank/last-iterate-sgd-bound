module

public import LastIterate.LogFactor
public import LastIterate.Geometry

@[expose] public section

/-!
# Rate engine for the manuscript

This file joins the deterministic estimates. Its hypotheses are explicit estimates on
the histories; it does not assert that WR/WOR SGD satisfies them. The finite-sampling
instantiation must be proved separately before these theorems certify Theorem 2.1.
-/

namespace LastIterate

open Finset

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem natLog_two_le {m M : ℕ} (hm : 0 < m) (hmM : m ≤ M) :
    (Nat.log 2 m : ℝ) ≤ 2 * ell M := by
  have hpow : (2 : ℝ) ^ Nat.log 2 m ≤ (m : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 (Nat.ne_of_gt hm)
  have hh := Real.log_le_log (by positivity) hpow
  rw [Real.log_pow] at hh
  have hhalf := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
  norm_num at hhalf
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hlogm : Real.log m ≤ ell M :=
    Real.log_le_log hm0 (by
      have hr : (m : ℝ) ≤ M := by exact_mod_cast hmM
      linarith)
  have hJ : (0 : ℝ) ≤ Nat.log 2 m := Nat.cast_nonneg _
  nlinarith

theorem dyadic_log_bound (g : ℕ → E) {m M : ℕ} {C B : ℝ}
    (hm : 0 < m) (hmM : m ≤ M) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (henergy : (∑ i ∈ range m, ‖g i‖ ^ 2) ≤ m * B)
    (hlag : ∀ l : ℕ, 0 < l → 2 * l ≤ m →
      (∑ i ∈ range l, ‖g i - g (l + i)‖ ^ 2) ≤ l * C) :
    ‖g 0‖ ^ 2 ≤ 4 * B + 2 * ell M ^ 2 * C := by
  have hh := dyadic_gradient g hm hC hB henergy hlag
  have hJ := natLog_two_le hm hmM
  have hJ0 : (0 : ℝ) ≤ Nat.log 2 m := Nat.cast_nonneg _
  have hl := one_le_ell (lt_of_lt_of_le hm hmM)
  have hsq : (Nat.log 2 m : ℝ) ^ 2 ≤ 4 * ell M ^ 2 := by nlinarith
  have hmC := mul_le_mul_of_nonneg_right hsq hC
  nlinarith

/-- A uniform gradient estimate from a separate dyadic comparison at every endpoint. -/
theorem uniform_gradient (g : ℕ → ℕ → E) {m M : ℕ} {Q b c : ℝ}
    (hmM : m ≤ M) (hQ : 0 ≤ Q) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (henergy : ∀ j < m, (∑ i ∈ range (j + 1), ‖g j i‖ ^ 2) ≤ (j + 1) * (b * Q))
    (hlag : ∀ j < m, ∀ l : ℕ, 0 < l → 2 * l ≤ j + 1 →
      (∑ i ∈ range l, ‖g j i - g j (l + i)‖ ^ 2) ≤ l * (c * Q)) :
    ∀ j < m, ‖g j 0‖ ^ 2 ≤ (4 * b + 2 * c) * ell M ^ 2 * Q := by
  intro j hj
  have hM : 0 < M := by omega
  have hh := dyadic_log_bound (g j) (by omega) (show j + 1 ≤ M by omega)
    (mul_nonneg hc hQ) (mul_nonneg hb hQ)
    (by simpa only [Nat.cast_add, Nat.cast_one] using henergy j hj) (hlag j hj)
  have hl := one_le_ell hM
  have hs : 1 ≤ ell M ^ 2 := by nlinarith
  have hh' := mul_le_mul_of_nonneg_right hs (show 0 ≤ 4 * b * Q by positivity)
  nlinarith only [hh, hh']

omit [InnerProductSpace ℝ E] [NormedAddCommGroup E] in
theorem restart_average {m : ℕ} {A Γ : ℝ} (μ K : ℕ → ℝ) (hm : 0 < m)
    (h : ∀ r < m, A ≤ μ r + Γ * K r) :
    A ≤ mean μ m + Γ * mean K m := by
  have hs := sum_le_sum (s := range m) (fun r hr ↦ h r (mem_range.mp hr))
  simp only [sum_add_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul] at hs
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hh : A ≤ ((∑ r ∈ range m, μ r) + Γ * ∑ r ∈ range m, K r) / m :=
    (le_div_iff₀ hm0).mpr (by nlinarith only [hs])
  unfold mean
  convert hh using 1
  ring

/-- The pre-restart interpolation amplification, with an explicit universal constant. -/
theorem interpolation_amplification (a : ℕ → ℝ) {m M : ℕ} {A₀ b d : ℝ}
    (hm : 0 < m) (hmM : m ≤ M) (hA : 0 ≤ A₀)
    (h : WindowComparison a m b d) (hb : 0 ≤ b) (hd : 0 ≤ d)
    (hav : mean a m ≤ 4 * A₀)
    (hgrad : b ≤ 20 * ell M ^ 2 * A₀) (hhist : d ≤ 2 * A₀) :
    a 0 ≤ 80 * polylog M * A₀ := by
  have hh := amplification a hm hmM h hb hd hA (cA := 4) (cB := 20) (cD := 2)
    (μ := 0) (by norm_num) (by norm_num) (by norm_num) (by simpa using hav) hgrad hhist
  norm_num at hh
  exact hh

/-- The pre-restart noisy amplification, including the affine residual mean. -/
theorem noisy_amplification (a : ℕ → ℝ) {m M : ℕ} {K δ μ b d : ℝ}
    (hm : 0 < m) (hmM : m ≤ M) (hK : 0 ≤ K) (hδ : 0 < δ)
    (h : WindowComparison a m b d) (hb : 0 ≤ b) (hd : 0 ≤ d)
    (hav : mean a m ≤ μ + 2 * (K / δ))
    (hgrad : b ≤ 22 * ell M ^ 2 * (K / δ)) (hhist : d ≤ (1 / 2) * (K / δ)) :
    a 0 ≤ μ + 73 * polylog M * (K / δ) := by
  have hh := amplification a hm hmM h hb hd (div_nonneg hK hδ.le)
    (cA := 2) (cB := 22) (cD := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
    hav hgrad hhist
  norm_num at hh
  exact hh

end LastIterate
