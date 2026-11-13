module

public import LastIterate.Suffix
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Tactic.Module

@[expose] public section

/-!
# Dyadic gradient estimate

The vectors are reversed histories: `g 0` is the last queried gradient. The hypotheses
are the total energy and the lag energy used in Lemmas `thm: grad` and `lem: grad noise`.
This is a theorem for arbitrary real inner product spaces, including the history L² space.
-/

namespace LastIterate

open Finset

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def vmean (g : ℕ → E) (l : ℕ) : E :=
  (l : ℝ)⁻¹ • ∑ i ∈ range l, g i

@[simp] theorem vmean_one (g : ℕ → E) : vmean g 1 = g 0 := by simp [vmean]

omit [InnerProductSpace ℝ E] in
theorem norm_sum_sq_le (g : ℕ → E) (l : ℕ) :
    ‖∑ i ∈ range l, g i‖ ^ 2 ≤ (l : ℝ) * ∑ i ∈ range l, ‖g i‖ ^ 2 := by
  have htri := norm_sum_le (range l) g
  have hcs := sq_sum_le_card_mul_sum_sq (s := range l) (f := fun i ↦ ‖g i‖)
  simp only [card_range] at hcs
  nlinarith [norm_nonneg (∑ i ∈ range l, g i),
    sum_nonneg (fun i (_ : i ∈ range l) ↦ norm_nonneg (g i))]

theorem vmean_sq_le (g : ℕ → E) {l : ℕ} (hl : 0 < l) :
    ‖vmean g l‖ ^ 2 ≤ (∑ i ∈ range l, ‖g i‖ ^ 2) / l := by
  have hlr : (0 : ℝ) < l := by exact_mod_cast hl
  have hs := norm_sum_sq_le g l
  unfold vmean
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  apply (le_div_iff₀ hlr).mpr
  field_simp
  nlinarith

theorem vmean_double (g : ℕ → E) {l : ℕ} (hl : 0 < l) :
    vmean g l - vmean g (2 * l) =
      ((2 * l : ℝ)⁻¹) • ∑ i ∈ range l, (g i - g (l + i)) := by
  have hlr : (l : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hl)
  have hi : (l : ℝ)⁻¹ = 2 * (2 * (l : ℝ))⁻¹ := by field_simp
  unfold vmean
  rw [show 2 * l = l + l by omega, sum_range_add, sum_sub_distrib]
  push_cast
  rw [show (l : ℝ) + l = 2 * l by ring, hi]
  module

theorem vmean_double_sq (g : ℕ → E) {l : ℕ} {C : ℝ} (hl : 0 < l)
    (h : (∑ i ∈ range l, ‖g i - g (l + i)‖ ^ 2) ≤ l * C) :
    ‖vmean g l - vmean g (2 * l)‖ ^ 2 ≤ C / 4 := by
  have hlr : (0 : ℝ) < l := by exact_mod_cast hl
  have hs := norm_sum_sq_le (fun i ↦ g i - g (l + i)) l
  have hh := mul_le_mul_of_nonneg_left h (le_of_lt hlr)
  rw [vmean_double g hl, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  field_simp
  nlinarith

theorem dyadic_gradient (g : ℕ → E) {m : ℕ} {C B : ℝ}
    (hm : 0 < m) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (henergy : (∑ i ∈ range m, ‖g i‖ ^ 2) ≤ m * B)
    (hlag : ∀ l : ℕ, 0 < l → 2 * l ≤ m →
      (∑ i ∈ range l, ‖g i - g (l + i)‖ ^ 2) ≤ l * C) :
    ‖g 0‖ ^ 2 ≤ 4 * B + (Nat.log 2 m : ℝ) ^ 2 * C / 2 := by
  let J := Nat.log 2 m
  have hpow : 2 ^ J ≤ m := Nat.pow_log_le_self 2 (Nat.ne_of_gt hm)
  have hm2 : m < 2 * 2 ^ J := by
    have hh := Nat.lt_pow_succ_log_self (show 1 < 2 by omega) m
    simpa [pow_succ, Nat.mul_comm] using hh
  have hcoarse : ‖vmean g (2 ^ J)‖ ^ 2 ≤ 2 * B := by
    have hv := vmean_sq_le g (show 0 < 2 ^ J by positivity)
    have hsub : (∑ i ∈ range (2 ^ J), ‖g i‖ ^ 2) ≤ ∑ i ∈ range m, ‖g i‖ ^ 2 :=
      sum_le_sum_of_subset_of_nonneg (range_mono hpow) (fun _ _ _ ↦ sq_nonneg _)
    apply hv.trans
    apply (div_le_iff₀ (show (0 : ℝ) < (2 ^ J : ℕ) by positivity)).mpr
    have hr : (m : ℝ) ≤ 2 * (2 ^ J : ℕ) := by exact_mod_cast (Nat.le_of_lt hm2)
    have hh := mul_le_mul_of_nonneg_right hr hB
    linarith
  have hstep (p : ℕ) (hp : p < J) :
      ‖vmean g (2 ^ p) - vmean g (2 ^ (p + 1))‖ ≤ Real.sqrt C / 2 := by
    have hle : 2 * 2 ^ p ≤ m := by
      calc
        2 * 2 ^ p = 2 ^ (p + 1) := by ring
        _ ≤ 2 ^ J := Nat.pow_le_pow_right (by omega) (by omega)
        _ ≤ m := hpow
    have hsq := vmean_double_sq g (show 0 < 2 ^ p by positivity)
      (hlag (2 ^ p) (by positivity) hle)
    have he : 2 * 2 ^ p = 2 ^ (p + 1) := by ring
    rw [he] at hsq
    have hs := Real.sq_sqrt hC
    have hnn := Real.sqrt_nonneg C
    nlinarith [norm_nonneg (vmean g (2 ^ p) - vmean g (2 ^ (p + 1)))]
  have hi (p : ℕ) (hp : p ≤ J) :
      ‖g 0‖ ≤ ‖vmean g (2 ^ p)‖ + (p : ℝ) * (Real.sqrt C / 2) := by
    induction p with
    | zero => simp
    | succ p ih =>
      have hprev := ih (by omega)
      have hs := hstep p (by omega)
      have ht := norm_add_le (vmean g (2 ^ p) - vmean g (2 ^ (p + 1)))
        (vmean g (2 ^ (p + 1)))
      rw [sub_add_cancel] at ht
      push_cast
      linarith
  have ht := hi J le_rfl
  have hs := Real.sq_sqrt hC
  have hnn := Real.sqrt_nonneg C
  have hJ : (0 : ℝ) ≤ J := Nat.cast_nonneg _
  have hsq : ‖g 0‖ ^ 2 ≤
      2 * ‖vmean g (2 ^ J)‖ ^ 2 + 2 * ((J : ℝ) * (Real.sqrt C / 2)) ^ 2 := by
    nlinarith [sq_nonneg (‖vmean g (2 ^ J)‖ - (J : ℝ) * (Real.sqrt C / 2)),
      norm_nonneg (g 0), norm_nonneg (vmean g (2 ^ J)), mul_nonneg hJ hnn]
  nlinarith [sq_nonneg (J : ℝ)]

end LastIterate
