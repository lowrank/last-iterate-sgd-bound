module

public import LastIterate.Suffix
public import Mathlib.Analysis.SpecialFunctions.Log.Base

@[expose] public section

/-!
# Explicit log-log saving

The scale ratio is `ceil (log (m + 2) + 2)`. Unlike an asymptotic big-O argument, the
estimates below include `m = 1` and use constants independent of every SGD parameter.
-/

namespace LastIterate

open Finset

noncomputable def ell (m : ℕ) : ℝ := Real.log ((m : ℝ) + 2)
noncomputable def lam (m : ℕ) : ℝ := Real.log (ell m + 2)
noncomputable def polylog (m : ℕ) : ℝ := ell m ^ 3 / lam m
noncomputable def ratio (m : ℕ) : ℕ := ⌈ell m + 2⌉₊
noncomputable def gradFactor (m : ℕ) : ℝ := 4 + (Nat.clog 2 m : ℝ)

theorem one_le_ell {m : ℕ} (hm : 0 < m) : 1 ≤ ell m := by
  have hlog := Real.le_log_one_add_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)
  norm_num at hlog
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  exact hlog.trans (Real.log_le_log (by norm_num) (by linarith))

theorem lam_pos {m : ℕ} (hm : 0 < m) : 0 < lam m := by
  apply Real.log_pos
  have := one_le_ell hm
  linarith

theorem lam_le_two_ell {m : ℕ} (hm : 0 < m) : lam m ≤ 2 * ell m := by
  have h1 := one_le_ell hm
  have hlog := Real.log_le_sub_one_of_pos (show 0 < ell m + 2 by linarith)
  dsimp [lam]
  linarith

theorem ratio_ge_two {m : ℕ} (hm : 0 < m) : 2 ≤ ratio m := by
  have h1 := one_le_ell hm
  have hc := Nat.le_ceil (ell m + 2)
  have hh : (2 : ℝ) ≤ ratio m := by dsimp [ratio]; linarith
  exact_mod_cast hh

theorem ratio_le_four_ell {m : ℕ} (hm : 0 < m) : (ratio m : ℝ) ≤ 4 * ell m := by
  have h1 := one_le_ell hm
  have hc := Nat.ceil_lt_add_one (show 0 ≤ ell m + 2 by linarith)
  dsimp [ratio]
  linarith

theorem lam_le_log_ratio {m : ℕ} (hm : 0 < m) :
    lam m ≤ Real.log (ratio m) := by
  apply Real.log_le_log
  · have := one_le_ell hm; linarith
  · exact Nat.le_ceil _

theorem clog_le_log_div_add_one {m κ : ℕ} (hm : 0 < m) (hκ : 2 ≤ κ) :
    (Nat.clog κ m : ℝ) ≤ Real.log m / Real.log κ + 1 := by
  rw [← Real.natCeil_logb_natCast]
  apply le_of_lt (Nat.ceil_lt_add_one _)
  apply Real.logb_nonneg
  · exact_mod_cast hκ
  · exact_mod_cast hm

theorem scale_count {m : ℕ} (hm : 0 < m) :
    (Nat.clog (ratio m) m : ℝ) ≤ 3 * ell m / lam m := by
  have hl := one_le_ell hm
  have hp := lam_pos hm
  have hlam := lam_le_two_ell hm
  have hk := lam_le_log_ratio hm
  have hlogm : Real.log m ≤ ell m :=
    Real.log_le_log (by exact_mod_cast hm) (by linarith)
  have hlogm0 : 0 ≤ Real.log (m : ℝ) := Real.log_natCast_nonneg m
  have hdiv : Real.log m / Real.log (ratio m) ≤ ell m / lam m :=
    div_le_div₀ (by linarith) hlogm hp hk
  have hc := clog_le_log_div_add_one hm (ratio_ge_two hm)
  have hc' : (Nat.clog (ratio m) m : ℝ) ≤ ell m / lam m + 1 := hc.trans (by linarith)
  apply hc'.trans
  apply (le_div_iff₀ hp).mpr
  have he : (ell m / lam m + 1) * lam m = ell m + lam m := by
    field_simp
  rw [he]
  linarith

theorem gradFactor_le {m : ℕ} (hm : 0 < m) : gradFactor m ≤ 7 * ell m := by
  have hl := one_le_ell hm
  have hlog := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
  norm_num at hlog
  have hp : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogm : Real.log m ≤ ell m :=
    Real.log_le_log (by exact_mod_cast hm) (by linarith)
  have hd : Real.log m / Real.log 2 ≤ 2 * ell m := by
    apply (div_le_iff₀ hp).mpr
    nlinarith
  have hc := clog_le_log_div_add_one hm (show 2 ≤ 2 by omega)
  dsimp [gradFactor]
  linarith

/-- This is the deterministic log-log improvement, before restarting the trajectory. -/
theorem logarithmic_suffix (a : ℕ → ℝ) {m : ℕ} {b d : ℝ}
    (hm : 0 < m) (h : WindowComparison a m b d) (hb : 0 ≤ b) (hd : 0 ≤ d) :
    a 0 ≤ mean a m + (3 * ell m / lam m) * (b + 2 * ell m * d) := by
  have hg := geometric_suffix a hm (ratio_ge_two hm) h hb hd
  have hk : ((ratio m - 1 : ℕ) : ℝ) ≤ 4 * ell m := by
    exact (show ((ratio m - 1 : ℕ) : ℝ) ≤ ratio m by
      exact_mod_cast Nat.sub_le (ratio m) 1).trans (ratio_le_four_ell hm)
  have hcost : b + (ratio m - 1 : ℕ) * d / 2 ≤ b + 2 * ell m * d := by
    nlinarith [mul_le_mul_of_nonneg_right hk hd]
  exact hg.trans (add_le_add_right (mul_le_mul (scale_count hm) hcost
    (by positivity) (by have := lam_pos hm; have := one_le_ell hm; positivity)) _)

theorem ell_mono : Monotone ell := by
  intro m M hm
  apply Real.log_le_log (by positivity)
  exact_mod_cast Nat.add_le_add_right hm 2

theorem lam_mono : Monotone lam := by
  intro m M hm
  apply Real.log_le_log
  · have hh : 0 ≤ ell m := Real.log_nonneg (by
      have := Nat.cast_nonneg (α := ℝ) m
      linarith)
    linarith
  · linarith [ell_mono hm]

theorem one_le_two_polylog {m : ℕ} (hm : 0 < m) : 1 ≤ 2 * polylog m := by
  have hl := one_le_ell hm
  have hp := lam_pos hm
  have hh := lam_le_two_ell hm
  have hpow : ell m ≤ ell m ^ 3 := by nlinarith [sq_nonneg (ell m - 1)]
  unfold polylog
  rw [← mul_div_assoc]
  apply (le_div_iff₀ hp).mpr
  linarith

/-- Use one scale ratio for all the restarted horizons `m ≤ M`. -/
theorem logarithmic_suffix_up_to (a : ℕ → ℝ) {m M : ℕ} {b d : ℝ}
    (hm : 0 < m) (hmM : m ≤ M) (h : WindowComparison a m b d)
    (hb : 0 ≤ b) (hd : 0 ≤ d) :
    a 0 ≤ mean a m + (3 * ell M / lam M) * (b + 2 * ell M * d) := by
  have hM : 0 < M := lt_of_lt_of_le hm hmM
  have hg := geometric_suffix a hm (ratio_ge_two hM) h hb hd
  have hcount : (Nat.clog (ratio M) m : ℝ) ≤ 3 * ell M / lam M :=
    (show (Nat.clog (ratio M) m : ℝ) ≤ Nat.clog (ratio M) M by
      exact_mod_cast Nat.clog_mono_right (ratio M) hmM).trans (scale_count hM)
  have hk : ((ratio M - 1 : ℕ) : ℝ) ≤ 4 * ell M := by
    exact (show ((ratio M - 1 : ℕ) : ℝ) ≤ ratio M by
      exact_mod_cast Nat.sub_le (ratio M) 1).trans (ratio_le_four_ell hM)
  have hcost : b + (ratio M - 1 : ℕ) * d / 2 ≤ b + 2 * ell M * d := by
    nlinarith [mul_le_mul_of_nonneg_right hk hd]
  exact hg.trans (add_le_add_right (mul_le_mul hcount hcost
    (by positivity) (by have := lam_pos hM; have := one_le_ell hM; positivity)) _)

/-- The loss amplification theorem with separate average, gradient, and history costs. -/
theorem amplification (a : ℕ → ℝ) {m M : ℕ} {b d Q μ cA cB cD : ℝ}
    (hm : 0 < m) (hmM : m ≤ M) (h : WindowComparison a m b d)
    (hb : 0 ≤ b) (hd : 0 ≤ d) (hQ : 0 ≤ Q)
    (hcA : 0 ≤ cA) (_hcB : 0 ≤ cB) (hcD : 0 ≤ cD)
    (hav : mean a m ≤ μ + cA * Q)
    (hgrad : b ≤ cB * ell M ^ 2 * Q) (hhist : d ≤ cD * Q) :
    a 0 ≤ μ + (2 * cA + 3 * cB + 6 * cD) * polylog M * Q := by
  have hM : 0 < M := lt_of_lt_of_le hm hmM
  have hl := one_le_ell hM
  have hp := lam_pos hM
  have hP := one_le_two_polylog hM
  have hsq : ell M ≤ ell M ^ 2 := by nlinarith
  have hcost : b + 2 * ell M * d ≤ (cB + 2 * cD) * ell M ^ 2 * Q := by
    have hh1 := mul_le_mul_of_nonneg_left hhist (show 0 ≤ 2 * ell M by positivity)
    have hh2 := mul_le_mul_of_nonneg_right hsq (show 0 ≤ 2 * cD * Q by positivity)
    nlinarith only [hgrad, hh1, hh2]
  have hh := logarithmic_suffix_up_to a hm hmM h hb hd
  have hs := mul_le_mul_of_nonneg_left hcost
    (show 0 ≤ 3 * ell M / lam M by positivity)
  have hbase := mul_le_mul_of_nonneg_right hP (show 0 ≤ cA * Q by positivity)
  have hid : (3 * ell M / lam M) * ((cB + 2 * cD) * ell M ^ 2 * Q) =
      (3 * cB + 6 * cD) * polylog M * Q := by unfold polylog; ring
  rw [hid] at hs
  nlinarith only [hh, hs, hav, hbase]

theorem polylog_succ_le {m : ℕ} (hm : 0 < m) : polylog (m + 1) ≤ 8 * polylog m := by
  have hl := one_le_ell hm
  have hp := lam_pos hm
  have hps := lam_pos (show 0 < m + 1 by omega)
  have hl2 : ell (m + 1) ≤ 2 * ell m := by
    have hs : (m : ℝ) + 1 + 2 ≤ ((m : ℝ) + 2) ^ 2 := by
      have hn : (0 : ℝ) ≤ m := Nat.cast_nonneg _
      nlinarith
    have hh := Real.log_le_log (by positivity) hs
    rw [Real.log_pow] at hh
    simpa [ell, Nat.cast_add, Nat.cast_one] using hh
  have hnum : ell (m + 1) ^ 3 ≤ 8 * ell m ^ 3 := by
    have hh := pow_le_pow_left₀ (by have := one_le_ell (show 0 < m + 1 by omega); linarith)
      hl2 3
    nlinarith only [hh]
  unfold polylog
  rw [← mul_div_assoc]
  exact div_le_div₀ (by positivity) hnum hp (lam_mono (by omega))

end LastIterate
