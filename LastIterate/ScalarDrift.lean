module

public import LastIterate.Noise
public import LastIterate.HistoryComparison

@[expose] public section

/-! # Closing the full noisy loss/displacement budgets by finite maxima -/

namespace LastIterate

open Finset

theorem sum_inv_sqrt_remaining {m s : ℕ} (hs : s ≤ m) :
    (∑ j ∈ range s, 1 / Real.sqrt (m - j : ℕ)) ≤ 2 * Real.sqrt s := by
  have hh : (∑ j ∈ range s, 1 / Real.sqrt (m - j : ℕ)) ≤
      ∑ j ∈ range s, 1 / Real.sqrt (s - j : ℕ) := by
    apply sum_le_sum
    intro j hj
    have hj' := mem_range.mp hj
    apply div_le_div_of_nonneg_left (by norm_num)
    · apply Real.sqrt_pos.mpr
      exact_mod_cast (show 0 < s - j by omega)
    · apply Real.sqrt_le_sqrt
      exact_mod_cast (show s - j ≤ m - j by omega)
  have he : (∑ j ∈ range s, 1 / Real.sqrt (s - j : ℕ)) =
      ∑ j ∈ range s, 1 / Real.sqrt ((j : ℝ) + 1) := by
    rw [← sum_range_reflect (fun j ↦ 1 / Real.sqrt ((j : ℝ) + 1)) s]
    apply sum_congr rfl
    intro j hj
    have hj' := mem_range.mp hj
    have hi : s - j = (s - 1 - j) + 1 := by omega
    rw [hi, Nat.cast_add, Nat.cast_one]
  exact hh.trans (he ▸ sum_inv_sqrt s)

theorem sum_sqrt_ratio {m s : ℕ} (hs : s ≤ m) :
    (∑ j ∈ range s, Real.sqrt j / Real.sqrt (m - j : ℕ)) ≤ 2 * s := by
  have hh : (∑ j ∈ range s, Real.sqrt j / Real.sqrt (m - j : ℕ)) ≤
      Real.sqrt s * ∑ j ∈ range s, 1 / Real.sqrt (m - j : ℕ) := by
    rw [mul_sum]
    apply sum_le_sum
    intro j hj
    have hj' := mem_range.mp hj
    have hm := Real.sqrt_le_sqrt (show (j : ℝ) ≤ s by exact_mod_cast (by omega : j ≤ s))
    simpa only [mul_one_div] using div_le_div_of_nonneg_right hm (Real.sqrt_nonneg _)
  have hh' := mul_le_mul_of_nonneg_left (sum_inv_sqrt_remaining hs) (Real.sqrt_nonneg s)
  have hsq := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) s)
  nlinarith

theorem drift_telescope (D h c : ℕ → ℝ) (δ : ℝ) {m : ℕ}
    (hstep : ∀ j < m, D (j + 1) - D j + δ * h j ≤ c j) :
    D m + δ * (∑ j ∈ range m, h j) ≤ D 0 + ∑ j ∈ range m, c j := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hp := ih (fun j hj ↦ hstep j (by omega))
    have hs := hstep m (by omega)
    rw [sum_range_succ, sum_range_succ]
    linarith

/-- A maximum closes the radius estimate while keeping the loss sum. -/
theorem radius_drift (D h : ℕ → ℝ) {m : ℕ} {δ C σ : ℝ}
    (hδ : 0 ≤ δ) (hC : 0 ≤ C) (hσ : 0 ≤ σ)
    (hD : ∀ j ≤ m, 0 ≤ D j) (hh : ∀ j < m, 0 ≤ h j)
    (hstep : ∀ j < m, D (j + 1) ^ 2 - D j ^ 2 + δ * h j ≤
      C + 2 * σ * D j / Real.sqrt (m - j : ℕ)) :
    D m ^ 2 + δ * (∑ j ∈ range m, h j) ≤
      2 * D 0 ^ 2 + 2 * m * C + 16 * m * σ ^ 2 := by
  obtain ⟨r, hr, hmax⟩ := (range (m + 1)).exists_max_image D
    (nonempty_range_iff.mpr (by omega))
  have hrm : r ≤ m := by have := mem_range.mp hr; omega
  have hDr := hD r hrm
  have hmax' (j : ℕ) (hj : j ≤ m) : D j ≤ D r := hmax j (mem_range.mpr (by omega))
  have hbound (l : ℕ) (hl : l ≤ m) :
      D l ^ 2 + δ * (∑ j ∈ range l, h j) ≤
        D 0 ^ 2 + m * C + (4 * σ * Real.sqrt m) * D r := by
    have ht := drift_telescope (fun j ↦ D j ^ 2) h
      (fun j ↦ C + 2 * σ * D j / Real.sqrt (m - j : ℕ)) δ
      (m := l) (fun j hj ↦ hstep j (by omega))
    have hc : (∑ j ∈ range l, 2 * σ * D j / Real.sqrt (m - j : ℕ)) ≤
        (2 * σ * D r) * ∑ j ∈ range l, 1 / Real.sqrt (m - j : ℕ) := by
      rw [mul_sum]
      apply sum_le_sum
      intro j hj
      have hj' := mem_range.mp hj
      have ht := mul_le_mul_of_nonneg_left (hmax' j (by omega))
        (show 0 ≤ 2 * σ by positivity)
      simpa only [mul_one_div] using div_le_div_of_nonneg_right ht (Real.sqrt_nonneg _)
    have hs := mul_le_mul_of_nonneg_left (sum_inv_sqrt_remaining hl)
      (show 0 ≤ 2 * σ * D r by positivity)
    have hsm := Real.sqrt_le_sqrt (show (l : ℝ) ≤ m by exact_mod_cast hl)
    have hsm' := mul_le_mul_of_nonneg_left hsm (show 0 ≤ 4 * σ * D r by positivity)
    have hlC := mul_le_mul_of_nonneg_right (show (l : ℝ) ≤ m by exact_mod_cast hl) hC
    simp only [sum_add_distrib, sum_const, card_range, nsmul_eq_mul] at ht
    nlinarith only [ht, hc, hs, hsm', hlC]
  have hrbound : D r ^ 2 ≤ D 0 ^ 2 + m * C + (4 * σ * Real.sqrt m) * D r := by
    have hs := hbound r hrm
    have hn : 0 ≤ δ * ∑ j ∈ range r, h j :=
      mul_nonneg hδ (sum_nonneg (fun j hj ↦ hh j (by have := mem_range.mp hj; omega)))
    linarith
  have he := (quadratic_bootstrap hrbound (hbound m le_rfl)).2
  have hsq := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) m)
  nlinarith only [he, hsq]

/-- A maximum of distance divided by square-root time closes every restarted budget. -/
theorem displacement_drift (D h : ℕ → ℝ) {m s : ℕ} {δ C σ : ℝ}
    (hs : s ≤ m) (hδ : 0 ≤ δ) (hC : 0 ≤ C) (hσ : 0 ≤ σ)
    (hzero : D 0 = 0) (hD : ∀ j ≤ s, 0 ≤ D j) (hh : ∀ j < s, 0 ≤ h j)
    (hstep : ∀ j < s, D (j + 1) ^ 2 - D j ^ 2 + δ * h j ≤
      C + 2 * σ * D j / Real.sqrt (m - j : ℕ)) :
    D s ^ 2 + δ * (∑ j ∈ range s, h j) ≤ s * (2 * C + 16 * σ ^ 2) := by
  obtain ⟨r, hr, hmax⟩ := (range (s + 1)).exists_max_image
    (fun j ↦ D j / Real.sqrt j) (nonempty_range_iff.mpr (by omega))
  have hrs : r ≤ s := by have := mem_range.mp hr; omega
  let B := D r / Real.sqrt r
  have hB : 0 ≤ B := div_nonneg (hD r hrs) (Real.sqrt_nonneg _)
  have hmax' (j : ℕ) (hj : j ≤ s) : D j ≤ Real.sqrt j * B := by
    by_cases hj0 : j = 0
    · simp [hj0, hzero]
    · have ht := hmax j (mem_range.mpr (by omega))
      have hp : 0 < Real.sqrt (j : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < j))
      exact (div_le_iff₀ hp).mp ht |>.trans_eq (mul_comm _ _)
  have hbound (l : ℕ) (hl : l ≤ s) :
      D l ^ 2 + δ * (∑ j ∈ range l, h j) ≤ l * (C + 4 * σ * B) := by
    have ht := drift_telescope (fun j ↦ D j ^ 2) h
      (fun j ↦ C + 2 * σ * D j / Real.sqrt (m - j : ℕ)) δ
      (m := l) (fun j hj ↦ hstep j (by omega))
    have hc : (∑ j ∈ range l, 2 * σ * D j / Real.sqrt (m - j : ℕ)) ≤
        (2 * σ * B) * ∑ j ∈ range l, Real.sqrt j / Real.sqrt (m - j : ℕ) := by
      rw [mul_sum]
      apply sum_le_sum
      intro j hj
      have hj' := mem_range.mp hj
      have ht := mul_le_mul_of_nonneg_left (hmax' j (by omega))
        (show 0 ≤ 2 * σ by positivity)
      convert! div_le_div_of_nonneg_right ht (Real.sqrt_nonneg (m - j : ℕ)) using 1 <;> ring
    have hsum := mul_le_mul_of_nonneg_left (sum_sqrt_ratio (le_trans hl hs))
      (show 0 ≤ 2 * σ * B by positivity)
    simp only [hzero, zero_pow (by omega : (2 : ℕ) ≠ 0), zero_add,
      sum_add_distrib, sum_const, card_range, nsmul_eq_mul] at ht
    nlinarith only [ht, hc, hsum]
  have hquad : B ^ 2 ≤ C + (4 * σ) * B := by
    by_cases hr0 : r = 0
    · simp [B, hr0, hzero, hC]
    · have hrpos : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
      have ht := hbound r hrs
      have hn : 0 ≤ δ * ∑ j ∈ range r, h j :=
        mul_nonneg hδ (sum_nonneg (fun j hj ↦ hh j (by have := mem_range.mp hj; omega)))
      have he : B ^ 2 * r = D r ^ 2 := by
        dsimp [B]
        rw [div_pow, Real.sq_sqrt hrpos.le, div_mul_cancel₀ _ (ne_of_gt hrpos)]
      apply (mul_le_mul_iff_left₀ hrpos).mp
      nlinarith only [ht, hn, he]
  have hb := (quadratic_bootstrap hquad (le_refl (C + 4 * σ * B))).2
  have hs' := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg (α := ℝ) s)
  have ht := hbound s le_rfl
  nlinarith only [ht, hs']

theorem averaged_correlation_constant {R v δ : ℝ} {m : ℕ}
    (hR : 0 ≤ R) (hv : 0 ≤ v) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hm : 0 < m) :
    2 * Real.sqrt v * Real.sqrt (2 * R + 26 * m * v / δ) * Real.sqrt m / m ≤
      R / m + 13 * v / δ := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  let W := (m : ℝ) * v / δ
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hmv : (m : ℝ) * v ≤ W := by
    apply (le_div_iff₀ hδ).mpr
    have hh := mul_le_mul_of_nonneg_left hδ1 (show 0 ≤ (m : ℝ) * v by positivity)
    simpa only [mul_one] using hh
  have hB : 0 ≤ 2 * R + 26 * W := by positivity
  have he : 2 * R + 26 * m * v / δ = 2 * R + 26 * W := by dsimp [W]; ring
  rw [he]
  have hs : (2 * Real.sqrt v * Real.sqrt (2 * R + 26 * W) * Real.sqrt m) ^ 2 =
      4 * ((m : ℝ) * v) * (2 * R + 26 * W) := by
    simp only [mul_pow, Real.sq_sqrt hv, Real.sq_sqrt hB, Real.sq_sqrt hm0.le]
    ring
  have hc := mul_le_mul_of_nonneg_right hmv hB
  have hsq : (2 * Real.sqrt v * Real.sqrt (2 * R + 26 * W) * Real.sqrt m) ^ 2 ≤
      (R + 13 * W) ^ 2 := by
    rw [hs]
    nlinarith only [hc, sq_nonneg R, sq_nonneg W, mul_nonneg hR hW]
  have hlin : 2 * Real.sqrt v * Real.sqrt (2 * R + 26 * W) * Real.sqrt m ≤ R + 13 * W := by
    nlinarith only [hsq, show 0 ≤ R + 13 * W by positivity]
  apply (div_le_iff₀ hm0).mpr
  have ht : (R / m + 13 * v / δ) * m = R + 13 * W := by
    dsimp [W]
    field_simp
  rw [ht]
  exact hlin

end LastIterate
