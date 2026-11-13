module

public import LastIterate.GlobalQuery

@[expose] public section

/-! # Scalar constants for the population-risk conversion -/

namespace LastIterate

noncomputable def baseRate (δ R V : ℝ) (m : ℕ) : ℝ :=
  R / (m * δ ^ 3) + V / δ ^ 4

theorem baseRate_nonneg {δ R V : ℝ} (hδ : 0 < δ) (hR : 0 ≤ R) (hV : 0 ≤ V)
    (m : ℕ) : 0 ≤ baseRate δ R V m := by
  unfold baseRate
  positivity

theorem ell_sq_le_two_polylog {m : ℕ} (hm : 0 < m) : ell m ^ 2 ≤ 2 * polylog m := by
  have hh := mul_le_mul_of_nonneg_left (lam_le_two_ell hm) (sq_nonneg (ell m))
  unfold polylog
  rw [← mul_div_assoc]
  apply (le_div_iff₀ (lam_pos hm)).mpr
  nlinarith only [hh]

theorem baseRate_antitone {δ R V : ℝ} (hδ : 0 < δ) (hR : 0 ≤ R)
    {m M : ℕ} (hm : 0 < m) (hmM : m ≤ M) : baseRate δ R V M ≤ baseRate δ R V m := by
  unfold baseRate
  apply add_le_add_left
  apply div_le_div_of_nonneg_left hR (mul_pos (by exact_mod_cast hm) (pow_pos hδ _))
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hmM) (pow_nonneg hδ.le _)

theorem energy_coarse {α δ R V : ℝ} {m : ℕ} (hm : 0 < m)
    (hα : 0 ≤ α) (hα2 : α ≤ 2) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hR : 0 ≤ R) (hV : 0 ≤ V) :
    8 * α * R / δ + (104 * α / δ ^ 2 + 2) * m * V ≤
      210 * m * baseRate δ R V m := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hd2 : δ ^ 2 ≤ 1 := pow_le_one₀ hδ.le hδ1
  have hd4 : δ ^ 4 ≤ 1 := pow_le_one₀ hδ.le hδ1
  have hd32 : δ ^ 3 ≤ δ := by nlinarith [mul_le_mul_of_nonneg_left hd2 hδ.le]
  have hd42 : δ ^ 4 ≤ δ ^ 2 := by nlinarith [sq_nonneg (δ ^ 2), mul_le_mul_of_nonneg_left hd2 (sq_nonneg δ)]
  have hr := div_le_div_of_nonneg_left hR (pow_pos hδ 3) hd32
  have hr' := mul_le_mul_of_nonneg_right hα2 hR
  have hr'' := div_le_div_of_nonneg_right hr' hδ.le
  have hRpart : 8 * α * R / δ ≤ 16 * R / δ ^ 3 := by linear_combination 8 * hr'' + 16 * hr
  have hv := div_le_div_of_nonneg_left (show (0 : ℝ) ≤ 208 by norm_num) (pow_pos hδ 4) hd42
  have hv' := div_le_div_of_nonneg_right (show 104 * α ≤ 208 by linarith) (sq_nonneg δ)
  have hv'' : (2 : ℝ) ≤ 2 / δ ^ 4 := (le_div_iff₀ (pow_pos hδ 4)).mpr (by linarith)
  have hVpart : 104 * α / δ ^ 2 + 2 ≤ 210 / δ ^ 4 := by linear_combination hv + hv' + hv''
  have hVmul := mul_le_mul_of_nonneg_right hVpart (show 0 ≤ (m : ℝ) * V by positivity)
  have hrlarge : 16 * R / δ ^ 3 ≤ 210 * R / δ ^ 3 := by
    gcongr
    norm_num
  have he : 210 * (m : ℝ) * baseRate δ R V m =
      210 * R / δ ^ 3 + (210 / δ ^ 4) * ((m : ℝ) * V) := by
    unfold baseRate
    field_simp
  rw [he]
  nlinarith only [hRpart, hVmul, hrlarge]

theorem training_constant {α Q A G S : ℝ} {m : ℕ} (hm : 0 < m)
    (hα : 0 < α) (hα2 : α ≤ 2) (hQ : 0 ≤ Q)
    (hA : A ≤ 35000 * polylog m * Q)
    (hG : G ≤ 21000 * ell m ^ 2 * Q) (hS : S ≤ 210 * m * Q) :
    (m : ℝ) * (A + G / 2) + (1 + α) / 2 * S ≤
      60000 * m * polylog m * Q := by
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hp := one_le_two_polylog hm
  have hQp : 0 ≤ polylog m * Q := mul_nonneg (by linarith) hQ
  have hg := mul_le_mul_of_nonneg_right (ell_sq_le_two_polylog hm) hQ
  have hgb : G ≤ 42000 * polylog m * Q := by nlinarith only [hG, hg]
  have ha := mul_le_mul_of_nonneg_left (show A + G / 2 ≤ 56000 * polylog m * Q by
    linarith) hm0
  have hs := mul_le_mul_of_nonneg_left hS (show 0 ≤ (1 + α) / 2 by linarith)
  have hc := mul_le_mul_of_nonneg_right (show (1 + α) / 2 ≤ (3 : ℝ) / 2 by linarith)
    (show 0 ≤ 210 * (m : ℝ) * Q by positivity)
  have hb := mul_le_mul_of_nonneg_right hp (show 0 ≤ (m : ℝ) * Q by positivity)
  have hn := mul_nonneg hm0 hQp
  nlinarith only [ha, hs, hc, hb, hn]

theorem successor_query_constant {δ R V : ℝ} {T : ℕ} (hT : 0 < T)
    (hδ : 0 < δ) (hR : 0 ≤ R) (hV : 0 ≤ V) :
    35000 * polylog (T + 1) * baseRate δ R V (T + 1) ≤
      280000 * polylog T * baseRate δ R V T := by
  have hp : 0 ≤ polylog T := by linarith [one_le_two_polylog hT]
  have hq := baseRate_antitone hδ hR hT (Nat.le_succ T) (V := V)
  have hh := mul_le_mul (polylog_succ_le hT) hq (baseRate_nonneg hδ hR hV _)
    (mul_nonneg (by norm_num) hp)
  nlinarith only [hh]

end LastIterate
