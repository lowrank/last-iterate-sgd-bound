module

public import Mathlib.Data.Nat.Log
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Push

@[expose] public section

/-!
# Geometric suffix comparison

This file formalizes the deterministic comparison in Corollary `cor: Am` of `main4.tex`.
The sequence is reversed: `a 0` is the last loss and `mean a l` is the last-`l` average.
Losses need not be nonnegative, so the same argument applies in the noisy case.
-/

namespace LastIterate

open Finset

noncomputable def mean (a : ℕ → ℝ) (l : ℕ) : ℝ := (∑ i ∈ range l, a i) / l

/-- Frozen-history comparison, with the gradient and displacement costs kept separate. -/
def WindowComparison (a : ℕ → ℝ) (m : ℕ) (b d : ℝ) : Prop :=
  ∀ l j : ℕ, 0 < l → l + j < m →
    (∑ i ∈ range l, a i) ≤ l * a (l + j) + l * b + (j + 1) * d

@[simp] theorem mean_one (a : ℕ → ℝ) : mean a 1 = a 0 := by simp [mean]

theorem sum_succ_real (v : ℕ) : (∑ j ∈ range v, ((j : ℝ) + 1)) = v * (v + 1) / 2 := by
  induction v with
  | zero => simp
  | succ v ih => rw [sum_range_succ, ih]; push_cast; ring

/-- The exact rearrangement before choosing a geometric spacing. -/
theorem window_sum (a : ℕ → ℝ) {m l v : ℕ} {b d : ℝ}
    (h : WindowComparison a m b d) (hl : 0 < l) (hlv : l + v ≤ m) :
    (v : ℝ) * (∑ i ∈ range l, a i) ≤
      l * (∑ j ∈ range v, a (l + j)) + v * l * b + d * (v * (v + 1) / 2) := by
  have hs := sum_le_sum (s := range v) (fun j hj ↦ h l j hl (by
    have := mem_range.mp hj
    omega))
  rw [sum_add_distrib, sum_add_distrib] at hs
  simp only [sum_const, card_range, nsmul_eq_mul] at hs
  rw [← mul_sum, ← sum_mul, sum_succ_real] at hs
  nlinarith only [hs]

/-- A single comparison between two suffix lengths. -/
theorem mean_step (a : ℕ → ℝ) {m l v κ : ℕ} {b d : ℝ}
    (h : WindowComparison a m b d) (hb : 0 ≤ b) (hd : 0 ≤ d)
    (hl : 0 < l) (hv : 0 < v) (hlv : l + v ≤ m) (hκ : v ≤ l * (κ - 1)) :
    mean a l - mean a (l + v) ≤ b + (κ - 1 : ℕ) * d / 2 := by
  have hs := window_sum a h hl hlv
  have hlr : (0 : ℝ) < l := by exact_mod_cast hl
  have hvr : (0 : ℝ) < v := by exact_mod_cast hv
  have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast hl
  have hκr : (v : ℝ) ≤ l * (κ - 1 : ℕ) := by exact_mod_cast hκ
  have hnon : (0 : ℝ) ≤ (κ - 1 : ℕ) := Nat.cast_nonneg _
  have hprod : (v : ℝ) * (v + 1) ≤ l * (l + v) * (κ - 1 : ℕ) := by
    calc
      (v : ℝ) * (v + 1) ≤ v * (l + v) := by nlinarith
      _ ≤ (l * (κ - 1 : ℕ)) * (l + v) :=
        mul_le_mul_of_nonneg_right hκr (by positivity)
      _ = _ := by ring
  have hcost := mul_le_mul_of_nonneg_right hprod hd
  have heq : mean a l - mean a (l + v) =
      ((v : ℝ) * (∑ i ∈ range l, a i) - l * (∑ j ∈ range v, a (l + j))) /
        (l * (l + v)) := by
    unfold mean
    rw [sum_range_add]
    push_cast
    field_simp
    ring
  rw [heq]
  apply (div_le_iff₀ (show (0 : ℝ) < l * (l + v) by positivity)).mpr
  nlinarith only [hs, hcost, mul_nonneg (sq_nonneg (l : ℝ)) hb]

/-- The geometric suffix theorem. No positivity of the loss sequence is assumed. -/
theorem geometric_suffix (a : ℕ → ℝ) {m κ : ℕ} {b d : ℝ}
    (hm : 0 < m) (hκ : 2 ≤ κ) (h : WindowComparison a m b d)
    (hb : 0 ≤ b) (hd : 0 ≤ d) :
    a 0 ≤ mean a m + (Nat.clog κ m : ℝ) * (b + (κ - 1 : ℕ) * d / 2) := by
  let c : ℝ := b + (κ - 1 : ℕ) * d / 2
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hstep (p : ℕ) :
      mean a (min m (κ ^ p)) - mean a (min m (κ ^ (p + 1))) ≤ c := by
    let l := min m (κ ^ p)
    let u := min m (κ ^ (p + 1))
    have hl : 0 < l := lt_min hm (pow_pos (by omega) _)
    have hlu : l ≤ u := min_le_min_left m (Nat.pow_le_pow_right (by omega) (by omega))
    have hum : u ≤ m := min_le_left _ _
    by_cases heq : l = u
    · change mean a l - mean a u ≤ c
      simpa [heq] using hc
    have hlt : l < u := lt_of_le_of_ne hlu heq
    have hlpow : l = κ ^ p := by
      dsimp [l]
      apply min_eq_right
      by_contra hn
      have he : min m (κ ^ p) = m := min_eq_left (by omega)
      change min m (κ ^ p) < u at hlt
      omega
    have humul : u ≤ l * κ := by
      rw [hlpow]
      exact (min_le_right _ _).trans_eq (pow_succ κ p)
    have hvκ : u - l ≤ l * (κ - 1) := by
      have hk1 : 1 ≤ κ := by omega
      have he : l * (κ - 1) + l = l * κ := by
        rw [Nat.mul_sub_left_distrib, Nat.mul_one, Nat.sub_add_cancel]
        exact Nat.le_mul_of_pos_right _ (by omega)
      omega
    have hh := mean_step a h hb hd hl (show 0 < u - l by omega)
      (show l + (u - l) ≤ m by omega) hvκ
    simpa only [Nat.add_sub_of_le hlu] using hh
  have hi (p : ℕ) : a 0 ≤ mean a (min m (κ ^ p)) + (p : ℝ) * c := by
    induction p with
    | zero => simp [Nat.min_eq_right (show 1 ≤ m by omega)]
    | succ p ih =>
      have hh := hstep p
      push_cast
      linarith
  have hlast := hi (Nat.clog κ m)
  simpa only [min_eq_left (Nat.le_pow_clog (show 1 < κ by omega) m)] using hlast

end LastIterate
