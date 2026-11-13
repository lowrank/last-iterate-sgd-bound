module

public import LastIterate.FrozenSampling
public import LastIterate.RateEngine

@[expose] public section

/-! # From concrete cyclic histories to the dyadic gradient estimate -/

namespace LastIterate

open Finset
open scoped Fin.NatCast RealInnerProductSpace

theorem sum_tail_le (a : ℕ → ℝ) {n l : ℕ} (hl : l ≤ n) (ha : ∀ i, 0 ≤ a i) :
    (∑ i ∈ range l, a (n - l + i)) ≤ ∑ i ∈ range n, a i := by
  have hh := sum_range_add a (n - l) l
  rw [Nat.sub_add_cancel hl] at hh
  have hn : 0 ≤ ∑ i ∈ range (n - l), a i := sum_nonneg (fun i _ ↦ ha i)
  linarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem reversed_lag_sum_le (G : ℕ → E) {n l : ℕ} (hl : 2 * l ≤ n) :
    (∑ i ∈ range l, ‖G (n - 1 - i) - G (n - 1 - (l + i))‖ ^ 2) ≤
      ∑ j ∈ range (n - l), ‖G (l + j) - G j‖ ^ 2 := by
  let a := fun j ↦ ‖G (l + j) - G j‖ ^ 2
  have he : (∑ i ∈ range l, ‖G (n - 1 - i) - G (n - 1 - (l + i))‖ ^ 2) =
      ∑ i ∈ range l, a (n - l - 1 - i) := by
    apply sum_congr rfl
    intro i hi
    have hi' := mem_range.mp hi
    dsimp [a]
    have h1 : n - 1 - i = l + (n - l - 1 - i) := by omega
    have h2 : n - 1 - (l + i) = n - l - 1 - i := by omega
    rw [h1, h2]
  rw [he, reverse_suffix_sum a (by omega)]
  exact sum_tail_le a (by omega) (fun _ ↦ sq_nonneg _)

namespace HistoryLaw

variable {Ω Z : Type*} {m : ℕ} [Fintype Ω] [NeZero m]

theorem gradient_bound (L : HistoryLaw Ω Z m) (f : Z → E → ℝ) (g : Z → E → E)
    (x0 : Ω → E) (h0 : L.StartInvariant x0) {α δ B D : ℝ} {M : ℕ}
    (hα : 0 < α) (hδ : 0 < δ) (hδα : δ ≤ 2 - α)
    (hf : ∀ z, SmoothInterpolation (f z) (g z) α)
    (hB : 0 ≤ B) (hD : 0 ≤ D) (hmM : m ≤ M)
    (hdisp : ∀ s ≤ m,
      ‖L.past (fun z x ↦ x - g z x) x0 0 s -
        L.past (fun z x ↦ x - g z x) x0 0 0‖ ^ 2 ≤ s * D)
    (henergy : ∀ s ≤ m,
      (∑ j ∈ range s, ‖L.queriedGradient g x0 j‖ ^ 2) ≤ s * B)
    {k : ℕ} (hk : k < m) :
    ‖L.queriedGradient g x0 k‖ ^ 2 ≤ 4 * B + 2 * ell M ^ 2 * (α * D / δ) := by
  let X := L.past (fun z x ↦ x - g z x) x0 0
  let G := L.queriedGradient g x0
  have hsmooth := lift_interpolation (fun ω ↦ f (L.label ω (-1)))
    (fun ω ↦ g (L.label ω (-1))) (fun ω ↦ hf (L.label ω (-1)))
  have hlag (l : ℕ) (_ : 0 < l) (hl : 2 * l ≤ k + 1) :
      (∑ i ∈ range l, ‖G (k - i) - G (k - (l + i))‖ ^ 2) ≤
        l * (α * D / δ) := by
    have hh := lag_energy X G (L.shift (-1)) _ _ hα hsmooth
      (fun U V ↦ by simpa only [dist_eq_norm] using (L.shift (-1)).dist_map U V)
      (L.past_succ g x0 h0) (fun _ ↦ rfl) l (k + 1 - l)
    have hd := hdisp l (by omega)
    have hs : 0 ≤ ∑ j ∈ range (k + 1 - l), ‖G (l + j) - G j‖ ^ 2 :=
      sum_nonneg (fun _ _ ↦ sq_nonneg _)
    have hcoeff : δ / α ≤ (2 - α) / α := div_le_div_of_nonneg_right hδα hα.le
    have hmul := mul_le_mul_of_nonneg_right hcoeff hs
    have hh' : δ / α * (∑ j ∈ range (k + 1 - l), ‖G (l + j) - G j‖ ^ 2) ≤
        l * D := by
      dsimp [X] at hh
      nlinarith only [hh, hd, hmul, sq_nonneg ‖X (l + (k + 1 - l)) - X (k + 1 - l)‖]
    have hc : (∑ j ∈ range (k + 1 - l), ‖G (l + j) - G j‖ ^ 2) ≤
        l * D / (δ / α) := (le_div_iff₀ (show 0 < δ / α by positivity)).mpr
      (by nlinarith only [hh'])
    have he : (l : ℝ) * D / (δ / α) = l * (α * D / δ) := by
      field_simp
    rw [he] at hc
    have hr := reversed_lag_sum_le G hl
    simpa only [Nat.add_sub_cancel] using hr.trans hc
  have he : (∑ i ∈ range (k + 1), ‖G (k - i)‖ ^ 2) ≤ (k + 1 : ℕ) * B := by
    have hr := reverse_suffix_sum (fun j ↦ ‖G j‖ ^ 2) (le_refl (k + 1))
    simp only [Nat.add_sub_cancel, Nat.sub_self, Nat.zero_add] at hr
    rw [hr]
    exact henergy (k + 1) (by omega)
  have hh := dyadic_log_bound (fun i ↦ G (k - i)) (by omega : 0 < k + 1)
    (show k + 1 ≤ M by omega) (show 0 ≤ α * D / δ by positivity) hB he hlag
  simpa only [Nat.sub_zero] using hh

end HistoryLaw

end LastIterate
