module

public import LastIterate.NoiseBudgets
public import LastIterate.GradientSampling

@[expose] public section

/-! # Log-log improved amplification for actual exchangeable histories -/

namespace LastIterate

open Finset
open scoped Fin.NatCast RealInnerProductSpace

variable {Ω Z E : Type*} {m : ℕ} [Fintype Ω] [NeZero m]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace NoiseModel

noncomputable def initialLinear (p : NoiseModel Z E) (L : HistoryLaw Ω Z m)
    (x0 : Ω → E) : ℝ := L.queriedLoss (fun z x ↦ ⟪p.ζ z, x - p.star⟫) p.step x0 0

theorem loss_decomposition (p : NoiseModel Z E) (L : HistoryLaw Ω Z m)
    (x0 : Ω → E) (h0 : L.StartInvariant x0) (j : ℕ) :
    L.queriedLoss p.loss p.step x0 j =
      p.lossAt L (j : Fin m) (L.current p.step x0 j) +
      ⟪L.residual p.ζ (j : Fin m), L.current p.step x0 j - L.current p.step x0 0⟫ +
        p.initialLinear L x0 := by
  have hμ : (∑ ω, ⟪p.ζ (L.label ω (j : Fin m)), L.current p.step x0 0 ω - p.star⟫) =
      p.initialLinear L x0 := by
    unfold initialLinear
    rw [L.queriedLoss_forward _ p.step x0 h0]
    simpa only [Nat.cast_zero] using L.sum_future_query p.step x0 h0
      (fun z x ↦ ⟪p.ζ z, x - p.star⟫) (k := 0) (j : Fin m) 0 (by omega) (by omega)
  rw [L.queriedLoss_forward p.loss p.step x0 h0, ← hμ, PiLp.inner_apply]
  change (∑ ω, (p.h (L.label ω (j : Fin m)) (L.current p.step x0 j ω) +
      ⟪p.ζ (L.label ω (j : Fin m)), L.current p.step x0 j ω - p.star⟫)) =
    (∑ ω, p.h (L.label ω (j : Fin m)) (L.current p.step x0 j ω)) +
      (∑ ω, ⟪p.ζ (L.label ω (j : Fin m)),
        L.current p.step x0 j ω - L.current p.step x0 0 ω⟫) +
      ∑ ω, ⟪p.ζ (L.label ω (j : Fin m)), L.current p.step x0 0 ω - p.star⟫
  simp only [inner_sub_right, sum_add_distrib, sum_sub_distrib]
  ring

theorem budget_le_div (p : NoiseModel Z E) (L : HistoryLaw Ω Z m)
    (x0 : Ω → E) {v : ℝ} (hv : 0 ≤ v) :
    p.budget L x0 v ≤ p.budget L x0 v / p.δ := by
  apply (le_div_iff₀ p.delta_pos).mpr
  have hh := mul_le_mul_of_nonneg_left p.delta_le_one (p.budget_nonneg L x0 hv)
  simpa only [mul_one] using hh

theorem loss_average (p : NoiseModel Z E) (L : HistoryLaw Ω Z m) (v : ResidualControl p L)
    (x0 : Ω → E) (h0 : L.StartInvariant x0) :
    (∑ j ∈ range m, L.queriedLoss p.loss p.step x0 j) ≤
      m * (p.initialLinear L x0 + 2 * (p.budget L x0 v.variance / p.δ)) := by
  let K := p.budget L x0 v.variance
  have hK : 0 ≤ K := p.budget_nonneg L x0 v.nonneg
  have hdiff (j : ℕ) (hj : j < m) :
      ⟪L.residual p.ζ (j : Fin m), L.current p.step x0 j - L.current p.step x0 0⟫ ≤
        (Real.sqrt v.variance * Real.sqrt K) *
          (Real.sqrt j / Real.sqrt (m - j : ℕ)) := by
    have hi := L.futureInvariant_current p.step x0 h0 (le_refl j)
    have ht := L.futureInvariant_current p.step x0 h0 (Nat.zero_le j)
    have hc := p.correlation L v _ hj le_rfl (L.futureInvariant_sub hi ht)
    have hd := p.displacement_budget L v x0 h0 (Nat.le_of_lt hj)
    rw [L.past_current_distance p.step x0 h0] at hd
    have hroot := Real.sqrt_le_sqrt hd
    rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul (Nat.cast_nonneg (α := ℝ) j)] at hroot
    have hmul := mul_le_mul_of_nonneg_left hroot (Real.sqrt_nonneg v.variance)
    have hdiv := div_le_div_of_nonneg_right hmul (Real.sqrt_nonneg (m - j : ℕ))
    have hinner := le_abs_self
      ⟪L.residual p.ζ (j : Fin m), L.current p.step x0 j - L.current p.step x0 0⟫
    calc
      _ ≤ Real.sqrt v.variance * ‖L.current p.step x0 j - L.current p.step x0 0‖ /
          Real.sqrt (m - j : ℕ) := hinner.trans hc
      _ ≤ _ := by convert! hdiv using 1 <;> ring
  have hsum := sum_le_sum (s := range m) (fun j hj ↦ hdiff j (mem_range.mp hj))
  rw [← mul_sum] at hsum
  have hs := mul_le_mul_of_nonneg_left (sum_sqrt_ratio (le_refl m))
    (mul_nonneg (Real.sqrt_nonneg v.variance) (Real.sqrt_nonneg K))
  have hvK := p.variance_le_budget L x0 v.nonneg
  have hroot : 2 * Real.sqrt v.variance * Real.sqrt K ≤ K := by
    have hv := Real.sq_sqrt v.nonneg
    have hk := Real.sq_sqrt hK
    dsimp [K] at hk ⊢
    nlinarith [sq_nonneg (Real.sqrt K - 2 * Real.sqrt v.variance), v.nonneg]
  have hr := mul_le_mul_of_nonneg_left hroot (Nat.cast_nonneg (α := ℝ) m)
  have hδ := mul_le_mul_of_nonneg_left (p.budget_le_div L x0 v.nonneg)
    (Nat.cast_nonneg (α := ℝ) m)
  have he := p.initial_budget L v x0 h0 (le_refl m)
  have hφ : (∑ j ∈ range m, p.lossAt L (j : Fin m) (L.current p.step x0 j)) ≤ m * K / p.δ := by
    apply (le_div_iff₀ p.delta_pos).mpr
    nlinarith only [he, sq_nonneg ‖L.current p.step x0 m - L.current p.step x0 0‖]
  simp_rw [p.loss_decomposition L x0 h0]
  simp only [sum_add_distrib, sum_const, card_range, nsmul_eq_mul]
  dsimp [K] at hsum hs hr hφ
  linear_combination hsum + hs + hr + hδ + hφ

theorem gradient_uniform (p : NoiseModel Z E) (L : HistoryLaw Ω Z m)
    (v : ResidualControl p L) (x0 : Ω → E) (h0 : L.StartInvariant x0)
    {M : ℕ} (hmM : m ≤ M) {j : ℕ} (hj : j < m) :
    ‖L.queriedGradient p.g x0 j‖ ^ 2 ≤
      44 * ell M ^ 2 * (p.budget L x0 v.variance / p.δ) := by
  let K := p.budget L x0 v.variance
  have hK : 0 ≤ K := p.budget_nonneg L x0 v.nonneg
  have hQ : 0 ≤ K / p.δ := div_nonneg hK p.delta_pos.le
  have hvK := p.variance_le_budget L x0 v.nonneg
  have hKd := p.budget_le_div L x0 v.nonneg
  have hv : v.variance ≤ K / p.δ := by dsimp [K]; nlinarith [v.nonneg]
  have ha := mul_le_mul_of_nonneg_right p.alpha_lt_two.le hQ
  have hB : 0 ≤ 4 * p.α * K / p.δ + 2 * v.variance := by
    have := v.nonneg
    have := p.alpha_pos
    have := p.delta_pos
    positivity
  have hg := L.gradient_bound p.loss p.g x0 h0 p.alpha_pos p.delta_pos p.delta_le
    p.loss_smooth hB hK hmM (fun s hs ↦ p.displacement_budget L v x0 h0 hs)
    (fun s hs ↦ p.gradient_budget L v x0 h0 hs) hj
  have hαD : p.α * K / p.δ ≤ 2 * (K / p.δ) := by convert! ha using 1 <;> ring
  have hBB : 4 * p.α * K / p.δ + 2 * v.variance ≤ 10 * (K / p.δ) := by
    linear_combination 4 * hαD + 2 * hv
  have hBB' := mul_le_mul_of_nonneg_left hBB (by norm_num : (0 : ℝ) ≤ 4)
  have hC := mul_le_mul_of_nonneg_left hαD (show 0 ≤ 2 * ell M ^ 2 by positivity)
  have hl := one_le_ell (show 0 < M by omega)
  have hsq : 1 ≤ ell M ^ 2 := by nlinarith
  have hsq' := mul_le_mul_of_nonneg_right hsq hQ
  dsimp [K] at hg hBB' hC hsq'
  linear_combination hg + hBB' + hC + 40 * hsq'

theorem history_amplification (p : NoiseModel Z E) (L : HistoryLaw Ω Z m)
    (v : ResidualControl p L) (x0 : Ω → E) (h0 : L.StartInvariant x0)
    {M : ℕ} (hmM : m ≤ M) :
    L.queriedLoss p.loss p.step x0 (m - 1) ≤ p.initialLinear L x0 +
      73 * polylog M * (p.budget L x0 v.variance / p.δ) := by
  let K := p.budget L x0 v.variance
  let a := L.queriedLoss p.loss p.step x0
  let k := fun j ↦ ‖L.queriedGradient p.g x0 j‖ ^ 2
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hK : 0 ≤ K := p.budget_nonneg L x0 v.nonneg
  have hwindow := window_of_frozen a k
    (B := 44 * ell M ^ 2 * (K / p.δ)) (D := K)
    (fun j hj ↦ p.gradient_uniform L v x0 h0 hmM hj) (fun r s l hrs _ hsl ↦ by
      have hh := L.frozen_comparison p.loss p.g x0 h0 p.alpha_pos p.loss_smooth hrs hsl
      have hd := L.past_distance p.step x0 h0
        (fun z x y ↦ nonexpansive_step (p.loss_smooth z) p.alpha_pos p.alpha_lt_two.le x y)
        (s - r) r
      rw [Nat.sub_add_cancel hrs] at hd
      have he := p.displacement_budget L v x0 h0 (show s - r ≤ m by omega)
      have hd' := hd.trans he
      calc
        (∑ i ∈ range l, (a (s + i) - k (s + i) / 2)) ≤
            l * a r + ‖L.past p.step x0 0 s - L.past p.step x0 0 r‖ ^ 2 / 2 := hh
        _ ≤ l * a r + (s - r : ℕ) * K / 2 := by
          change _ ≤ l * a r + (s - r : ℕ) * p.budget L x0 v.variance / 2
          linarith only [hd'])
  have hav : mean (fun i ↦ a (m - 1 - i)) m ≤ p.initialLinear L x0 + 2 * (K / p.δ) := by
    unfold mean
    rw [reverse_suffix_sum a (le_refl m), Nat.sub_self]
    simp only [Nat.zero_add]
    apply (div_le_iff₀ (show (0 : ℝ) < m by exact_mod_cast hm)).mpr
    have hh := p.loss_average L v x0 h0
    nlinarith only [hh]
  have hh := noisy_amplification (fun i ↦ a (m - 1 - i)) hm hmM hK p.delta_pos hwindow
    (by have := p.delta_pos; positivity) (by positivity) hav
    (by ring_nf; exact le_rfl)
    (by have hd := p.budget_le_div L x0 v.nonneg; dsimp [K]; linarith)
  simpa only [Nat.sub_zero] using hh

end NoiseModel

end LastIterate
