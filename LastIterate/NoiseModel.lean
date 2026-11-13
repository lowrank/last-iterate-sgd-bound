module

public import LastIterate.ResidualSampling
public import LastIterate.ScalarDrift
public import LastIterate.Normalization

@[expose] public section

/-! # Centered smooth losses and their residual gradients -/

namespace LastIterate

open Finset
open scoped Fin.NatCast RealInnerProductSpace

variable {Z E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

structure NoiseModel (Z E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  h : Z → E → ℝ
  q : Z → E → E
  ζ : Z → E
  star : E
  α : ℝ
  δ : ℝ
  alpha_pos : 0 < α
  delta_pos : 0 < δ
  delta_le_one : δ ≤ 1
  delta_le : δ ≤ 2 - α
  smooth : ∀ z, SmoothInterpolation (h z) (q z) α
  zero_loss : ∀ z, h z star = 0
  zero_grad : ∀ z, q z star = 0

namespace NoiseModel

def g (p : NoiseModel Z E) (z : Z) (x : E) : E := p.q z x + p.ζ z

def loss (p : NoiseModel Z E) (z : Z) (x : E) : ℝ := p.h z x + ⟪p.ζ z, x - p.star⟫

def step (p : NoiseModel Z E) (z : Z) (x : E) : E := x - p.g z x

theorem alpha_lt_two (p : NoiseModel Z E) : p.α < 2 := by
  linarith [p.delta_pos, p.delta_le]

theorem nonneg (p : NoiseModel Z E) (z : Z) (x : E) : 0 ≤ p.h z x := by
  have hh := p.smooth z p.star x
  rw [p.zero_loss, p.zero_grad, inner_zero_left, zero_add, zero_add, sub_zero] at hh
  exact (div_nonneg (sq_nonneg _) (by linarith [p.alpha_pos])).trans hh

theorem loss_smooth (p : NoiseModel Z E) (z : Z) :
    SmoothInterpolation (p.loss z) (p.g z) p.α := by
  intro x y
  have hh := p.smooth z x y
  dsimp [loss, g]
  rw [add_sub_add_right_eq_sub]
  simp only [inner_add_left, inner_sub_right] at *
  linarith

variable {Ω : Type*} {m : ℕ} [Fintype Ω] [NeZero m]

noncomputable def lossAt (p : NoiseModel Z E) (L : HistoryLaw Ω Z m) (i : Fin m) :
    HistorySpace Ω E → ℝ := liftLoss (fun ω ↦ p.h (L.label ω i))

noncomputable def gradientAt (p : NoiseModel Z E) (L : HistoryLaw Ω Z m) (i : Fin m) :
    HistorySpace Ω E → HistorySpace Ω E := liftGradient (fun ω ↦ p.q (L.label ω i))

noncomputable def starField (p : NoiseModel Z E) : HistorySpace Ω E :=
  WithLp.toLp 2 (fun _ ↦ p.star)

theorem lossAt_smooth (p : NoiseModel Z E) (L : HistoryLaw Ω Z m) (i : Fin m) :
    SmoothInterpolation (p.lossAt L i) (p.gradientAt L i) p.α :=
  lift_interpolation _ _ (fun ω ↦ p.smooth (L.label ω i))

theorem lossAt_nonneg (p : NoiseModel Z E) (L : HistoryLaw Ω Z m)
    (i : Fin m) (U : HistorySpace Ω E) : 0 ≤ p.lossAt L i U :=
  sum_nonneg (fun ω _ ↦ p.nonneg (L.label ω i) (U ω))

theorem lossAt_star (p : NoiseModel Z E) (L : HistoryLaw Ω Z m) (i : Fin m) :
    p.lossAt L i p.starField = 0 := by
  change (∑ ω, p.h (L.label ω i) p.star) = 0
  simp only [p.zero_loss, sum_const_zero]

theorem gradientAt_star (p : NoiseModel Z E) (L : HistoryLaw Ω Z m) (i : Fin m) :
    p.gradientAt L i p.starField = 0 := by
  ext ω
  exact p.zero_grad (L.label ω i)

theorem gradientAt_self_bound (p : NoiseModel Z E) (L : HistoryLaw Ω Z m)
    (i : Fin m) (U : HistorySpace Ω E) :
    ‖p.gradientAt L i U‖ ^ 2 ≤ 2 * p.α * p.lossAt L i U :=
  self_bound_at_common_zero p.alpha_pos (p.lossAt_smooth L i)
    (p.lossAt_star L i) (p.gradientAt_star L i) U

theorem update (p : NoiseModel Z E) (L : HistoryLaw Ω Z m) (x0 : Ω → E) (j : ℕ) :
    L.current p.step x0 (j + 1) = L.current p.step x0 j -
      p.gradientAt L (j : Fin m) (L.current p.step x0 j) - L.residual p.ζ (j : Fin m) := by
  ext ω
  change L.current p.step x0 j ω -
      (p.q (L.label ω (j : Fin m)) (L.current p.step x0 j ω) + p.ζ (L.label ω (j : Fin m))) =
    L.current p.step x0 j ω - p.q (L.label ω (j : Fin m)) (L.current p.step x0 j ω) -
      p.ζ (L.label ω (j : Fin m))
  abel

theorem initial_loss (p : NoiseModel Z E) (L : HistoryLaw Ω Z m)
    (x0 : Ω → E) (h0 : L.StartInvariant x0) (i : Fin m) :
    p.lossAt L i (L.current p.step x0 0) = L.queriedLoss p.h p.step x0 0 := by
  rw [L.queriedLoss_forward p.h p.step x0 h0]
  exact L.sum_future_query p.step x0 h0 p.h i 0 (by omega) (by omega)

/-- Exact one-step radius drift in the finite history Hilbert space. -/
theorem radius_step (p : NoiseModel Z E) (L : HistoryLaw Ω Z m)
    (x0 : Ω → E) (j : ℕ) :
    ‖L.current p.step x0 (j + 1) - p.starField‖ ^ 2 -
      ‖L.current p.step x0 j - p.starField‖ ^ 2 +
      p.δ * p.lossAt L (j : Fin m) (L.current p.step x0 j) ≤
      (1 + 2 * p.α / p.δ) * ‖L.residual p.ζ (j : Fin m)‖ ^ 2 -
        2 * ⟪L.current p.step x0 j - p.starField, L.residual p.ζ (j : Fin m)⟫ := by
  let U := L.current p.step x0 j
  let Q := p.gradientAt L (j : Fin m) U
  have hc := p.lossAt_smooth L (j : Fin m) U p.starField
  rw [p.lossAt_star, p.gradientAt_star, zero_sub, norm_neg] at hc
  have hi : ⟪Q, p.starField - U⟫ = -⟪U - p.starField, Q⟫ := by
    rw [inner_sub_right, inner_sub_left]
    rw [real_inner_comm U Q, real_inner_comm p.starField Q]
    ring
  change p.lossAt L (j : Fin m) U + ⟪Q, p.starField - U⟫ + ‖Q‖ ^ 2 / (2 * p.α) ≤ 0 at hc
  rw [hi] at hc
  have hci : 2 * p.lossAt L (j : Fin m) U + ‖Q‖ ^ 2 / p.α ≤ 2 * ⟪U - p.starField, Q⟫ := by
    linear_combination 2 * hc
  have hh := noisy_distance_step (U - p.starField) Q (L.residual p.ζ (j : Fin m))
    p.alpha_pos p.delta_pos p.delta_le_one p.delta_le (p.lossAt_nonneg L _ U)
    (p.gradientAt_self_bound L _ U) hci
  rw [p.update]
  have he : L.current p.step x0 j - p.gradientAt L (j : Fin m)
      (L.current p.step x0 j) - L.residual p.ζ (j : Fin m) - p.starField =
      (U - p.starField) - Q - L.residual p.ζ (j : Fin m) := by dsimp [U, Q]; abel
  rw [he]
  exact hh

/-- Exact one-step drift from the (possibly random, past-dependent) restart state. -/
theorem initial_step (p : NoiseModel Z E) (L : HistoryLaw Ω Z m)
    (x0 : Ω → E) (h0 : L.StartInvariant x0) (j : ℕ) :
    ‖L.current p.step x0 (j + 1) - L.current p.step x0 0‖ ^ 2 -
      ‖L.current p.step x0 j - L.current p.step x0 0‖ ^ 2 +
      p.δ * p.lossAt L (j : Fin m) (L.current p.step x0 j) ≤
      8 * L.queriedLoss p.h p.step x0 0 / p.δ +
        (1 + 4 * p.α / p.δ) * ‖L.residual p.ζ (j : Fin m)‖ ^ 2 -
        2 * ⟪L.current p.step x0 j - L.current p.step x0 0,
          L.residual p.ζ (j : Fin m)⟫ := by
  let U := L.current p.step x0 j
  let V := L.current p.step x0 0
  let Q := p.gradientAt L (j : Fin m) U
  let R := p.gradientAt L (j : Fin m) V
  have hc := p.lossAt_smooth L (j : Fin m) U V
  have hi : ⟪Q, V - U⟫ = -⟪Q, U - V⟫ := by simp only [inner_sub_right]; ring
  change p.lossAt L (j : Fin m) U + ⟪Q, V - U⟫ + ‖R - Q‖ ^ 2 / (2 * p.α) ≤
    p.lossAt L (j : Fin m) V at hc
  rw [hi, norm_sub_rev R Q] at hc
  have hh := noisy_initial_step (U - V) Q R (L.residual p.ζ (j : Fin m))
    p.alpha_pos p.delta_pos p.delta_le_one p.delta_le (p.lossAt_nonneg L _ U)
    (p.lossAt_nonneg L _ V) (p.gradientAt_self_bound L _ U)
    (p.gradientAt_self_bound L _ V) (by simpa only [sub_eq_add_neg] using hc)
  rw [p.update]
  have he : L.current p.step x0 j - p.gradientAt L (j : Fin m)
      (L.current p.step x0 j) - L.residual p.ζ (j : Fin m) - L.current p.step x0 0 =
      (U - V) - Q - L.residual p.ζ (j : Fin m) := by dsimp [U, V, Q]; abel
  rw [he]
  rw [p.initial_loss L x0 h0] at hh
  exact hh

end NoiseModel

end LastIterate
