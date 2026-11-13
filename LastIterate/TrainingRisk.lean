module

public import LastIterate.DeletionSampling
public import LastIterate.EndpointConstants
public import LastIterate.PrefixSampling

@[expose] public section

/-! # Risk on the labels used during the actual pass -/

namespace LastIterate

open Finset
open scoped Fin.NatCast

variable {Ω Z E : Type*} [Fintype Ω]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace NoiseModel

theorem training_loss_bound {m : ℕ} [NeZero m] (p : NoiseModel Z E)
    (L : HistoryLaw Ω Z m) (v : ResidualControl p L)
    (x0 : Ω → E) (h0 : L.StartInvariant x0) :
    (∑ i : Fin m, ∑ ω, p.loss (L.label ω i) (L.current p.step x0 m ω)) ≤
      60000 * m * polylog m *
        baseRate p.δ (‖L.current p.step x0 0 - p.starField‖ ^ 2) v.variance m := by
  cases m with
  | zero => exact False.elim (NeZero.ne 0 rfl)
  | succ t =>
    have hm : 0 < t + 1 := Nat.succ_pos t
    have hs := sum_le_sum (s := (univ : Finset (Fin (t + 1))))
      (fun i _ ↦ L.used_label_bound p x0 h0 i)
    simp only [sum_add_distrib, sum_const, card_univ, Fintype.card_fin,
      nsmul_eq_mul, ← mul_sum] at hs
    have he : (∑ i : Fin (t + 1), ‖L.queriedGradient p.g x0 i.val‖ ^ 2) =
        ∑ j ∈ range (t + 1), ‖L.queriedGradient p.g x0 j‖ ^ 2 :=
      Fin.sum_univ_eq_sum_range (fun (j : ℕ) ↦ ‖L.queriedGradient p.g x0 j‖ ^ 2) (t + 1)
    rw [he] at hs
    have hA := p.queried_loss_bound L v x0 h0 (le_refl (t + 1))
    have hG := p.queried_gradient_bound L v x0 h0 (le_refl (t + 1))
    simp only [Nat.add_sub_cancel] at hA hG
    have hS := (p.gradient_energy L v x0 h0).trans
      (energy_coarse hm p.alpha_pos.le p.alpha_lt_two.le p.delta_pos p.delta_le_one
        (sq_nonneg _) v.nonneg)
    have hc := training_constant hm p.alpha_pos p.alpha_lt_two.le
      (baseRate_nonneg p.delta_pos (sq_nonneg _) v.nonneg (t + 1)) hA hG hS
    nlinarith only [hs, hc]

end NoiseModel

end LastIterate
