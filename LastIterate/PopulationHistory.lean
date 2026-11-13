module

public import LastIterate.TrainingRisk

@[expose] public section

/-! # Averaging used and unused positions, including a complete pass -/

namespace LastIterate

open Finset
open scoped Fin.NatCast

variable {Ω Z E : Type*} {m T : ℕ} [Fintype Ω] [NeZero m]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace NoiseModel

theorem all_positions_bound (p : NoiseModel Z E) (L : HistoryLaw Ω Z m)
    (v : ResidualControl p L) (x0 : Ω → E) (h0 : L.StartInvariant x0)
    (hT : 0 < T) (hTm : T ≤ m) :
    (∑ i : Fin m, ∑ ω, p.loss (L.label ω i) (L.current p.step x0 T ω)) ≤
      280000 * m * polylog T *
        baseRate p.δ (‖L.current p.step x0 0 - p.starField‖ ^ 2) v.variance T := by
  let : NeZero T := ⟨by omega⟩
  let R := ‖L.current p.step x0 0 - p.starField‖ ^ 2
  let Q := baseRate p.δ R v.variance T
  let B := 280000 * polylog T * Q
  let F : ℕ → ℝ := fun j ↦ ∑ ω, p.loss (L.label ω (j : Fin m)) (L.current p.step x0 T ω)
  have hQ : 0 ≤ Q := baseRate_nonneg p.delta_pos (sq_nonneg _) v.nonneg T
  have hP : 0 ≤ polylog T := by linarith [one_le_two_polylog hT]
  have htrain := p.training_loss_bound (L.prefixLaw hTm)
    (v.restrict (HistoryLaw.firstEmbedding hTm)) x0 (L.prefix_start x0 h0 hTm)
  rw [L.prefix_current p.step x0 hTm (le_refl T),
    L.prefix_current p.step x0 hTm (Nat.zero_le T)] at htrain
  have hused : (∑ j ∈ range T, F j) ≤ (T : ℝ) * B := by
    have he : (∑ j ∈ range T, F j) =
        ∑ i : Fin T, ∑ ω, p.loss ((L.prefixLaw hTm).label ω i) (L.current p.step x0 T ω) := by
      rw [← Fin.sum_univ_eq_sum_range F T]
      apply sum_congr rfl
      intro i _
      have hc : (i.val : Fin m) = Fin.castLE hTm i := by
        apply Fin.ext
        simp only [Fin.val_natCast, Fin.val_castLE,
          Nat.mod_eq_of_lt (lt_of_lt_of_le i.isLt hTm)]
      dsimp only [F]
      rw [hc]
      rfl
    rw [he]
    have hh : 0 ≤ (T : ℝ) * polylog T * Q := by positivity
    change _ ≤ 60000 * T * polylog T * Q at htrain
    dsimp only [B]
    nlinarith only [htrain, hh]
  have hfuture (j : ℕ) (hj : T ≤ j) (hjm : j < m) : F j ≤ B := by
    have hTm' : T + 1 ≤ m := by omega
    have hq := p.queried_loss_bound (L.prefixLaw hTm')
      (v.restrict (HistoryLaw.firstEmbedding hTm')) x0 (L.prefix_start x0 h0 hTm')
      (le_refl (T + 1))
    simp only [Nat.add_sub_cancel] at hq
    rw [L.prefix_query p.loss p.step x0 h0 hTm' (Nat.lt_succ_self T),
      L.prefix_current p.step x0 hTm' (Nat.zero_le _)] at hq
    have hc := successor_query_constant hT p.delta_pos (sq_nonneg
      ‖L.current p.step x0 0 - p.starField‖) v.nonneg
    have he : F j = L.queriedLoss p.loss p.step x0 T := by
      rw [L.queriedLoss_forward p.loss p.step x0 h0]
      exact L.sum_future_query p.step x0 h0 p.loss (j : Fin m) (T : Fin m)
        (by simpa only [Fin.val_natCast, Nat.mod_eq_of_lt hjm] using hj)
        (by simp only [Fin.val_natCast, Nat.mod_eq_of_lt (show T < m by omega)]; exact le_rfl)
    rw [he]
    exact hq.trans hc
  have htail : (∑ j ∈ range (m - T), F (T + j)) ≤ (m - T : ℕ) * B := by
    have hs := sum_le_sum (s := range (m - T)) (fun j hj ↦
      hfuture (T + j) (by omega) (by have := mem_range.mp hj; omega))
    simpa only [sum_const, card_range, nsmul_eq_mul] using hs
  have hsum : (∑ i : Fin m, ∑ ω, p.loss (L.label ω i) (L.current p.step x0 T ω)) =
      ∑ j ∈ range m, F j := by
    rw [← Fin.sum_univ_eq_sum_range F m]
    apply sum_congr rfl
    intro i _
    simp only [F, Fin.cast_val_eq_self]
  have hsplit : (∑ j ∈ range m, F j) =
      (∑ j ∈ range T, F j) + ∑ j ∈ range (m - T), F (T + j) := by
    conv_lhs => arg 1; rw [show m = T + (m - T) from (Nat.add_sub_of_le hTm).symm]
    exact sum_range_add F T (m - T)
  rw [hsum, hsplit]
  have he : (m : ℝ) = (T : ℝ) + (m - T : ℕ) := by
    exact_mod_cast (Nat.add_sub_of_le hTm).symm
  change _ ≤ 280000 * (m : ℝ) * polylog T * Q
  rw [he]
  dsimp only [B] at hused htail
  linarith

end NoiseModel

end LastIterate
