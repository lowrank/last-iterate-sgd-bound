module

public import LastIterate.PopulationHistory
public import LastIterate.ConcreteNoise

@[expose] public section

/-! # Population-risk bounds for the concrete finite WR and WOR laws -/

namespace LastIterate

open Finset
open scoped Fin.NatCast

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def wordRun {Z : Type*} {k : ℕ} (step : Z → E → E) (x0 : E) (z : Fin k → Z) : E :=
  (List.ofFn z).foldl (fun x a ↦ step a x) x0

theorem uniformMean_mul {Ω : Type*} [Fintype Ω] (c : ℝ) (f : Ω → ℝ) :
    uniformMean (fun ω ↦ c * f ω) = c * uniformMean f := by
  simp only [uniformMean, ← mul_sum]
  ring

theorem uniformMean_sub {Ω : Type*} [Fintype Ω] (f g : Ω → ℝ) :
    uniformMean (fun ω ↦ f ω - g ω) = uniformMean f - uniformMean g := by
  simp only [uniformMean, sum_sub_distrib, sub_div]

theorem baseRate_scale (δ R V c : ℝ) (m : ℕ) :
    baseRate δ (c * R) (c * V) m = c * baseRate δ R V m := by
  unfold baseRate
  ring

theorem mean_of_sum_rate {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (f : Ω → ℝ) (C δ R V : ℝ) (T : ℕ)
    (h : (∑ ω, f ω) ≤ C * polylog T *
      baseRate δ (Fintype.card Ω * R) (Fintype.card Ω * V) T) :
    uniformMean f ≤ C * polylog T * baseRate δ R V T := by
  have hN : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  unfold uniformMean
  apply (div_le_iff₀ hN).mpr
  rw [baseRate_scale] at h
  nlinarith only [h]

namespace NoiseModel

theorem constant_radius {Ω Z : Type*} {m : ℕ} [Fintype Ω] [NeZero m]
    (p : NoiseModel Z E) (L : HistoryLaw Ω Z m) (x0 : E) :
    ‖L.current p.step (fun _ ↦ x0) 0 - p.starField‖ ^ 2 =
      Fintype.card Ω * ‖x0 - p.star‖ ^ 2 := by
  rw [history_norm_sq]
  simp only [PiLp.sub_apply, HistoryLaw.current_apply, forward_zero, starField,
    sum_const, card_univ, nsmul_eq_mul]

theorem wr_population_bound {n T : ℕ} (p : NoiseModel (Fin n) E)
    (hn : 0 < n) (hzero : ∑ z, p.ζ z = 0) (x0 : E) (hT : 0 < T) :
    uniformMean (fun ω : WR n T ↦
      uniformMean (fun z ↦ p.loss z (wordRun p.step x0 ω))) ≤
      280000 * polylog T * baseRate p.δ (‖x0 - p.star‖ ^ 2)
        (uniformMean (fun z ↦ ‖p.ζ z‖ ^ 2)) T := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let : NeZero T := ⟨by omega⟩
  let L := wrHistoryLaw n (T + 1)
  let v := p.wrControl (m := T + 1) hn hzero
  have h0 := L.startInvariant_const x0
  have hq := p.queried_loss_bound L v (fun _ ↦ x0) h0 (le_refl (T + 1))
  simp only [Nat.add_sub_cancel] at hq
  rw [p.constant_radius L x0] at hq
  have hc := successor_query_constant hT p.delta_pos
    (mul_nonneg (Nat.cast_nonneg (Fintype.card (WR n (T + 1)))) (sq_nonneg ‖x0 - p.star‖)) v.nonneg
  have hh := hq.trans hc
  rw [L.queriedLoss_forward p.loss p.step _ h0] at hh
  have hav := mean_of_sum_rate
    (fun ω ↦ p.loss (L.label ω (T : Fin (T + 1))) (L.current p.step (fun _ ↦ x0) T ω))
    280000 p.δ (‖x0 - p.star‖ ^ 2) (uniformMean (fun z ↦ ‖p.ζ z‖ ^ 2)) T hh
  rw [← wr_last_query (fun ω : WR n T ↦ fun z ↦ p.loss z (wordRun p.step x0 ω))]
  convert! hav using 1
  apply congrArg uniformMean
  funext ω
  have hs := L.current_prefixRun p.step x0 (Nat.le_succ T) ω
  have hi : (T : Fin (T + 1)) = Fin.last T := by
    apply Fin.ext
    simp
  rw [hi]
  change p.loss (ω (Fin.last T)) _ = p.loss (ω (Fin.last T)) _
  congr 1
  exact hs.symm

theorem wor_population_bound {n T : ℕ} (p : NoiseModel (Fin n) E)
    (hn : 0 < n) (hzero : ∑ z, p.ζ z = 0) (x0 : E) (hT : 0 < T) (hTn : T ≤ n) :
    uniformMean (fun ω : WOR n T ↦
      uniformMean (fun z ↦ p.loss z (wordRun p.step x0 (fun i ↦ ω i)))) ≤
      280000 * polylog T * baseRate p.δ (‖x0 - p.star‖ ^ 2)
        (uniformMean (fun z ↦ ‖p.ζ z‖ ^ 2)) T := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let : Nonempty (WOR n n) := ⟨Function.Embedding.refl _⟩
  let : NeZero n := ⟨by omega⟩
  let : NeZero T := ⟨by omega⟩
  let L := worHistoryLaw n n
  let v := p.worControl (le_refl n) hzero
  have h0 := L.startInvariant_const x0
  have hq := p.all_positions_bound L v (fun _ ↦ x0) h0 hT hTn
  rw [p.constant_radius L x0] at hq
  have he : (∑ i : Fin n, ∑ ω, p.loss (L.label ω i) (L.current p.step (fun _ ↦ x0) T ω)) =
      (n : ℝ) * ∑ ω : WOR n n, uniformMean (fun z ↦ p.loss z (L.current p.step (fun _ ↦ x0) T ω)) := by
    rw [sum_comm, mul_sum]
    apply sum_congr rfl
    intro ω _
    change (∑ i, p.loss (ω i) _) = _
    rw [full_wor_sum ω (fun z ↦ p.loss z (L.current p.step (fun _ ↦ x0) T ω)),
      sum_eq_card_mul_mean, Fintype.card_fin]
  rw [he] at hq
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : (∑ ω : WOR n n, uniformMean (fun z ↦ p.loss z (L.current p.step (fun _ ↦ x0) T ω))) ≤
      280000 * polylog T *
        baseRate p.δ (Fintype.card (WOR n n) * ‖x0 - p.star‖ ^ 2)
          (Fintype.card (WOR n n) * uniformMean (fun z ↦ ‖p.ζ z‖ ^ 2)) T := by
    change (n : ℝ) * _ ≤ 280000 * n * polylog T *
      baseRate p.δ (Fintype.card (WOR n n) * ‖x0 - p.star‖ ^ 2)
        (Fintype.card (WOR n n) * uniformMean (fun z ↦ ‖p.ζ z‖ ^ 2)) T at hq
    nlinarith only [hq, hn0]
  have hav := mean_of_sum_rate
    (fun ω : WOR n n ↦ uniformMean (fun z ↦ p.loss z (L.current p.step (fun _ ↦ x0) T ω)))
    280000 p.δ (‖x0 - p.star‖ ^ 2) (uniformMean (fun z ↦ ‖p.ζ z‖ ^ 2)) T hs
  rw [← wor_restrict (le_refl n) (HistoryLaw.firstEmbedding hTn)
    (fun ω : WOR n T ↦ uniformMean (fun z ↦ p.loss z (wordRun p.step x0 (fun i ↦ ω i))))]
  convert! hav using 1
  apply congrArg uniformMean
  funext ω
  apply congrArg uniformMean
  funext z
  congr 1
  exact (L.current_prefixRun p.step x0 hTn ω).symm

end NoiseModel

end LastIterate
