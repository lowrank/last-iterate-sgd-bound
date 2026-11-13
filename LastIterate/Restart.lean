module

public import LastIterate.NoiseBudgets
public import Mathlib.Logic.Equiv.Fintype

@[expose] public section

/-! # Restarting by permutations that fix the already observed prefix -/

namespace LastIterate

open Finset
open scoped Fin.NatCast RealInnerProductSpace

variable {Ω Z E : Type*} {m k : ℕ}

namespace HistoryLaw

noncomputable def restrict (L : HistoryLaw Ω Z m) (q : Fin k ↪ Fin m) :
    HistoryLaw Ω Z k where
  label ω i := L.label ω (q i)
  reindex e := L.reindex (e.viaFintypeEmbedding q)
  label_reindex e ω i := by
    rw [L.label_reindex, Equiv.Perm.viaFintypeEmbedding_apply_image]

def tailEmbedding (r m : ℕ) : Fin (m - r) ↪ Fin m where
  toFun i := ⟨r + i.val, by omega⟩
  inj' := by
    intro i j h
    have he := congrArg Fin.val h
    apply Fin.ext
    change r + i.val = r + j.val at he
    omega

noncomputable def restart (L : HistoryLaw Ω Z m) (r : ℕ) : HistoryLaw Ω Z (m - r) :=
  L.restrict (tailEmbedding r m)

variable [Fintype Ω] [NeZero m] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem restart_start (L : HistoryLaw Ω Z m) (step : Z → E → E)
    (x0 : Ω → E) (h0 : L.StartInvariant x0) {r : ℕ} (hr : r ≤ m) :
    (L.restart r).StartInvariant (fun ω ↦ L.current step x0 r ω) := by
  classical
  intro e ω
  change forward step (x0 (L.reindex (e.viaFintypeEmbedding (tailEmbedding r m)) ω))
      (fun i ↦ L.label (L.reindex (e.viaFintypeEmbedding (tailEmbedding r m)) ω) (i : Fin m)) r =
    forward step (x0 ω) (fun i ↦ L.label ω (i : Fin m)) r
  rw [h0]
  apply forward_congr
  intro j hj
  rw [L.label_reindex, Equiv.Perm.viaFintypeEmbedding_apply_notMem_range]
  rintro ⟨i, hi⟩
  have he := congrArg Fin.val hi
  change r + i.val = ((j : Fin m) : ℕ) at he
  rw [Fin.val_natCast, Nat.mod_eq_of_lt (show j < m by omega)] at he
  omega

theorem restart_current (L : HistoryLaw Ω Z m) (step : Z → E → E)
    (x0 : Ω → E) {r : ℕ} [NeZero (m - r)] {s : ℕ} (hs : s ≤ m - r) :
    (L.restart r).current step (fun ω ↦ L.current step x0 r ω) s =
      L.current step x0 (r + s) := by
  ext ω
  change forward step (forward step (x0 ω) (fun i ↦ L.label ω (i : Fin m)) r)
      (fun i ↦ L.label ω (tailEmbedding r m (i : Fin (m - r)))) s =
    forward step (x0 ω) (fun i ↦ L.label ω (i : Fin m)) (r + s)
  rw [forward_add]
  apply forward_congr
  intro j hj
  congr 1
  apply Fin.ext
  change r + ((j : Fin (m - r)) : ℕ) = (((r + j : ℕ) : Fin m) : ℕ)
  simp only [Fin.val_natCast, Nat.mod_eq_of_lt (show j < m - r by omega),
    Nat.mod_eq_of_lt (show r + j < m by omega)]

theorem restart_query (L : HistoryLaw Ω Z m) (f : Z → E → ℝ) (step : Z → E → E)
    (x0 : Ω → E) (h0 : L.StartInvariant x0) {r s : ℕ} [NeZero (m - r)]
    (hr : r ≤ m) (hs : s < m - r) :
    (L.restart r).queriedLoss f step (fun ω ↦ L.current step x0 r ω) s =
      L.queriedLoss f step x0 (r + s) := by
  rw [(L.restart r).queriedLoss_forward f step _ (L.restart_start step x0 h0 hr),
    L.queriedLoss_forward f step x0 h0, L.restart_current step x0 (Nat.le_of_lt hs)]
  apply sum_congr rfl
  intro ω _
  have hi : tailEmbedding r m (s : Fin (m - r)) = ((r + s : ℕ) : Fin m) := by
    apply Fin.ext
    change r + ((s : Fin (m - r)) : ℕ) = (((r + s : ℕ) : Fin m) : ℕ)
    simp only [Fin.val_natCast, Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt (show r + s < m by omega)]
  change f (L.label ω (tailEmbedding r m (s : Fin (m - r)))) _ = _
  rw [hi]

theorem restart_gradient (L : HistoryLaw Ω Z m) (g : Z → E → E)
    (x0 : Ω → E) (h0 : L.StartInvariant x0) {r s : ℕ} [NeZero (m - r)]
    (hr : r ≤ m) (hs : s < m - r) :
    ‖(L.restart r).queriedGradient g
      (fun ω ↦ L.current (fun z x ↦ x - g z x) x0 r ω) s‖ ^ 2 =
      ‖L.queriedGradient g x0 (r + s)‖ ^ 2 := by
  rw [HistoryLaw.queriedGradient_sq_loss, HistoryLaw.queriedGradient_sq_loss]
  exact L.restart_query (fun z x ↦ ‖g z x‖ ^ 2) (fun z x ↦ x - g z x) x0 h0 hr hs

end HistoryLaw

namespace ResidualControl

variable [Fintype Ω] [NeZero m] [NeZero k]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def restrict {p : NoiseModel Z E} {L : HistoryLaw Ω Z m}
    (v : ResidualControl p L) (q : Fin k ↪ Fin m) : ResidualControl p (L.restrict q) where
  variance := v.variance
  nonneg := v.nonneg
  diagonal i := v.diagonal (q i)
  cross i j h := v.cross (q i) (q j) (fun he ↦ h (q.injective he))

end ResidualControl

end LastIterate
