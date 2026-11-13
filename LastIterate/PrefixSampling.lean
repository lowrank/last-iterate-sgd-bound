module

public import LastIterate.GlobalQuery

@[expose] public section

/-! # Restricting an exchangeable history to its actual prefix -/

namespace LastIterate

open Finset
open scoped Fin.NatCast RealInnerProductSpace

variable {Ω Z E : Type*} {m k : ℕ} [Fintype Ω]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace HistoryLaw

def firstEmbedding (h : k ≤ m) : Fin k ↪ Fin m := ⟨Fin.castLE h, Fin.castLE_injective h⟩

noncomputable def prefixLaw (L : HistoryLaw Ω Z m) (h : k ≤ m) : HistoryLaw Ω Z k :=
  L.restrict (firstEmbedding h)

variable [NeZero m] [NeZero k]

theorem prefix_start (L : HistoryLaw Ω Z m) (x0 : Ω → E) (h0 : L.StartInvariant x0)
    (h : k ≤ m) : (L.prefixLaw h).StartInvariant x0 := by
  intro e ω
  exact h0 _ ω

theorem prefix_current (L : HistoryLaw Ω Z m) (step : Z → E → E)
    (x0 : Ω → E) (h : k ≤ m) {s : ℕ} (hs : s ≤ k) :
    (L.prefixLaw h).current step x0 s = L.current step x0 s := by
  ext ω
  change forward step (x0 ω) (fun j ↦ L.label ω (Fin.castLE h (j : Fin k))) s =
    forward step (x0 ω) (fun j ↦ L.label ω (j : Fin m)) s
  apply forward_congr
  intro j hj
  congr 1
  apply Fin.ext
  simp only [Fin.coe_castLE, Fin.val_natCast,
    Nat.mod_eq_of_lt (show j < k by omega), Nat.mod_eq_of_lt (show j < m by omega)]

theorem prefix_query (L : HistoryLaw Ω Z m) (f : Z → E → ℝ) (step : Z → E → E)
    (x0 : Ω → E) (h0 : L.StartInvariant x0) (h : k ≤ m) {s : ℕ} (hs : s < k) :
    (L.prefixLaw h).queriedLoss f step x0 s = L.queriedLoss f step x0 s := by
  rw [(L.prefixLaw h).queriedLoss_forward f step x0 (L.prefix_start x0 h0 h),
    L.queriedLoss_forward f step x0 h0, L.prefix_current step x0 h hs.le]
  have hi : Fin.castLE h (s : Fin k) = (s : Fin m) := by
    apply Fin.ext
    simp only [Fin.coe_castLE, Fin.val_natCast, Nat.mod_eq_of_lt hs,
      Nat.mod_eq_of_lt (lt_of_lt_of_le hs h)]
  apply sum_congr rfl
  intro ω _
  change f (L.label ω (Fin.castLE h (s : Fin k))) _ = _
  rw [hi]

theorem prefix_gradient (L : HistoryLaw Ω Z m) (g : Z → E → E)
    (x0 : Ω → E) (h0 : L.StartInvariant x0) (h : k ≤ m) {s : ℕ} (hs : s < k) :
    ‖(L.prefixLaw h).queriedGradient g x0 s‖ ^ 2 = ‖L.queriedGradient g x0 s‖ ^ 2 := by
  rw [HistoryLaw.queriedGradient_sq_loss, HistoryLaw.queriedGradient_sq_loss]
  exact L.prefix_query _ _ x0 h0 h hs

theorem current_prefixRun (L : HistoryLaw Ω Z m) (step : Z → E → E)
    (x0 : E) (h : k ≤ m) (ω : Ω) :
    L.current step (fun _ ↦ x0) k ω =
      (List.ofFn (fun i : Fin k ↦ L.label ω (Fin.castLE h i))).foldl
        (fun x z ↦ step z x) x0 := by
  rw [current_apply, forward_foldl]
  congr 2
  funext i
  congr 1
  apply Fin.ext
  simp only [Fin.val_natCast, Fin.coe_castLE,
    Nat.mod_eq_of_lt (lt_of_lt_of_le i.isLt h)]

end HistoryLaw

end LastIterate
