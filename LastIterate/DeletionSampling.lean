module

public import LastIterate.GlobalQuery
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

/-! # Deleting a used label, with the exact finite permutation law -/

namespace LastIterate

open Finset
open scoped Fin.NatCast RealInnerProductSpace

variable {Z E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem smooth_upper_of_interpolation {f : E → ℝ} {g : E → E} {α : ℝ}
    (h : SmoothInterpolation f g α) (hα : 0 < α) (x y : E) :
    f x ≤ f y + ⟪g y, x - y⟫ + α / 2 * ‖x - y‖ ^ 2 := by
  have hh := h x y
  have hy := inner_young (g x - g y) (x - y) (inv_pos.mpr hα)
  rw [inner_sub_left] at hy
  have he : ⟪g x, y - x⟫ = -⟪g x, x - y⟫ := by
    simp only [inner_sub_right]; ring
  rw [he, norm_sub_rev (g y) (g x)] at hh
  simp only [div_inv_eq_mul] at hy
  linear_combination hh + hy / 2

theorem deletion_loss {f : E → ℝ} {g : E → E} {α : ℝ}
    (h : SmoothInterpolation f g α) (hα : 0 < α) (x y : E) :
    f x ≤ f y + ‖g y‖ ^ 2 / 2 + (1 + α) / 2 * ‖x - y‖ ^ 2 := by
  have hu := smooth_upper_of_interpolation h hα x y
  have hy := inner_young (g y) (x - y) (show (0 : ℝ) < 1 by norm_num)
  norm_num at hy
  linarith

def skipWord (z : ℕ → Z) (i : ℕ) : ℕ → Z := fun j ↦ z (if j < i then j else j + 1)

theorem forward_skip_distance (g : Z → E → E)
    (hstep : ∀ z x y, ‖(x - g z x) - (y - g z y)‖ ^ 2 ≤ ‖x - y‖ ^ 2)
    (x0 : E) (z : ℕ → Z) {i t : ℕ} (hi : i < t) :
    ‖forward (fun z x ↦ x - g z x) x0 z t -
      forward (fun z x ↦ x - g z x) x0 (skipWord z i) (t - 1)‖ ^ 2 ≤
      ‖g (z i) (forward (fun z x ↦ x - g z x) x0 z i)‖ ^ 2 := by
  let step := fun z x ↦ x - g z x
  have hp : forward step x0 (skipWord z i) i = forward step x0 z i := by
    apply forward_congr
    intro j hj
    simp [skipWord, hj]
  have ht : t = (i + 1) + (t - i - 1) := by omega
  have ht' : t - 1 = i + (t - i - 1) := by omega
  have he : (fun j ↦ skipWord z i (i + j)) = fun j ↦ z (i + 1 + j) := by
    funext j
    simp only [skipWord, show ¬i + j < i by omega, ite_false]
    congr 1
    omega
  change ‖forward step x0 z t - forward step x0 (skipWord z i) (t - 1)‖ ^ 2 ≤ _
  have hrun : forward step x0 z t =
      forward step (step (z i) (forward step x0 z i))
        (fun j ↦ z (i + 1 + j)) (t - i - 1) := by
    conv_lhs => rw [ht, forward_add, forward_succ]
  rw [hrun, ht', forward_add, hp, he]
  simpa only [step, sub_sub_cancel_left, norm_neg] using
    forward_nonexpansive step hstep (step (z i) (forward step x0 z i))
      (forward step x0 z i) (fun j ↦ z (i + 1 + j)) (t - i - 1)

def deletePerm {t : ℕ} (i : Fin (t + 1)) : Equiv.Perm (Fin (t + 1)) :=
  (finSuccEquiv' (Fin.last t)).trans (finSuccEquiv' i).symm

@[simp] theorem deletePerm_last {t : ℕ} (i : Fin (t + 1)) :
    deletePerm i (Fin.last t) = i := by simp [deletePerm]

theorem deletePerm_prefix {t : ℕ} (i : Fin (t + 1)) (j : Fin t) :
    deletePerm i j.castSucc = i.succAbove j := by
  simp [deletePerm, finSuccEquiv'_last_apply_castSucc]

theorem deletePerm_cast {t j : ℕ} (i : Fin (t + 1)) (hj : j < t) :
    deletePerm i (j : Fin (t + 1)) =
      ((if j < i.val then j else j + 1 : ℕ) : Fin (t + 1)) := by
  have hcast : (j : Fin (t + 1)) = (⟨j, hj⟩ : Fin t).castSucc := by
    apply Fin.ext
    simp [Fin.val_natCast, Nat.mod_eq_of_lt (show j < t + 1 by omega)]
  rw [hcast, deletePerm_prefix]
  by_cases hji : j < i.val
  · rw [Fin.succAbove_of_castSucc_lt _ _ hji, if_pos hji]
    exact hcast.symm
  · rw [Fin.succAbove_of_le_castSucc _ _ (show i.val ≤ j by omega), if_neg hji]
    apply Fin.ext
    change j + 1 = (((j + 1 : ℕ) : Fin (t + 1)) : ℕ)
    rw [Fin.val_natCast, Nat.mod_eq_of_lt (show j + 1 < t + 1 by omega)]

namespace HistoryLaw

variable {Ω : Type*} [Fintype Ω] {t : ℕ}

theorem deleted_current (L : HistoryLaw Ω Z (t + 1)) (step : Z → E → E)
    (x0 : Ω → E) (h0 : L.StartInvariant x0) (i : Fin (t + 1)) (ω : Ω) :
    L.current step x0 t (L.reindex (deletePerm i) ω) =
      forward step (x0 ω) (skipWord (fun j ↦ L.label ω (j : Fin (t + 1))) i.val) t := by
  change forward step (x0 (L.reindex (deletePerm i) ω))
    (fun j ↦ L.label (L.reindex (deletePerm i) ω) (j : Fin (t + 1))) t = _
  rw [h0]
  apply forward_congr
  intro j hj
  rw [L.label_reindex, deletePerm_cast i hj]
  rfl

theorem deleted_query (L : HistoryLaw Ω Z (t + 1)) (f : Z → E → ℝ)
    (step : Z → E → E) (x0 : Ω → E) (h0 : L.StartInvariant x0) (i : Fin (t + 1)) :
    (∑ ω, f (L.label ω i) (L.current step x0 t (L.reindex (deletePerm i) ω))) =
      L.queriedLoss f step x0 t := by
  rw [L.queriedLoss_forward f step x0 h0]
  have hc : (t : Fin (t + 1)) = Fin.last t := by
    apply Fin.ext
    simp [Fin.val_natCast, Nat.mod_eq_of_lt (Nat.lt_succ_self t)]
  rw [hc]
  have hh := L.sum_invariant (deletePerm i)
    (fun ω ↦ f (L.label ω (Fin.last t)) (L.current step x0 t ω))
  simpa only [L.label_reindex, deletePerm_last] using hh

theorem used_label_bound (L : HistoryLaw Ω Z (t + 1)) (p : NoiseModel Z E)
    (x0 : Ω → E) (h0 : L.StartInvariant x0) (i : Fin (t + 1)) :
    (∑ ω, p.loss (L.label ω i) (L.current p.step x0 (t + 1) ω)) ≤
      L.queriedLoss p.loss p.step x0 t + ‖L.queriedGradient p.g x0 t‖ ^ 2 / 2 +
        (1 + p.α) / 2 * ‖L.queriedGradient p.g x0 i.val‖ ^ 2 := by
  have hstep := fun z ↦ nonexpansive_step (p.loss_smooth z) p.alpha_pos p.alpha_lt_two.le
  have hd (ω : Ω) :
      ‖L.current p.step x0 (t + 1) ω -
        L.current p.step x0 t (L.reindex (deletePerm i) ω)‖ ^ 2 ≤
        ‖p.g (L.label ω i) (L.current p.step x0 i.val ω)‖ ^ 2 := by
    rw [L.deleted_current p.step x0 h0 i ω]
    have hh := forward_skip_distance p.g hstep (x0 ω)
      (fun j ↦ L.label ω (j : Fin (t + 1))) i.isLt
    simp only [Nat.add_sub_cancel, Fin.cast_val_eq_self] at hh
    convert! hh using 1 <;> rfl
  have hs (ω : Ω) : p.loss (L.label ω i) (L.current p.step x0 (t + 1) ω) ≤
      p.loss (L.label ω i) (L.current p.step x0 t (L.reindex (deletePerm i) ω)) +
        ‖p.g (L.label ω i) (L.current p.step x0 t (L.reindex (deletePerm i) ω))‖ ^ 2 / 2 +
        (1 + p.α) / 2 * ‖p.g (L.label ω i) (L.current p.step x0 i.val ω)‖ ^ 2 := by
    have hu := deletion_loss (p.loss_smooth (L.label ω i)) p.alpha_pos
      (L.current p.step x0 (t + 1) ω)
      (L.current p.step x0 t (L.reindex (deletePerm i) ω))
    have hm := mul_le_mul_of_nonneg_left (hd ω)
      (show 0 ≤ (1 + p.α) / 2 by linarith [p.alpha_pos])
    linarith
  have hh := sum_le_sum (s := (univ : Finset Ω)) (fun ω _ ↦ hs ω)
  simp only [sum_add_distrib, ← sum_div, ← mul_sum] at hh
  rw [L.deleted_query p.loss p.step x0 h0 i,
    L.deleted_query (fun z x ↦ ‖p.g z x‖ ^ 2) p.step x0 h0 i] at hh
  have hg : ‖L.queriedGradient p.g x0 t‖ ^ 2 =
      L.queriedLoss (fun z x ↦ ‖p.g z x‖ ^ 2) p.step x0 t :=
    L.queriedGradient_sq_loss p.g x0 t
  have hi : ‖L.queriedGradient p.g x0 i.val‖ ^ 2 =
      ∑ ω, ‖p.g (L.label ω i) (L.current p.step x0 i.val ω)‖ ^ 2 := by
    rw [L.queriedGradient_sq_loss p.g x0,
      L.queriedLoss_forward (fun z x ↦ ‖p.g z x‖ ^ 2) (fun z x ↦ x - p.g z x) x0 h0,
      Fin.cast_val_eq_self]
    rfl
  rwa [← hg, ← hi] at hh

end HistoryLaw

end LastIterate
