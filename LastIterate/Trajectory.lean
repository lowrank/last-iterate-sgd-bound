module

public import LastIterate.FiniteLift
public import LastIterate.HistoryComparison
public import Mathlib.Algebra.Group.Fin.Basic
public import Mathlib.Data.List.OfFn

@[expose] public section

/-! # Actual trajectories and exchangeable finite histories -/

namespace LastIterate

open Finset

/-- Coordinate permutations are realized by bijections of the finite sample space. -/
structure HistoryLaw (Ω Z : Type*) (m : ℕ) where
  label : Ω → Fin m → Z
  reindex : Equiv.Perm (Fin m) → Equiv.Perm Ω
  label_reindex : ∀ e ω i, label (reindex e ω) i = label ω (e i)

def wrHistoryLaw (n m : ℕ) : HistoryLaw (WR n m) (Fin n) m where
  label ω := ω
  reindex := wrPerm
  label_reindex _ _ _ := rfl

def worHistoryLaw (n m : ℕ) : HistoryLaw (WOR n m) (Fin n) m where
  label ω := ω
  reindex := worPerm
  label_reindex _ _ _ := rfl

variable {Ω Z E : Type*} {m : ℕ}

namespace HistoryLaw

theorem invariant [Fintype Ω] (L : HistoryLaw Ω Z m)
    (e : Equiv.Perm (Fin m)) (f : Ω → ℝ) :
    uniformMean (fun ω ↦ f (L.reindex e ω)) = uniformMean f :=
  uniformMean_equiv (L.reindex e) f

end HistoryLaw

/-- The forward recursion is defined at every time; finite words are extended periodically. -/
def forward (step : Z → E → E) (x0 : E) (z : ℕ → Z) : ℕ → E
  | 0 => x0
  | k + 1 => step (z k) (forward step x0 z k)

@[simp] theorem forward_zero (step : Z → E → E) (x0 : E) (z : ℕ → Z) :
    forward step x0 z 0 = x0 := rfl

@[simp] theorem forward_succ (step : Z → E → E) (x0 : E) (z : ℕ → Z) (k : ℕ) :
    forward step x0 z (k + 1) = step (z k) (forward step x0 z k) := rfl

theorem forward_congr (step : Z → E → E) (x0 : E) {z w : ℕ → Z} {k : ℕ}
    (h : ∀ i < k, z i = w i) : forward step x0 z k = forward step x0 w k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [forward_succ, forward_succ, h k (by omega), ih (fun i hi ↦ h i (by omega))]

theorem forward_add (step : Z → E → E) (x0 : E) (z : ℕ → Z) (s k : ℕ) :
    forward step x0 z (s + k) =
      forward step (forward step x0 z s) (fun i ↦ z (s + i)) k := by
  induction k with
  | zero => simp
  | succ k ih => simp only [Nat.add_succ, forward_succ, ih]

theorem forward_foldl (step : Z → E → E) (x0 : E) (z : ℕ → Z) (k : ℕ) :
    forward step x0 z k =
      (List.ofFn (fun i : Fin k ↦ z i.val)).foldl (fun x a ↦ step a x) x0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.ofFn_succ', List.concat_eq_append, List.foldl_append]
    simpa only [forward_succ, List.foldl_cons, List.foldl_nil, Fin.val_last,
      Fin.val_castSucc] using
      congrArg (step (z k)) ih

section Cyclic

variable [NeZero m]
open scoped Fin.NatCast

def rotateWord (z : Fin m → Z) (a : Fin m) : Fin m → Z := fun i ↦ z (i + a)

@[simp] theorem rotateWord_zero (z : Fin m → Z) : rotateWord z 0 = z := by
  funext i
  simp [rotateWord]

def suffix (step : Z → E → E) (x0 : E) (z : Fin m → Z) (k : ℕ) : E :=
  forward step x0 (fun i ↦ z ((i : Fin m) - (k : Fin m))) k

@[simp] theorem suffix_zero (step : Z → E → E) (x0 : E) (z : Fin m → Z) :
    suffix step x0 z 0 = x0 := rfl

theorem suffix_succ (step : Z → E → E) (x0 : E) (z : Fin m → Z) (k : ℕ) :
    suffix step x0 z (k + 1) = step (z (-1))
      (suffix step x0 (rotateWord z (-1)) k) := by
  unfold suffix
  rw [forward_succ]
  have he : (k : Fin m) - ((k + 1 : ℕ) : Fin m) = -1 := by
    push_cast
    abel
  rw [he]
  congr 1
  apply forward_congr
  intro i _
  simp only [rotateWord, Nat.cast_add, Nat.cast_one]
  congr 1
  abel

theorem suffix_forward (step : Z → E → E) (x0 : E) (z : Fin m → Z) (k : ℕ) :
    suffix step x0 (rotateWord z (k : Fin m)) k =
      forward step x0 (fun i ↦ z (i : Fin m)) k := by
  unfold suffix rotateWord
  simp only [sub_add_cancel]

theorem suffix_split (step : Z → E → E) (x0 : E) (z : Fin m → Z) (s r : ℕ) :
    suffix step x0 z (s + r) =
      suffix step (suffix step x0 (rotateWord z (-(r : Fin m))) s) z r := by
  unfold suffix
  rw [forward_add]
  have hstart :
      forward step x0 (fun i ↦ z ((i : Fin m) - ((s + r : ℕ) : Fin m))) s =
      forward step x0 (fun i ↦
        rotateWord z (-(r : Fin m)) ((i : Fin m) - (s : Fin m))) s := by
    apply forward_congr
    intro i _
    simp only [rotateWord, Nat.cast_add]
    congr 1
    abel
  rw [hstart]
  apply forward_congr
  intro i _
  push_cast
  congr 1
  abel

end Cyclic

section Contraction

variable [NormedAddCommGroup E]
open scoped Fin.NatCast

theorem forward_nonexpansive (step : Z → E → E)
    (hstep : ∀ z x y, ‖step z x - step z y‖ ^ 2 ≤ ‖x - y‖ ^ 2)
    (x y : E) (z : ℕ → Z) (k : ℕ) :
    ‖forward step x z k - forward step y z k‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
  induction k with
  | zero => exact le_rfl
  | succ k ih => exact (hstep (z k) _ _).trans ih

theorem suffix_nonexpansive [NeZero m] (step : Z → E → E)
    (hstep : ∀ z x y, ‖step z x - step z y‖ ^ 2 ≤ ‖x - y‖ ^ 2)
    (x0 : E) (z : Fin m → Z) (s r : ℕ) :
    ‖suffix step x0 z (s + r) - suffix step x0 z r‖ ^ 2 ≤
      ‖suffix step x0 (rotateWord z (-(r : Fin m))) s - x0‖ ^ 2 := by
  rw [suffix_split]
  exact forward_nonexpansive step hstep _ _ _ _

end Contraction

end LastIterate
