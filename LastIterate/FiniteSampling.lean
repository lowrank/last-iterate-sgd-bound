module

public import LastIterate.Suffix
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Algebra.BigOperators.Field

@[expose] public section

/-!
# Finite WR and WOR sampling spaces

Uniform expectations are literal finite averages, with no measure-theoretic axioms.
Both sampling spaces are invariant under arbitrary permutations of update positions.
-/

namespace LastIterate

open Finset

abbrev WR (n m : ℕ) := Fin m → Fin n
abbrev WOR (n m : ℕ) := Fin m ↪ Fin n

noncomputable def uniformMean {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) : ℝ :=
  (∑ ω, f ω) / Fintype.card Ω

theorem uniformMean_sum {Ω I : Type*} [Fintype Ω] (s : Finset I) (f : I → Ω → ℝ) :
    uniformMean (fun ω ↦ ∑ i ∈ s, f i ω) = ∑ i ∈ s, uniformMean (f i) := by
  simp only [uniformMean, sum_comm (s := univ) (t := s), ← sum_div]

theorem uniformMean_add {Ω : Type*} [Fintype Ω] (f g : Ω → ℝ) :
    uniformMean (fun ω ↦ f ω + g ω) = uniformMean f + uniformMean g := by
  simp only [uniformMean, sum_add_distrib, add_div]

theorem uniformMean_nonneg {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) (h : ∀ ω, 0 ≤ f ω) :
    0 ≤ uniformMean f := by
  unfold uniformMean
  exact div_nonneg (sum_nonneg (fun ω _ ↦ h ω)) (Nat.cast_nonneg _)

theorem uniformMean_congr_equiv {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]
    (e : Ω ≃ Ξ) (f : Ξ → ℝ) : uniformMean (fun ω ↦ f (e ω)) = uniformMean f := by
  unfold uniformMean
  rw [Equiv.sum_comp, Fintype.card_congr e]

theorem uniformMean_equiv {Ω : Type*} [Fintype Ω] (e : Ω ≃ Ω) (f : Ω → ℝ) :
    uniformMean (fun ω ↦ f (e ω)) = uniformMean f := by
  unfold uniformMean
  rw [Equiv.sum_comp]

def wrPerm {n m : ℕ} (e : Equiv.Perm (Fin m)) : WR n m ≃ WR n m where
  toFun ω := fun i ↦ ω (e i)
  invFun ω := fun i ↦ ω (e.symm i)
  left_inv ω := by funext i; simp
  right_inv ω := by funext i; simp

def worPerm {n m : ℕ} (e : Equiv.Perm (Fin m)) : WOR n m ≃ WOR n m where
  toFun ω := e.toEmbedding.trans ω
  invFun ω := e.symm.toEmbedding.trans ω
  left_inv ω := by ext i; simp
  right_inv ω := by ext i; simp

theorem wr_invariant {n m : ℕ} (e : Equiv.Perm (Fin m)) (f : WR n m → ℝ) :
    uniformMean (fun ω : WR n m ↦ f (fun i ↦ ω (e i))) = uniformMean f :=
  uniformMean_equiv (wrPerm e) f

theorem wor_invariant {n m : ℕ} (e : Equiv.Perm (Fin m)) (f : WOR n m → ℝ) :
    uniformMean (fun ω ↦ f (e.toEmbedding.trans ω)) = uniformMean f :=
  uniformMean_equiv (worPerm e) f

theorem uniformMean_mono {Ω : Type*} [Fintype Ω] {f g : Ω → ℝ}
    (h : ∀ ω, f ω ≤ g ω) : uniformMean f ≤ uniformMean g := by
  unfold uniformMean
  exact div_le_div_of_nonneg_right (sum_le_sum (fun ω _ ↦ h ω)) (Nat.cast_nonneg _)

theorem uniformMean_const {Ω : Type*} [Fintype Ω] [Nonempty Ω] (c : ℝ) :
    uniformMean (fun _ : Ω ↦ c) = c := by
  unfold uniformMean
  simp only [sum_const, card_univ, nsmul_eq_mul]
  exact mul_div_cancel_left₀ c (by exact_mod_cast Fintype.card_ne_zero)

theorem uniformMean_product {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ] (f : Ω × Ξ → ℝ) :
    uniformMean f = uniformMean (fun ω ↦ uniformMean (fun ξ ↦ f (ω, ξ))) := by
  simp only [uniformMean, Fintype.card_prod, Nat.cast_mul, Fintype.sum_prod_type,
    div_eq_mul_inv, ← sum_mul]
  ring

/-- A state determined by the first `r` labels. -/
def PrefixDependent {n m : ℕ} {E : Type*} (X : WR n m → E) (r : ℕ) : Prop :=
  ∀ ω ω', (∀ i : Fin m, i.val < r → ω i = ω' i) → X ω = X ω'

theorem prefix_swap {n m r : ℕ} {E : Type*} (X : WR n m → E)
    (hX : PrefixDependent X r) (i j : Fin m) (hi : r ≤ i.val) (hj : r ≤ j.val)
    (ω : WR n m) : X (fun k ↦ ω (Equiv.swap i j k)) = X ω := by
  apply hX
  intro k hk
  rw [Equiv.swap_apply_of_ne_of_ne]
  · intro he
    have hv := congrArg Fin.val he
    omega
  · intro he
    have hv := congrArg Fin.val he
    omega

/-- Future-query exchangeability, the exact expectation identity used by frozen histories. -/
theorem wr_frozen_query {n m r : ℕ} {E : Type*} (X : WR n m → E)
    (hX : PrefixDependent X r) (f : E → Fin n → ℝ)
    (i j : Fin m) (hi : r ≤ i.val) (hj : r ≤ j.val) :
    uniformMean (fun ω : WR n m ↦ f (X ω) (ω i)) =
      uniformMean (fun ω : WR n m ↦ f (X ω) (ω j)) := by
  have hh := wr_invariant (Equiv.swap i j) (fun ω : WR n m ↦ f (X ω) (ω i))
  simpa only [prefix_swap X hX i j hi hj, Equiv.swap_apply_left] using hh.symm

theorem wor_frozen_query {n m r : ℕ} {E : Type*} (X : WR n m → E)
    (hX : PrefixDependent X r) (f : E → Fin n → ℝ)
    (i j : Fin m) (hi : r ≤ i.val) (hj : r ≤ j.val) :
    uniformMean (fun ω : WOR n m ↦ f (X ω) (ω i)) =
      uniformMean (fun ω : WOR n m ↦ f (X ω) (ω j)) := by
  have hh := wor_invariant (Equiv.swap i j) (fun ω : WOR n m ↦ f (X ω) (ω i))
  have he (ω : WOR n m) :
      X ((Equiv.swap i j).toEmbedding.trans ω) = X ω := prefix_swap X hX i j hi hj ω
  simpa only [he, Function.Embedding.trans_apply, Equiv.toEmbedding_apply,
    Equiv.swap_apply_left] using hh.symm

/-- Actual prefix iterates have the dependence required by the frozen-query identity. -/
def prefixRun {n m r : ℕ} {E : Type*} (hr : r ≤ m) (step : Fin n → E → E)
    (x0 : E) (ω : WR n m) : E :=
  (List.ofFn (fun i : Fin r ↦ ω (Fin.castLE hr i))).foldl (fun x z ↦ step z x) x0

theorem prefixRun_dependent {n m r : ℕ} {E : Type*} (hr : r ≤ m)
    (step : Fin n → E → E) (x0 : E) : PrefixDependent (prefixRun hr step x0) r := by
  intro ω ω' h
  unfold prefixRun
  congr 2
  funext i
  exact h (Fin.castLE hr i) i.isLt

/-- The WR query after the last update is independent and uniformly distributed. -/
theorem wr_last_query {n m : ℕ} (f : WR n m → Fin n → ℝ) :
    uniformMean (fun ω : WR n (m + 1) ↦ f (fun i ↦ ω i.castSucc) (ω (Fin.last m))) =
      uniformMean (fun ω : WR n m ↦ uniformMean (fun z : Fin n ↦ f ω z)) := by
  let e : (WR n m × Fin n) ≃ WR n (m + 1) :=
    (Equiv.prodComm _ _).trans (Fin.snocEquiv (fun _ ↦ Fin n))
  have hh := uniformMean_congr_equiv e
    (fun ω : WR n (m + 1) ↦ f (fun i ↦ ω i.castSucc) (ω (Fin.last m)))
  have he : (fun p : WR n m × Fin n ↦
      f (fun i ↦ e p i.castSucc) (e p (Fin.last m))) = fun p ↦ f p.1 p.2 := by
    funext p
    simp [e, Fin.snocEquiv]
  rw [he] at hh
  rw [← hh, uniformMean_product]

end LastIterate
