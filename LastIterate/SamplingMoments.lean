module

public import LastIterate.UniformFibers
public import LastIterate.FiniteLift

@[expose] public section

/-! # Exact first and second noise moments for WR and WOR -/

namespace LastIterate

open Finset
open scoped RealInnerProductSpace

theorem wr_coordinate {n m : ℕ} (hn : 0 < n) (i : Fin m) (f : Fin n → ℝ) :
    uniformMean (fun ω : WR n m ↦ f (ω i)) = uniformMean f := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  cases m with
  | zero => exact Fin.elim0 i
  | succ m =>
    have hh := wr_invariant (Equiv.swap i (Fin.last m)) (fun ω ↦ f (ω i))
    simp only [Equiv.swap_apply_left] at hh
    rw [← hh, wr_last_query (fun _ z ↦ f z)]
    exact uniformMean_const _

theorem full_wor_sum {n : ℕ} (ω : WOR n n) {E : Type*} [AddCommMonoid E]
    (f : Fin n → E) : (∑ i, f (ω i)) = ∑ z, f z := by
  let e := Equiv.ofBijective ω ⟨ω.injective, Finite.surjective_of_injective ω.injective⟩
  exact Equiv.sum_comp e f

theorem full_wor_coordinate {n : ℕ} (hn : 0 < n) (i : Fin n) (f : Fin n → ℝ) :
    uniformMean (fun ω : WOR n n ↦ f (ω i)) = uniformMean f := by
  let : Nonempty (WOR n n) := ⟨Function.Embedding.refl _⟩
  have hcoord (j : Fin n) : uniformMean (fun ω : WOR n n ↦ f (ω j)) =
      uniformMean (fun ω : WOR n n ↦ f (ω i)) := by
    have hh := wor_invariant (Equiv.swap i j) (fun ω : WOR n n ↦ f (ω i))
    simpa only [Function.Embedding.trans_apply, Equiv.toEmbedding_apply,
      Equiv.swap_apply_left] using hh
  have hs := uniformMean_sum (univ : Finset (Fin n))
    (fun j (ω : WOR n n) ↦ f (ω j))
  have ht : uniformMean (fun ω : WOR n n ↦ ∑ j, f (ω j)) = ∑ z, f z := by
    simp only [full_wor_sum]
    exact uniformMean_const _
  rw [ht] at hs
  simp only [hcoord, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  unfold uniformMean
  simp only [Fintype.card_fin]
  apply (eq_div_iff (show (n : ℝ) ≠ 0 by exact_mod_cast (Nat.ne_of_gt hn))).mpr
  change uniformMean (fun ω : WOR n n ↦ f (ω i)) * n = _
  nlinarith only [hs]

theorem wor_coordinate {n m : ℕ} (hn : m ≤ n) (i : Fin m) (f : Fin n → ℝ) :
    uniformMean (fun ω : WOR n m ↦ f (ω i)) = uniformMean f := by
  let q : Fin m ↪ Fin n := ⟨Fin.castLE hn, Fin.castLE_injective hn⟩
  rw [← wor_restrict (le_refl n) q (fun ω ↦ f (ω i))]
  exact full_wor_coordinate (by have := i.isLt; omega) (q i) f

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem wr_cross_moment {n m : ℕ} (hn : 0 < n) (ζ : Fin n → E)
    (hzero : ∑ z, ζ z = 0) (i j : Fin m) (hij : i ≠ j) :
    uniformMean (fun ω : WR n m ↦ ⟪ζ (ω i), ζ (ω j)⟫) = 0 := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  cases m with
  | zero => exact Fin.elim0 i
  | succ m =>
    let e := Equiv.swap j (Fin.last m)
    have hne : e i ≠ Fin.last m := by
      intro he
      have hh : e i = e j := by simpa only [e, Equiv.swap_apply_left] using he
      exact hij (e.injective hh)
    have hlt : (e i).val < m := by
      have hi := (e i).isLt
      have hv : (e i).val ≠ m := by
        intro he
        exact hne (Fin.ext he)
      omega
    let k : Fin m := ⟨(e i).val, hlt⟩
    have hk : k.castSucc = e i := Fin.ext rfl
    have hh := wr_invariant e (fun ω : WR n (m + 1) ↦ ⟪ζ (ω i), ζ (ω j)⟫)
    rw [← hh]
    change uniformMean (fun ω : WR n (m + 1) ↦ ⟪ζ (ω (e i)), ζ (ω (e j))⟫) = 0
    simp only [show e j = Fin.last m from Equiv.swap_apply_left _ _, ← hk]
    rw [wr_last_query (fun ω z ↦ ⟪ζ (ω k), ζ z⟫)]
    have hz (ω : WR n m) : uniformMean (fun z ↦ ⟪ζ (ω k), ζ z⟫) = 0 := by
      simp only [uniformMean, ← inner_sum, hzero, inner_zero_right, zero_div]
    change uniformMean (fun ω : WR n m ↦ uniformMean (fun z ↦ ⟪ζ (ω k), ζ z⟫)) = 0
    calc
      _ = uniformMean (fun _ : WR n m ↦ (0 : ℝ)) := congrArg uniformMean (funext hz)
      _ = 0 := uniformMean_const 0

theorem full_wor_cross_moment {n : ℕ} (ζ : Fin n → E)
    (hzero : ∑ z, ζ z = 0) (i j : Fin n) (hij : i ≠ j) :
    uniformMean (fun ω : WOR n n ↦ ⟪ζ (ω i), ζ (ω j)⟫) ≤ 0 := by
  classical
  let c := fun k ↦ uniformMean (fun ω : WOR n n ↦ ⟪ζ (ω i), ζ (ω k)⟫)
  have hrow (k : Fin n) (hk : k ≠ i) : c k = c j := by
    have hh := wor_invariant (Equiv.swap j k)
      (fun ω : WOR n n ↦ ⟪ζ (ω i), ζ (ω j)⟫)
    simpa only [Function.Embedding.trans_apply, Equiv.toEmbedding_apply,
      Equiv.swap_apply_of_ne_of_ne hij (Ne.symm hk), Equiv.swap_apply_left] using hh
  have hsum : (∑ k, c k) = 0 := by
    rw [← uniformMean_sum (univ : Finset (Fin n))
      (fun k (ω : WOR n n) ↦ ⟪ζ (ω i), ζ (ω k)⟫)]
    simp only [← inner_sum, full_wor_sum, hzero, inner_zero_right, uniformMean, sum_const_zero,
      zero_div]
  have hdiag : 0 ≤ c i := uniformMean_nonneg _ (fun ω ↦ real_inner_self_nonneg)
  have hn : 0 < n - 1 := by
    by_contra hn
    apply hij
    apply Fin.ext
    have hi := i.isLt
    have hj := j.isLt
    omega
  have hn' : (0 : ℝ) < (n - 1 : ℕ) := by exact_mod_cast hn
  have hrest : (∑ k ∈ (univ : Finset (Fin n)).erase i, c k) = (n - 1 : ℕ) * c j := by
    calc
      _ = ∑ _k ∈ (univ : Finset (Fin n)).erase i, c j :=
        sum_congr rfl (fun k hk ↦ hrow k (mem_erase.mp hk).1)
      _ = _ := by simp
  have ht := sum_erase_add (univ : Finset (Fin n)) c (mem_univ i)
  rw [hrest, hsum] at ht
  change c j ≤ 0
  nlinarith only [ht, hdiag, hn']

theorem wor_cross_moment {n m : ℕ} (hn : m ≤ n) (ζ : Fin n → E)
    (hzero : ∑ z, ζ z = 0) (i j : Fin m) (hij : i ≠ j) :
    uniformMean (fun ω : WOR n m ↦ ⟪ζ (ω i), ζ (ω j)⟫) ≤ 0 := by
  let q : Fin m ↪ Fin n := ⟨Fin.castLE hn, Fin.castLE_injective hn⟩
  rw [← wor_restrict (le_refl n) q (fun ω ↦ ⟪ζ (ω i), ζ (ω j)⟫)]
  exact full_wor_cross_moment ζ hzero (q i) (q j) (fun h ↦ hij (q.injective h))

end LastIterate
