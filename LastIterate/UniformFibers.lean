module

public import LastIterate.FiniteSampling
public import Mathlib.Logic.Equiv.Fintype

@[expose] public section

/-! # Uniform finite marginals, proved by bijections of their fibers -/

namespace LastIterate

open Finset

theorem uniformMean_map_of_fibers {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]
    [Nonempty Ω] [Nonempty Ξ] (p : Ω → Ξ)
    (hfiber : ∀ y z : Ξ, Nonempty ({ω // p ω = y} ≃ {ω // p ω = z}))
    (h : Ξ → ℝ) : uniformMean (fun ω ↦ h (p ω)) = uniformMean h := by
  classical
  let y0 : Ξ := Classical.choice inferInstance
  let K : ℝ := Fintype.card {ω // p ω = y0}
  have hcard (y : Ξ) : (Fintype.card {ω // p ω = y} : ℝ) = K := by
    dsimp [K]
    exact_mod_cast Fintype.card_congr (Classical.choice (hfiber y y0))
  have hsum (g : Ξ → ℝ) : (∑ ω, g (p ω)) = K * ∑ y, g y := by
    rw [← Fintype.sum_fiberwise p (fun ω ↦ g (p ω))]
    calc
      (∑ y, ∑ ω : {ω // p ω = y}, g (p ω)) = ∑ y, K * g y := by
        apply sum_congr rfl
        intro y _
        have he : (fun ω : {ω // p ω = y} ↦ g (p ω)) = fun _ ↦ g y := by
          funext ω
          rw [ω.property]
        rw [he]
        simp only [sum_const, card_univ, nsmul_eq_mul, hcard]
      _ = _ := by rw [mul_sum]
  have htotal : (Fintype.card Ω : ℝ) = K * Fintype.card Ξ := by
    simpa using hsum (fun _ ↦ 1)
  have hK : K ≠ 0 := by
    intro hk
    have hn : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    rw [hk, zero_mul] at htotal
    exact hn htotal
  unfold uniformMean
  rw [hsum, htotal]
  exact mul_div_mul_left _ _ hK

def worLabels {n m : ℕ} (e : Equiv.Perm (Fin n)) : WOR n m ≃ WOR n m where
  toFun ω := ω.trans e.toEmbedding
  invFun ω := ω.trans e.symm.toEmbedding
  left_inv ω := by ext i; simp
  right_inv ω := by ext i; simp

/-- Restricting a uniform injective word to any ordered set of positions remains uniform. -/
theorem wor_restrict {n m k : ℕ} (hn : m ≤ n) (q : Fin k ↪ Fin m)
    (h : WOR n k → ℝ) :
    uniformMean (fun ω : WOR n m ↦ h (q.trans ω)) = uniformMean h := by
  classical
  let ω0 : WOR n m := ⟨Fin.castLE hn, Fin.castLE_injective hn⟩
  letI : Nonempty (WOR n m) := ⟨ω0⟩
  letI : Nonempty (WOR n k) := ⟨q.trans ω0⟩
  apply uniformMean_map_of_fibers (fun ω : WOR n m ↦ q.trans ω)
  intro a b
  obtain ⟨e, he⟩ := Equiv.Perm.exists_extending_pair a b a.injective b.injective
  refine ⟨(worLabels e).subtypeEquiv ?_⟩
  intro ω
  constructor
  · intro hh
    apply Function.Embedding.ext
    intro i
    change e (ω (q i)) = b i
    have hi := DFunLike.congr_fun hh i
    change ω (q i) = a i at hi
    rw [hi, he]
  · intro hh
    apply Function.Embedding.ext
    intro i
    apply e.injective
    have hi := DFunLike.congr_fun hh i
    change e (ω (q i)) = b i at hi
    exact hi.trans (he i).symm

end LastIterate
