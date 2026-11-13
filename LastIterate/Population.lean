module

public import LastIterate.Targets
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

@[expose] public section

/-! # The population optimum and the centered residual gradients -/

namespace LastIterate

open Finset
open scoped RealInnerProductSpace

namespace SGDProblem

theorem gradient_sum_zero {d n : ℕ} (p : SGDProblem d n) :
    (∑ z : Fin n, p.grad z p.xstar) = 0 := by
  have hn : (0 : ℝ) < n := by exact_mod_cast p.population_nonempty
  have hmin : IsLocalMin (fun x ↦ ∑ z : Fin n, p.loss z x) p.xstar := by
    apply Filter.Eventually.of_forall
    intro x
    have hh := p.minimizes x
    simp only [uniformMean, Fintype.card_fin] at hh
    exact (div_le_div_iff_of_pos_right hn).mp hh
  have hd := HasFDerivAt.sum (u := univ)
    (fun z _ ↦ (p.hasGradient z p.xstar).hasFDerivAt)
  have he : (∑ z : Fin n, p.loss z) = fun x ↦ ∑ z : Fin n, p.loss z x := by
    funext x
    simp
  rw [he] at hd
  have hz := hmin.hasFDerivAt_eq_zero hd
  have hv := DFunLike.congr_fun hz (∑ z : Fin n, p.grad z p.xstar)
  have hh : ‖∑ z : Fin n, p.grad z p.xstar‖ ^ 2 = 0 := by
    rw [← real_inner_self_eq_norm_sq, inner_sum]
    simpa [sum_inner] using hv
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hh)

theorem radiusSq_nonneg {d n : ℕ} (p : SGDProblem d n) : 0 ≤ p.radiusSq :=
  sq_nonneg _

theorem noiseSq_nonneg {d n : ℕ} (p : SGDProblem d n) : 0 ≤ p.noiseSq := by
  unfold noiseSq uniformMean
  exact div_nonneg (sum_nonneg (fun _ _ ↦ sq_nonneg _)) (Nat.cast_nonneg _)

end SGDProblem

end LastIterate
