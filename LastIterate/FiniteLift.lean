module

public import LastIterate.Geometry
public import LastIterate.FiniteSampling
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Algebra.BigOperators.Field

@[expose] public section

/-!
# Finite history Hilbert space

The lift uses the unnormalized finite sum inner product. Dividing its squared norm by
the number of histories gives exactly the uniform second moment. This avoids any
measure-theoretic assumptions, while retaining all vector geometry of the histories.
-/

namespace LastIterate

open Finset
open scoped RealInnerProductSpace

variable {Ω E : Type*} [Fintype Ω] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

abbrev HistorySpace (Ω E : Type*) := PiLp 2 (fun _ : Ω ↦ E)

noncomputable def liftLoss (f : Ω → E → ℝ) (U : HistorySpace Ω E) : ℝ := ∑ ω, f ω (U ω)

noncomputable def liftGradient (g : Ω → E → E) (U : HistorySpace Ω E) : HistorySpace Ω E :=
  WithLp.toLp 2 (fun ω ↦ g ω (U ω))

theorem history_norm_sq (U : HistorySpace Ω E) : ‖U‖ ^ 2 = ∑ ω, ‖U ω‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
  simp only [real_inner_self_eq_norm_sq]

theorem history_second_moment (U : HistorySpace Ω E) :
    uniformMean (fun ω ↦ ‖U ω‖ ^ 2) = ‖U‖ ^ 2 / Fintype.card Ω := by
  rw [history_norm_sq]
  rfl

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
theorem history_loss_mean (f : Ω → E → ℝ) (U : HistorySpace Ω E) :
    uniformMean (fun ω ↦ f ω (U ω)) = liftLoss f U / Fintype.card Ω := rfl

theorem lift_interpolation (f : Ω → E → ℝ) (g : Ω → E → E) {α : ℝ}
    (h : ∀ ω, SmoothInterpolation (f ω) (g ω) α) :
    SmoothInterpolation (liftLoss f) (liftGradient g) α := by
  intro U V
  have hh := sum_le_sum (s := univ) (fun ω _ ↦ h ω (U ω) (V ω))
  simp only [sum_add_distrib, ← sum_div] at hh
  change (∑ ω, f ω (U ω)) + ⟪liftGradient g U, V - U⟫ +
    ‖liftGradient g V - liftGradient g U‖ ^ 2 / (2 * α) ≤ ∑ ω, f ω (V ω)
  rw [PiLp.inner_apply, history_norm_sq]
  exact hh

/-- Compose every history field with a permutation of the sampling space. -/
noncomputable def historyShift (e : Ω ≃ Ω) : HistorySpace Ω E ≃ₗᵢ[ℝ] HistorySpace Ω E :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ E e.symm

@[simp] theorem historyShift_apply (e : Ω ≃ Ω) (U : HistorySpace Ω E) (ω : Ω) :
    historyShift e U ω = U (e ω) := rfl

theorem historyShift_distance (e : Ω ≃ Ω) (U V : HistorySpace Ω E) :
    ‖historyShift e U - historyShift e V‖ = ‖U - V‖ := by
  rw [← map_sub]
  exact (historyShift e).norm_map (U - V)

end LastIterate
