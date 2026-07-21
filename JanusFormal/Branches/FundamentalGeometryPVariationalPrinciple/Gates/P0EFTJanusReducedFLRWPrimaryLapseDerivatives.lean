import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusReducedFLRWLegendreBridge

/-!
# Exact reduced FLRW primary lapse derivatives

The existing Legendre gate derives the reduced Candidate-A Hamiltonian from
the same explicit FLRW Lagrangian.  Here its two lapse coefficients are
identified as actual derivatives with respect to the two independent lapses.

This is only the supplied spatially flat FLRW reduction.  It contains no
shift, covariant ADM reduction, continuum constraint algebra, or
Boulware--Deser conclusion.
-/

namespace JanusFormal
namespace P0EFTJanusReducedFLRWPrimaryLapseDerivatives

set_option autoImplicit false

noncomputable section

open P0EFTJanusReducedFLRWSecondaryConstraint
open P0EFTJanusReducedFLRWLegendreBridge

/-- The Legendre transform is affine in both lapses on the regular reduced
phase-space domain; no nonvanishing hypothesis on the lapses themselves is
needed. -/
theorem reducedLegendreTransform_eq_lapse_constraints_for_all_lapses
    (parameters : ReducedParameters) (x : PhasePoint)
    (lapsePlus lapseMinus : ℝ)
    (hPlanckPlus : parameters.planckPlusSq ≠ 0)
    (hPlanckMinus : parameters.planckMinusSq ≠ 0)
    (haPlus : x.aPlus ≠ 0)
    (haMinus : x.aMinus ≠ 0) :
    reducedLegendreTransform parameters x lapsePlus lapseMinus =
      lapsePlus * plusConstraint parameters x +
        lapseMinus * minusConstraint parameters x := by
  unfold reducedLegendreTransform reducedCandidateLagrangian
    plusKineticLagrangian minusKineticLagrangian
    reducedInteractionLagrangian plusVelocityFromMomentum
    minusVelocityFromMomentum plusConstraint minusConstraint
  field_simp [hPlanckPlus, hPlanckMinus, haPlus, haMinus]
  ring

/-- The plus Hamiltonian constraint is the actual derivative of the same
Legendre transform with respect to the plus lapse. -/
theorem reducedLegendreTransform_plusLapse_hasDerivAt
    (parameters : ReducedParameters) (x : PhasePoint)
    (lapsePlus lapseMinus : ℝ)
    (hPlanckPlus : parameters.planckPlusSq ≠ 0)
    (hPlanckMinus : parameters.planckMinusSq ≠ 0)
    (haPlus : x.aPlus ≠ 0)
    (haMinus : x.aMinus ≠ 0) :
    HasDerivAt
      (fun variedLapsePlus =>
        reducedLegendreTransform parameters x variedLapsePlus lapseMinus)
      (plusConstraint parameters x) lapsePlus := by
  have hFunction :
      (fun variedLapsePlus =>
        reducedLegendreTransform parameters x variedLapsePlus lapseMinus) =
        (fun variedLapsePlus =>
          variedLapsePlus * plusConstraint parameters x +
            lapseMinus * minusConstraint parameters x) := by
    funext variedLapsePlus
    exact reducedLegendreTransform_eq_lapse_constraints_for_all_lapses
      parameters x variedLapsePlus lapseMinus hPlanckPlus hPlanckMinus
        haPlus haMinus
  rw [hFunction]
  simpa using
    ((hasDerivAt_id lapsePlus).mul_const (plusConstraint parameters x)).add_const
      (lapseMinus * minusConstraint parameters x)

/-- The minus Hamiltonian constraint is likewise the actual derivative with
respect to the independent minus lapse. -/
theorem reducedLegendreTransform_minusLapse_hasDerivAt
    (parameters : ReducedParameters) (x : PhasePoint)
    (lapsePlus lapseMinus : ℝ)
    (hPlanckPlus : parameters.planckPlusSq ≠ 0)
    (hPlanckMinus : parameters.planckMinusSq ≠ 0)
    (haPlus : x.aPlus ≠ 0)
    (haMinus : x.aMinus ≠ 0) :
    HasDerivAt
      (fun variedLapseMinus =>
        reducedLegendreTransform parameters x lapsePlus variedLapseMinus)
      (minusConstraint parameters x) lapseMinus := by
  have hFunction :
      (fun variedLapseMinus =>
        reducedLegendreTransform parameters x lapsePlus variedLapseMinus) =
        (fun variedLapseMinus =>
          lapsePlus * plusConstraint parameters x +
            variedLapseMinus * minusConstraint parameters x) := by
    funext variedLapseMinus
    exact reducedLegendreTransform_eq_lapse_constraints_for_all_lapses
      parameters x lapsePlus variedLapseMinus hPlanckPlus hPlanckMinus
        haPlus haMinus
  rw [hFunction]
  simpa using
    ((hasDerivAt_id lapseMinus).mul_const (minusConstraint parameters x)).const_add
      (lapsePlus * plusConstraint parameters x)

/-- Both reduced primary lapse equations come from partial derivatives of the
single Legendre transform derived from the explicit Candidate-A FLRW
Lagrangian. -/
theorem reducedFLRW_primary_lapse_derivatives_from_same_action
    (parameters : ReducedParameters) (x : PhasePoint)
    (lapsePlus lapseMinus : ℝ)
    (hPlanckPlus : parameters.planckPlusSq ≠ 0)
    (hPlanckMinus : parameters.planckMinusSq ≠ 0)
    (haPlus : x.aPlus ≠ 0)
    (haMinus : x.aMinus ≠ 0) :
    HasDerivAt
        (fun variedLapsePlus =>
          reducedLegendreTransform parameters x variedLapsePlus lapseMinus)
        (plusConstraint parameters x) lapsePlus ∧
      HasDerivAt
        (fun variedLapseMinus =>
          reducedLegendreTransform parameters x lapsePlus variedLapseMinus)
        (minusConstraint parameters x) lapseMinus :=
  ⟨reducedLegendreTransform_plusLapse_hasDerivAt parameters x
      lapsePlus lapseMinus hPlanckPlus hPlanckMinus haPlus haMinus,
    reducedLegendreTransform_minusLapse_hasDerivAt parameters x
      lapsePlus lapseMinus hPlanckPlus hPlanckMinus haPlus haMinus⟩

end

end P0EFTJanusReducedFLRWPrimaryLapseDerivatives
end JanusFormal
