import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusReducedFLRWSecondaryConstraint

/-!
# Reduced FLRW Legendre bridge for Candidate A

This gate starts from the explicit spatially flat FLRW Lagrangian

`L = -3 M_+^2 a_+ v_+^2 / N_+ - 3 M_-^2 a_- v_-^2 / N_-
     - mu (N_+ P_+ + N_- P_-)`.

It proves the actual velocity derivatives, constructs the regular inverse
Legendre maps, and identifies `p * v - L` with the two Hamiltonian constraints
used by `P0EFTJanusReducedFLRWSecondaryConstraint`.  The interaction term is
also tied exactly to the existing Candidate-A FLRW square-root spectrum.

The displayed reduced Einstein--Hilbert kinetic terms are the starting data of
this gate.  No reduction from the covariant Einstein--Hilbert/GHY action, ADM
shift analysis, functional Poisson bracket, or Boulware--Deser closure is
claimed.
-/

namespace JanusFormal
namespace P0EFTJanusReducedFLRWLegendreBridge

set_option autoImplicit false

noncomputable section

open P0EFTJanusReciprocalBimetricPotential
open P0EFTJanusExplicitReciprocalCrossDensities
open P0EFTJanusCandidateMinisuperspaceLapseConstraint
open P0EFTJanusReducedFLRWSecondaryConstraint

/-- `HasDerivAt` with Mathlib's analytic real-vector-space instances. -/
abbrev AnalyticRealHasDerivAt
    (function : ℝ → ℝ) (derivative point : ℝ) : Prop :=
  @HasDerivAt ℝ DenselyNormedField.toNontriviallyNormedField ℝ
    NormedDivisionRing.toNormedRing.toAddCommGroup
    (NormedAlgebra.toNormedSpace ℝ).toModule
    (inferInstance : TopologicalSpace ℝ)
    (inferInstance : ContinuousSMul ℝ ℝ)
    function derivative point

/-- Plus-sector spatially flat FLRW kinetic Lagrangian. -/
def plusKineticLagrangian
    (parameters : ReducedParameters) (x : PhasePoint)
    (lapsePlus velocityPlus : ℝ) : ℝ :=
  -3 * parameters.planckPlusSq * x.aPlus *
    (velocityPlus * velocityPlus) / lapsePlus

/-- Minus-sector spatially flat FLRW kinetic Lagrangian. -/
def minusKineticLagrangian
    (parameters : ReducedParameters) (x : PhasePoint)
    (lapseMinus velocityMinus : ℝ) : ℝ :=
  -3 * parameters.planckMinusSq * x.aMinus *
    (velocityMinus * velocityMinus) / lapseMinus

/-- Common Candidate-A interaction after the FLRW spatial-volume factor has
been restored. -/
def reducedInteractionLagrangian
    (parameters : ReducedParameters) (x : PhasePoint)
    (lapsePlus lapseMinus : ℝ) : ℝ :=
  -parameters.interactionScale *
    (lapsePlus * plusPotential parameters x +
      lapseMinus * minusPotential parameters x)

/-- Explicit two-sector reduced Candidate-A Lagrangian. -/
def reducedCandidateLagrangian
    (parameters : ReducedParameters) (x : PhasePoint)
    (lapsePlus lapseMinus velocityPlus velocityMinus : ℝ) : ℝ :=
  plusKineticLagrangian parameters x lapsePlus velocityPlus +
    minusKineticLagrangian parameters x lapseMinus velocityMinus +
    reducedInteractionLagrangian parameters x lapsePlus lapseMinus

/-- Canonical plus momentum read from the explicit reduced Lagrangian. -/
def plusCanonicalMomentum
    (parameters : ReducedParameters) (x : PhasePoint)
    (lapsePlus velocityPlus : ℝ) : ℝ :=
  -6 * parameters.planckPlusSq * x.aPlus * velocityPlus / lapsePlus

/-- Canonical minus momentum read from the explicit reduced Lagrangian. -/
def minusCanonicalMomentum
    (parameters : ReducedParameters) (x : PhasePoint)
    (lapseMinus velocityMinus : ℝ) : ℝ :=
  -6 * parameters.planckMinusSq * x.aMinus * velocityMinus / lapseMinus

/-- Unit affine-increment form of the plus-velocity derivative. -/
theorem reducedCandidateLagrangian_plusVelocityIncrement_hasDerivAt
    (parameters : ReducedParameters) (x : PhasePoint)
    (lapsePlus lapseMinus velocityPlus velocityMinus : ℝ) :
    HasDerivAt
      (fun increment =>
        reducedCandidateLagrangian parameters x lapsePlus lapseMinus
          (velocityPlus + increment) velocityMinus)
      (plusCanonicalMomentum parameters x lapsePlus velocityPlus)
      0 := by
  have hVelocity : HasDerivAt
      (fun increment : ℝ => velocityPlus + increment * 1) 1 0 :=
    affineCoordinate_hasDerivAt velocityPlus 1
  have hKinetic : HasDerivAt
      (fun increment : ℝ =>
        plusKineticLagrangian parameters x lapsePlus
          (velocityPlus + increment))
      (plusCanonicalMomentum parameters x lapsePlus velocityPlus)
      0 := by
    have hRaw := ((hVelocity.mul hVelocity).const_mul
      (-3 * parameters.planckPlusSq * x.aPlus)).div_const lapsePlus
    have hDerivative := hRaw.congr_deriv
      (show
        -3 * parameters.planckPlusSq * x.aPlus *
            (1 * (velocityPlus + 0 * 1) +
              (velocityPlus + 0 * 1) * 1) / lapsePlus =
          plusCanonicalMomentum parameters x lapsePlus velocityPlus by
        simp [plusCanonicalMomentum]
        ring)
    simpa [plusKineticLagrangian] using hDerivative
  simpa [reducedCandidateLagrangian, plusKineticLagrangian] using
    (hKinetic.add_const
      (minusKineticLagrangian parameters x lapseMinus velocityMinus)).add_const
        (reducedInteractionLagrangian parameters x lapsePlus lapseMinus)

/-- The plus momentum is the actual derivative of the reduced Lagrangian as a
function of the plus velocity. -/
theorem reducedCandidateLagrangian_plusVelocity_hasDerivAt
    (parameters : ReducedParameters) (x : PhasePoint)
    (lapsePlus lapseMinus velocityPlus velocityMinus : ℝ) :
    AnalyticRealHasDerivAt
      (fun variedVelocity =>
        reducedCandidateLagrangian parameters x lapsePlus lapseMinus
          variedVelocity velocityMinus)
      (plusCanonicalMomentum parameters x lapsePlus velocityPlus)
      velocityPlus := by
  have hKinetic : AnalyticRealHasDerivAt
      (fun variedVelocity =>
        plusKineticLagrangian parameters x lapsePlus variedVelocity)
      (plusCanonicalMomentum parameters x lapsePlus velocityPlus)
      velocityPlus := by
    have hRaw : AnalyticRealHasDerivAt
        (fun variedVelocity : ℝ =>
          -3 * parameters.planckPlusSq * x.aPlus *
            (variedVelocity * variedVelocity) / lapsePlus)
        ((-3 * parameters.planckPlusSq * x.aPlus) *
          (velocityPlus + velocityPlus) / lapsePlus)
        velocityPlus := by
      simpa only [Pi.mul_apply, id_eq, one_mul, mul_one] using
        (((hasDerivAt_id velocityPlus).mul
          (hasDerivAt_id velocityPlus)).const_mul
            (-3 * parameters.planckPlusSq * x.aPlus)).div_const lapsePlus
    refine hRaw.congr_deriv ?_
    unfold plusCanonicalMomentum
    ring
  simpa [reducedCandidateLagrangian] using
    (hKinetic.add_const
      (minusKineticLagrangian parameters x lapseMinus velocityMinus)).add_const
        (reducedInteractionLagrangian parameters x lapsePlus lapseMinus)

/-- Unit affine-increment form of the minus-velocity derivative. -/
theorem reducedCandidateLagrangian_minusVelocityIncrement_hasDerivAt
    (parameters : ReducedParameters) (x : PhasePoint)
    (lapsePlus lapseMinus velocityPlus velocityMinus : ℝ) :
    HasDerivAt
      (fun increment =>
        reducedCandidateLagrangian parameters x lapsePlus lapseMinus
          velocityPlus (velocityMinus + increment))
      (minusCanonicalMomentum parameters x lapseMinus velocityMinus)
      0 := by
  have hVelocity : HasDerivAt
      (fun increment : ℝ => velocityMinus + increment * 1) 1 0 :=
    affineCoordinate_hasDerivAt velocityMinus 1
  have hKinetic : HasDerivAt
      (fun increment : ℝ =>
        minusKineticLagrangian parameters x lapseMinus
          (velocityMinus + increment))
      (minusCanonicalMomentum parameters x lapseMinus velocityMinus)
      0 := by
    have hRaw := ((hVelocity.mul hVelocity).const_mul
      (-3 * parameters.planckMinusSq * x.aMinus)).div_const lapseMinus
    have hDerivative := hRaw.congr_deriv
      (show
        -3 * parameters.planckMinusSq * x.aMinus *
            (1 * (velocityMinus + 0 * 1) +
              (velocityMinus + 0 * 1) * 1) / lapseMinus =
          minusCanonicalMomentum parameters x lapseMinus velocityMinus by
        simp [minusCanonicalMomentum]
        ring)
    simpa [minusKineticLagrangian] using hDerivative
  simpa [reducedCandidateLagrangian, minusKineticLagrangian] using
    ((hKinetic.const_add
      (plusKineticLagrangian parameters x lapsePlus velocityPlus)).add_const
        (reducedInteractionLagrangian parameters x lapsePlus lapseMinus))

/-- The minus momentum is the actual derivative of the reduced Lagrangian as
a function of the minus velocity. -/
theorem reducedCandidateLagrangian_minusVelocity_hasDerivAt
    (parameters : ReducedParameters) (x : PhasePoint)
    (lapsePlus lapseMinus velocityPlus velocityMinus : ℝ) :
    AnalyticRealHasDerivAt
      (fun variedVelocity =>
        reducedCandidateLagrangian parameters x lapsePlus lapseMinus
          velocityPlus variedVelocity)
      (minusCanonicalMomentum parameters x lapseMinus velocityMinus)
      velocityMinus := by
  have hKinetic : AnalyticRealHasDerivAt
      (fun variedVelocity =>
        minusKineticLagrangian parameters x lapseMinus variedVelocity)
      (minusCanonicalMomentum parameters x lapseMinus velocityMinus)
      velocityMinus := by
    have hRaw : AnalyticRealHasDerivAt
        (fun variedVelocity : ℝ =>
          -3 * parameters.planckMinusSq * x.aMinus *
            (variedVelocity * variedVelocity) / lapseMinus)
        ((-3 * parameters.planckMinusSq * x.aMinus) *
          (velocityMinus + velocityMinus) / lapseMinus)
        velocityMinus := by
      simpa only [Pi.mul_apply, id_eq, one_mul, mul_one] using
        (((hasDerivAt_id velocityMinus).mul
          (hasDerivAt_id velocityMinus)).const_mul
            (-3 * parameters.planckMinusSq * x.aMinus)).div_const lapseMinus
    refine hRaw.congr_deriv ?_
    unfold minusCanonicalMomentum
    ring
  simpa [reducedCandidateLagrangian] using
    ((hKinetic.const_add
      (plusKineticLagrangian parameters x lapsePlus velocityPlus)).add_const
        (reducedInteractionLagrangian parameters x lapsePlus lapseMinus))

/-- Regular inverse of the plus momentum--velocity relation. -/
def plusVelocityFromMomentum
    (parameters : ReducedParameters) (x : PhasePoint)
    (lapsePlus momentumPlus : ℝ) : ℝ :=
  -(lapsePlus * momentumPlus) /
    (6 * parameters.planckPlusSq * x.aPlus)

/-- Regular inverse of the minus momentum--velocity relation. -/
def minusVelocityFromMomentum
    (parameters : ReducedParameters) (x : PhasePoint)
    (lapseMinus momentumMinus : ℝ) : ℝ :=
  -(lapseMinus * momentumMinus) /
    (6 * parameters.planckMinusSq * x.aMinus)

theorem plusMomentum_after_velocityFromMomentum
    (parameters : ReducedParameters) (x : PhasePoint)
    (lapsePlus momentumPlus : ℝ)
    (hLapsePlus : lapsePlus ≠ 0)
    (hPlanckPlus : parameters.planckPlusSq ≠ 0)
    (haPlus : x.aPlus ≠ 0) :
    plusCanonicalMomentum parameters x lapsePlus
        (plusVelocityFromMomentum parameters x lapsePlus momentumPlus) =
      momentumPlus := by
  unfold plusCanonicalMomentum plusVelocityFromMomentum
  field_simp [hLapsePlus, hPlanckPlus, haPlus]

theorem plusVelocity_after_canonicalMomentum
    (parameters : ReducedParameters) (x : PhasePoint)
    (lapsePlus velocityPlus : ℝ)
    (hLapsePlus : lapsePlus ≠ 0)
    (hPlanckPlus : parameters.planckPlusSq ≠ 0)
    (haPlus : x.aPlus ≠ 0) :
    plusVelocityFromMomentum parameters x lapsePlus
        (plusCanonicalMomentum parameters x lapsePlus velocityPlus) =
      velocityPlus := by
  unfold plusCanonicalMomentum plusVelocityFromMomentum
  field_simp [hLapsePlus, hPlanckPlus, haPlus]

theorem minusMomentum_after_velocityFromMomentum
    (parameters : ReducedParameters) (x : PhasePoint)
    (lapseMinus momentumMinus : ℝ)
    (hLapseMinus : lapseMinus ≠ 0)
    (hPlanckMinus : parameters.planckMinusSq ≠ 0)
    (haMinus : x.aMinus ≠ 0) :
    minusCanonicalMomentum parameters x lapseMinus
        (minusVelocityFromMomentum parameters x lapseMinus momentumMinus) =
      momentumMinus := by
  unfold minusCanonicalMomentum minusVelocityFromMomentum
  field_simp [hLapseMinus, hPlanckMinus, haMinus]

theorem minusVelocity_after_canonicalMomentum
    (parameters : ReducedParameters) (x : PhasePoint)
    (lapseMinus velocityMinus : ℝ)
    (hLapseMinus : lapseMinus ≠ 0)
    (hPlanckMinus : parameters.planckMinusSq ≠ 0)
    (haMinus : x.aMinus ≠ 0) :
    minusVelocityFromMomentum parameters x lapseMinus
        (minusCanonicalMomentum parameters x lapseMinus velocityMinus) =
      velocityMinus := by
  unfold minusCanonicalMomentum minusVelocityFromMomentum
  field_simp [hLapseMinus, hPlanckMinus, haMinus]

/-- Exact bridge from the common square-root interaction, including the FLRW
spatial-volume factor, to the interaction term of the reduced Lagrangian. -/
theorem flrw_commonInteraction_eq_reducedInteractionLagrangian
    (parameters : ReducedParameters) (x : PhasePoint)
    (lapsePlus lapseMinus : ℝ)
    (hLapsePlus : lapsePlus ≠ 0)
    (haPlus : x.aPlus ≠ 0) :
    x.aPlus ^ 3 *
        (lapsePlus *
          commonInteractionPotential parameters.interactionScale
            parameters.coefficients
            (flrwDiagonalSpectrum (lapseMinus / lapsePlus)
              (x.aMinus / x.aPlus))) =
      reducedInteractionLagrangian parameters x lapsePlus lapseMinus := by
  rw [reciprocal_spectral_interaction_is_lapse_linear
    parameters.interactionScale parameters.coefficients
    (x.aMinus / x.aPlus) lapsePlus lapseMinus hLapsePlus]
  unfold candidateLapseInteraction plusLapseCoefficient minusLapseCoefficient
    reducedInteractionLagrangian plusPotential minusPotential
  field_simp [haPlus]

/-- Candidate A's reduced Lagrangian can therefore be written directly with
the common square-root interaction on the FLRW spectrum. -/
theorem reducedCandidateLagrangian_eq_commonInteraction_form
    (parameters : ReducedParameters) (x : PhasePoint)
    (lapsePlus lapseMinus velocityPlus velocityMinus : ℝ)
    (hLapsePlus : lapsePlus ≠ 0)
    (haPlus : x.aPlus ≠ 0) :
    reducedCandidateLagrangian parameters x lapsePlus lapseMinus
        velocityPlus velocityMinus =
      plusKineticLagrangian parameters x lapsePlus velocityPlus +
        minusKineticLagrangian parameters x lapseMinus velocityMinus +
        x.aPlus ^ 3 *
          (lapsePlus *
            commonInteractionPotential parameters.interactionScale
              parameters.coefficients
              (flrwDiagonalSpectrum (lapseMinus / lapsePlus)
                (x.aMinus / x.aPlus))) := by
  unfold reducedCandidateLagrangian
  rw [flrw_commonInteraction_eq_reducedInteractionLagrangian parameters x
    lapsePlus lapseMinus hLapsePlus haPlus]

/-- Legendre transform evaluated at the regular inverse velocities associated
with the phase-space momenta. -/
def reducedLegendreTransform
    (parameters : ReducedParameters) (x : PhasePoint)
    (lapsePlus lapseMinus : ℝ) : ℝ :=
  let velocityPlus :=
    plusVelocityFromMomentum parameters x lapsePlus x.pPlus
  let velocityMinus :=
    minusVelocityFromMomentum parameters x lapseMinus x.pMinus
  x.pPlus * velocityPlus + x.pMinus * velocityMinus -
    reducedCandidateLagrangian parameters x lapsePlus lapseMinus
      velocityPlus velocityMinus

/-- The exact Legendre transform is the lapse-weighted sum of the two
Hamiltonian constraints used by the reduced Dirac-chain gate. -/
theorem reducedLegendreTransform_eq_lapse_constraints
    (parameters : ReducedParameters) (x : PhasePoint)
    (lapsePlus lapseMinus : ℝ)
    (_hLapsePlus : lapsePlus ≠ 0)
    (_hLapseMinus : lapseMinus ≠ 0)
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

end

end P0EFTJanusReducedFLRWLegendreBridge
end JanusFormal
