import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT05CutBulkLocalDensityStokesBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteNullFaceAction

/-!
# T05 null-face to joint local-density incidence

This module adds the existing finite null-generator reparametrization density
and its two endpoint-joint densities to the partial local realization of T05.
Their interval integral and oriented endpoint evaluation obey the proved FTOC,
and hence realize the `nullBoundary → joint` component of Gate 819's nonzero
horizontal differential.

The construction realizes only the normalization transgression of one reduced
null generator.  It is not a local jet Euler density, and it does not supply
null-position, screen-metric, metric/GHY, or LL density sectors.  T05 remains
open.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT05NullJointLocalDensityIncidence4D

set_option autoImplicit false
noncomputable section

open scoped Interval
open P0EFTJanusNullJointReparametrizationCancellation
open P0EFTJanusFiniteStratifiedBoundaryVariation
open P0EFTJanusFiniteNullFaceAction
open P0EFTJanusProgramPRelativeJetVariationalBicomplexCore4D
open P0EFTJanusProgramPRelativeJetVariationalBicomplexCore4D.RelativeJetStratum4D
open P0EFTJanusProgramPT05ExactT03RelativeVariationalRealization4D

/-- A local normalization-transgression density on one null face together with
the two oriented endpoint-joint densities. -/
structure ProgramPT05NullJointLocalDensityCochain where
  nullBoundaryDensity : Real → Real
  initialJointDensity : Real
  finalJointDensity : Real

/-- The actual finite-rescaling density difference and its endpoint shifts. -/
def programPT05CanonicalNullJointLocalDensityCochain
    (face : FiniteNullFaceActionDatum) :
    ProgramPT05NullJointLocalDensityCochain where
  nullBoundaryDensity parameter :=
    reparametrizedNullFaceDensity face parameter -
      nullFaceDensity face parameter
  initialJointDensity :=
    nullFaceCoefficient face *
      endpointPrimitive face.generator face.interval.initialParameter
  finalJointDensity :=
    -(nullFaceCoefficient face *
      endpointPrimitive face.generator face.interval.finalParameter)

/-- Integral of a typed local null-face density on its oriented generator. -/
def programPT05NullBoundaryDensityIntegral
    (face : FiniteNullFaceActionDatum)
    (density : ProgramPT05NullJointLocalDensityCochain) : Real :=
  ∫ parameter in face.interval.initialParameter..face.interval.finalParameter,
    density.nullBoundaryDensity parameter

/-- Oriented evaluation of the two endpoint-joint densities. -/
def programPT05JointDensityEvaluation
    (density : ProgramPT05NullJointLocalDensityCochain) : Real :=
  density.initialJointDensity + density.finalJointDensity

/-- The local null-face entry is exactly the already proved transgression
density. -/
theorem programPT05CanonicalNullBoundaryDensity_apply
    (face : FiniteNullFaceActionDatum) (parameter : Real) :
    (programPT05CanonicalNullJointLocalDensityCochain face).nullBoundaryDensity
        parameter =
      nullFaceCoefficient face * localFaceShift face.generator parameter := by
  change reparametrizedNullFaceDensity face parameter -
      nullFaceDensity face parameter = _
  rw [reparametrizedNullFaceDensity_eq]
  ring

/-- The endpoint evaluation is the actual change of the supplied joint
action. -/
theorem programPT05CanonicalJointDensityEvaluation_eq_action_change
    (face : FiniteNullFaceActionDatum) :
    programPT05JointDensityEvaluation
        (programPT05CanonicalNullJointLocalDensityCochain face) =
      reparametrizedEndpointJointAction face - endpointJointAction face := by
  rw [reparametrizedEndpointJointAction_eq]
  simp [programPT05JointDensityEvaluation,
    programPT05CanonicalNullJointLocalDensityCochain]
  ring

/-- The existing FTOC identifies the integral of the local face transgression
with the oriented endpoint primitive. -/
theorem programPT05CanonicalNullBoundaryDensityIntegral_eq_endpoint
    (face : FiniteNullFaceActionDatum)
    (contract : NullFaceIntervalIntegrability face) :
    programPT05NullBoundaryDensityIntegral face
        (programPT05CanonicalNullJointLocalDensityCochain face) =
      nullFaceCoefficient face *
        (endpointPrimitive face.generator face.interval.finalParameter -
          endpointPrimitive face.generator face.interval.initialParameter) := by
  have hDensity :
      (programPT05CanonicalNullJointLocalDensityCochain face).nullBoundaryDensity =
        fun parameter ↦
          nullFaceCoefficient face * localFaceShift face.generator parameter := by
    funext parameter
    exact programPT05CanonicalNullBoundaryDensity_apply face parameter
  rw [programPT05NullBoundaryDensityIntegral, hDensity,
    intervalIntegral.integral_const_mul]
  have hFTOC := integratedNullFaceShift_eq_endpointTransgression
    (reparametrizationVariationDatum face contract)
  change
    (∫ parameter in
        face.interval.initialParameter..face.interval.finalParameter,
      localFaceShift face.generator parameter) =
      endpointPrimitive face.generator face.interval.finalParameter -
        endpointPrimitive face.generator face.interval.initialParameter at hFTOC
  rw [hFTOC]

/-- The integrated null-face density and its two joint densities cancel with
the exact orientation signs. -/
theorem programPT05CanonicalNullJointDensity_stokes
    (face : FiniteNullFaceActionDatum)
    (contract : NullFaceIntervalIntegrability face) :
    programPT05NullBoundaryDensityIntegral face
        (programPT05CanonicalNullJointLocalDensityCochain face) +
      programPT05JointDensityEvaluation
        (programPT05CanonicalNullJointLocalDensityCochain face) = 0 := by
  rw [programPT05CanonicalNullBoundaryDensityIntegral_eq_endpoint face contract]
  simp [programPT05JointDensityEvaluation,
    programPT05CanonicalNullJointLocalDensityCochain]
  ring

/-- Support extension of the integrated null density to Gate 819.  The zero
entries record absent strata; the horizontal differential itself is unchanged
and nonzero. -/
def programPT05NullBoundaryDensityIntegratedCochain
    (face : FiniteNullFaceActionDatum)
    (density : ProgramPT05NullJointLocalDensityCochain) :
    RelativeJetCochain ProgramPT05PhysicalJetComponent 3 0
  | .bulk => 0
  | .nonNullBoundary => 0
  | .nullBoundary =>
      (programPT05NullBoundaryDensityIntegral face density, 0)
  | .joint => 0

/-- Support extension of the endpoint evaluation to Gate 819's joint slot. -/
def programPT05JointDensityIntegratedCochain
    (density : ProgramPT05NullJointLocalDensityCochain) :
    RelativeJetCochain ProgramPT05PhysicalJetComponent 4 0
  | .bulk => 0
  | .nonNullBoundary => 0
  | .nullBoundary => 0
  | .joint => (programPT05JointDensityEvaluation density, 0)

/-- For the canonical local densities, Gate 819's joint incidence is exactly
the finite null-face Stokes/FTOC law. -/
theorem programPT05CanonicalNullJointLocalDensity_dH_joint
    (face : FiniteNullFaceActionDatum)
    (contract : NullFaceIntervalIntegrability face) :
    (programPT05ExactT03RelativeBicomplex.dH 3 0
      (programPT05NullBoundaryDensityIntegratedCochain face
        (programPT05CanonicalNullJointLocalDensityCochain face))) .joint =
    (programPT05JointDensityIntegratedCochain
      (programPT05CanonicalNullJointLocalDensityCochain face)) .joint := by
  change
    (0 : Real × Real) -
      (programPT05NullBoundaryDensityIntegral face
        (programPT05CanonicalNullJointLocalDensityCochain face), 0) =
      (programPT05JointDensityEvaluation
        (programPT05CanonicalNullJointLocalDensityCochain face), 0)
  have hStokes := programPT05CanonicalNullJointDensity_stokes face contract
  apply Prod.ext
  · change 0 - programPT05NullBoundaryDensityIntegral face
        (programPT05CanonicalNullJointLocalDensityCochain face) =
      programPT05JointDensityEvaluation
        (programPT05CanonicalNullJointLocalDensityCochain face)
    linarith
  · simp

end
end P0EFTJanusProgramPT05NullJointLocalDensityIncidence4D
end JanusFormal
