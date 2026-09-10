import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06AffineJetCutBulkStokesBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT05NullJointLocalDensityIncidence4D

/-!
# Affine jet realization of the T05 null-face to joint transgression

This gate realizes the canonical normalization transgression on one null face
inside the order-one/order-two jet calculus of Gate 879.  The value coefficient
stores the endpoint primitive and its first coefficient in the chosen formal
normal direction stores its actual derivative.  The affine divergence is
therefore exactly T05's local null-face density.

The existing T05 FTOC then identifies its integral with the two oriented joint
values and Gate 819's null-to-joint horizontal differential.  This covers one
reduced normalization transgression; it does not realize arbitrary null-face
fields or the other physical boundary sectors.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06AffineJetNullJointStokesBridge4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusNullJointReparametrizationCancellation
open P0EFTJanusFiniteNullFaceAction
open P0EFTJanusProgramPRelativeJetVariationalBicomplexCore4D
open P0EFTJanusProgramPRelativeJetVariationalBicomplexCore4D.RelativeJetStratum4D
open P0EFTJanusProgramPT05ExactT03RelativeVariationalRealization4D
open P0EFTJanusProgramPT05NullJointLocalDensityIncidence4D
open P0EFTJanusProgramPT06ThroatSpatialFinsuppJetTower4D
open P0EFTJanusProgramPT06SecondOrderLocalEuler4D
open P0EFTJanusProgramPT06HorizontalDivergenceEulerSoundness4D
open P0EFTJanusProgramPT06AffineJetCutBulkStokesBridge4D

private theorem throatSpatialCoordinateMultiIndex_ne_zero
    (direction : Fin 3) :
    Not (throatSpatialCoordinateMultiIndex direction = 0) := by
  intro hIndex
  have hOrder := congrArg throatSpatialMultiIndexOrder hIndex
  simp at hOrder

/-- The scaled endpoint primitive has the canonical local face shift as its
actual derivative. -/
theorem programPT06CanonicalNullJointPrimitive_hasDerivAt
    (face : FiniteNullFaceActionDatum) (parameter : Real) :
    HasDerivAt
        (fun current =>
          nullFaceCoefficient face *
            endpointPrimitive face.generator current)
        (nullFaceCoefficient face *
          localFaceShift face.generator parameter)
        parameter := by
  simpa [endpointPrimitive] using
    (area_mul_sigma_hasDerivAt face.generator parameter).const_mul
      (nullFaceCoefficient face)

theorem programPT06CanonicalNullJointPrimitive_deriv
    (face : FiniteNullFaceActionDatum) (parameter : Real) :
    deriv
        (fun current =>
          nullFaceCoefficient face *
            endpointPrimitive face.generator current)
        parameter =
      nullFaceCoefficient face * localFaceShift face.generator parameter := by
  exact (programPT06CanonicalNullJointPrimitive_hasDerivAt face parameter).deriv

/-- A genuine second jet carrying the scaled endpoint primitive and its
derivative in the distinguished formal normal direction. -/
def programPT06CanonicalNullJointNormalSecondJet
    (face : FiniteNullFaceActionDatum) (parameter : Real) :
    ThroatSpatialMultiindexJet2 Real :=
  fun index =>
    if index.1 = 0 then
      nullFaceCoefficient face *
        endpointPrimitive face.generator parameter
    else if index.1 = throatSpatialCoordinateMultiIndex
        programPT06CutBulkNormalDirection then
      deriv
        (fun current =>
          nullFaceCoefficient face *
            endpointPrimitive face.generator current)
        parameter
    else
      0

@[simp] theorem programPT06CanonicalNullJointNormalSecondJet_value
    (face : FiniteNullFaceActionDatum) (parameter : Real) :
    programPT06CanonicalNullJointNormalSecondJet face parameter
        programPT06SecondOrderZeroMultiIndex =
      nullFaceCoefficient face *
        endpointPrimitive face.generator parameter := by
  simp [programPT06CanonicalNullJointNormalSecondJet,
    programPT06SecondOrderZeroMultiIndex]

@[simp] theorem programPT06CanonicalNullJointNormalSecondJet_normalFirst
    (face : FiniteNullFaceActionDatum) (parameter : Real) :
    programPT06CanonicalNullJointNormalSecondJet face parameter
        (programPT06SecondOrderFirstMultiIndex
          programPT06CutBulkNormalDirection) =
      deriv
        (fun current =>
          nullFaceCoefficient face *
            endpointPrimitive face.generator current)
        parameter := by
  simp [programPT06CanonicalNullJointNormalSecondJet,
    programPT06SecondOrderFirstMultiIndex,
    throatSpatialCoordinateMultiIndex_ne_zero]

/-- The distinguished affine-current component reads the actual scaled
endpoint primitive from the realized jet. -/
theorem programPT06CanonicalNullJointNormalAffineCurrent_component_eq_primitive
    (face : FiniteNullFaceActionDatum) (parameter : Real) :
    programPT06AffineHorizontalCurrentComponent
        programPT06CanonicalCutBulkNormalAffineCurrent
        programPT06CutBulkNormalDirection
        (truncateThroatSpatialMultiindexJet (by omega : 1 <= 2)
          (programPT06CanonicalNullJointNormalSecondJet face parameter)) =
      nullFaceCoefficient face *
        endpointPrimitive face.generator parameter := by
  simp [programPT06AffineHorizontalCurrentComponent,
    programPT06CanonicalCutBulkNormalAffineCurrent,
    programPT06CutBulkFirstOrderZeroMultiIndex,
    truncateThroatSpatialMultiindexJet,
    programPT06CanonicalNullJointNormalSecondJet]

@[simp] theorem
    programPT06CanonicalNullJointNormalAffineCurrent_linear_totalDerivative
    (face : FiniteNullFaceActionDatum) (parameter : Real) :
    programPT06CanonicalCutBulkNormalAffineCurrent.linear
        programPT06CutBulkNormalDirection
        (throatSpatialTotalDerivative programPT06CutBulkNormalDirection
          (programPT06CanonicalNullJointNormalSecondJet face parameter)) =
      deriv
        (fun current =>
          nullFaceCoefficient face *
            endpointPrimitive face.generator current)
        parameter := by
  simp [programPT06CanonicalCutBulkNormalAffineCurrent,
    programPT06CutBulkFirstOrderZeroMultiIndex,
    throatSpatialTotalDerivative,
    programPT06CanonicalNullJointNormalSecondJet,
    throatSpatialCoordinateMultiIndex_ne_zero]

/-- Gate 879's affine horizontal divergence is exactly the canonical T05
null-face transgression density. -/
theorem programPT06CanonicalNullJointNormalAffineDivergence_eq_density
    (face : FiniteNullFaceActionDatum) (parameter : Real) :
    programPT06AffineHorizontalCurrentDivergence
        programPT06CanonicalCutBulkNormalAffineCurrent
        (programPT06CanonicalNullJointNormalSecondJet face parameter) =
      nullFaceCoefficient face * localFaceShift face.generator parameter := by
  rw [programPT06AffineHorizontalCurrentDivergence_apply]
  rw [Finset.sum_eq_single programPT06CutBulkNormalDirection]
  ·
    rw [programPT06CanonicalNullJointNormalAffineCurrent_linear_totalDerivative]
    exact programPT06CanonicalNullJointPrimitive_deriv face parameter
  · intro direction _ hDirection
    rw [programPT06CanonicalCutBulkNormalAffineCurrent_linear_of_ne direction
      hDirection]
    rfl
  · simp

theorem programPT06CanonicalNullJointNormalAffineDivergence_eq_canonical
    (face : FiniteNullFaceActionDatum) (parameter : Real) :
    programPT06AffineHorizontalCurrentDivergence
        programPT06CanonicalCutBulkNormalAffineCurrent
        (programPT06CanonicalNullJointNormalSecondJet face parameter) =
      (programPT05CanonicalNullJointLocalDensityCochain face).nullBoundaryDensity
        parameter := by
  rw [programPT06CanonicalNullJointNormalAffineDivergence_eq_density,
    programPT05CanonicalNullBoundaryDensity_apply]

/-- The realized null-face divergence lies in Gate 880's Euler kernel. -/
theorem programPT06CanonicalNullJointNormalAffineDivergence_euler_eq_zero
    (jet : ThroatSpatialMultiindexJet4 Real) :
    programPT06SecondOrderLocalEuler
        (programPT06AffineHorizontalCurrentDivergence
          programPT06CanonicalCutBulkNormalAffineCurrent) jet = 0 := by
  exact programPT06SecondOrderLocalEuler_horizontalDivergence_eq_zero
    programPT06CanonicalCutBulkNormalAffineCurrent jet

/-- T05's canonical null-to-joint cochain with its face density presented by
the genuine affine jet divergence. -/
def programPT06CanonicalNullJointJetLocalDensityCochain
    (face : FiniteNullFaceActionDatum) :
    ProgramPT05NullJointLocalDensityCochain where
  nullBoundaryDensity parameter :=
    programPT06AffineHorizontalCurrentDivergence
      programPT06CanonicalCutBulkNormalAffineCurrent
      (programPT06CanonicalNullJointNormalSecondJet face parameter)
  initialJointDensity :=
    nullFaceCoefficient face *
      endpointPrimitive face.generator face.interval.initialParameter
  finalJointDensity :=
    -(nullFaceCoefficient face *
      endpointPrimitive face.generator face.interval.finalParameter)

/-- The jet presentation is definitionally the existing geometric T05
cochain in the joint entries and propositionally equal in the face entry. -/
theorem programPT06CanonicalNullJointJetLocalDensityCochain_eq_geometric
    (face : FiniteNullFaceActionDatum) :
    programPT06CanonicalNullJointJetLocalDensityCochain face =
      programPT05CanonicalNullJointLocalDensityCochain face := by
  unfold programPT06CanonicalNullJointJetLocalDensityCochain
  unfold programPT05CanonicalNullJointLocalDensityCochain
  congr 1
  funext parameter
  exact programPT06CanonicalNullJointNormalAffineDivergence_eq_canonical
    face parameter

/-- The integrated local jet divergence and its two oriented joint values obey
the already proved null-face Stokes/FTOC identity. -/
theorem programPT06CanonicalNullJointJetLocalDensity_stokes
    (face : FiniteNullFaceActionDatum)
    (contract : NullFaceIntervalIntegrability face) :
    programPT05NullBoundaryDensityIntegral face
        (programPT06CanonicalNullJointJetLocalDensityCochain face) +
      programPT05JointDensityEvaluation
        (programPT06CanonicalNullJointJetLocalDensityCochain face) = 0 := by
  rw [programPT06CanonicalNullJointJetLocalDensityCochain_eq_geometric]
  exact programPT05CanonicalNullJointDensity_stokes face contract

/-- Integration of the local affine jet divergence is exactly Gate 819's
null-boundary to joint horizontal incidence. -/
theorem programPT06CanonicalNullJointJetLocalDensity_dH_joint
    (face : FiniteNullFaceActionDatum)
    (contract : NullFaceIntervalIntegrability face) :
    (programPT05ExactT03RelativeBicomplex.dH 3 0
      (programPT05NullBoundaryDensityIntegratedCochain face
        (programPT06CanonicalNullJointJetLocalDensityCochain face))) .joint =
    (programPT05JointDensityIntegratedCochain
      (programPT06CanonicalNullJointJetLocalDensityCochain face)) .joint := by
  rw [programPT06CanonicalNullJointJetLocalDensityCochain_eq_geometric]
  exact programPT05CanonicalNullJointLocalDensity_dH_joint face contract

end
end P0EFTJanusProgramPT06AffineJetNullJointStokesBridge4D
end JanusFormal
