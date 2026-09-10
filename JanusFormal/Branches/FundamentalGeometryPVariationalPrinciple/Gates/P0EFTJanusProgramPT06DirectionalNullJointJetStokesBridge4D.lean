import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06AffineJetNullJointStokesBridge4D

/-!
# Direction-parametrized jet realization of the null-to-joint transgression

Gate 899 uses the distinguished first formal throat direction to represent the
one-dimensional null-generator parameter.  This gate removes that coordinate
choice: every supplied `Fin 3` direction gives a genuine order-one current and
order-two jet whose horizontal divergence is the same canonical T05 null-face
density.  Integration is consequently the existing null-to-joint relative
incidence of Gate 819.

The direction is explicit coordinate-assignment data: it says which formal jet
coordinate represents the generator parameter.  It does not assert that this
coordinate is a geometric tangent vector, that the remaining coordinates are
holonomic, or that T05 supplies a three-dimensional tangential Stokes theorem.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06DirectionalNullJointJetStokesBridge4D

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
open P0EFTJanusProgramPT06AffineJetNullJointStokesBridge4D

private theorem throatSpatialCoordinateMultiIndex_ne_zero
    (direction : Fin 3) :
    throatSpatialCoordinateMultiIndex direction ≠ 0 := by
  intro hIndex
  have hOrder := congrArg throatSpatialMultiIndexOrder hIndex
  simp at hOrder

/-- The affine current that reads the value coefficient in one supplied formal
direction and vanishes in the other two directions. -/
def programPT06DirectionalValueAffineCurrent
    (assignedDirection : Fin 3) :
    ProgramPT06AffineHorizontalCurrent4D Real where
  constant := 0
  linear direction :=
    if direction = assignedDirection then
      ContinuousLinearMap.proj programPT06CutBulkFirstOrderZeroMultiIndex
    else
      0

@[simp] theorem programPT06DirectionalValueAffineCurrent_linear_self
    (assignedDirection : Fin 3) :
    (programPT06DirectionalValueAffineCurrent assignedDirection).linear
        assignedDirection =
      (ContinuousLinearMap.proj programPT06CutBulkFirstOrderZeroMultiIndex :
        ThroatSpatialMultiindexJet1 Real →L[Real] Real) := by
  simp [programPT06DirectionalValueAffineCurrent]

@[simp] theorem programPT06DirectionalValueAffineCurrent_linear_of_ne
    (assignedDirection direction : Fin 3)
    (hDirection : direction ≠ assignedDirection) :
    (programPT06DirectionalValueAffineCurrent assignedDirection).linear
        direction = 0 := by
  simp [programPT06DirectionalValueAffineCurrent, hDirection]

/-- The second jet representing the scaled endpoint primitive and its actual
parameter derivative in the supplied formal direction. -/
def programPT06DirectionalNullJointSecondJet
    (assignedDirection : Fin 3)
    (face : FiniteNullFaceActionDatum) (parameter : Real) :
    ThroatSpatialMultiindexJet2 Real :=
  fun index =>
    if index.1 = 0 then
      nullFaceCoefficient face *
        endpointPrimitive face.generator parameter
    else if index.1 = throatSpatialCoordinateMultiIndex assignedDirection then
      deriv
        (fun current =>
          nullFaceCoefficient face *
            endpointPrimitive face.generator current)
        parameter
    else
      0

@[simp] theorem programPT06DirectionalNullJointSecondJet_value
    (assignedDirection : Fin 3)
    (face : FiniteNullFaceActionDatum) (parameter : Real) :
    programPT06DirectionalNullJointSecondJet assignedDirection face parameter
        programPT06SecondOrderZeroMultiIndex =
      nullFaceCoefficient face *
        endpointPrimitive face.generator parameter := by
  simp [programPT06DirectionalNullJointSecondJet,
    programPT06SecondOrderZeroMultiIndex]

@[simp] theorem programPT06DirectionalNullJointSecondJet_first
    (assignedDirection : Fin 3)
    (face : FiniteNullFaceActionDatum) (parameter : Real) :
    programPT06DirectionalNullJointSecondJet assignedDirection face parameter
        (programPT06SecondOrderFirstMultiIndex assignedDirection) =
      deriv
        (fun current =>
          nullFaceCoefficient face *
            endpointPrimitive face.generator current)
        parameter := by
  simp [programPT06DirectionalNullJointSecondJet,
    programPT06SecondOrderFirstMultiIndex,
    throatSpatialCoordinateMultiIndex_ne_zero]

/-- The selected current component reads the actual endpoint primitive. -/
theorem programPT06DirectionalValueAffineCurrent_component_eq_primitive
    (assignedDirection : Fin 3)
    (face : FiniteNullFaceActionDatum) (parameter : Real) :
    programPT06AffineHorizontalCurrentComponent
        (programPT06DirectionalValueAffineCurrent assignedDirection)
        assignedDirection
        (truncateThroatSpatialMultiindexJet (by omega : 1 <= 2)
          (programPT06DirectionalNullJointSecondJet assignedDirection face
            parameter)) =
      nullFaceCoefficient face *
        endpointPrimitive face.generator parameter := by
  simp [programPT06AffineHorizontalCurrentComponent,
    programPT06DirectionalValueAffineCurrent,
    programPT06CutBulkFirstOrderZeroMultiIndex,
    truncateThroatSpatialMultiindexJet,
    programPT06DirectionalNullJointSecondJet]

@[simp] theorem
    programPT06DirectionalValueAffineCurrent_linear_totalDerivative
    (assignedDirection : Fin 3)
    (face : FiniteNullFaceActionDatum) (parameter : Real) :
    (programPT06DirectionalValueAffineCurrent assignedDirection).linear
        assignedDirection
        (throatSpatialTotalDerivative assignedDirection
          (programPT06DirectionalNullJointSecondJet assignedDirection face
            parameter)) =
      deriv
        (fun current =>
          nullFaceCoefficient face *
            endpointPrimitive face.generator current)
        parameter := by
  simp [programPT06DirectionalValueAffineCurrent,
    programPT06CutBulkFirstOrderZeroMultiIndex,
    throatSpatialTotalDerivative,
    programPT06DirectionalNullJointSecondJet,
    throatSpatialCoordinateMultiIndex_ne_zero]

/-- In every supplied formal direction, Gate 879's divergence is the canonical
T05 null-face density. -/
theorem programPT06DirectionalNullJointAffineDivergence_eq_density
    (assignedDirection : Fin 3)
    (face : FiniteNullFaceActionDatum) (parameter : Real) :
    programPT06AffineHorizontalCurrentDivergence
        (programPT06DirectionalValueAffineCurrent assignedDirection)
        (programPT06DirectionalNullJointSecondJet assignedDirection face
          parameter) =
      nullFaceCoefficient face * localFaceShift face.generator parameter := by
  rw [programPT06AffineHorizontalCurrentDivergence_apply]
  rw [Finset.sum_eq_single assignedDirection]
  ·
    rw [programPT06DirectionalValueAffineCurrent_linear_totalDerivative]
    exact programPT06CanonicalNullJointPrimitive_deriv face parameter
  · intro direction _ hDirection
    rw [programPT06DirectionalValueAffineCurrent_linear_of_ne
      assignedDirection direction hDirection]
    rfl
  · simp

theorem programPT06DirectionalNullJointAffineDivergence_eq_canonical
    (assignedDirection : Fin 3)
    (face : FiniteNullFaceActionDatum) (parameter : Real) :
    programPT06AffineHorizontalCurrentDivergence
        (programPT06DirectionalValueAffineCurrent assignedDirection)
        (programPT06DirectionalNullJointSecondJet assignedDirection face
          parameter) =
      (programPT05CanonicalNullJointLocalDensityCochain face).nullBoundaryDensity
        parameter := by
  rw [programPT06DirectionalNullJointAffineDivergence_eq_density,
    programPT05CanonicalNullBoundaryDensity_apply]

/-- Every member of the direction-parametrized family is in Gate 880's Euler
kernel. -/
theorem programPT06DirectionalNullJointAffineDivergence_euler_eq_zero
    (assignedDirection : Fin 3)
    (jet : ThroatSpatialMultiindexJet4 Real) :
    programPT06SecondOrderLocalEuler
        (programPT06AffineHorizontalCurrentDivergence
          (programPT06DirectionalValueAffineCurrent assignedDirection)) jet = 0 := by
  exact programPT06SecondOrderLocalEuler_horizontalDivergence_eq_zero
    (programPT06DirectionalValueAffineCurrent assignedDirection) jet

/-- T05's local null-to-joint cochain with its face density represented in the
supplied formal jet direction. -/
def programPT06DirectionalNullJointJetLocalDensityCochain
    (assignedDirection : Fin 3)
    (face : FiniteNullFaceActionDatum) :
    ProgramPT05NullJointLocalDensityCochain where
  nullBoundaryDensity parameter :=
    programPT06AffineHorizontalCurrentDivergence
      (programPT06DirectionalValueAffineCurrent assignedDirection)
      (programPT06DirectionalNullJointSecondJet assignedDirection face
        parameter)
  initialJointDensity :=
    nullFaceCoefficient face *
      endpointPrimitive face.generator face.interval.initialParameter
  finalJointDensity :=
    -(nullFaceCoefficient face *
      endpointPrimitive face.generator face.interval.finalParameter)

theorem programPT06DirectionalNullJointJetLocalDensityCochain_eq_geometric
    (assignedDirection : Fin 3)
    (face : FiniteNullFaceActionDatum) :
    programPT06DirectionalNullJointJetLocalDensityCochain assignedDirection face =
      programPT05CanonicalNullJointLocalDensityCochain face := by
  unfold programPT06DirectionalNullJointJetLocalDensityCochain
  unfold programPT05CanonicalNullJointLocalDensityCochain
  congr 1
  funext parameter
  exact programPT06DirectionalNullJointAffineDivergence_eq_canonical
    assignedDirection face parameter

/-- The local divergence in any supplied direction obeys the existing T05
null-face Stokes/FTOC identity. -/
theorem programPT06DirectionalNullJointJetLocalDensity_stokes
    (assignedDirection : Fin 3)
    (face : FiniteNullFaceActionDatum)
    (contract : NullFaceIntervalIntegrability face) :
    programPT05NullBoundaryDensityIntegral face
        (programPT06DirectionalNullJointJetLocalDensityCochain
          assignedDirection face) +
      programPT05JointDensityEvaluation
        (programPT06DirectionalNullJointJetLocalDensityCochain
          assignedDirection face) = 0 := by
  rw [programPT06DirectionalNullJointJetLocalDensityCochain_eq_geometric]
  exact programPT05CanonicalNullJointDensity_stokes face contract

/-- Integration sends every direction-parametrized local jet divergence to the
existing Gate-819 `nullBoundary -> joint` incidence. -/
theorem programPT06DirectionalNullJointJetLocalDensity_dH_joint
    (assignedDirection : Fin 3)
    (face : FiniteNullFaceActionDatum)
    (contract : NullFaceIntervalIntegrability face) :
    (programPT05ExactT03RelativeBicomplex.dH 3 0
      (programPT05NullBoundaryDensityIntegratedCochain face
        (programPT06DirectionalNullJointJetLocalDensityCochain
          assignedDirection face))) .joint =
    (programPT05JointDensityIntegratedCochain
      (programPT06DirectionalNullJointJetLocalDensityCochain
        assignedDirection face)) .joint := by
  rw [programPT06DirectionalNullJointJetLocalDensityCochain_eq_geometric]
  exact programPT05CanonicalNullJointLocalDensity_dH_joint face contract

end
end P0EFTJanusProgramPT06DirectionalNullJointJetStokesBridge4D
end JanusFormal
