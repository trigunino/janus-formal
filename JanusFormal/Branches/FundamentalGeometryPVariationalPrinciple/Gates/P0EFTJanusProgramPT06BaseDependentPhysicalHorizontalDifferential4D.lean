import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06ActualPhysicalThirdJetVectorDensityHorizontalDifferential4D

/-!
# Base-dependent chartwise horizontal differential

This gate lets a physical third-jet vector density depend explicitly on one
throat chart coordinate.  Its total derivative is the sum of the two partial
Frechet derivatives in the Cartan direction `(e_i, D_i j)`: the coordinate
direction and the formal jet shift.

For an autonomous density the coordinate term vanishes and the construction
reduces exactly to Gate 1019.  Everything here remains local to one fixed
throat chart.  No atlas descent, integration, Stokes theorem, or terminal T06
classification is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06BaseDependentPhysicalHorizontalDifferential4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000

noncomputable section

open scoped BigOperators
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusProgramPT06ThroatSpatialFinsuppJetTower4D
open P0EFTJanusProgramPT06LocalFunctionTotalDerivative4D
open P0EFTJanusProgramPT06SecondOrderRadialCartanHomotopy4D
open P0EFTJanusProgramPT06ThroatSpatialMultiindexSecondJetBridge4D
open P0EFTJanusProgramPT06ActualPhysicalValueProductSecondJetBridge4D
open P0EFTJanusProgramPT06ActualPhysicalValueProductThirdJetBridge4D
open P0EFTJanusProgramPT06ActualPhysicalThirdJetVectorDensityCovariance4D
open P0EFTJanusProgramPT06ActualPhysicalThirdJetVectorDensityHorizontalDifferential4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

attribute [local instance]
  P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D.actualPhysicalValueProductNormedAddCommGroup
  P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D.actualPhysicalValueProductNormedSpace
  P0EFTJanusProgramPT06ActualPhysicalValueProductThirdJetBridge4D.actualPhysicalThirdOrderJetProductNormedAddCommGroup
  P0EFTJanusProgramPT06ActualPhysicalValueProductThirdJetBridge4D.actualPhysicalThirdOrderJetProductNormedSpace

/-- Formal third-jet coordinates for the complete physical value fiber. -/
abbrev ProgramPT06ActualPhysicalFormalThirdJet4D :=
  ThroatSpatialMultiindexJet3 ActualPhysicalValueProductFiber

/-- A weight-one vector density written in one throat chart and allowed to
depend on both the chart coordinate and the physical formal third jet. -/
abbrev ProgramPT06BaseDependentPhysicalThirdJetVectorDensity4D :=
  ThroatCoverCoordinates →
    ProgramPT06ActualPhysicalFormalThirdJet4D → ThroatCoverCoordinates

/-- Scalar fourth-jet density written in the same local chart. -/
abbrev ProgramPT06BaseDependentPhysicalFourthJetScalarDensity4D :=
  ThroatCoverCoordinates →
    ProgramPT06ActualPhysicalFormalFourthJet4D → Real

/-- The Cartan direction combines the selected coordinate basis vector with
the formal total derivative of the third jet. -/
def programPT06BaseDependentPhysicalCartanDirection
    (direction : Fin 3)
    (jet : ProgramPT06ActualPhysicalFormalFourthJet4D) :
    ThroatCoverCoordinates × ProgramPT06ActualPhysicalFormalThirdJet4D :=
  (programPT06ThroatSpatialBasis direction,
    throatSpatialTotalDerivative direction jet)

/-- One scalar component of a local physical vector density. -/
def programPT06BaseDependentPhysicalVectorDensityComponent
    (density : ProgramPT06BaseDependentPhysicalThirdJetVectorDensity4D)
    (direction : Fin 3) (coordinate : ThroatCoverCoordinates)
    (jet : ProgramPT06ActualPhysicalFormalThirdJet4D) : Real :=
  programPT06ThroatSpatialBasis.equivFun (density coordinate jet) direction

/-- One total derivative in the Cartan direction.  The split formula keeps
the explicit coordinate derivative visible and uses the same totalized
`fderiv` convention as Gate 1019. -/
def programPT06BaseDependentPhysicalTotalDerivative
    (direction : Fin 3)
    (density : ProgramPT06BaseDependentPhysicalThirdJetVectorDensity4D)
    (coordinate : ThroatCoverCoordinates)
    (jet : ProgramPT06ActualPhysicalFormalFourthJet4D) : Real :=
  let thirdJet :=
    truncateThroatSpatialMultiindexJet (by omega : 3 ≤ 4) jet
  let cartanDirection :=
    programPT06BaseDependentPhysicalCartanDirection direction jet
  fderiv Real
      (fun variedCoordinate =>
        programPT06BaseDependentPhysicalVectorDensityComponent density
          direction variedCoordinate thirdJet)
      coordinate cartanDirection.1 +
    fderiv Real
      (fun variedJet =>
        programPT06BaseDependentPhysicalVectorDensityComponent density
          direction coordinate variedJet)
      thirdJet cartanDirection.2

/-- Chartwise horizontal differential of a base-dependent physical vector
density. -/
def programPT06BaseDependentPhysicalHorizontalDifferential
    (density : ProgramPT06BaseDependentPhysicalThirdJetVectorDensity4D) :
    ProgramPT06BaseDependentPhysicalFourthJetScalarDensity4D :=
  fun coordinate jet =>
    ∑ direction : Fin 3,
      programPT06BaseDependentPhysicalTotalDerivative direction density
        coordinate jet

/-- Regard a Gate-1019 density as independent of the explicit chart
coordinate. -/
def programPT06BaseDependentPhysicalVectorDensityOfAutonomous
    (density : ProgramPT06ActualPhysicalThirdJetVectorDensity4D) :
    ProgramPT06BaseDependentPhysicalThirdJetVectorDensity4D :=
  fun _ jet =>
    density (programPT06ActualPhysicalValueProductThirdJetLinearEquiv jet)

/-- For an autonomous density, each base-dependent total derivative is the
corresponding formal total derivative from Gate 1019. -/
theorem programPT06BaseDependentPhysicalTotalDerivative_of_autonomous
    (density : ProgramPT06ActualPhysicalThirdJetVectorDensity4D)
    (direction : Fin 3) (coordinate : ThroatCoverCoordinates)
    (jet : ProgramPT06ActualPhysicalFormalFourthJet4D) :
    programPT06BaseDependentPhysicalTotalDerivative direction
        (programPT06BaseDependentPhysicalVectorDensityOfAutonomous density)
        coordinate jet =
      programPT06ThroatSpatialLocalFunctionTotalDerivative direction
        ((programPT06ActualPhysicalThirdJetVectorDensitySpatialCurrent
          density) direction) jet := by
  simp [programPT06BaseDependentPhysicalTotalDerivative,
    programPT06BaseDependentPhysicalCartanDirection,
    programPT06BaseDependentPhysicalVectorDensityOfAutonomous,
    programPT06BaseDependentPhysicalVectorDensityComponent,
    programPT06ThroatSpatialLocalFunctionTotalDerivative]
  have hFunction :
      (fun variedJet : ProgramPT06ActualPhysicalFormalThirdJet4D =>
        (programPT06ThroatSpatialBasis.repr
          (density
            (programPT06ActualPhysicalValueProductThirdJetLinearEquiv
              variedJet))) direction) =
        (programPT06ActualPhysicalThirdJetVectorDensitySpatialCurrent
          density) direction := by
    funext variedJet
    rfl
  rw [hFunction]

/-- The base-dependent horizontal differential reduces exactly to Gate 1019
when the vector density has no explicit coordinate dependence. -/
theorem baseDependentDH_of_autonomous
    (density : ProgramPT06ActualPhysicalThirdJetVectorDensity4D)
    (coordinate : ThroatCoverCoordinates) :
    programPT06BaseDependentPhysicalHorizontalDifferential
        (programPT06BaseDependentPhysicalVectorDensityOfAutonomous density)
        coordinate =
      programPT06ActualPhysicalThirdJetVectorDensityChartwiseDH density := by
  funext jet
  unfold programPT06BaseDependentPhysicalHorizontalDifferential
    programPT06ActualPhysicalThirdJetVectorDensityChartwiseDH
    programPT06SecondOrderHorizontalCurrentDH
  apply Finset.sum_congr rfl
  intro direction _
  exact programPT06BaseDependentPhysicalTotalDerivative_of_autonomous
    density direction coordinate jet

end

end P0EFTJanusProgramPT06BaseDependentPhysicalHorizontalDifferential4D
end JanusFormal
