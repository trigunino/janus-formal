import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06ActualPhysicalThirdJetTotalTangentTransition4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06BaseDependentPhysicalHorizontalDifferential4D

/-!
# Actual physical third-jet Cartan-frame transport

The tangent map of the local physical J3 total-space coordinate formula
transports a vertical Cartan frame after normalizing its base argument by the
inverse base Jacobian.  The resulting frame intertwines the two Cartan lifts
exactly and retains the base-variation term of the physical J3 transition.

This is a non-holonomic frame over J3.  No physical J4 atlas, Piola identity,
integrated Stokes map, or terminal T06 classification is asserted here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06ActualPhysicalThirdJetCartanFrameTransport4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000

noncomputable section

open Set
open scoped Manifold ContDiff RealInnerProductSpace Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusProgramPActualPhysicalThirdOrderJetProductVectorBundleCore4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionJacobianEquiv4D
open P0EFTJanusProgramPT06ThroatSpatialFinsuppJetTower4D
open P0EFTJanusProgramPT06ThroatSpatialMultiindexSecondJetBridge4D
open P0EFTJanusProgramPT06ActualPhysicalValueProductThirdJetBridge4D
open P0EFTJanusProgramPT06ActualPhysicalThirdJetVectorDensityHorizontalDifferential4D
open P0EFTJanusProgramPT06BaseDependentPhysicalHorizontalDifferential4D
open P0EFTJanusProgramPT06ActualPhysicalThirdJetTotalTangentTransition4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

attribute [local instance]
  P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D.actualPhysicalValueProductNormedAddCommGroup
  P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D.actualPhysicalValueProductNormedSpace
  P0EFTJanusProgramPT06ActualPhysicalValueProductThirdJetBridge4D.actualPhysicalThirdOrderJetProductNormedAddCommGroup
  P0EFTJanusProgramPT06ActualPhysicalValueProductThirdJetBridge4D.actualPhysicalThirdOrderJetProductNormedSpace
  P0EFTJanusProgramPT06ActualPhysicalValueProductThirdJetBridge4D.actualPhysicalThirdOrderJetProductFiniteDimensional

local instance actualPhysicalFormalThirdJetContinuousSMul :
    ContinuousSMul Real ProgramPT06ActualPhysicalFormalThirdJet4D :=
  IsBoundedSMul.continuousSMul

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev Base :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (Base period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω (Base period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

private abbrev Chart :=
  ActualPhysicalThirdOrderJetProductBundleIndex period hPeriod

private abbrev PhysicalThirdJet :=
  ActualPhysicalThirdOrderJetProductFiber

private abbrev PhysicalThirdJetCore :=
  actualPhysicalThirdOrderJetProductVectorBundleCore
    period hPeriod .positiveQuarter

/-- A non-holonomic vertical Cartan frame over the physical J3 fiber. -/
abbrev ProgramPT06ActualPhysicalThirdJetCartanFrame4D :=
  ThroatCoverCoordinates →L[Real] PhysicalThirdJet

/-- Lift a base direction by a supplied vertical Cartan frame. -/
def programPT06ActualPhysicalThirdJetCartanLift
    (frame : ProgramPT06ActualPhysicalThirdJetCartanFrame4D) :
    ThroatCoverCoordinates →L[Real]
      ProgramPT06ActualPhysicalThirdJetTotalCoordinateCarrier4D :=
  (ContinuousLinearMap.id Real ThroatCoverCoordinates).prod frame

@[simp]
theorem programPT06ActualPhysicalThirdJetCartanLift_apply
    (frame : ProgramPT06ActualPhysicalThirdJetCartanFrame4D)
    (direction : ThroatCoverCoordinates) :
    programPT06ActualPhysicalThirdJetCartanLift frame direction =
      (direction, frame direction) :=
  rfl

/-- Transport a Cartan frame by the tangent of the local total J3 coordinate
formula, with the source direction normalized by the inverse base Jacobian. -/
def programPT06ActualPhysicalThirdJetCartanFrameTransport
    (firstCenter secondCenter base : Base period hPeriod)
    (hFirst : base ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : base ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source)
    (first second : Chart period hPeriod)
    (_hBase : base ∈
      (PhysicalThirdJetCore period hPeriod).baseSet first ∩
        (PhysicalThirdJetCore period hPeriod).baseSet second)
    (jet : PhysicalThirdJet)
    (frame : ProgramPT06ActualPhysicalThirdJetCartanFrame4D) :
    ProgramPT06ActualPhysicalThirdJetCartanFrame4D :=
  (ContinuousLinearMap.snd Real ThroatCoverCoordinates PhysicalThirdJet).comp
    ((fderiv Real
      (programPT06ActualPhysicalThirdJetTotalCoordChange period hPeriod
        firstCenter secondCenter first second)
      (extChartAt throatCoverModelWithCorners firstCenter base, jet)).comp
      ((programPT06ActualPhysicalThirdJetCartanLift frame).comp
        (LinearMap.toContinuousLinearMap
          ((throatGaugeBaseChartTransitionJacobianEquivAt period hPeriod
            firstCenter secondCenter base hFirst hSecond).symm.toLinearMap))))

/-- Exact formula for the transported frame.  The second summand is the
base-variation term absent from a frozen fiber transition. -/
theorem programPT06ActualPhysicalThirdJetCartanFrameTransport_apply
    (firstCenter secondCenter base : Base period hPeriod)
    (hFirst : base ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : base ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source)
    (first second : Chart period hPeriod)
    (hBase : base ∈
      (PhysicalThirdJetCore period hPeriod).baseSet first ∩
        (PhysicalThirdJetCore period hPeriod).baseSet second)
    (jet : PhysicalThirdJet)
    (frame : ProgramPT06ActualPhysicalThirdJetCartanFrame4D)
    (direction : ThroatCoverCoordinates) :
    programPT06ActualPhysicalThirdJetCartanFrameTransport period hPeriod
        firstCenter secondCenter base hFirst hSecond first second hBase jet frame
        direction =
      (PhysicalThirdJetCore period hPeriod).coordChange first second base
          (frame
            ((throatGaugeBaseChartTransitionJacobianEquivAt period hPeriod
              firstCenter secondCenter base hFirst hSecond).symm direction)) +
        fderiv Real
            (programPT06ActualPhysicalThirdJetFiberCoordChangeInBaseChart
              period hPeriod firstCenter first second)
            (extChartAt throatCoverModelWithCorners firstCenter base)
            ((throatGaugeBaseChartTransitionJacobianEquivAt period hPeriod
              firstCenter secondCenter base hFirst hSecond).symm direction)
            jet := by
  unfold programPT06ActualPhysicalThirdJetCartanFrameTransport
  simp only [ContinuousLinearMap.comp_apply,
    programPT06ActualPhysicalThirdJetCartanLift_apply]
  rw [programPT06ActualPhysicalThirdJetTotalCoordChange_fderiv_apply
    period hPeriod firstCenter secondCenter base hFirst hSecond first second
    hBase]
  rfl

/-- The total tangent transition sends every lifted source direction to the
lifted transported frame at the transformed base direction. -/
theorem programPT06ActualPhysicalThirdJetCartanFrameTransport_intertwines
    (firstCenter secondCenter base : Base period hPeriod)
    (hFirst : base ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : base ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source)
    (first second : Chart period hPeriod)
    (hBase : base ∈
      (PhysicalThirdJetCore period hPeriod).baseSet first ∩
        (PhysicalThirdJetCore period hPeriod).baseSet second)
    (jet : PhysicalThirdJet)
    (frame : ProgramPT06ActualPhysicalThirdJetCartanFrame4D)
    (direction : ThroatCoverCoordinates) :
    fderiv Real
        (programPT06ActualPhysicalThirdJetTotalCoordChange period hPeriod
          firstCenter secondCenter first second)
        (extChartAt throatCoverModelWithCorners firstCenter base, jet)
        (programPT06ActualPhysicalThirdJetCartanLift frame
          direction) =
      programPT06ActualPhysicalThirdJetCartanLift
        (programPT06ActualPhysicalThirdJetCartanFrameTransport period hPeriod
          firstCenter secondCenter base hFirst hSecond first second hBase jet frame)
        (throatGaugeBaseChartTransitionJacobianEquivAt period hPeriod
          firstCenter secondCenter base hFirst hSecond direction) := by
  rw [programPT06ActualPhysicalThirdJetCartanLift_apply,
    programPT06ActualPhysicalThirdJetTotalCoordChange_fderiv_apply
      period hPeriod firstCenter secondCenter base hFirst hSecond first second
      hBase,
    programPT06ActualPhysicalThirdJetCartanLift_apply,
    programPT06ActualPhysicalThirdJetCartanFrameTransport_apply
      period hPeriod firstCenter secondCenter base hFirst hSecond first second
      hBase]
  rw [LinearEquiv.symm_apply_apply]

/-! ## Formal J4 source frame -/

/-- A formal physical J4 supplies a non-holonomic physical J3 Cartan frame by
linear extension of its three formal total derivatives. -/
def programPT06ActualPhysicalFormalFourthJetCartanFrame
    (jet : ProgramPT06ActualPhysicalFormalFourthJet4D) :
    ProgramPT06ActualPhysicalThirdJetCartanFrame4D :=
  programPT06ActualPhysicalValueProductThirdJetContinuousLinearEquiv.toContinuousLinearMap.comp
    (LinearMap.toContinuousLinearMap
      (programPT06ThroatSpatialBasis.constr Real fun direction =>
        throatSpatialTotalDerivative direction jet))

/-- On the spatial basis, the formal-J4 frame is exactly the corresponding
formal total derivative transported through the physical J3 bridge. -/
@[simp]
theorem programPT06ActualPhysicalFormalFourthJetCartanFrame_basis
    (jet : ProgramPT06ActualPhysicalFormalFourthJet4D)
    (direction : Fin 3) :
    programPT06ActualPhysicalFormalFourthJetCartanFrame jet
        (programPT06ThroatSpatialBasis direction) =
      programPT06ActualPhysicalValueProductThirdJetLinearEquiv
        (throatSpatialTotalDerivative direction jet) := by
  simp [programPT06ActualPhysicalFormalFourthJetCartanFrame,
    programPT06ActualPhysicalValueProductThirdJetContinuousLinearEquiv]

/-- The physical J3 point underlying a formal J4. -/
def programPT06ActualPhysicalFormalFourthJetBaseThirdJet
    (jet : ProgramPT06ActualPhysicalFormalFourthJet4D) : PhysicalThirdJet :=
  programPT06ActualPhysicalValueProductThirdJetLinearEquiv
    (truncateThroatSpatialMultiindexJet (by omega : 3 ≤ 4) jet)

/-- The J3 point and non-holonomic frame supplied together by a formal J4. -/
abbrev ProgramPT06ActualPhysicalThirdJetCartanState4D :=
  PhysicalThirdJet × ProgramPT06ActualPhysicalThirdJetCartanFrame4D

def programPT06ActualPhysicalFormalFourthJetCartanState
    (jet : ProgramPT06ActualPhysicalFormalFourthJet4D) :
    ProgramPT06ActualPhysicalThirdJetCartanState4D :=
  (programPT06ActualPhysicalFormalFourthJetBaseThirdJet jet,
    programPT06ActualPhysicalFormalFourthJetCartanFrame jet)

/-- The Cartan lift of a spatial basis vector is precisely the Gate-1020
formal Cartan direction transported through the physical J3 bridge. -/
@[simp]
theorem programPT06ActualPhysicalFormalFourthJetCartanLift_basis
    (jet : ProgramPT06ActualPhysicalFormalFourthJet4D)
    (direction : Fin 3) :
    programPT06ActualPhysicalThirdJetCartanLift
        (programPT06ActualPhysicalFormalFourthJetCartanFrame jet)
        (programPT06ThroatSpatialBasis direction) =
      (programPT06ThroatSpatialBasis direction,
        programPT06ActualPhysicalValueProductThirdJetLinearEquiv
          (throatSpatialTotalDerivative direction jet)) := by
  simp

end
end P0EFTJanusProgramPT06ActualPhysicalThirdJetCartanFrameTransport4D
end JanusFormal
