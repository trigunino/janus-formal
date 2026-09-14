import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06ThroatAbsoluteVectorPullbackPiola4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06RadialJointHorizontalDifferentialBridge4D

namespace JanusFormal
namespace P0EFTJanusProgramPT06ActualPhysicalThirdJetCartanPiolaNaturality4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000

noncomputable section

open Set Filter
open scoped BigOperators Manifold ContDiff RealInnerProductSpace Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusProgramPActualPhysicalThirdOrderJetProductVectorBundleCore4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionGerm4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionJacobianEquiv4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionSecondOrderGroupoid4D
open P0EFTJanusProgramPT02InvariantLocalFunctionalBasisTerminalCertificate4D
open P0EFTJanusProgramPT06ThroatSpatialMultiindexSecondJetBridge4D
open P0EFTJanusProgramPT06ActualPhysicalValueProductThirdJetBridge4D
open P0EFTJanusProgramPT06ActualPhysicalThirdJetVectorDensityCovariance4D
open P0EFTJanusProgramPT06BaseDependentPhysicalHorizontalDifferential4D
open P0EFTJanusProgramPT06ActualPhysicalThirdJetTotalTangentTransition4D
open P0EFTJanusProgramPT06ActualPhysicalThirdJetCartanFrameTransport4D
open P0EFTJanusProgramPT06ActualPhysicalThirdJetJointHorizontalDifferential4D
open P0EFTJanusProgramPT06ActualPhysicalThirdJetVectorDensityJointRegularity4D
open P0EFTJanusProgramPT06ActualPhysicalThirdJetVectorDensityRegularity4D
open P0EFTJanusProgramPT06RadialJointHorizontalDifferentialBridge4D
open P0EFTJanusProgramPT06ThroatSignedDifferentialFormPiola4D
open P0EFTJanusProgramPT06ThroatAbsoluteVectorPullbackPiola4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

attribute [local instance]
  P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D.actualPhysicalValueProductNormedAddCommGroup
  P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D.actualPhysicalValueProductNormedSpace
  P0EFTJanusProgramPT06ActualPhysicalValueProductThirdJetBridge4D.actualPhysicalThirdOrderJetProductNormedAddCommGroup
  P0EFTJanusProgramPT06ActualPhysicalValueProductThirdJetBridge4D.actualPhysicalThirdOrderJetProductNormedSpace
  P0EFTJanusProgramPT06ActualPhysicalValueProductThirdJetBridge4D.actualPhysicalThirdOrderJetProductFiniteDimensional

private abbrev PhysicalThirdJet :=
  ActualPhysicalThirdOrderJetProductFiber

/-- Affine base slice tangent to a supplied non-holonomic Cartan frame. -/
def programPT06ActualPhysicalThirdJetCartanSlice
    (coordinate : ThroatCoverCoordinates) (jet : PhysicalThirdJet)
    (frame : ProgramPT06ActualPhysicalThirdJetCartanFrame4D) :
    ThroatCoverCoordinates →
      ProgramPT06ActualPhysicalThirdJetTotalCoordinateCarrier4D :=
  fun variedCoordinate =>
    (variedCoordinate,
      frame variedCoordinate + (jet - frame coordinate))

@[simp] theorem programPT06ActualPhysicalThirdJetCartanSlice_self
    (coordinate : ThroatCoverCoordinates) (jet : PhysicalThirdJet)
    (frame : ProgramPT06ActualPhysicalThirdJetCartanFrame4D) :
    programPT06ActualPhysicalThirdJetCartanSlice coordinate jet frame coordinate =
      (coordinate, jet) := by
  simp [programPT06ActualPhysicalThirdJetCartanSlice]

theorem programPT06ActualPhysicalThirdJetCartanSlice_hasFDerivAt
    (coordinate : ThroatCoverCoordinates) (jet : PhysicalThirdJet)
    (frame : ProgramPT06ActualPhysicalThirdJetCartanFrame4D) :
    HasFDerivAt
      (programPT06ActualPhysicalThirdJetCartanSlice coordinate jet frame)
      (programPT06ActualPhysicalThirdJetCartanLift frame) coordinate := by
  change HasFDerivAt
    (fun variedCoordinate : ThroatCoverCoordinates =>
      (variedCoordinate,
        frame variedCoordinate + (jet - frame coordinate)))
    ((ContinuousLinearMap.id Real ThroatCoverCoordinates).prod frame) coordinate
  exact
    (hasFDerivAt_id coordinate).prodMk
      (frame.hasFDerivAt.add_const (jet - frame coordinate))

/-- Restriction of a base-dependent density to its affine Cartan slice. -/
def programPT06ActualPhysicalThirdJetCartanSliceField
    (density : ProgramPT06BaseDependentPhysicalThirdJetVectorDensity4D)
    (coordinate : ThroatCoverCoordinates) (jet : PhysicalThirdJet)
    (frame : ProgramPT06ActualPhysicalThirdJetCartanFrame4D) :
    ThroatCoverCoordinates → ThroatCoverCoordinates :=
  fun variedCoordinate =>
    density variedCoordinate
      (programPT06ActualPhysicalValueProductThirdJetContinuousLinearEquiv.symm
        (frame variedCoordinate + (jet - frame coordinate)))

/-- The joint Cartan horizontal differential is the coordinate divergence
of the density restricted to an affine slice tangent to the frame. -/
theorem programPT06ActualPhysicalThirdJetJointHorizontalDifferential_eq_divergence_slice
    (density : ProgramPT06BaseDependentPhysicalThirdJetVectorDensity4D)
    (coordinate : ThroatCoverCoordinates) (jet : PhysicalThirdJet)
    (frame : ProgramPT06ActualPhysicalThirdJetCartanFrame4D)
    (hJoint : DifferentiableAt Real
      (fun point : ProgramPT06ActualPhysicalThirdJetTotalCoordinateCarrier4D =>
        density point.1
          (programPT06ActualPhysicalValueProductThirdJetContinuousLinearEquiv.symm
            point.2))
      (coordinate, jet)) :
    programPT06ActualPhysicalThirdJetJointHorizontalDifferential density
        coordinate jet frame =
      programPT06ThroatCoordinateDivergence
        (programPT06ActualPhysicalThirdJetCartanSliceField
          density coordinate jet frame) coordinate := by
  unfold programPT06ActualPhysicalThirdJetJointHorizontalDifferential
    programPT06ActualPhysicalThirdJetJointTotalDerivative
    programPT06ActualPhysicalThirdJetJointCartanDerivative
    programPT06ThroatCoordinateDivergence
  apply Finset.sum_congr rfl
  intro direction _
  let component : ThroatCoverCoordinates →L[Real] Real :=
    (ContinuousLinearMap.proj direction).comp
      programPT06ThroatSpatialBasis.equivFun.toContinuousLinearEquiv.toContinuousLinearMap
  let joint :=
    fun point : ProgramPT06ActualPhysicalThirdJetTotalCoordinateCarrier4D =>
      density point.1
        (programPT06ActualPhysicalValueProductThirdJetContinuousLinearEquiv.symm
          point.2)
  have hSlice :=
    programPT06ActualPhysicalThirdJetCartanSlice_hasFDerivAt coordinate jet frame
  have hJointDerivative : HasFDerivAt joint (fderiv Real joint (coordinate, jet))
      (coordinate, jet) := hJoint.hasFDerivAt
  have hSliceFieldDerivative : HasFDerivAt
      (programPT06ActualPhysicalThirdJetCartanSliceField density coordinate jet frame)
      ((fderiv Real joint (coordinate, jet)).comp
        (programPT06ActualPhysicalThirdJetCartanLift frame)) coordinate := by
    have hJointAtSlice : HasFDerivAt joint
        (fderiv Real joint (coordinate, jet))
        (programPT06ActualPhysicalThirdJetCartanSlice coordinate jet frame
          coordinate) := by
      simpa using hJointDerivative
    change HasFDerivAt
      (joint ∘ programPT06ActualPhysicalThirdJetCartanSlice coordinate jet frame)
      ((fderiv Real joint (coordinate, jet)).comp
        (programPT06ActualPhysicalThirdJetCartanLift frame)) coordinate
    exact hJointAtSlice.comp coordinate hSlice
  have hComponentDerivative : HasFDerivAt
      (programPT06ActualPhysicalThirdJetJointComponent density direction)
      (component.comp (fderiv Real joint (coordinate, jet))) (coordinate, jet) := by
    change HasFDerivAt (component ∘ joint)
      (component.comp (fderiv Real joint (coordinate, jet))) (coordinate, jet)
    exact component.hasFDerivAt.comp (coordinate, jet) hJointDerivative
  rw [hComponentDerivative.fderiv, hSliceFieldDerivative.fderiv]
  simp [component, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply]

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

private abbrev PhysicalThirdJetCore :=
  actualPhysicalThirdOrderJetProductVectorBundleCore
    period hPeriod .positiveQuarter

/-- Formal-fiber presentation of the existing joint vector-density pullback. -/
def programPT06ActualPhysicalThirdJetVectorDensityJointPullbackFormalDensity
    (firstCenter secondCenter : Base period hPeriod)
    (first second : Chart period hPeriod)
    (current : ProgramPT06ActualPhysicalThirdJetVectorDensity4D) :
    ProgramPT06BaseDependentPhysicalThirdJetVectorDensity4D :=
  fun coordinate formalJet =>
    programPT06ActualPhysicalThirdJetVectorDensityJointPullback period hPeriod
      firstCenter secondCenter first second current
      (coordinate,
        programPT06ActualPhysicalValueProductThirdJetContinuousLinearEquiv
          formalJet)

/-- Value of the total J3 coordinate change at a genuine overlap point. -/
theorem programPT06ActualPhysicalThirdJetTotalCoordChange_at
    (firstCenter secondCenter base : Base period hPeriod)
    (hFirst : base ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (first second : Chart period hPeriod)
    (jet : PhysicalThirdJet) :
    programPT06ActualPhysicalThirdJetTotalCoordChange period hPeriod
        firstCenter secondCenter first second
        (extChartAt throatCoverModelWithCorners firstCenter base, jet) =
      (extChartAt throatCoverModelWithCorners secondCenter base,
        (PhysicalThirdJetCore period hPeriod).coordChange first second base jet) := by
  unfold programPT06ActualPhysicalThirdJetTotalCoordChange
  rw [throatGaugeBaseChartTransition_apply_current period hPeriod
    firstCenter secondCenter base hFirst]
  rw [programPT06ActualPhysicalThirdJetFiberCoordChangeInBaseChart_at
    period hPeriod firstCenter base hFirst first second]

/-- Target-coordinate curve obtained by transporting a source Cartan slice
through the actual total-space transition. -/
def programPT06ActualPhysicalThirdJetCartanTransportCurve
    (firstCenter secondCenter : Base period hPeriod)
    (first second : Chart period hPeriod)
    (coordinate : ThroatCoverCoordinates) (jet : PhysicalThirdJet)
    (frame : ProgramPT06ActualPhysicalThirdJetCartanFrame4D) :
    ThroatCoverCoordinates →
      ProgramPT06ActualPhysicalThirdJetTotalCoordinateCarrier4D :=
  fun targetCoordinate =>
    programPT06ActualPhysicalThirdJetTotalCoordChange period hPeriod
      firstCenter secondCenter first second
      (programPT06ActualPhysicalThirdJetCartanSlice coordinate jet frame
        (throatGaugeBaseChartTransition period hPeriod
          secondCenter firstCenter targetCoordinate))

/-- The transported curve is tangent to the Cartan lift of the transported
frame.  This is the local Cartan content of the total tangent transition. -/
theorem programPT06ActualPhysicalThirdJetCartanTransportCurve_hasFDerivAt
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
    (frame : ProgramPT06ActualPhysicalThirdJetCartanFrame4D) :
    HasFDerivAt
      (programPT06ActualPhysicalThirdJetCartanTransportCurve period hPeriod
        firstCenter secondCenter first second
        (extChartAt throatCoverModelWithCorners firstCenter base) jet frame)
      (programPT06ActualPhysicalThirdJetCartanLift
        (programPT06ActualPhysicalThirdJetCartanFrameTransport period hPeriod
          firstCenter secondCenter base hFirst hSecond first second hBase jet
          frame))
      (extChartAt throatCoverModelWithCorners secondCenter base) := by
  let sourceCoordinate :=
    extChartAt throatCoverModelWithCorners firstCenter base
  let targetCoordinate :=
    extChartAt throatCoverModelWithCorners secondCenter base
  let reverse :=
    throatGaugeBaseChartTransition period hPeriod secondCenter firstCenter
  let transition :=
    programPT06ActualPhysicalThirdJetTotalCoordChange period hPeriod
      firstCenter secondCenter first second
  let sourceSlice :=
    programPT06ActualPhysicalThirdJetCartanSlice sourceCoordinate jet frame
  let targetFrame :=
    programPT06ActualPhysicalThirdJetCartanFrameTransport period hPeriod
      firstCenter secondCenter base hFirst hSecond first second hBase jet frame
  have hReverseValue : reverse targetCoordinate = sourceCoordinate := by
    dsimp only [reverse, targetCoordinate, sourceCoordinate]
    exact throatGaugeBaseChartTransition_apply_current period hPeriod
      secondCenter firstCenter base hSecond
  have hReverse : HasFDerivAt reverse
      (fderiv Real reverse targetCoordinate) targetCoordinate :=
    (throatGaugeBaseChartTransition_contDiffAt_two period hPeriod
      secondCenter firstCenter base hSecond hFirst
      |>.differentiableAt (by norm_num)).hasFDerivAt
  have hSliceAtReverse : HasFDerivAt sourceSlice
      (programPT06ActualPhysicalThirdJetCartanLift frame)
      (reverse targetCoordinate) := by
    rw [hReverseValue]
    exact programPT06ActualPhysicalThirdJetCartanSlice_hasFDerivAt
      sourceCoordinate jet frame
  have hSliceReverse := hSliceAtReverse.comp targetCoordinate hReverse
  have hSliceReverseValue :
      sourceSlice (reverse targetCoordinate) = (sourceCoordinate, jet) := by
    rw [hReverseValue]
    exact programPT06ActualPhysicalThirdJetCartanSlice_self
      sourceCoordinate jet frame
  have hTransition : HasFDerivAt transition
      (fderiv Real transition (sourceCoordinate, jet))
      (sourceCoordinate, jet) :=
    (programPT06ActualPhysicalThirdJetTotalCoordChange_differentiableAt
      period hPeriod firstCenter secondCenter base hFirst hSecond first second
      hBase jet).hasFDerivAt
  have hTransitionAtSlice : HasFDerivAt transition
      (fderiv Real transition (sourceCoordinate, jet))
      (sourceSlice (reverse targetCoordinate)) := by
    rw [hSliceReverseValue]
    exact hTransition
  have hRaw := hTransitionAtSlice.comp targetCoordinate hSliceReverse
  have hDerivative :
      (fderiv Real transition (sourceCoordinate, jet)).comp
          ((programPT06ActualPhysicalThirdJetCartanLift frame).comp
            (fderiv Real reverse targetCoordinate)) =
        programPT06ActualPhysicalThirdJetCartanLift targetFrame := by
    apply ContinuousLinearMap.ext
    intro direction
    simp only [ContinuousLinearMap.comp_apply]
    rw [← throatGaugeBaseChartTransitionJacobianEquivAt_symm_apply
      period hPeriod firstCenter secondCenter base hFirst hSecond direction]
    simpa only [LinearEquiv.apply_symm_apply] using
      (programPT06ActualPhysicalThirdJetCartanFrameTransport_intertwines
        period hPeriod firstCenter secondCenter base hFirst hSecond first second
        hBase jet frame
        ((throatGaugeBaseChartTransitionJacobianEquivAt period hPeriod
          firstCenter secondCenter base hFirst hSecond).symm direction))
  change HasFDerivAt
    (fun target => transition (sourceSlice (reverse target)))
    (programPT06ActualPhysicalThirdJetCartanLift targetFrame) targetCoordinate
  exact hRaw.congr_fderiv hDerivative

/-- A target-coordinate vector field obtained by evaluating a physical J3
current along the transported Cartan curve. -/
def programPT06ActualPhysicalThirdJetCartanTransportedTargetField
    (firstCenter secondCenter : Base period hPeriod)
    (first second : Chart period hPeriod)
    (coordinate : ThroatCoverCoordinates) (jet : PhysicalThirdJet)
    (frame : ProgramPT06ActualPhysicalThirdJetCartanFrame4D)
    (current : ProgramPT06ActualPhysicalThirdJetVectorDensity4D) :
    ThroatCoverCoordinates → ThroatCoverCoordinates :=
  fun targetCoordinate =>
    current
      ((programPT06ActualPhysicalThirdJetCartanTransportCurve period hPeriod
        firstCenter secondCenter first second coordinate jet frame
        targetCoordinate).2)

theorem
    programPT06ActualPhysicalThirdJetCartanTransportedTargetField_differentiableAt
    (firstCenter secondCenter base : Base period hPeriod)
    (hFirst : base ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : base ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source)
    (first second : Chart period hPeriod)
    (hBase : base ∈
      (PhysicalThirdJetCore period hPeriod).baseSet first ∩
        (PhysicalThirdJetCore period hPeriod).baseSet second)
    (current : ProgramPT06ActualPhysicalThirdJetVectorDensity4D)
    (hCurrent : ContDiff Real ∞ current)
    (jet : PhysicalThirdJet)
    (frame : ProgramPT06ActualPhysicalThirdJetCartanFrame4D) :
    DifferentiableAt Real
      (programPT06ActualPhysicalThirdJetCartanTransportedTargetField
        period hPeriod firstCenter secondCenter first second
        (extChartAt throatCoverModelWithCorners firstCenter base) jet frame
        current)
      (extChartAt throatCoverModelWithCorners secondCenter base) := by
  let sourceCoordinate :=
    extChartAt throatCoverModelWithCorners firstCenter base
  let targetCoordinate :=
    extChartAt throatCoverModelWithCorners secondCenter base
  let targetJet :=
    (PhysicalThirdJetCore period hPeriod).coordChange first second base jet
  let curve :=
    programPT06ActualPhysicalThirdJetCartanTransportCurve period hPeriod
      firstCenter secondCenter first second sourceCoordinate jet frame
  let currentOnTotal :=
    fun point : ProgramPT06ActualPhysicalThirdJetTotalCoordinateCarrier4D =>
      current point.2
  have hCurve :=
    programPT06ActualPhysicalThirdJetCartanTransportCurve_hasFDerivAt
      period hPeriod firstCenter secondCenter base hFirst hSecond first second
      hBase jet frame
  have hCurveValue : curve targetCoordinate = (targetCoordinate, targetJet) := by
    dsimp only [curve, targetCoordinate, targetJet, sourceCoordinate,
      programPT06ActualPhysicalThirdJetCartanTransportCurve]
    rw [throatGaugeBaseChartTransition_apply_current period hPeriod
      secondCenter firstCenter base hSecond]
    rw [programPT06ActualPhysicalThirdJetCartanSlice_self]
    exact programPT06ActualPhysicalThirdJetTotalCoordChange_at period hPeriod
      firstCenter secondCenter base hFirst first second jet
  have hCurrentOnTotal : DifferentiableAt Real currentOnTotal
      (targetCoordinate, targetJet) :=
    (hCurrent.contDiffAt.comp (targetCoordinate, targetJet) contDiffAt_snd)
      |>.differentiableAt (by simp)
  have hCurrentAtCurve : DifferentiableAt Real currentOnTotal
      (curve targetCoordinate) := by
    rw [hCurveValue]
    exact hCurrentOnTotal
  change DifferentiableAt Real (currentOnTotal ∘ curve) targetCoordinate
  exact hCurrentAtCurve.comp targetCoordinate hCurve.differentiableAt

/-- The divergence of the transported target field is the joint horizontal
differential in the transported Cartan frame. -/
theorem
    programPT06ActualPhysicalThirdJetCartanTransportedTargetField_divergence
    (firstCenter secondCenter base : Base period hPeriod)
    (hFirst : base ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : base ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source)
    (first second : Chart period hPeriod)
    (hBase : base ∈
      (PhysicalThirdJetCore period hPeriod).baseSet first ∩
        (PhysicalThirdJetCore period hPeriod).baseSet second)
    (current : ProgramPT06ActualPhysicalThirdJetVectorDensity4D)
    (hCurrent : ContDiff Real ∞ current)
    (jet : PhysicalThirdJet)
    (frame : ProgramPT06ActualPhysicalThirdJetCartanFrame4D) :
    programPT06ThroatCoordinateDivergence
        (programPT06ActualPhysicalThirdJetCartanTransportedTargetField
          period hPeriod firstCenter secondCenter first second
          (extChartAt throatCoverModelWithCorners firstCenter base) jet frame
          current)
        (extChartAt throatCoverModelWithCorners secondCenter base) =
      programPT06ActualPhysicalThirdJetJointHorizontalDifferential
        (programPT06BaseDependentPhysicalVectorDensityOfAutonomous current)
        (extChartAt throatCoverModelWithCorners secondCenter base)
        ((PhysicalThirdJetCore period hPeriod).coordChange first second base jet)
        (programPT06ActualPhysicalThirdJetCartanFrameTransport period hPeriod
          firstCenter secondCenter base hFirst hSecond first second hBase jet
          frame) := by
  let sourceCoordinate :=
    extChartAt throatCoverModelWithCorners firstCenter base
  let targetCoordinate :=
    extChartAt throatCoverModelWithCorners secondCenter base
  let targetJet :=
    (PhysicalThirdJetCore period hPeriod).coordChange first second base jet
  let targetFrame :=
    programPT06ActualPhysicalThirdJetCartanFrameTransport period hPeriod
      firstCenter secondCenter base hFirst hSecond first second hBase jet frame
  let curve :=
    programPT06ActualPhysicalThirdJetCartanTransportCurve period hPeriod
      firstCenter secondCenter first second sourceCoordinate jet frame
  let currentOnTotal :=
    fun point : ProgramPT06ActualPhysicalThirdJetTotalCoordinateCarrier4D =>
      current point.2
  have hCurve :=
    programPT06ActualPhysicalThirdJetCartanTransportCurve_hasFDerivAt
      period hPeriod firstCenter secondCenter base hFirst hSecond first second
      hBase jet frame
  have hCurveValue : curve targetCoordinate = (targetCoordinate, targetJet) := by
    dsimp only [curve, targetCoordinate, targetJet, sourceCoordinate,
      programPT06ActualPhysicalThirdJetCartanTransportCurve]
    rw [throatGaugeBaseChartTransition_apply_current period hPeriod
      secondCenter firstCenter base hSecond]
    rw [programPT06ActualPhysicalThirdJetCartanSlice_self]
    exact programPT06ActualPhysicalThirdJetTotalCoordChange_at period hPeriod
      firstCenter secondCenter base hFirst first second jet
  have hCurrentOnTotal : DifferentiableAt Real currentOnTotal
      (targetCoordinate, targetJet) := by
    exact (hCurrent.contDiffAt.comp (targetCoordinate, targetJet)
      contDiffAt_snd).differentiableAt (by simp)
  have hCurrentAtCurve : HasFDerivAt currentOnTotal
      (fderiv Real currentOnTotal (targetCoordinate, targetJet))
      (curve targetCoordinate) := by
    rw [hCurveValue]
    exact hCurrentOnTotal.hasFDerivAt
  have hTargetFieldDerivative : HasFDerivAt
      (programPT06ActualPhysicalThirdJetCartanTransportedTargetField
        period hPeriod firstCenter secondCenter first second sourceCoordinate
        jet frame current)
      ((fderiv Real currentOnTotal (targetCoordinate, targetJet)).comp
        (programPT06ActualPhysicalThirdJetCartanLift targetFrame))
      targetCoordinate := by
    change HasFDerivAt (currentOnTotal ∘ curve)
      ((fderiv Real currentOnTotal (targetCoordinate, targetJet)).comp
        (programPT06ActualPhysicalThirdJetCartanLift targetFrame))
      targetCoordinate
    exact hCurrentAtCurve.comp targetCoordinate hCurve
  have hTargetSlice :=
    programPT06ActualPhysicalThirdJetCartanSlice_hasFDerivAt
      targetCoordinate targetJet targetFrame
  have hCurrentAtTargetSlice : HasFDerivAt currentOnTotal
      (fderiv Real currentOnTotal (targetCoordinate, targetJet))
      (programPT06ActualPhysicalThirdJetCartanSlice
        targetCoordinate targetJet targetFrame targetCoordinate) := by
    rw [programPT06ActualPhysicalThirdJetCartanSlice_self]
    exact hCurrentOnTotal.hasFDerivAt
  have hTargetSliceField :
      programPT06ActualPhysicalThirdJetCartanSliceField
          (programPT06BaseDependentPhysicalVectorDensityOfAutonomous current)
          targetCoordinate targetJet targetFrame =
        currentOnTotal ∘ programPT06ActualPhysicalThirdJetCartanSlice
          targetCoordinate targetJet targetFrame := by
    funext variedCoordinate
    simp [programPT06ActualPhysicalThirdJetCartanSliceField,
      programPT06ActualPhysicalThirdJetCartanSlice,
      programPT06BaseDependentPhysicalVectorDensityOfAutonomous,
      currentOnTotal,
      programPT06ActualPhysicalValueProductThirdJetContinuousLinearEquiv]
  have hTargetSliceFieldDerivative : HasFDerivAt
      (programPT06ActualPhysicalThirdJetCartanSliceField
        (programPT06BaseDependentPhysicalVectorDensityOfAutonomous current)
        targetCoordinate targetJet targetFrame)
      ((fderiv Real currentOnTotal (targetCoordinate, targetJet)).comp
        (programPT06ActualPhysicalThirdJetCartanLift targetFrame))
      targetCoordinate := by
    rw [hTargetSliceField]
    exact hCurrentAtTargetSlice.comp targetCoordinate hTargetSlice
  have hFDeriv :
      fderiv Real
          (programPT06ActualPhysicalThirdJetCartanTransportedTargetField
            period hPeriod firstCenter secondCenter first second sourceCoordinate
            jet frame current) targetCoordinate =
        fderiv Real
          (programPT06ActualPhysicalThirdJetCartanSliceField
            (programPT06BaseDependentPhysicalVectorDensityOfAutonomous current)
            targetCoordinate targetJet targetFrame) targetCoordinate :=
    hTargetFieldDerivative.fderiv.trans hTargetSliceFieldDerivative.fderiv.symm
  have hAutonomousJoint : DifferentiableAt Real
      (fun point : ProgramPT06ActualPhysicalThirdJetTotalCoordinateCarrier4D =>
        programPT06BaseDependentPhysicalVectorDensityOfAutonomous current
          point.1
          (programPT06ActualPhysicalValueProductThirdJetContinuousLinearEquiv.symm
            point.2))
      (targetCoordinate, targetJet) := by
    simpa [programPT06BaseDependentPhysicalVectorDensityOfAutonomous,
      currentOnTotal,
      programPT06ActualPhysicalValueProductThirdJetContinuousLinearEquiv] using
      hCurrentOnTotal
  calc
    _ = programPT06ThroatCoordinateDivergence
        (programPT06ActualPhysicalThirdJetCartanSliceField
          (programPT06BaseDependentPhysicalVectorDensityOfAutonomous current)
          targetCoordinate targetJet targetFrame) targetCoordinate := by
      unfold programPT06ThroatCoordinateDivergence
      rw [hFDeriv]
    _ = _ :=
      (programPT06ActualPhysicalThirdJetJointHorizontalDifferential_eq_divergence_slice
        (programPT06BaseDependentPhysicalVectorDensityOfAutonomous current)
        targetCoordinate targetJet targetFrame hAutonomousJoint).symm

/-- Local absolute Piola naturality for the joint Cartan horizontal
differential on a genuine physical J3 overlap. -/
theorem
    programPT06ActualPhysicalThirdJetVectorDensityJointPullbackFormalDensity_horizontalDifferential
    (firstCenter secondCenter base : Base period hPeriod)
    (hFirst : base ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : base ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source)
    (first second : Chart period hPeriod)
    (hBase : base ∈
      (PhysicalThirdJetCore period hPeriod).baseSet first ∩
        (PhysicalThirdJetCore period hPeriod).baseSet second)
    (current : ProgramPT06ActualPhysicalThirdJetVectorDensity4D)
    (hCurrent : ContDiff Real ∞ current)
    (jet : PhysicalThirdJet)
    (frame : ProgramPT06ActualPhysicalThirdJetCartanFrame4D) :
    programPT06ActualPhysicalThirdJetJointHorizontalDifferential
        (programPT06ActualPhysicalThirdJetVectorDensityJointPullbackFormalDensity
          period hPeriod firstCenter secondCenter first second current)
        (extChartAt throatCoverModelWithCorners firstCenter base) jet frame =
      programPT06ActualThroatBaseJacobianDensityInCoordinates period hPeriod
          firstCenter secondCenter
          (extChartAt throatCoverModelWithCorners firstCenter base) *
        programPT06ActualPhysicalThirdJetJointHorizontalDifferential
          (programPT06BaseDependentPhysicalVectorDensityOfAutonomous current)
          (extChartAt throatCoverModelWithCorners secondCenter base)
          ((PhysicalThirdJetCore period hPeriod).coordChange first second base jet)
          (programPT06ActualPhysicalThirdJetCartanFrameTransport period hPeriod
            firstCenter secondCenter base hFirst hSecond first second hBase jet
            frame) := by
  let sourceCoordinate :=
    extChartAt throatCoverModelWithCorners firstCenter base
  let targetCoordinate :=
    extChartAt throatCoverModelWithCorners secondCenter base
  let forward :=
    throatGaugeBaseChartTransition period hPeriod firstCenter secondCenter
  let reverse :=
    throatGaugeBaseChartTransition period hPeriod secondCenter firstCenter
  let formalPullback :=
    programPT06ActualPhysicalThirdJetVectorDensityJointPullbackFormalDensity
      period hPeriod firstCenter secondCenter first second current
  let sourceSliceField :=
    programPT06ActualPhysicalThirdJetCartanSliceField formalPullback
      sourceCoordinate jet frame
  let targetField :=
    programPT06ActualPhysicalThirdJetCartanTransportedTargetField period hPeriod
      firstCenter secondCenter first second sourceCoordinate jet frame current
  have hFormalJoint :
      (fun point : ProgramPT06ActualPhysicalThirdJetTotalCoordinateCarrier4D =>
        formalPullback point.1
          (programPT06ActualPhysicalValueProductThirdJetContinuousLinearEquiv.symm
            point.2)) =
        programPT06ActualPhysicalThirdJetVectorDensityJointPullback period hPeriod
          firstCenter secondCenter first second current := by
    funext point
    simp [formalPullback,
      programPT06ActualPhysicalThirdJetVectorDensityJointPullbackFormalDensity,
      programPT06ActualPhysicalValueProductThirdJetContinuousLinearEquiv]
  have hSourceJoint : DifferentiableAt Real
      (fun point : ProgramPT06ActualPhysicalThirdJetTotalCoordinateCarrier4D =>
        formalPullback point.1
          (programPT06ActualPhysicalValueProductThirdJetContinuousLinearEquiv.symm
            point.2))
      (sourceCoordinate, jet) := by
    rw [hFormalJoint]
    exact
      (programPT06ActualPhysicalThirdJetVectorDensityJointPullback_contDiffAt
        period hPeriod firstCenter secondCenter base hFirst hSecond first second
        hBase current hCurrent jet).differentiableAt (by simp)
  have hSourceDivergence :=
    programPT06ActualPhysicalThirdJetJointHorizontalDifferential_eq_divergence_slice
      formalPullback sourceCoordinate jet frame hSourceJoint
  have hInverse :=
    throatGaugeBaseChartTransition_inverse_comp_eventuallyEq period hPeriod
      firstCenter secondCenter base hFirst hSecond
  have hPullbackGerm : sourceSliceField =ᶠ[nhds sourceCoordinate]
      programPT06ThroatAbsoluteVectorPullback forward reverse targetField := by
    filter_upwards [hInverse] with nearby hNearby
    have hNearbyInverse : reverse (forward nearby) = nearby := by
      simpa only [Function.comp_apply, id_eq] using hNearby
    dsimp only [sourceSliceField, formalPullback, sourceCoordinate, forward,
      reverse, targetField]
    unfold programPT06ActualPhysicalThirdJetCartanSliceField
      programPT06ActualPhysicalThirdJetVectorDensityJointPullbackFormalDensity
    simp only [
      programPT06ActualPhysicalValueProductThirdJetContinuousLinearEquiv,
      ContinuousLinearEquiv.apply_symm_apply]
    rw [programPT06ActualThroatAbsoluteVectorPullback_apply]
    unfold programPT06ActualPhysicalThirdJetVectorDensityJointPullback
      programPT06ActualPhysicalThirdJetCartanTransportedTargetField
      programPT06ActualPhysicalThirdJetCartanTransportCurve
      programPT06ActualPhysicalThirdJetTotalCoordChange
      programPT06ActualPhysicalThirdJetCartanSlice
    dsimp only [reverse, forward] at hNearbyInverse
    rw [hNearbyInverse]
  have hTargetDifferentiable :=
    programPT06ActualPhysicalThirdJetCartanTransportedTargetField_differentiableAt
      period hPeriod firstCenter secondCenter base hFirst hSecond first second
      hBase current hCurrent jet frame
  have hTargetDivergence :=
    programPT06ActualPhysicalThirdJetCartanTransportedTargetField_divergence
      period hPeriod firstCenter secondCenter base hFirst hSecond first second
      hBase current hCurrent jet frame
  calc
    _ = programPT06ThroatCoordinateDivergence sourceSliceField
        sourceCoordinate := hSourceDivergence
    _ = programPT06ThroatCoordinateDivergence
        (programPT06ThroatAbsoluteVectorPullback forward reverse targetField)
        sourceCoordinate :=
      programPT06ThroatCoordinateDivergence_congr hPullbackGerm
    _ = |LinearMap.det (fderiv Real forward sourceCoordinate).toLinearMap| *
        programPT06ThroatCoordinateDivergence targetField targetCoordinate :=
      programPT06ActualThroatAbsoluteVectorPullback_divergence_eq_abs_det_mul
        period hPeriod firstCenter secondCenter base hFirst hSecond targetField
        hTargetDifferentiable
    _ = _ := by
      rw [hTargetDivergence]
      rfl

/-- The radial Cartan current satisfies the local absolute Piola law with no
additional regularity hypothesis. -/
theorem
    programPT06T02DegreeFourRadialCartanJointPullbackFormalDensity_horizontalDifferential
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (referenceCenter chartCenter base : Base period hPeriod)
    (hReferenceCenter : base ∈
      (extChartAt throatCoverModelWithCorners referenceCenter).source)
    (hChartCenter : base ∈
      (extChartAt throatCoverModelWithCorners chartCenter).source)
    (reference chart : Chart period hPeriod)
    (hBase : base ∈
      (PhysicalThirdJetCore period hPeriod).baseSet chart ∩
        (PhysicalThirdJetCore period hPeriod).baseSet reference)
    (jet : PhysicalThirdJet)
    (frame : ProgramPT06ActualPhysicalThirdJetCartanFrame4D) :
    programPT06ActualPhysicalThirdJetJointHorizontalDifferential
        (programPT06T02DegreeFourRadialCartanJointPullbackFormalDensity
          period hPeriod functional referenceCenter chartCenter reference chart)
        (extChartAt throatCoverModelWithCorners chartCenter base) jet frame =
      programPT06ActualThroatBaseJacobianDensityInCoordinates period hPeriod
          chartCenter referenceCenter
          (extChartAt throatCoverModelWithCorners chartCenter base) *
        programPT06ActualPhysicalThirdJetJointHorizontalDifferential
          (programPT06BaseDependentPhysicalVectorDensityOfAutonomous
            (programPT06T02DegreeFourRadialCartanActualPhysicalThirdJetVectorDensity
              period hPeriod functional))
          (extChartAt throatCoverModelWithCorners referenceCenter base)
          ((PhysicalThirdJetCore period hPeriod).coordChange chart reference base
            jet)
          (programPT06ActualPhysicalThirdJetCartanFrameTransport period hPeriod
            chartCenter referenceCenter base hChartCenter hReferenceCenter
            chart reference hBase jet frame) := by
  have hFormal :
      programPT06T02DegreeFourRadialCartanJointPullbackFormalDensity
          period hPeriod functional referenceCenter chartCenter reference chart =
        programPT06ActualPhysicalThirdJetVectorDensityJointPullbackFormalDensity
          period hPeriod chartCenter referenceCenter chart reference
          (programPT06T02DegreeFourRadialCartanActualPhysicalThirdJetVectorDensity
            period hPeriod functional) := by
    funext coordinate formalJet
    simp only [
      programPT06T02DegreeFourRadialCartanJointPullbackFormalDensity,
      programPT06ActualPhysicalThirdJetVectorDensityJointPullbackFormalDensity,
      programPT06ActualPhysicalValueProductThirdJetContinuousLinearEquiv]
  rw [hFormal]
  exact
    programPT06ActualPhysicalThirdJetVectorDensityJointPullbackFormalDensity_horizontalDifferential
      period hPeriod chartCenter referenceCenter base hChartCenter
      hReferenceCenter chart reference hBase
      (programPT06T02DegreeFourRadialCartanActualPhysicalThirdJetVectorDensity
        period hPeriod functional)
      (programPT06T02DegreeFourRadialCartanActualPhysicalThirdJetVectorDensity_contDiff
        period hPeriod functional)
      jet frame

end
end P0EFTJanusProgramPT06ActualPhysicalThirdJetCartanPiolaNaturality4D
end JanusFormal
