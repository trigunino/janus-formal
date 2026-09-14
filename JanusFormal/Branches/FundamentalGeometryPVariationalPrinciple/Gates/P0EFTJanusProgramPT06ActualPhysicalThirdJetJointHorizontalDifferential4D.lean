import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06ActualPhysicalThirdJetCartanFrameTransport4D

/-!
# Joint non-holonomic horizontal differential on physical J3

A base-dependent vector density is read as a joint function on the local
physical J3 total-space carrier.  Its horizontal differential differentiates
each component along a supplied non-holonomic Cartan frame.

For the frame supplied by a formal physical J4, joint differentiability gives
exactly the split base-plus-jet differential of Gate 1020.  A scalar chain-rule
lemma records the naturality supplied by the Gate-1023 Cartan intertwining.
No vector-density Piola identity or integrated Stokes statement is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06ActualPhysicalThirdJetJointHorizontalDifferential4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000

noncomputable section

open Set
open scoped BigOperators Manifold ContDiff RealInnerProductSpace Topology
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
open P0EFTJanusProgramPT06ActualPhysicalThirdJetCartanFrameTransport4D

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

private abbrev PhysicalThirdJet :=
  ActualPhysicalThirdOrderJetProductFiber

/-! ## Joint differential -/

/-- A component of a Gate-1020 density, read jointly in actual physical J3
total-space coordinates. -/
def programPT06ActualPhysicalThirdJetJointComponent
    (density : ProgramPT06BaseDependentPhysicalThirdJetVectorDensity4D)
    (direction : Fin 3) :
    ProgramPT06ActualPhysicalThirdJetTotalCoordinateCarrier4D → Real :=
  fun point =>
    programPT06BaseDependentPhysicalVectorDensityComponent density direction
      point.1
      (programPT06ActualPhysicalValueProductThirdJetContinuousLinearEquiv.symm
        point.2)

/-- Directional derivative of a scalar on the local physical J3 total space
along a non-holonomic Cartan lift. -/
def programPT06ActualPhysicalThirdJetJointCartanDerivative
    (scalar : ProgramPT06ActualPhysicalThirdJetTotalCoordinateCarrier4D → Real)
    (point : ProgramPT06ActualPhysicalThirdJetTotalCoordinateCarrier4D)
    (frame : ProgramPT06ActualPhysicalThirdJetCartanFrame4D)
    (direction : ThroatCoverCoordinates) : Real :=
  fderiv Real scalar point
    (programPT06ActualPhysicalThirdJetCartanLift frame direction)

/-- One component derivative along the corresponding spatial Cartan
direction. -/
def programPT06ActualPhysicalThirdJetJointTotalDerivative
    (direction : Fin 3)
    (density : ProgramPT06BaseDependentPhysicalThirdJetVectorDensity4D)
    (coordinate : ThroatCoverCoordinates) (jet : PhysicalThirdJet)
    (frame : ProgramPT06ActualPhysicalThirdJetCartanFrame4D) : Real :=
  programPT06ActualPhysicalThirdJetJointCartanDerivative
    (programPT06ActualPhysicalThirdJetJointComponent density direction)
    (coordinate, jet) frame (programPT06ThroatSpatialBasis direction)

/-- Sum of the three joint component derivatives along a supplied Cartan
frame. -/
def programPT06ActualPhysicalThirdJetJointHorizontalDifferential
    (density : ProgramPT06BaseDependentPhysicalThirdJetVectorDensity4D)
    (coordinate : ThroatCoverCoordinates) (jet : PhysicalThirdJet)
    (frame : ProgramPT06ActualPhysicalThirdJetCartanFrame4D) : Real :=
  ∑ direction : Fin 3,
    programPT06ActualPhysicalThirdJetJointTotalDerivative direction density
      coordinate jet frame

/-! ## Exact specialization to Gate 1020 -/

private theorem fderiv_joint_equiv_eq_partial_add
    {E G : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E]
    [NormedAddCommGroup G] [NormedSpace Real G]
    (equivalence : E ≃L[Real] G)
    (action : ThroatCoverCoordinates → E → Real)
    (coordinate : ThroatCoverCoordinates) (jet : E)
    (hJoint : DifferentiableAt Real
      (fun point : ThroatCoverCoordinates × G =>
        action point.1 (equivalence.symm point.2))
      (coordinate, equivalence jet))
    (baseDirection : ThroatCoverCoordinates) (jetDirection : E) :
    fderiv Real
        (fun point : ThroatCoverCoordinates × G =>
          action point.1 (equivalence.symm point.2))
        (coordinate, equivalence jet)
        (baseDirection, equivalence jetDirection) =
      fderiv Real (fun variedCoordinate => action variedCoordinate jet)
          coordinate baseDirection +
        fderiv Real (action coordinate) jet jetDirection := by
  let joint := fun point : ThroatCoverCoordinates × G =>
    action point.1 (equivalence.symm point.2)
  let derivative := fderiv Real joint (coordinate, equivalence jet)
  have hJoint' : HasFDerivAt joint derivative
      (coordinate, equivalence jet) :=
    hJoint.hasFDerivAt
  have hBase : HasFDerivAt
      (fun variedCoordinate => action variedCoordinate jet)
      (derivative.comp
        (ContinuousLinearMap.inl Real ThroatCoverCoordinates G)) coordinate := by
    simpa only [Function.comp_def, joint,
      ContinuousLinearEquiv.symm_apply_apply] using
      hJoint'.comp coordinate
        (hasFDerivAt_prodMk_left (𝕜 := Real) coordinate (equivalence jet))
  have hFiberActual : HasFDerivAt
      (fun actualJet : G => action coordinate (equivalence.symm actualJet))
      (derivative.comp
        (ContinuousLinearMap.inr Real ThroatCoverCoordinates G))
      (equivalence jet) := by
    simpa only [Function.comp_def, joint] using
      hJoint'.comp (equivalence jet)
        (hasFDerivAt_prodMk_right coordinate (equivalence jet))
  have hFiber : HasFDerivAt (action coordinate)
      ((derivative.comp
        (ContinuousLinearMap.inr Real ThroatCoverCoordinates G)).comp
          equivalence.toContinuousLinearMap) jet := by
    simpa only [Function.comp_def,
      ContinuousLinearEquiv.symm_apply_apply] using
      hFiberActual.comp jet equivalence.hasFDerivAt
  rw [hBase.fderiv, hFiber.fderiv]
  change derivative (baseDirection, equivalence jetDirection) =
    derivative (baseDirection, 0) +
      derivative (0, equivalence jetDirection)
  rw [show (baseDirection, equivalence jetDirection) =
      (baseDirection, (0 : G)) +
        ((0 : ThroatCoverCoordinates), equivalence jetDirection) by
      ext <;> simp,
    map_add]

/-- On the Cartan state supplied by a formal physical J4, one joint component
derivative is exactly Gate 1020's split total derivative. -/
theorem
    programPT06ActualPhysicalThirdJetJointTotalDerivative_formalFourthJet
    (density : ProgramPT06BaseDependentPhysicalThirdJetVectorDensity4D)
    (coordinate : ThroatCoverCoordinates)
    (jet : ProgramPT06ActualPhysicalFormalFourthJet4D)
    (direction : Fin 3)
    (hJoint : DifferentiableAt Real
      (programPT06ActualPhysicalThirdJetJointComponent density direction)
      (coordinate,
        programPT06ActualPhysicalFormalFourthJetBaseThirdJet jet)) :
    programPT06ActualPhysicalThirdJetJointTotalDerivative direction density
        coordinate
        (programPT06ActualPhysicalFormalFourthJetBaseThirdJet jet)
        (programPT06ActualPhysicalFormalFourthJetCartanFrame jet) =
      programPT06BaseDependentPhysicalTotalDerivative direction density
        coordinate jet := by
  let thirdJet : ProgramPT06ActualPhysicalFormalThirdJet4D :=
    truncateThroatSpatialMultiindexJet (by omega : 3 ≤ 4) jet
  change DifferentiableAt Real
    (fun point : ThroatCoverCoordinates × PhysicalThirdJet =>
      programPT06BaseDependentPhysicalVectorDensityComponent density direction
        point.1
        (programPT06ActualPhysicalValueProductThirdJetContinuousLinearEquiv.symm
          point.2))
    (coordinate,
      programPT06ActualPhysicalValueProductThirdJetContinuousLinearEquiv
        thirdJet) at hJoint
  have hSplit := fderiv_joint_equiv_eq_partial_add
    programPT06ActualPhysicalValueProductThirdJetContinuousLinearEquiv
    (programPT06BaseDependentPhysicalVectorDensityComponent density direction)
    coordinate thirdJet hJoint
    (programPT06ThroatSpatialBasis direction)
    (throatSpatialTotalDerivative direction jet)
  unfold programPT06ActualPhysicalThirdJetJointTotalDerivative
    programPT06ActualPhysicalThirdJetJointCartanDerivative
  rw [programPT06ActualPhysicalFormalFourthJetCartanLift_basis]
  unfold programPT06ActualPhysicalThirdJetJointComponent
    programPT06ActualPhysicalFormalFourthJetBaseThirdJet
    programPT06BaseDependentPhysicalTotalDerivative
  simpa [thirdJet,
    programPT06ActualPhysicalValueProductThirdJetContinuousLinearEquiv,
    programPT06BaseDependentPhysicalCartanDirection] using hSplit

/-- Under joint differentiability of all three components, the joint
non-holonomic differential on a formal-J4 Cartan state is exactly Gate 1020. -/
theorem
    programPT06ActualPhysicalThirdJetJointHorizontalDifferential_formalFourthJet
    (density : ProgramPT06BaseDependentPhysicalThirdJetVectorDensity4D)
    (coordinate : ThroatCoverCoordinates)
    (jet : ProgramPT06ActualPhysicalFormalFourthJet4D)
    (hJoint : ∀ direction : Fin 3, DifferentiableAt Real
      (programPT06ActualPhysicalThirdJetJointComponent density direction)
      (coordinate,
        programPT06ActualPhysicalFormalFourthJetBaseThirdJet jet)) :
    programPT06ActualPhysicalThirdJetJointHorizontalDifferential density
        coordinate
        (programPT06ActualPhysicalFormalFourthJetBaseThirdJet jet)
        (programPT06ActualPhysicalFormalFourthJetCartanFrame jet) =
      programPT06BaseDependentPhysicalHorizontalDifferential density
        coordinate jet := by
  unfold programPT06ActualPhysicalThirdJetJointHorizontalDifferential
    programPT06BaseDependentPhysicalHorizontalDifferential
  apply Finset.sum_congr rfl
  intro direction _
  exact
    programPT06ActualPhysicalThirdJetJointTotalDerivative_formalFourthJet
      density coordinate jet direction (hJoint direction)

/-! ## Scalar naturality from Cartan intertwining -/

/-- Chain-rule naturality of one joint Cartan derivative under any
differentiable transition intertwining the source and target lifts. -/
theorem
    programPT06ActualPhysicalThirdJetJointCartanDerivative_precompose_of_intertwines
    (transition :
      ProgramPT06ActualPhysicalThirdJetTotalCoordinateCarrier4D →
        ProgramPT06ActualPhysicalThirdJetTotalCoordinateCarrier4D)
    (point : ProgramPT06ActualPhysicalThirdJetTotalCoordinateCarrier4D)
    (sourceFrame targetFrame :
      ProgramPT06ActualPhysicalThirdJetCartanFrame4D)
    (baseTransition :
      ThroatCoverCoordinates →L[Real] ThroatCoverCoordinates)
    (scalar :
      ProgramPT06ActualPhysicalThirdJetTotalCoordinateCarrier4D → Real)
    (hTransition : DifferentiableAt Real transition point)
    (hScalar : DifferentiableAt Real scalar (transition point))
    (hIntertwines : ∀ direction : ThroatCoverCoordinates,
      fderiv Real transition point
          (programPT06ActualPhysicalThirdJetCartanLift sourceFrame direction) =
        programPT06ActualPhysicalThirdJetCartanLift targetFrame
          (baseTransition direction))
    (direction : ThroatCoverCoordinates) :
    programPT06ActualPhysicalThirdJetJointCartanDerivative
        (scalar ∘ transition) point sourceFrame direction =
      programPT06ActualPhysicalThirdJetJointCartanDerivative scalar
        (transition point) targetFrame (baseTransition direction) := by
  unfold programPT06ActualPhysicalThirdJetJointCartanDerivative
  have hComposition := fderiv_comp (𝕜 := Real) (x := point)
    (f := transition) (g := scalar) hScalar hTransition
  have hApplied := congrArg
    (fun derivative :
        ProgramPT06ActualPhysicalThirdJetTotalCoordinateCarrier4D →L[Real]
          Real =>
      derivative
        (programPT06ActualPhysicalThirdJetCartanLift sourceFrame direction))
    hComposition
  simp only [ContinuousLinearMap.comp_apply] at hApplied
  rw [hIntertwines] at hApplied
  exact hApplied

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

/-- Gate 1023 specializes scalar Cartan naturality to the local physical J3
total-space coordinate formula. -/
theorem
    programPT06ActualPhysicalThirdJetJointCartanDerivative_totalCoordChange
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
    (scalar :
      ProgramPT06ActualPhysicalThirdJetTotalCoordinateCarrier4D → Real)
    (hScalar : DifferentiableAt Real scalar
      (programPT06ActualPhysicalThirdJetTotalCoordChange period hPeriod
        firstCenter secondCenter first second
        (extChartAt throatCoverModelWithCorners firstCenter base, jet)))
    (direction : ThroatCoverCoordinates) :
    programPT06ActualPhysicalThirdJetJointCartanDerivative
        (scalar ∘
          programPT06ActualPhysicalThirdJetTotalCoordChange period hPeriod
            firstCenter secondCenter first second)
        (extChartAt throatCoverModelWithCorners firstCenter base, jet)
        frame direction =
      programPT06ActualPhysicalThirdJetJointCartanDerivative scalar
        (programPT06ActualPhysicalThirdJetTotalCoordChange period hPeriod
          firstCenter secondCenter first second
          (extChartAt throatCoverModelWithCorners firstCenter base, jet))
        (programPT06ActualPhysicalThirdJetCartanFrameTransport period hPeriod
          firstCenter secondCenter base hFirst hSecond first second hBase jet
          frame)
        (throatGaugeBaseChartTransitionJacobianEquivAt period hPeriod
          firstCenter secondCenter base hFirst hSecond direction) := by
  apply
    programPT06ActualPhysicalThirdJetJointCartanDerivative_precompose_of_intertwines
      (transition :=
        programPT06ActualPhysicalThirdJetTotalCoordChange period hPeriod
          firstCenter secondCenter first second)
      (sourceFrame := frame)
      (targetFrame :=
        programPT06ActualPhysicalThirdJetCartanFrameTransport period hPeriod
          firstCenter secondCenter base hFirst hSecond first second hBase jet
          frame)
      (baseTransition :=
        (throatGaugeBaseChartTransitionJacobianEquivAt period hPeriod
          firstCenter secondCenter base hFirst hSecond).toContinuousLinearMap)
      (scalar := scalar)
  · exact programPT06ActualPhysicalThirdJetTotalCoordChange_differentiableAt
      period hPeriod firstCenter secondCenter base hFirst hSecond first second
      hBase jet
  · exact hScalar
  · intro vector
    exact
      programPT06ActualPhysicalThirdJetCartanFrameTransport_intertwines
        period hPeriod firstCenter secondCenter base hFirst hSecond first second
        hBase jet frame vector

end
end P0EFTJanusProgramPT06ActualPhysicalThirdJetJointHorizontalDifferential4D
end JanusFormal
