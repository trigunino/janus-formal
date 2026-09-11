import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06T02ActualAtlasRadialCurrentNaturality4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06T02MovingFrameRankOneCompatibility4D

/-!
# Compatible third-jet transport for the T02 Cartan current

Gate916's compatibility data identify the genuine derivative-corrected T02
second-jet transition with Gate902's coefficientwise moving-frame action.
This gate uses the same action at order three.  Its truncation is exactly the
genuine T02 transition, and its identity and cocycle laws follow from the
uniqueness of deck windings on the mapping-torus cover.

Pullback along this order-three lift gives a genuine cocycle on horizontal
current representatives.  Applying it to Gate942's canonical radial current
produces chart representatives satisfying the current transition law.

This does not identify the order-three lift with a derivative-corrected
geometric third-jet atlas; only its order-two truncation has that status.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06T02CompatibleThirdJetCurrentTransport4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000
set_option maxRecDepth 100000
noncomputable section

open Set
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusProgramPActualPhysicalSecondOrderJetProductVectorBundleCore4D
open P0EFTJanusProgramPT02InvariantLocalFunctionalBasisTerminalCertificate4D
open P0EFTJanusProgramPT06ThroatSpatialFinsuppJetTower4D
open P0EFTJanusProgramPT06ActualPhysicalValueProductSecondJetBridge4D
open P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D
open P0EFTJanusProgramPT06T02FinsuppSecondJetFrechetDerivative4D
open P0EFTJanusProgramPT06SecondOrderRadialCartanHomotopy4D
open P0EFTJanusProgramPT06T02DegreeFourRadialCartanClassification4D
open P0EFTJanusProgramPT06MovingFrameDeckConjugation4D
open P0EFTJanusProgramPT06T02MovingFrameRankOneCompatibility4D
open P0EFTJanusProgramPT06T02ActualAtlasRadialCurrentNaturality4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

attribute [local instance]
  P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D.actualPhysicalValueProductNormedAddCommGroup
  P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D.actualPhysicalValueProductNormedSpace
  P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D.actualPhysicalValueProductFinsuppSecondJetFiniteDimensional
  P0EFTJanusProgramPT06T02DegreeFourFrechetDerivative4D.gate878ActualPhysicalFiniteDimensional
  P0EFTJanusProgramPT06T02DegreeFourFrechetDerivative4D.gate878ActualPhysicalNormedAddCommGroup
  P0EFTJanusProgramPT06T02DegreeFourFrechetDerivative4D.gate878ActualPhysicalNormedSpace

private abbrev Fiber := ActualPhysicalValueProductFiber
private abbrev ThirdJet := ThroatSpatialMultiindexJet3 Fiber
private abbrev Current :=
  ProgramPT06SecondOrderHorizontalCurrent4D (Fiber := Fiber)

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev Base := MappingTorus (fixedEquatorData period hPeriod)
private abbrev Chart :=
  ActualPhysicalSecondOrderJetProductBundleIndex period hPeriod

/-- The winding attached by Gate916 to an identity overlap is zero. -/
theorem programPT06T02CompatibleTransitionWinding_self
    (compatibility :
      ProgramPT06T02MovingFrameJetCompatibility4D period hPeriod)
    (chart : Chart period hPeriod) (base : Base period hPeriod)
    (hBase : base ∈
      (actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
        .positiveQuarter).baseSet chart) :
    compatibility.transitionWinding chart chart base = 0 := by
  have hTarget := compatibility.target_point chart chart base ⟨hBase, hBase⟩
  change compatibility.transitionWinding chart chart base +ᵥ
      compatibility.chartLift chart base =
    compatibility.chartLift chart base at hTarget
  exact (vadd_eq_self_iff (fixedEquatorData period hPeriod) _ _).mp hTarget

/-- Gate916's transition windings satisfy the Cech cocycle on triple
overlaps; this is derived from their target points and freeness of the deck
action. -/
theorem programPT06T02CompatibleTransitionWinding_comp
    (compatibility :
      ProgramPT06T02MovingFrameJetCompatibility4D period hPeriod)
    (first second third : Chart period hPeriod)
    (base : Base period hPeriod)
    (hBase : base ∈
      (actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
          .positiveQuarter).baseSet first ∩
        (actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
          .positiveQuarter).baseSet second ∩
        (actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
          .positiveQuarter).baseSet third) :
    compatibility.transitionWinding second third base +
        compatibility.transitionWinding first second base =
      compatibility.transitionWinding first third base := by
  have hFirstSecond := compatibility.target_point first second base
    ⟨hBase.1.1, hBase.1.2⟩
  have hSecondThird := compatibility.target_point second third base
    ⟨hBase.1.2, hBase.2⟩
  have hFirstThird := compatibility.target_point first third base
    ⟨hBase.1.1, hBase.2⟩
  change compatibility.transitionWinding first second base +ᵥ
      compatibility.chartLift first base =
    compatibility.chartLift second base at hFirstSecond
  change compatibility.transitionWinding second third base +ᵥ
      compatibility.chartLift second base =
    compatibility.chartLift third base at hSecondThird
  change compatibility.transitionWinding first third base +ᵥ
      compatibility.chartLift first base =
    compatibility.chartLift third base at hFirstThird
  apply IsCancelVAdd.right_cancel
    (compatibility.transitionWinding second third base +
      compatibility.transitionWinding first second base)
    (compatibility.transitionWinding first third base)
    (compatibility.chartLift first base)
  calc
    (compatibility.transitionWinding second third base +
          compatibility.transitionWinding first second base) +ᵥ
        compatibility.chartLift first base =
      compatibility.transitionWinding second third base +ᵥ
        (compatibility.transitionWinding first second base +ᵥ
          compatibility.chartLift first base) :=
        add_vadd _ _ _
    _ = compatibility.transitionWinding second third base +ᵥ
        compatibility.chartLift second base := by rw [hFirstSecond]
    _ = compatibility.chartLift third base := hSecondThird
    _ = compatibility.transitionWinding first third base +ᵥ
        compatibility.chartLift first base := hFirstThird.symm

/-- The order-three lift selected by Gate916's already supplied atlas
compatibility data. -/
def programPT06T02CompatibleFinsuppThirdJetCoordChange
    (compatibility :
      ProgramPT06T02MovingFrameJetCompatibility4D period hPeriod)
    (first second : Chart period hPeriod) (base : Base period hPeriod)
    (jet : ThirdJet) : ThirdJet :=
  programPT06ActualPhysicalMovingFrameJetDeckAction
    compatibility.trivialization .positiveQuarter
    (compatibility.transitionWinding first second base)
    (compatibility.chartLift first base) 3 jet

@[simp] theorem programPT06T02CompatibleFinsuppThirdJetCoordChange_self
    (compatibility :
      ProgramPT06T02MovingFrameJetCompatibility4D period hPeriod)
    (chart : Chart period hPeriod) (base : Base period hPeriod)
    (hBase : base ∈
      (actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
        .positiveQuarter).baseSet chart)
    (jet : ThirdJet) :
    programPT06T02CompatibleFinsuppThirdJetCoordChange
        period hPeriod compatibility chart chart base jet = jet := by
  rw [programPT06T02CompatibleFinsuppThirdJetCoordChange,
    programPT06T02CompatibleTransitionWinding_self
      period hPeriod compatibility chart base hBase]
  exact programPT06ActualPhysicalMovingFrameJetDeckAction_zero
    compatibility.trivialization .positiveQuarter
      (compatibility.chartLift chart base) 3 jet

/-- The selected order-three lifts form a cocycle. -/
theorem programPT06T02CompatibleFinsuppThirdJetCoordChange_comp
    (compatibility :
      ProgramPT06T02MovingFrameJetCompatibility4D period hPeriod)
    (first second third : Chart period hPeriod)
    (base : Base period hPeriod)
    (hBase : base ∈
      (actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
          .positiveQuarter).baseSet first ∩
        (actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
          .positiveQuarter).baseSet second ∩
        (actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
          .positiveQuarter).baseSet third)
    (jet : ThirdJet) :
    programPT06T02CompatibleFinsuppThirdJetCoordChange period hPeriod
        compatibility second third base
        (programPT06T02CompatibleFinsuppThirdJetCoordChange period hPeriod
          compatibility first second base jet) =
      programPT06T02CompatibleFinsuppThirdJetCoordChange period hPeriod
        compatibility first third base jet := by
  unfold programPT06T02CompatibleFinsuppThirdJetCoordChange
  rw [← compatibility.target_point first second base
    ⟨hBase.1.1, hBase.1.2⟩]
  rw [← programPT06ActualPhysicalMovingFrameJetDeckAction_add]
  rw [programPT06T02CompatibleTransitionWinding_comp
    period hPeriod compatibility first second third base hBase]

/-- Truncating the selected third-jet lift recovers exactly the genuine
derivative-corrected T02 second-jet coordinate change. -/
theorem programPT06T02CompatibleFinsuppThirdJetCoordChange_truncate
    (compatibility :
      ProgramPT06T02MovingFrameJetCompatibility4D period hPeriod)
    (first second : Chart period hPeriod) (base : Base period hPeriod)
    (hBase : base ∈
      (actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
          .positiveQuarter).baseSet first ∩
        (actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
          .positiveQuarter).baseSet second)
    (jet : ThirdJet) :
    truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 3)
        (programPT06T02CompatibleFinsuppThirdJetCoordChange period hPeriod
          compatibility first second base jet) =
      programPT06T02ActualAtlasFinsuppSecondJetCoordChange period hPeriod
        first second base
        (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 3) jet) := by
  rw [programPT06T02CompatibleFinsuppThirdJetCoordChange,
    programPT06ActualPhysicalMovingFrameJetDeckAction_commutes_truncation]
  have hIntertwines := compatibility.coordChange_intertwines
    first second base hBase
    (programPT06ActualPhysicalValueProductFinsuppSecondJetContinuousLinearEquiv
      (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 3) jet))
  simpa [programPT06T02ActualAtlasFinsuppSecondJetCoordChange,
    programPT06T02MovingFramePullbackSecondJet] using hIntertwines.symm

/-- Contravariant pullback of a third-jet horizontal current along the
compatible order-three chart transition. -/
def programPT06T02CompatibleThirdJetCurrentPullback
    (compatibility :
      ProgramPT06T02MovingFrameJetCompatibility4D period hPeriod)
    (first second : Chart period hPeriod) (base : Base period hPeriod)
    (current : Current) : Current :=
  fun direction jet => current direction
    (programPT06T02CompatibleFinsuppThirdJetCoordChange period hPeriod
      compatibility first second base jet)

/-- Pullback of currents respects composition on triple overlaps. -/
theorem programPT06T02CompatibleThirdJetCurrentPullback_comp
    (compatibility :
      ProgramPT06T02MovingFrameJetCompatibility4D period hPeriod)
    (first second third : Chart period hPeriod)
    (base : Base period hPeriod)
    (hBase : base ∈
      (actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
          .positiveQuarter).baseSet first ∩
        (actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
          .positiveQuarter).baseSet second ∩
        (actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
          .positiveQuarter).baseSet third)
    (current : Current) :
    programPT06T02CompatibleThirdJetCurrentPullback period hPeriod
        compatibility first second base
        (programPT06T02CompatibleThirdJetCurrentPullback period hPeriod
          compatibility second third base current) =
      programPT06T02CompatibleThirdJetCurrentPullback period hPeriod
        compatibility first third base current := by
  funext direction jet
  exact congrArg (current direction)
    (programPT06T02CompatibleFinsuppThirdJetCoordChange_comp
      period hPeriod compatibility first second third base hBase jet)

/-- Chart representative obtained by transporting the canonical T02 radial
current from one reference chart. -/
def programPT06T02DegreeFourRadialCartanCurrentChartRepresentative
    (compatibility :
      ProgramPT06T02MovingFrameJetCompatibility4D period hPeriod)
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (reference chart : Chart period hPeriod) (base : Base period hPeriod) :
    Current :=
  programPT06T02CompatibleThirdJetCurrentPullback period hPeriod
    compatibility chart reference base
    (programPT06T02DegreeFourRadialCartanCurrent
      period hPeriod functional)

/-- The transported canonical radial-current representatives obey the full
third-jet chart-change law. -/
theorem programPT06T02DegreeFourRadialCartanCurrent_chartChange
    (compatibility :
      ProgramPT06T02MovingFrameJetCompatibility4D period hPeriod)
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (reference first second : Chart period hPeriod)
    (base : Base period hPeriod)
    (hBase : base ∈
      (actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
          .positiveQuarter).baseSet first ∩
        (actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
          .positiveQuarter).baseSet second ∩
        (actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
          .positiveQuarter).baseSet reference)
    (direction : Fin 3) (jet : ThirdJet) :
    programPT06T02DegreeFourRadialCartanCurrentChartRepresentative
        period hPeriod compatibility functional reference second base direction
        (programPT06T02CompatibleFinsuppThirdJetCoordChange period hPeriod
          compatibility first second base jet) =
      programPT06T02DegreeFourRadialCartanCurrentChartRepresentative
        period hPeriod compatibility functional reference first base direction
        jet := by
  exact congrArg
    ((programPT06T02DegreeFourRadialCartanCurrent
      period hPeriod functional) direction)
    (programPT06T02CompatibleFinsuppThirdJetCoordChange_comp
      period hPeriod compatibility first second reference base hBase jet)

end
end P0EFTJanusProgramPT06T02CompatibleThirdJetCurrentTransport4D
end JanusFormal
