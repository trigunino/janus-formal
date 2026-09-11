import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06T02CompatibleThirdJetCurrentTransport4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06ThroatSpatialFinsuppThirdJetBridge4D

/-!
# Framed transport of the selected complete physical third jet

The generic spatial-to-framed equivalence is applied to the complete physical
value product of Gate 874.  Conjugating Gate 945's selected spatial third-jet
transition gives a framed carrier whose truncation is exactly the actual T02
physical second-jet transition supplied by Gate 916.

This remains the coefficientwise lift selected by Gate 916.  It is not an
identification with a geometrically prolonged third-jet atlas.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06ActualPhysicalFramedThirdJetTransport4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000
set_option maxRecDepth 100000
noncomputable section

open Set
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPActualPhysicalSecondOrderJetProductVectorBundleCore4D
open P0EFTJanusProgramPFramedThirdOrderJetConstantFiberBaseChange4D
open P0EFTJanusProgramPT02InvariantLocalFunctionalBasisTerminalCertificate4D
open P0EFTJanusProgramPT06ThroatSpatialMultiindexSecondJetBridge4D
open P0EFTJanusProgramPT06ThroatSpatialFinsuppJetTower4D
open P0EFTJanusProgramPT06ActualPhysicalValueProductSecondJetBridge4D
open P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D
open P0EFTJanusProgramPT06T02FinsuppSecondJetFrechetDerivative4D
open P0EFTJanusProgramPT06T02ActualAtlasRadialCurrentNaturality4D
open P0EFTJanusProgramPT06T02MovingFrameRankOneCompatibility4D
open P0EFTJanusProgramPT06T02CompatibleThirdJetCurrentTransport4D
open P0EFTJanusProgramPT06ThroatSpatialFinsuppThirdJetBridge4D

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
private abbrev SpatialThirdJet := ThroatSpatialMultiindexJet3 Fiber
private abbrev PhysicalSecondJet := ActualPhysicalSecondOrderJetProductFiber

/-- The framed third jet of Gate 874's complete eleven-component value fiber. -/
abbrev ActualPhysicalFramedThirdOrderJetFiber :=
  FramedThirdOrderJet ThroatCoverCoordinates Fiber

/-- Horizontal currents written on the complete framed third-jet carrier. -/
abbrev ProgramPT06ActualPhysicalFramedThirdJetCurrent4D :=
  Fin 3 → ActualPhysicalFramedThirdOrderJetFiber → Real

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev Base := MappingTorus (fixedEquatorData period hPeriod)
private abbrev Chart :=
  ActualPhysicalSecondOrderJetProductBundleIndex period hPeriod

/-- Forget the cubic coefficients and identify the remaining spatial jet with
the exact physical T02 second-jet product. -/
def programPT06ActualPhysicalFramedThirdJetTruncate
    (_period : Real) (_hPeriod : _period ≠ 0) :
    ActualPhysicalFramedThirdOrderJetFiber →ₗ[Real] PhysicalSecondJet :=
  programPT06T02FinsuppSecondJetBridgeLinearMap.comp
    ((truncateThroatSpatialMultiindexJetLinear (by omega : 2 ≤ 3)).comp
      programPT06ThroatSpatialFinsuppThirdJetFramedLinearEquiv.symm.toLinearMap)

/-- On a spatial representative, physical truncation is Gate 881's exact
second-jet bridge after ordinary multi-index truncation. -/
@[simp] theorem programPT06ActualPhysicalFramedThirdJetTruncate_spatialFramed
    (jet : SpatialThirdJet) :
    programPT06ActualPhysicalFramedThirdJetTruncate period hPeriod
        (programPT06ThroatSpatialFinsuppThirdJetFramedLinearEquiv jet) =
      programPT06T02FinsuppSecondJetBridge
        (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 3) jet) := by
  change
    programPT06T02FinsuppSecondJetBridgeLinearMap
        (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 3)
          (programPT06ThroatSpatialFinsuppThirdJetFramedLinearEquiv.symm
            (programPT06ThroatSpatialFinsuppThirdJetFramedLinearEquiv jet))) =
      programPT06T02FinsuppSecondJetBridge
        (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 3) jet)
  rw [LinearEquiv.symm_apply_apply]
  rfl

/-- The framed lower-order component of the bridge is the canonical framed
reconstruction of the truncated spatial coefficients. -/
@[simp] theorem programPT06ActualPhysicalFramedThirdJet_toFramedSecondOrderJet
    (jet : SpatialThirdJet) :
    (programPT06ThroatSpatialFinsuppThirdJetFramedLinearEquiv jet
        ).toFramedSecondOrderJet =
      programPT06ThroatSpatialFinsuppSecondJetToFramed
        (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 3) jet) :=
  programPT06ThroatSpatialFinsuppThirdJetFramedLinearEquiv_truncate jet

/-- Gate 945's selected third-jet coordinate change, conjugated to the framed
complete physical carrier. -/
def programPT06T02CompatibleActualPhysicalFramedThirdJetCoordChange
    (compatibility :
      ProgramPT06T02MovingFrameJetCompatibility4D period hPeriod)
    (first second : Chart period hPeriod) (base : Base period hPeriod)
    (jet : ActualPhysicalFramedThirdOrderJetFiber) :
    ActualPhysicalFramedThirdOrderJetFiber :=
  programPT06ThroatSpatialFinsuppThirdJetFramedLinearEquiv
    (programPT06T02CompatibleFinsuppThirdJetCoordChange period hPeriod
      compatibility first second base
      (programPT06ThroatSpatialFinsuppThirdJetFramedLinearEquiv.symm jet))

/-- The spatial-to-framed equivalence intertwines Gate 945's selected
transition with the framed transport. -/
@[simp] theorem
    programPT06T02CompatibleActualPhysicalFramedThirdJetCoordChange_spatialFramed
    (compatibility :
      ProgramPT06T02MovingFrameJetCompatibility4D period hPeriod)
    (first second : Chart period hPeriod) (base : Base period hPeriod)
    (jet : SpatialThirdJet) :
    programPT06T02CompatibleActualPhysicalFramedThirdJetCoordChange
        period hPeriod compatibility first second base
        (programPT06ThroatSpatialFinsuppThirdJetFramedLinearEquiv jet) =
      programPT06ThroatSpatialFinsuppThirdJetFramedLinearEquiv
        (programPT06T02CompatibleFinsuppThirdJetCoordChange period hPeriod
          compatibility first second base jet) := by
  unfold programPT06T02CompatibleActualPhysicalFramedThirdJetCoordChange
  rw [LinearEquiv.symm_apply_apply]

/-- Identity overlaps act trivially on the framed physical third jet. -/
@[simp] theorem
    programPT06T02CompatibleActualPhysicalFramedThirdJetCoordChange_self
    (compatibility :
      ProgramPT06T02MovingFrameJetCompatibility4D period hPeriod)
    (chart : Chart period hPeriod) (base : Base period hPeriod)
    (hBase : base ∈
      (actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
        .positiveQuarter).baseSet chart)
    (jet : ActualPhysicalFramedThirdOrderJetFiber) :
    programPT06T02CompatibleActualPhysicalFramedThirdJetCoordChange
        period hPeriod compatibility chart chart base jet = jet := by
  unfold programPT06T02CompatibleActualPhysicalFramedThirdJetCoordChange
  rw [programPT06T02CompatibleFinsuppThirdJetCoordChange_self
    period hPeriod compatibility chart base hBase]
  exact LinearEquiv.apply_symm_apply _ jet

/-- The selected framed third-jet transports obey the overlap cocycle in the
same source-to-middle-to-target orientation as Gate 945. -/
theorem programPT06T02CompatibleActualPhysicalFramedThirdJetCoordChange_comp
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
    (jet : ActualPhysicalFramedThirdOrderJetFiber) :
    programPT06T02CompatibleActualPhysicalFramedThirdJetCoordChange
        period hPeriod compatibility second third base
        (programPT06T02CompatibleActualPhysicalFramedThirdJetCoordChange
          period hPeriod compatibility first second base jet) =
      programPT06T02CompatibleActualPhysicalFramedThirdJetCoordChange
        period hPeriod compatibility first third base jet := by
  unfold programPT06T02CompatibleActualPhysicalFramedThirdJetCoordChange
  rw [LinearEquiv.symm_apply_apply]
  rw [programPT06T02CompatibleFinsuppThirdJetCoordChange_comp
    period hPeriod compatibility first second third base hBase]

/-- Truncating the selected framed third-jet transport gives exactly the
derivative-corrected physical T02 second-jet coordinate change. -/
theorem
    programPT06T02CompatibleActualPhysicalFramedThirdJetCoordChange_truncate
    (compatibility :
      ProgramPT06T02MovingFrameJetCompatibility4D period hPeriod)
    (first second : Chart period hPeriod) (base : Base period hPeriod)
    (hBase : base ∈
      (actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
          .positiveQuarter).baseSet first ∩
        (actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
          .positiveQuarter).baseSet second)
    (jet : ActualPhysicalFramedThirdOrderJetFiber) :
    programPT06ActualPhysicalFramedThirdJetTruncate period hPeriod
        (programPT06T02CompatibleActualPhysicalFramedThirdJetCoordChange
          period hPeriod compatibility first second base jet) =
      (actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
          .positiveQuarter).coordChange first second base
        (programPT06ActualPhysicalFramedThirdJetTruncate period hPeriod jet) := by
  change
    programPT06T02FinsuppSecondJetBridge
        (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 3)
          (programPT06ThroatSpatialFinsuppThirdJetFramedLinearEquiv.symm
            (programPT06ThroatSpatialFinsuppThirdJetFramedLinearEquiv
              (programPT06T02CompatibleFinsuppThirdJetCoordChange
                period hPeriod compatibility first second base
                (programPT06ThroatSpatialFinsuppThirdJetFramedLinearEquiv.symm
                  jet))))) =
      (actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
          .positiveQuarter).coordChange first second base
        (programPT06T02FinsuppSecondJetBridge
          (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 3)
            (programPT06ThroatSpatialFinsuppThirdJetFramedLinearEquiv.symm
              jet)))
  rw [LinearEquiv.symm_apply_apply]
  rw [programPT06T02CompatibleFinsuppThirdJetCoordChange_truncate
    period hPeriod compatibility first second base hBase]
  exact programPT06T02FinsuppSecondJetBridge_actualAtlasCoordChange
    period hPeriod first second base
      (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 3)
        (programPT06ThroatSpatialFinsuppThirdJetFramedLinearEquiv.symm jet))

/-- Pull a framed horizontal current back through the selected framed
third-jet transition. -/
def programPT06T02CompatibleActualPhysicalFramedThirdJetCurrentPullback
    (compatibility :
      ProgramPT06T02MovingFrameJetCompatibility4D period hPeriod)
    (first second : Chart period hPeriod) (base : Base period hPeriod)
    (current : ProgramPT06ActualPhysicalFramedThirdJetCurrent4D) :
    ProgramPT06ActualPhysicalFramedThirdJetCurrent4D :=
  fun direction jet => current direction
    (programPT06T02CompatibleActualPhysicalFramedThirdJetCoordChange
      period hPeriod compatibility first second base jet)

/-- Framed current pullback respects composition on triple overlaps. -/
theorem
    programPT06T02CompatibleActualPhysicalFramedThirdJetCurrentPullback_comp
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
    (current : ProgramPT06ActualPhysicalFramedThirdJetCurrent4D) :
    programPT06T02CompatibleActualPhysicalFramedThirdJetCurrentPullback
        period hPeriod compatibility first second base
        (programPT06T02CompatibleActualPhysicalFramedThirdJetCurrentPullback
          period hPeriod compatibility second third base current) =
      programPT06T02CompatibleActualPhysicalFramedThirdJetCurrentPullback
        period hPeriod compatibility first third base current := by
  funext direction jet
  exact congrArg (current direction)
    (programPT06T02CompatibleActualPhysicalFramedThirdJetCoordChange_comp
      period hPeriod compatibility first second third base hBase jet)

/-- Gate 945's radial-current chart representative written on the framed
complete physical third-jet carrier. -/
def programPT06T02DegreeFourRadialCartanFramedCurrentChartRepresentative
    (compatibility :
      ProgramPT06T02MovingFrameJetCompatibility4D period hPeriod)
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (reference chart : Chart period hPeriod) (base : Base period hPeriod) :
    ProgramPT06ActualPhysicalFramedThirdJetCurrent4D :=
  fun direction jet =>
    programPT06T02DegreeFourRadialCartanCurrentChartRepresentative
      period hPeriod compatibility functional reference chart base direction
      (programPT06ThroatSpatialFinsuppThirdJetFramedLinearEquiv.symm jet)

/-- The framed radial-current representatives satisfy the selected third-jet
chart-change law. -/
theorem programPT06T02DegreeFourRadialCartanFramedCurrent_chartChange
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
    (direction : Fin 3) (jet : ActualPhysicalFramedThirdOrderJetFiber) :
    programPT06T02DegreeFourRadialCartanFramedCurrentChartRepresentative
        period hPeriod compatibility functional reference second base direction
        (programPT06T02CompatibleActualPhysicalFramedThirdJetCoordChange
          period hPeriod compatibility first second base jet) =
      programPT06T02DegreeFourRadialCartanFramedCurrentChartRepresentative
        period hPeriod compatibility functional reference first base direction
        jet := by
  unfold programPT06T02DegreeFourRadialCartanFramedCurrentChartRepresentative
    programPT06T02CompatibleActualPhysicalFramedThirdJetCoordChange
  rw [LinearEquiv.symm_apply_apply]
  exact programPT06T02DegreeFourRadialCartanCurrent_chartChange
    period hPeriod compatibility functional reference first second base hBase
      direction
      (programPT06ThroatSpatialFinsuppThirdJetFramedLinearEquiv.symm jet)

end
end P0EFTJanusProgramPT06ActualPhysicalFramedThirdJetTransport4D
end JanusFormal
