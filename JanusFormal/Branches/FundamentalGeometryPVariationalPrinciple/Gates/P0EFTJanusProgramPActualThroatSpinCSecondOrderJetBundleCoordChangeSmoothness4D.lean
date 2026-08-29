import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatSpinCSecondOrderJetBundleCoordChange4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatSpinCSecondOrderJetTransitionSmoothRegularity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFramedSecondOrderJetSemidirectTransportSmoothness4D

/-!
# Smoothness of throat SpinC second-jet coordinate changes

This gate upgrades continuity of the concrete SpinC semidirect coordinate
changes to `C∞` regularity on every double atlas overlap.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatSpinCSecondOrderJetBundleCoordChangeSmoothness4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 600000

noncomputable section

open Set
open scoped Manifold ContDiff Topology
open Bundle
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCBundle4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPFramedSecondOrderJetSemidirectTransport4D
open P0EFTJanusProgramPFramedSecondOrderJetSemidirectTransportSmoothness4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionGerm4D
open P0EFTJanusProgramPActualThroatSpinCSecondOrderTrivializationOverlap4D
open P0EFTJanusProgramPActualThroatSpinCSecondOrderJetSemidirectTransport4D
open P0EFTJanusProgramPActualThroatSpinCSecondOrderJetBundleAtlasData4D
open P0EFTJanusProgramPActualThroatSpinCSecondOrderJetBundleCoordChange4D
open P0EFTJanusProgramPActualThroatSpinCSecondOrderJetTransitionSmoothRegularity4D

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ThroatBase :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev SpinCModel := D9DoubledMatterFiber

private abbrev SpinCJet :=
  FramedSecondOrderJet ThroatCoverCoordinates SpinCModel

private abbrev SpinCEnd := SpinCModel →L[Real] SpinCModel

local instance spinCEndNormedAddCommGroup :
    NormedAddCommGroup SpinCEnd :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance spinCEndNormedSpace : NormedSpace Real SpinCEnd :=
  ContinuousLinearMap.toNormedSpace

private abbrev SpinCTransitionFirstDerivative :=
  ThroatCoverCoordinates →L[Real] SpinCEnd

local instance spinCTransitionFirstDerivativeNormedAddCommGroup :
    NormedAddCommGroup SpinCTransitionFirstDerivative :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance spinCTransitionFirstDerivativeNormedSpace :
    NormedSpace Real SpinCTransitionFirstDerivative :=
  ContinuousLinearMap.toNormedSpace

private abbrev BundleIndex :=
  ThroatSpinCSecondOrderJetBundleIndex period hPeriod

local instance throatBaseChartedSpace :
    ChartedSpace ThroatCoverModel (ThroatBase period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance throatBaseIsManifold :
    IsManifold throatCoverModelWithCorners ω (ThroatBase period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

private abbrev bundleOverlap
    (first second : BundleIndex period hPeriod) :
    Set (ThroatBase period hPeriod) :=
  throatSpinCSecondOrderJetBundleBaseSet period hPeriod first ∩
    throatSpinCSecondOrderJetBundleBaseSet period hPeriod second

/-- Identity coefficients used to totalize a SpinC semidirect change away
from its double overlap. -/
def identitySpinCFramedSecondOrderJetSemidirectChange :
    FramedSecondOrderJetSemidirectChange ThroatCoverCoordinates SpinCModel where
  baseFirst := ContinuousLinearMap.id Real ThroatCoverCoordinates
  baseSecond := 0
  baseSecond_symmetric first second := by simp
  fiberValue := ContinuousLinearMap.id Real SpinCModel
  fiberFirst := 0
  fiberSecond := 0
  fiberSecond_symmetric first second := by simp

/-- Globally defined coefficients whose overlap branch is the concrete SpinC
semidirect change. -/
def throatSpinCSecondOrderJetBundleTotalChange
    (choice : NormalRootChoice)
    (first second : BundleIndex period hPeriod)
    (current : ThroatBase period hPeriod) :
    FramedSecondOrderJetSemidirectChange ThroatCoverCoordinates SpinCModel := by
  classical
  exact if hCurrent : current ∈ bundleOverlap period hPeriod first second then
      throatSpinCSecondOrderJetBundleChangeOnOverlap period hPeriod choice
        first second ⟨current, hCurrent⟩
    else
      identitySpinCFramedSecondOrderJetSemidirectChange

/-- The totalized reverse-chart Jacobian coefficient is smooth on the double
overlap. -/
theorem throatSpinCSecondOrderJetBundleTotalChange_baseFirst_contMDiffOn
    (choice : NormalRootChoice)
    (first second : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, ThroatCoverCoordinates →L[Real] ThroatCoverCoordinates) ∞
      (fun current =>
        (throatSpinCSecondOrderJetBundleTotalChange period hPeriod choice
          first second current).baseFirst)
      (bundleOverlap period hPeriod first second) := by
  have hCoefficient := throatSpinCSecondOrderJet_baseFirst_contMDiffOn
    period hPeriod first second
  simp only [throatSpinCSecondOrderJetBundleOverlap] at hCoefficient
  apply hCoefficient.congr
  intro current hCurrent
  rw [throatSpinCSecondOrderJetBundleTotalChange, dif_pos hCurrent]
  simp [throatSpinCSecondOrderJetBundleChangeOnOverlap,
    throatSpinCSecondOrderJetSemidirectTrivializationChartAt]

/-- The totalized reverse-chart Hessian coefficient is smooth on the double
overlap. -/
theorem throatSpinCSecondOrderJetBundleTotalChange_baseSecond_contMDiffOn
    (choice : NormalRootChoice)
    (first second : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, ThroatCoverCoordinates →L[Real]
        ThroatCoverCoordinates →L[Real] ThroatCoverCoordinates) ∞
      (fun current =>
        (throatSpinCSecondOrderJetBundleTotalChange period hPeriod choice
          first second current).baseSecond)
      (bundleOverlap period hPeriod first second) := by
  have hCoefficient := throatSpinCSecondOrderJet_baseSecond_contMDiffOn
    period hPeriod first second
  simp only [throatSpinCSecondOrderJetBundleOverlap] at hCoefficient
  apply hCoefficient.congr
  intro current hCurrent
  rw [throatSpinCSecondOrderJetBundleTotalChange, dif_pos hCurrent]
  simp [throatSpinCSecondOrderJetBundleChangeOnOverlap,
    throatSpinCSecondOrderJetSemidirectTrivializationChartAt]

/-- The totalized SpinC fiber-value coefficient is smooth on the double
overlap. -/
theorem throatSpinCSecondOrderJetBundleTotalChange_fiberValue_contMDiffOn
    (choice : NormalRootChoice)
    (first second : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners 𝓘(Real, SpinCEnd) ∞
      (fun current =>
        (throatSpinCSecondOrderJetBundleTotalChange period hPeriod choice
          first second current).fiberValue)
      (bundleOverlap period hPeriod first second) := by
  have hCoefficient := throatSpinCSecondOrderJet_fiberValue_contMDiffOn
    period hPeriod choice first second
  simp only [throatSpinCSecondOrderJetBundleOverlap] at hCoefficient
  apply hCoefficient.congr
  intro current hCurrent
  rw [throatSpinCSecondOrderJetBundleTotalChange, dif_pos hCurrent]
  simp [throatSpinCSecondOrderJetBundleChangeOnOverlap,
    throatSpinCSecondOrderJetSemidirectTrivializationChartAt]

/-- The totalized first SpinC transition derivative is smooth on the double
overlap. -/
theorem throatSpinCSecondOrderJetBundleTotalChange_fiberFirst_contMDiffOn
    (choice : NormalRootChoice)
    (first second : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, SpinCTransitionFirstDerivative) ∞
      (fun current =>
        (throatSpinCSecondOrderJetBundleTotalChange period hPeriod choice
          first second current).fiberFirst)
      (bundleOverlap period hPeriod first second) := by
  have hCoefficient := throatSpinCSecondOrderJet_fiberFirst_contMDiffOn
    period hPeriod choice first second
  simp only [throatSpinCSecondOrderJetBundleOverlap] at hCoefficient
  apply hCoefficient.congr
  intro current hCurrent
  rw [throatSpinCSecondOrderJetBundleTotalChange, dif_pos hCurrent]
  simp [throatSpinCSecondOrderJetBundleChangeOnOverlap,
    throatSpinCSecondOrderJetSemidirectTrivializationChartAt]

/-- The totalized second SpinC transition derivative is smooth on the double
overlap. -/
theorem throatSpinCSecondOrderJetBundleTotalChange_fiberSecond_contMDiffOn
    (choice : NormalRootChoice)
    (first second : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, ThroatCoverCoordinates →L[Real]
        SpinCTransitionFirstDerivative) ∞
      (fun current =>
        (throatSpinCSecondOrderJetBundleTotalChange period hPeriod choice
          first second current).fiberSecond)
      (bundleOverlap period hPeriod first second) := by
  have hCoefficient := throatSpinCSecondOrderJet_fiberSecond_contMDiffOn
    period hPeriod choice first second
  simp only [throatSpinCSecondOrderJetBundleOverlap] at hCoefficient
  apply hCoefficient.congr
  intro current hCurrent
  rw [throatSpinCSecondOrderJetBundleTotalChange, dif_pos hCurrent]
  simp [throatSpinCTargetTrivializationTransitionSecondDerivativeAt,
    throatSpinCSecondOrderJetBundleChangeOnOverlap,
    throatSpinCSecondOrderJetSemidirectTrivializationChartAt]

/-- The totalized SpinC semidirect transport is smooth on the double
overlap. -/
theorem throatSpinCSecondOrderJetBundleTotalTransport_contMDiffOn
    (choice : NormalRootChoice)
    (first second : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, SpinCJet →L[Real] SpinCJet) ∞
      (fun current =>
        (throatSpinCSecondOrderJetBundleTotalChange period hPeriod choice
          first second current).toContinuousLinearMap)
      (bundleOverlap period hPeriod first second) :=
  contMDiffOn_semidirectTransport
    (throatSpinCSecondOrderJetBundleTotalChange period hPeriod choice
      first second)
    (throatSpinCSecondOrderJetBundleTotalChange_baseFirst_contMDiffOn
      period hPeriod choice first second)
    (throatSpinCSecondOrderJetBundleTotalChange_baseSecond_contMDiffOn
      period hPeriod choice first second)
    (throatSpinCSecondOrderJetBundleTotalChange_fiberValue_contMDiffOn
      period hPeriod choice first second)
    (throatSpinCSecondOrderJetBundleTotalChange_fiberFirst_contMDiffOn
      period hPeriod choice first second)
    (throatSpinCSecondOrderJetBundleTotalChange_fiberSecond_contMDiffOn
      period hPeriod choice first second)

/-- Concrete SpinC second-jet coordinate changes are smooth on every double
atlas overlap. -/
theorem throatSpinCSecondOrderJetBundleCoordChange_contMDiffOn
    (choice : NormalRootChoice)
    (first second : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, SpinCJet →L[Real] SpinCJet) ∞
      (throatSpinCSecondOrderJetBundleCoordChange period hPeriod choice
        first second)
      (throatSpinCSecondOrderJetBundleBaseSet period hPeriod first ∩
        throatSpinCSecondOrderJetBundleBaseSet period hPeriod second) := by
  apply
    (throatSpinCSecondOrderJetBundleTotalTransport_contMDiffOn
      period hPeriod choice first second).congr
  intro current hCurrent
  rw [throatSpinCSecondOrderJetBundleCoordChange_eq_of_mem
    period hPeriod choice first second current hCurrent]
  rw [throatSpinCSecondOrderJetBundleTotalChange, dif_pos hCurrent]
  rfl

end
end P0EFTJanusProgramPActualThroatSpinCSecondOrderJetBundleCoordChangeSmoothness4D
end JanusFormal
