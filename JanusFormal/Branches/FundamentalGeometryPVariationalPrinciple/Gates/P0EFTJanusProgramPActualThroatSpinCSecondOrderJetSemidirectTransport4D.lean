import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFramedSecondOrderJetSemidirectTransport4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionSecondOrderCocycle4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatSpinCSecondOrderTrivializationOverlap4D

/-!
# Semidirect transport of actual throat SpinC second jets

At one throat point, two valid SpinC-trivialization/base-chart pairs determine
the reverse base-chart two-jet and the forward SpinC fiber-transition two-jet.
The generic semidirect construction transports arbitrary framed SpinC second
jets continuously and linearly.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatSpinCSecondOrderJetSemidirectTransport4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 600000

noncomputable section

open Set
open scoped Manifold ContDiff Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCBundle4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPFramedSecondOrderJetSemidirectTransport4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionGerm4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionSecondOrderCocycle4D
open P0EFTJanusProgramPActualThroatSpinCSecondOrderTrivializationOverlap4D

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev SpinCJet :=
  FramedSecondOrderJet ThroatCoverCoordinates D9DoubledMatterFiber

private abbrev SpinCEnd :=
  D9DoubledMatterFiber →L[Real] D9DoubledMatterFiber

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

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-- A primitive SpinC trivialization and base chart both valid at one throat
point. -/
structure ThroatSpinCSecondOrderJetTrivializationChartAt
    (current : EffectiveThroat period hPeriod) where
  trivializationIndex : D9PrimitiveSpinCIndex period hPeriod
  chartAnchor : EffectiveThroat period hPeriod
  trivialization_mem : current ∈
    d9PrimitiveSpinCBaseSet period hPeriod trivializationIndex
  chart_mem : current ∈
    (extChartAt throatCoverModelWithCorners chartAnchor).source

private abbrev SpinCTrivializationChartAt
    (current : EffectiveThroat period hPeriod) :=
  ThroatSpinCSecondOrderJetTrivializationChartAt period hPeriod current

/-- Iterated derivative of the forward SpinC transition, expressed in the
target base chart. -/
def throatSpinCTargetTrivializationTransitionSecondDerivativeAt
    (choice : NormalRootChoice)
    {current : EffectiveThroat period hPeriod}
    (source target : SpinCTrivializationChartAt period hPeriod current) :
    ThroatCoverCoordinates →L[Real] SpinCTransitionFirstDerivative :=
  fderiv Real
    (fderiv Real
      (d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
        source.trivializationIndex target.trivializationIndex
          target.chartAnchor))
    (extChartAt throatCoverModelWithCorners target.chartAnchor current)

/-- Frozen reverse-base and forward-fiber coefficients from `source` to
`target`. -/
def throatSpinCSecondOrderJetSemidirectChangeAt
    (choice : NormalRootChoice)
    {current : EffectiveThroat period hPeriod}
    (source target : SpinCTrivializationChartAt period hPeriod current) :
    FramedSecondOrderJetSemidirectChange
      ThroatCoverCoordinates D9DoubledMatterFiber where
  baseFirst :=
    fderiv Real
      (throatGaugeBaseChartTransition period hPeriod
        target.chartAnchor source.chartAnchor)
      (extChartAt throatCoverModelWithCorners target.chartAnchor current)
  baseSecond :=
    (throatGaugeBaseChartTransitionSecondOrderJetAt period hPeriod
      target.chartAnchor source.chartAnchor current
        target.chart_mem source.chart_mem).secondDerivative
  baseSecond_symmetric first second :=
    (throatGaugeBaseChartTransitionSecondOrderJetAt period hPeriod
      target.chartAnchor source.chartAnchor current
        target.chart_mem source.chart_mem).secondDerivative_symmetric
          first second
  fiberValue :=
    d9PrimitiveSpinCCoordChange period hPeriod choice
      source.trivializationIndex target.trivializationIndex current
  fiberFirst :=
    fderiv Real
      (d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
        source.trivializationIndex target.trivializationIndex
          target.chartAnchor)
      (extChartAt throatCoverModelWithCorners target.chartAnchor current)
  fiberSecond :=
    throatSpinCTargetTrivializationTransitionSecondDerivativeAt period hPeriod
      choice source target
  fiberSecond_symmetric first second := by
    have hSmooth : minSmoothness Real 2 ≤ (∞ : ℕ∞ω) := by
      rw [minSmoothness_of_isRCLikeNormedField]
      change ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
      exact WithTop.coe_le_coe.mpr le_top
    simpa only [throatSpinCTargetTrivializationTransitionSecondDerivativeAt] using
      ((d9PrimitiveSpinCTransitionCenteredChart_contDiffAt_infty period hPeriod
        choice source.trivializationIndex target.trivializationIndex
          target.chartAnchor current
          ⟨source.trivialization_mem, target.trivialization_mem⟩
            target.chart_mem).isSymmSndFDerivAt hSmooth).eq first second

@[simp]
theorem throatSpinCSecondOrderJetSemidirectChangeAt_baseFirst
    (choice : NormalRootChoice)
    {current : EffectiveThroat period hPeriod}
    (source target : SpinCTrivializationChartAt period hPeriod current) :
    (throatSpinCSecondOrderJetSemidirectChangeAt period hPeriod choice
      source target).baseFirst =
      fderiv Real
        (throatGaugeBaseChartTransition period hPeriod
          target.chartAnchor source.chartAnchor)
        (extChartAt throatCoverModelWithCorners target.chartAnchor current) :=
  rfl

@[simp]
theorem throatSpinCSecondOrderJetSemidirectChangeAt_baseSecond
    (choice : NormalRootChoice)
    {current : EffectiveThroat period hPeriod}
    (source target : SpinCTrivializationChartAt period hPeriod current) :
    (throatSpinCSecondOrderJetSemidirectChangeAt period hPeriod choice
      source target).baseSecond =
      fderiv Real
        (fderiv Real
          (throatGaugeBaseChartTransition period hPeriod
            target.chartAnchor source.chartAnchor))
        (extChartAt throatCoverModelWithCorners target.chartAnchor current) := by
  simp [throatSpinCSecondOrderJetSemidirectChangeAt]

@[simp]
theorem throatSpinCSecondOrderJetSemidirectChangeAt_fiberValue
    (choice : NormalRootChoice)
    {current : EffectiveThroat period hPeriod}
    (source target : SpinCTrivializationChartAt period hPeriod current) :
    (throatSpinCSecondOrderJetSemidirectChangeAt period hPeriod choice
      source target).fiberValue =
      d9PrimitiveSpinCCoordChange period hPeriod choice
        source.trivializationIndex target.trivializationIndex current :=
  rfl

@[simp]
theorem throatSpinCSecondOrderJetSemidirectChangeAt_fiberFirst
    (choice : NormalRootChoice)
    {current : EffectiveThroat period hPeriod}
    (source target : SpinCTrivializationChartAt period hPeriod current) :
    (throatSpinCSecondOrderJetSemidirectChangeAt period hPeriod choice
      source target).fiberFirst =
      fderiv Real
        (d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
          source.trivializationIndex target.trivializationIndex
            target.chartAnchor)
        (extChartAt throatCoverModelWithCorners target.chartAnchor current) :=
  rfl

@[simp]
theorem throatSpinCSecondOrderJetSemidirectChangeAt_fiberSecond
    (choice : NormalRootChoice)
    {current : EffectiveThroat period hPeriod}
    (source target : SpinCTrivializationChartAt period hPeriod current) :
    (throatSpinCSecondOrderJetSemidirectChangeAt period hPeriod choice
      source target).fiberSecond =
      throatSpinCTargetTrivializationTransitionSecondDerivativeAt
        period hPeriod choice source target :=
  rfl

/-- Continuous linear transport on the full framed SpinC second-jet
carrier. -/
def throatSpinCSecondOrderJetSemidirectTransportAt
    (choice : NormalRootChoice)
    {current : EffectiveThroat period hPeriod}
    (source target : SpinCTrivializationChartAt period hPeriod current) :
    SpinCJet →L[Real] SpinCJet :=
  (throatSpinCSecondOrderJetSemidirectChangeAt period hPeriod choice
    source target).toContinuousLinearMap

@[simp]
theorem throatSpinCSecondOrderJetSemidirectTransportAt_value
    (choice : NormalRootChoice)
    {current : EffectiveThroat period hPeriod}
    (source target : SpinCTrivializationChartAt period hPeriod current)
    (jet : SpinCJet) :
    (throatSpinCSecondOrderJetSemidirectTransportAt period hPeriod choice
      source target jet).value =
      d9PrimitiveSpinCCoordChange period hPeriod choice
        source.trivializationIndex target.trivializationIndex current
          jet.value :=
  rfl

@[simp]
theorem throatSpinCSecondOrderJetSemidirectTransportAt_firstDerivative_apply
    (choice : NormalRootChoice)
    {current : EffectiveThroat period hPeriod}
    (source target : SpinCTrivializationChartAt period hPeriod current)
    (jet : SpinCJet) (direction : ThroatCoverCoordinates) :
    (throatSpinCSecondOrderJetSemidirectTransportAt period hPeriod choice
      source target jet).firstDerivative direction =
      d9PrimitiveSpinCCoordChange period hPeriod choice
          source.trivializationIndex target.trivializationIndex current
        (jet.firstDerivative
          (fderiv Real
            (throatGaugeBaseChartTransition period hPeriod
              target.chartAnchor source.chartAnchor)
            (extChartAt throatCoverModelWithCorners target.chartAnchor current)
            direction)) +
      fderiv Real
          (d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
            source.trivializationIndex target.trivializationIndex
              target.chartAnchor)
          (extChartAt throatCoverModelWithCorners target.chartAnchor current)
          direction jet.value :=
  rfl

@[simp]
theorem throatSpinCSecondOrderJetSemidirectTransportAt_secondDerivative_apply
    (choice : NormalRootChoice)
    {current : EffectiveThroat period hPeriod}
    (source target : SpinCTrivializationChartAt period hPeriod current)
    (jet : SpinCJet) (first second : ThroatCoverCoordinates) :
    (throatSpinCSecondOrderJetSemidirectTransportAt period hPeriod choice
      source target jet).secondDerivative first second =
      d9PrimitiveSpinCCoordChange period hPeriod choice
          source.trivializationIndex target.trivializationIndex current
        (jet.secondDerivative
          (fderiv Real
            (throatGaugeBaseChartTransition period hPeriod
              target.chartAnchor source.chartAnchor)
            (extChartAt throatCoverModelWithCorners target.chartAnchor current)
            first)
          (fderiv Real
            (throatGaugeBaseChartTransition period hPeriod
              target.chartAnchor source.chartAnchor)
            (extChartAt throatCoverModelWithCorners target.chartAnchor current)
            second)) +
      d9PrimitiveSpinCCoordChange period hPeriod choice
          source.trivializationIndex target.trivializationIndex current
        (jet.firstDerivative
          (fderiv Real
            (fderiv Real
              (throatGaugeBaseChartTransition period hPeriod
                target.chartAnchor source.chartAnchor))
            (extChartAt throatCoverModelWithCorners target.chartAnchor current)
            first second)) +
      fderiv Real
          (d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
            source.trivializationIndex target.trivializationIndex
              target.chartAnchor)
          (extChartAt throatCoverModelWithCorners target.chartAnchor current)
          first
        (jet.firstDerivative
          (fderiv Real
            (throatGaugeBaseChartTransition period hPeriod
              target.chartAnchor source.chartAnchor)
            (extChartAt throatCoverModelWithCorners target.chartAnchor current)
            second)) +
      fderiv Real
          (d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
            source.trivializationIndex target.trivializationIndex
              target.chartAnchor)
          (extChartAt throatCoverModelWithCorners target.chartAnchor current)
          second
        (jet.firstDerivative
          (fderiv Real
            (throatGaugeBaseChartTransition period hPeriod
              target.chartAnchor source.chartAnchor)
            (extChartAt throatCoverModelWithCorners target.chartAnchor current)
            first)) +
      throatSpinCTargetTrivializationTransitionSecondDerivativeAt
        period hPeriod choice source target first second jet.value :=
  rfl

end
end P0EFTJanusProgramPActualThroatSpinCSecondOrderJetSemidirectTransport4D
end JanusFormal
