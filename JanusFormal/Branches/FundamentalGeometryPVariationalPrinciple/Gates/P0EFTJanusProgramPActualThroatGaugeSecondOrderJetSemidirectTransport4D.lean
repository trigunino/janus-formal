import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFramedSecondOrderJetSemidirectTransport4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionJacobianEquiv4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeSecondOrderJetPresentationSetoid4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeSecondOrderJetTransitionSmoothRegularity4D

/-!
# Semidirect transport of actual throat gauge second-jet presentations

For two frame/chart pairs valid at the same throat point, this gate freezes
the inverse base-chart two-jet and the forward covector-frame two-jet in the
target chart.  The generic semidirect construction then gives a continuous
linear transport on arbitrary framed gauge second jets.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatGaugeSecondOrderJetSemidirectTransport4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 600000

noncomputable section

open Set
open scoped Manifold ContDiff RealInnerProductSpace Topology
open Bundle
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPFramedSecondOrderJetSemidirectTransport4D
open P0EFTJanusProgramPActualThroatGaugeZeroOrderTransitionCocycle4D
open P0EFTJanusProgramPActualThroatGaugeChartwiseFirstOrderOverlap4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionGerm4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionSecondOrderCocycle4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionJacobianEquiv4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetTransitionSmoothRegularity4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetPresentationSetoid4D

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev GaugeJet :=
  FramedSecondOrderJet ThroatCoverCoordinates
    (FramedCovector ThroatCoverCoordinates)

private abbrev GaugePresentationAt
    (current : EffectiveThroat period hPeriod) :=
  ThroatGaugeSecondOrderJetPresentationAt period hPeriod current

private abbrev CovectorEnd :=
  FramedCovector ThroatCoverCoordinates →L[Real]
    FramedCovector ThroatCoverCoordinates

local instance covectorEndNormedAddCommGroup :
    NormedAddCommGroup CovectorEnd :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance covectorEndNormedSpace : NormedSpace Real CovectorEnd :=
  ContinuousLinearMap.toNormedSpace

private abbrev CovectorTransitionFirstDerivative :=
  ThroatCoverCoordinates →L[Real] CovectorEnd

local instance covectorTransitionFirstDerivativeNormedAddCommGroup :
    NormedAddCommGroup CovectorTransitionFirstDerivative :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance covectorTransitionFirstDerivativeNormedSpace :
    NormedSpace Real CovectorTransitionFirstDerivative :=
  ContinuousLinearMap.toNormedSpace

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-- Iterated derivative of the forward frame transition, expressed in the
target chart.  The explicit result type keeps the nested operator-space
structure canonical. -/
def throatGaugeCovectorTargetTransitionSecondDerivativeAt
    {current : EffectiveThroat period hPeriod}
    (source target : GaugePresentationAt period hPeriod current) :
    ThroatCoverCoordinates →L[Real]
      CovectorTransitionFirstDerivative :=
  fderiv Real
    (fderiv Real
      (throatGaugeCovectorTransitionCenteredChart period hPeriod
        source.frameAnchor target.frameAnchor target.chartAnchor))
    (extChartAt throatCoverModelWithCorners target.chartAnchor current)

/-- Frozen semidirect coefficients from `source` to `target`.  Base
derivatives belong to the reverse chart transition, while fiber derivatives
belong to the forward frame transition expressed in the target chart. -/
def throatGaugeSecondOrderJetSemidirectChangeAt
    {current : EffectiveThroat period hPeriod}
    (source target : GaugePresentationAt period hPeriod current) :
    FramedSecondOrderJetSemidirectChange
      ThroatCoverCoordinates (FramedCovector ThroatCoverCoordinates) where
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
    throatGaugeCovectorTrivializationTransitionAt period hPeriod
      source.frameAnchor target.frameAnchor current
  fiberFirst :=
    fderiv Real
      (throatGaugeCovectorTransitionCenteredChart period hPeriod
        source.frameAnchor target.frameAnchor target.chartAnchor)
      (extChartAt throatCoverModelWithCorners target.chartAnchor current)
  fiberSecond :=
    throatGaugeCovectorTargetTransitionSecondDerivativeAt period hPeriod
      source target
  fiberSecond_symmetric first second := by
    have hSmooth : minSmoothness Real 2 ≤ (∞ : ℕ∞ω) := by
      rw [minSmoothness_of_isRCLikeNormedField]
      change ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
      exact WithTop.coe_le_coe.mpr le_top
    simpa only [throatGaugeCovectorTargetTransitionSecondDerivativeAt] using
      ((throatGaugeCovectorTransitionCenteredChart_contDiffAt_infty_of_mem_source
        period hPeriod source.frameAnchor target.frameAnchor
          target.chartAnchor current ⟨source.frame_mem, target.frame_mem⟩
            target.chart_mem).isSymmSndFDerivAt hSmooth).eq first second

@[simp]
theorem throatGaugeSecondOrderJetSemidirectChangeAt_baseFirst
    {current : EffectiveThroat period hPeriod}
    (source target : GaugePresentationAt period hPeriod current) :
    (throatGaugeSecondOrderJetSemidirectChangeAt period hPeriod
      source target).baseFirst =
      fderiv Real
        (throatGaugeBaseChartTransition period hPeriod
          target.chartAnchor source.chartAnchor)
        (extChartAt throatCoverModelWithCorners target.chartAnchor current) :=
  rfl

@[simp]
theorem throatGaugeSecondOrderJetSemidirectChangeAt_baseFirst_apply
    {current : EffectiveThroat period hPeriod}
    (source target : GaugePresentationAt period hPeriod current)
    (direction : ThroatCoverCoordinates) :
    (throatGaugeSecondOrderJetSemidirectChangeAt period hPeriod
      source target).baseFirst direction =
      (throatGaugeBaseChartTransitionJacobianEquivAt period hPeriod
        source.chartAnchor target.chartAnchor current
          source.chart_mem target.chart_mem).symm direction := by
  simp [throatGaugeSecondOrderJetSemidirectChangeAt]

@[simp]
theorem throatGaugeSecondOrderJetSemidirectChangeAt_baseSecond
    {current : EffectiveThroat period hPeriod}
    (source target : GaugePresentationAt period hPeriod current) :
    (throatGaugeSecondOrderJetSemidirectChangeAt period hPeriod
      source target).baseSecond =
      fderiv Real
        (fderiv Real
          (throatGaugeBaseChartTransition period hPeriod
            target.chartAnchor source.chartAnchor))
        (extChartAt throatCoverModelWithCorners target.chartAnchor current) := by
  simp [throatGaugeSecondOrderJetSemidirectChangeAt]

@[simp]
theorem throatGaugeSecondOrderJetSemidirectChangeAt_fiberValue
    {current : EffectiveThroat period hPeriod}
    (source target : GaugePresentationAt period hPeriod current) :
    (throatGaugeSecondOrderJetSemidirectChangeAt period hPeriod
      source target).fiberValue =
      throatGaugeCovectorTrivializationTransitionAt period hPeriod
        source.frameAnchor target.frameAnchor current :=
  rfl

@[simp]
theorem throatGaugeSecondOrderJetSemidirectChangeAt_fiberFirst
    {current : EffectiveThroat period hPeriod}
    (source target : GaugePresentationAt period hPeriod current) :
    (throatGaugeSecondOrderJetSemidirectChangeAt period hPeriod
      source target).fiberFirst =
      fderiv Real
        (throatGaugeCovectorTransitionCenteredChart period hPeriod
          source.frameAnchor target.frameAnchor target.chartAnchor)
        (extChartAt throatCoverModelWithCorners target.chartAnchor current) :=
  rfl

@[simp]
theorem throatGaugeSecondOrderJetSemidirectChangeAt_fiberSecond
    {current : EffectiveThroat period hPeriod}
    (source target : GaugePresentationAt period hPeriod current) :
    (throatGaugeSecondOrderJetSemidirectChangeAt period hPeriod
      source target).fiberSecond =
      throatGaugeCovectorTargetTransitionSecondDerivativeAt period hPeriod
        source target :=
  rfl

/-- Continuous linear transport on the full framed gauge second-jet
carrier. -/
def throatGaugeSecondOrderJetSemidirectTransportAt
    {current : EffectiveThroat period hPeriod}
    (source target : GaugePresentationAt period hPeriod current) :
    GaugeJet →L[Real] GaugeJet :=
  (throatGaugeSecondOrderJetSemidirectChangeAt period hPeriod
    source target).toContinuousLinearMap

@[simp]
theorem throatGaugeSecondOrderJetSemidirectTransportAt_value
    {current : EffectiveThroat period hPeriod}
    (source target : GaugePresentationAt period hPeriod current)
    (jet : GaugeJet) :
    (throatGaugeSecondOrderJetSemidirectTransportAt period hPeriod
      source target jet).value =
      throatGaugeCovectorTrivializationTransitionAt period hPeriod
        source.frameAnchor target.frameAnchor current jet.value :=
  rfl

@[simp]
theorem throatGaugeSecondOrderJetSemidirectTransportAt_firstDerivative_apply
    {current : EffectiveThroat period hPeriod}
    (source target : GaugePresentationAt period hPeriod current)
    (jet : GaugeJet) (direction : ThroatCoverCoordinates) :
    (throatGaugeSecondOrderJetSemidirectTransportAt period hPeriod
      source target jet).firstDerivative direction =
      throatGaugeCovectorTrivializationTransitionAt period hPeriod
          source.frameAnchor target.frameAnchor current
        (jet.firstDerivative
          (fderiv Real
            (throatGaugeBaseChartTransition period hPeriod
              target.chartAnchor source.chartAnchor)
            (extChartAt throatCoverModelWithCorners target.chartAnchor current)
            direction)) +
      fderiv Real
          (throatGaugeCovectorTransitionCenteredChart period hPeriod
            source.frameAnchor target.frameAnchor target.chartAnchor)
          (extChartAt throatCoverModelWithCorners target.chartAnchor current)
          direction jet.value :=
  rfl

@[simp]
theorem throatGaugeSecondOrderJetSemidirectTransportAt_secondDerivative_apply
    {current : EffectiveThroat period hPeriod}
    (source target : GaugePresentationAt period hPeriod current)
    (jet : GaugeJet) (first second : ThroatCoverCoordinates) :
    (throatGaugeSecondOrderJetSemidirectTransportAt period hPeriod
      source target jet).secondDerivative first second =
      throatGaugeCovectorTrivializationTransitionAt period hPeriod
          source.frameAnchor target.frameAnchor current
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
      throatGaugeCovectorTrivializationTransitionAt period hPeriod
          source.frameAnchor target.frameAnchor current
        (jet.firstDerivative
          (fderiv Real
            (fderiv Real
              (throatGaugeBaseChartTransition period hPeriod
                target.chartAnchor source.chartAnchor))
            (extChartAt throatCoverModelWithCorners target.chartAnchor current)
            first second)) +
      fderiv Real
          (throatGaugeCovectorTransitionCenteredChart period hPeriod
            source.frameAnchor target.frameAnchor target.chartAnchor)
          (extChartAt throatCoverModelWithCorners target.chartAnchor current)
          first
        (jet.firstDerivative
          (fderiv Real
            (throatGaugeBaseChartTransition period hPeriod
              target.chartAnchor source.chartAnchor)
            (extChartAt throatCoverModelWithCorners target.chartAnchor current)
            second)) +
      fderiv Real
          (throatGaugeCovectorTransitionCenteredChart period hPeriod
            source.frameAnchor target.frameAnchor target.chartAnchor)
          (extChartAt throatCoverModelWithCorners target.chartAnchor current)
          second
        (jet.firstDerivative
          (fderiv Real
            (throatGaugeBaseChartTransition period hPeriod
              target.chartAnchor source.chartAnchor)
            (extChartAt throatCoverModelWithCorners target.chartAnchor current)
            first)) +
      throatGaugeCovectorTargetTransitionSecondDerivativeAt period hPeriod
        source target first second jet.value :=
  rfl

/-- The target frame/chart pair equipped with the transported source jet. -/
def throatGaugeSecondOrderJetSemidirectTargetPresentationAt
    {current : EffectiveThroat period hPeriod}
    (source target : GaugePresentationAt period hPeriod current) :
    GaugePresentationAt period hPeriod current where
  frameAnchor := target.frameAnchor
  chartAnchor := target.chartAnchor
  frame_mem := target.frame_mem
  chart_mem := target.chart_mem
  jet := throatGaugeSecondOrderJetSemidirectTransportAt period hPeriod
    source target source.jet

@[simp]
theorem throatGaugeSecondOrderJetSemidirectTargetPresentationAt_jet
    {current : EffectiveThroat period hPeriod}
    (source target : GaugePresentationAt period hPeriod current) :
    (throatGaugeSecondOrderJetSemidirectTargetPresentationAt period hPeriod
      source target).jet =
      throatGaugeSecondOrderJetSemidirectTransportAt period hPeriod
        source target source.jet :=
  rfl

end
end P0EFTJanusProgramPActualThroatGaugeSecondOrderJetSemidirectTransport4D
end JanusFormal
