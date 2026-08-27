import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatSpinCSecondOrderJetSemidirectTransport4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatSpinCArbitraryTrivializationBaseChartSecondOrderJetOverlap4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionSecondOrderGroupoid4D

/-!
# Compatibility of SpinC second-jet semidirect transport

The concrete inverse-base/forward-fiber semidirect transport sends the second
jet of any genuine smooth SpinC section in a source trivialization and chart
exactly to its jet in any valid target trivialization and chart.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatSpinCSecondOrderJetSemidirectTransportCompatibility4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 600000

noncomputable section

open Set
open scoped Manifold ContDiff Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionGerm4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionSecondOrderCocycle4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionSecondOrderGroupoid4D
open P0EFTJanusProgramPActualThroatSpinCArbitraryTrivializationChartSecondOrderJetExtraction4D
open P0EFTJanusProgramPActualThroatSpinCBaseChartSecondOrderJetOverlap4D
open P0EFTJanusProgramPActualThroatSpinCSecondOrderTrivializationOverlap4D
open P0EFTJanusProgramPActualThroatSpinCArbitraryTrivializationBaseChartSecondOrderJetOverlap4D
open P0EFTJanusProgramPActualThroatSpinCSecondOrderJetSemidirectTransport4D

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

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

private theorem fderiv_clm_apply_const_apply
    {X Y Z : Type*}
    [NormedAddCommGroup X] [NormedSpace Real X]
    [NormedAddCommGroup Y] [NormedSpace Real Y]
    [NormedAddCommGroup Z] [NormedSpace Real Z]
    (field : X → Y →L[Real] Z) (point direction : X) (value : Y)
    (hField : DifferentiableAt Real field point) :
    fderiv Real (fun current ↦ field current value) point direction =
      fderiv Real field point direction value := by
  have hDerivative :=
    fderiv_clm_apply hField (differentiableAt_const (c := value))
  have hApplied := congrArg
    (fun derivative : X →L[Real] Z ↦ derivative direction) hDerivative
  simpa using hApplied

/-- Semidirect transport of an extracted smooth SpinC jet is exactly the jet
extracted in the target trivialization and chart. -/
theorem throatSpinCSecondOrderJetSemidirectTransportAt_extracted
    (choice : NormalRootChoice)
    {current : EffectiveThroat period hPeriod}
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice)
    (source target :
      ThroatSpinCSecondOrderJetTrivializationChartAt
        period hPeriod current) :
    throatSpinCSecondOrderJetSemidirectTransportAt period hPeriod choice
        source target
        (d9PrimitiveSpinCSectionSecondOrderJetInTrivializationChartAt
          period hPeriod choice state source.trivializationIndex
            source.chartAnchor current source.trivialization_mem
              source.chart_mem) =
      d9PrimitiveSpinCSectionSecondOrderJetInTrivializationChartAt
        period hPeriod choice state target.trivializationIndex
          target.chartAnchor current target.trivialization_mem
            target.chart_mem := by
  let sourceJet :=
    d9PrimitiveSpinCSectionSecondOrderJetInTrivializationChartAt
      period hPeriod choice state source.trivializationIndex
        source.chartAnchor current source.trivialization_mem source.chart_mem
  let sourceInTargetChart :=
    d9PrimitiveSpinCSectionSecondOrderJetInTrivializationChartAt
      period hPeriod choice state source.trivializationIndex
        target.chartAnchor current source.trivialization_mem target.chart_mem
  let targetJet :=
    d9PrimitiveSpinCSectionSecondOrderJetInTrivializationChartAt
      period hPeriod choice state target.trivializationIndex
        target.chartAnchor current target.trivialization_mem target.chart_mem
  let Ainv := fderiv Real
    (throatGaugeBaseChartTransition period hPeriod
      target.chartAnchor source.chartAnchor)
    (extChartAt throatCoverModelWithCorners target.chartAnchor current)
  let Binv := fderiv Real
    (fderiv Real
      (throatGaugeBaseChartTransition period hPeriod
        target.chartAnchor source.chartAnchor))
    (extChartAt throatCoverModelWithCorners target.chartAnchor current)
  let D := d9PrimitiveSpinCCoordChange period hPeriod choice
    source.trivializationIndex target.trivializationIndex current
  let E := fderiv Real
    (d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
      source.trivializationIndex target.trivializationIndex
        target.chartAnchor)
    (extChartAt throatCoverModelWithCorners target.chartAnchor current)
  let F := throatSpinCTargetTrivializationTransitionSecondDerivativeAt
    period hPeriod choice source target
  change throatSpinCSecondOrderJetSemidirectTransportAt period hPeriod choice
    source target sourceJet = targetJet
  have hTrivializations : current ∈
      d9PrimitiveSpinCBaseSet period hPeriod source.trivializationIndex ∩
        d9PrimitiveSpinCBaseSet period hPeriod target.trivializationIndex :=
    ⟨source.trivialization_mem, target.trivialization_mem⟩
  have hSourceValue : sourceInTargetChart.value = sourceJet.value := by
    simp only [sourceInTargetChart, sourceJet,
      d9PrimitiveSpinCSectionSecondOrderJetInTrivializationChartAt_value]
  have hBaseFirst : sourceInTargetChart.firstDerivative =
      sourceJet.firstDerivative.comp Ainv := by
    simpa only [sourceInTargetChart, sourceJet, Ainv] using
      P0EFTJanusProgramPActualThroatSpinCBaseChartSecondOrderJetOverlap4D.d9PrimitiveSpinCSectionSecondOrderJetInTrivializationChartAt_firstDerivative_transition
        period hPeriod choice state source.trivializationIndex
          target.chartAnchor source.chartAnchor current
            source.trivialization_mem target.chart_mem source.chart_mem
  have hBaseSecond (first second : ThroatCoverCoordinates) :
      sourceInTargetChart.secondDerivative first second =
        sourceJet.secondDerivative (Ainv first) (Ainv second) +
          sourceJet.firstDerivative (Binv first second) := by
    simpa only [sourceInTargetChart, sourceJet, Ainv, Binv] using
      P0EFTJanusProgramPActualThroatSpinCBaseChartSecondOrderJetOverlap4D.d9PrimitiveSpinCSectionSecondOrderJetInTrivializationChartAt_secondDerivative_transition_apply
        period hPeriod choice state source.trivializationIndex
          target.chartAnchor source.chartAnchor current
            source.trivialization_mem target.chart_mem source.chart_mem
              first second
  have hFiberValue : targetJet.value = D sourceInTargetChart.value := by
    simpa only [targetJet, sourceInTargetChart, D] using
      d9PrimitiveSpinCSectionSecondOrderJet_arbitraryTrivializationBaseChart_value
        period hPeriod choice state source.trivializationIndex
          target.trivializationIndex target.chartAnchor target.chartAnchor
            current hTrivializations target.chart_mem target.chart_mem
  have hBaseSelfFirst :
      fderiv Real
        (throatGaugeBaseChartTransition period hPeriod
          target.chartAnchor target.chartAnchor)
        (extChartAt throatCoverModelWithCorners target.chartAnchor current) =
      ContinuousLinearMap.id Real ThroatCoverCoordinates := by
    simpa only [
      throatGaugeBaseChartTransitionSecondOrderJetAt_firstDerivative] using
      throatGaugeBaseChartTransitionSecondOrderJetAt_self_firstDerivative
        period hPeriod target.chartAnchor current target.chart_mem
  have hBaseSelfSecond :
      fderiv Real
        (fderiv Real
          (throatGaugeBaseChartTransition period hPeriod
            target.chartAnchor target.chartAnchor))
        (extChartAt throatCoverModelWithCorners target.chartAnchor current) =
      0 := by
    simpa only [
      throatGaugeBaseChartTransitionSecondOrderJetAt_secondDerivative] using
      throatGaugeBaseChartTransitionSecondOrderJetAt_self_secondDerivative
        period hPeriod target.chartAnchor current target.chart_mem
  have hFiberFirst :=
    d9PrimitiveSpinCSectionSecondOrderJet_arbitraryTrivializationBaseChart_firstDerivative_transition
      period hPeriod choice state source.trivializationIndex
        target.trivializationIndex target.chartAnchor target.chartAnchor current
          hTrivializations target.chart_mem target.chart_mem
  have hFiberSecond (first second : ThroatCoverCoordinates) :=
    d9PrimitiveSpinCSectionSecondOrderJet_arbitraryTrivializationBaseChart_secondDerivative_transition_apply
      period hPeriod choice state source.trivializationIndex
        target.trivializationIndex target.chartAnchor target.chartAnchor current
          hTrivializations target.chart_mem target.chart_mem first second
  have hForwardDerivative : DifferentiableAt Real
      (fderiv Real
        (d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
          source.trivializationIndex target.trivializationIndex
            target.chartAnchor))
      (extChartAt throatCoverModelWithCorners target.chartAnchor current) := by
    have hSmooth : ((1 : ℕ∞ω) + 1) ≤ (∞ : ℕ∞ω) := by
      change ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
      exact WithTop.coe_le_coe.mpr le_top
    exact
      ((d9PrimitiveSpinCTransitionCenteredChart_contDiffAt_infty
        period hPeriod choice source.trivializationIndex
          target.trivializationIndex target.chartAnchor current
            hTrivializations target.chart_mem).fderiv_right
              (m := 1) hSmooth).differentiableAt (by norm_num)
  have hFBridge (first second : ThroatCoverCoordinates) :
      fderiv Real
          (fun coordinate ↦ fderiv Real
            (d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
              source.trivializationIndex target.trivializationIndex
                target.chartAnchor) coordinate second)
          (extChartAt throatCoverModelWithCorners target.chartAnchor current)
            first = F first second := by
    simpa only [F,
      throatSpinCTargetTrivializationTransitionSecondDerivativeAt] using
      fderiv_clm_apply_const_apply
        (fderiv Real
          (d9PrimitiveSpinCTransitionCenteredChart period hPeriod choice
            source.trivializationIndex target.trivializationIndex
              target.chartAnchor))
        (extChartAt throatCoverModelWithCorners target.chartAnchor current)
          first second hForwardDerivative
  apply FramedSecondOrderJet.ext_components
  · rw [throatSpinCSecondOrderJetSemidirectTransportAt_value]
    rw [hSourceValue] at hFiberValue
    exact hFiberValue.symm
  · apply ContinuousLinearMap.ext
    intro direction
    rw [throatSpinCSecondOrderJetSemidirectTransportAt_firstDerivative_apply]
    have hApplied := congrArg
      (fun derivative : ThroatCoverCoordinates →L[Real]
          D9DoubledMatterFiber ↦ derivative direction) hFiberFirst
    have hBaseApplied := congrArg
      (fun derivative : ThroatCoverCoordinates →L[Real]
          D9DoubledMatterFiber ↦ derivative direction) hBaseFirst
    simp only [hBaseSelfFirst, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, add_apply,
      ContinuousLinearMap.flip_apply] at hApplied
    simp only [ContinuousLinearMap.comp_apply] at hBaseApplied
    rw [hBaseApplied, hSourceValue] at hApplied
    simpa only [sourceJet, Ainv, D, E] using hApplied.symm
  · apply ContinuousLinearMap.ext
    intro first
    apply ContinuousLinearMap.ext
    intro second
    rw [throatSpinCSecondOrderJetSemidirectTransportAt_secondDerivative_apply]
    have hSecond := hFiberSecond first second
    simp only [hBaseSelfFirst, hBaseSelfSecond,
      ContinuousLinearMap.id_apply, zero_apply, map_zero, add_zero] at hSecond
    have hBaseFirstAppliedFirst := congrArg
      (fun derivative : ThroatCoverCoordinates →L[Real]
          D9DoubledMatterFiber ↦ derivative first) hBaseFirst
    have hBaseFirstAppliedSecond := congrArg
      (fun derivative : ThroatCoverCoordinates →L[Real]
          D9DoubledMatterFiber ↦ derivative second) hBaseFirst
    simp only [ContinuousLinearMap.comp_apply] at hBaseFirstAppliedFirst
    simp only [ContinuousLinearMap.comp_apply] at hBaseFirstAppliedSecond
    rw [hBaseSecond first second, hBaseFirstAppliedFirst,
      hBaseFirstAppliedSecond, hSourceValue, hFBridge first second] at hSecond
    simp only [map_add] at hSecond
    simpa only [sourceJet, Ainv, Binv, D, E, F] using hSecond.symm

/-- Physical primitive SpinC matter is the canonical specialization of the
generic compatibility theorem. -/
theorem globalGaugeFixedSpinCMatterSecondOrderJetSemidirectTransportAt_extracted
    {current : EffectiveThroat period hPeriod}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (sector : Sector)
    (source target :
      ThroatSpinCSecondOrderJetTrivializationChartAt
        period hPeriod current) :
    throatSpinCSecondOrderJetSemidirectTransportAt period hPeriod
        .positiveQuarter source target
        (globalGaugeFixedSpinCMatterSecondOrderJetInTrivializationChartAt
          period hPeriod configuration sector source.trivializationIndex
            source.chartAnchor current source.trivialization_mem
              source.chart_mem) =
      globalGaugeFixedSpinCMatterSecondOrderJetInTrivializationChartAt
        period hPeriod configuration sector target.trivializationIndex
          target.chartAnchor current target.trivialization_mem
            target.chart_mem :=
  throatSpinCSecondOrderJetSemidirectTransportAt_extracted period hPeriod
    .positiveQuarter (configuration.physical.spinCMatter sector) source target

end
end P0EFTJanusProgramPActualThroatSpinCSecondOrderJetSemidirectTransportCompatibility4D
end JanusFormal
