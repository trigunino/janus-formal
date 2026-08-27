import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeSecondOrderJetSemidirectTransportCompatibility4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeSecondOrderJetDirectTargetUniqueness4D

/-!
# Groupoid laws for the semidirect throat-gauge second-jet transport

Direct compatibility and fixed-target uniqueness imply the identity,
composition and inverse laws for the concrete continuous-linear transport.
This avoids a second expansion of the value, Jacobian and Hessian formulas.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatGaugeSecondOrderJetSemidirectTransportGroupoid4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 600000

noncomputable section

open scoped Manifold ContDiff RealInnerProductSpace Topology
open Bundle
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetPresentationSetoid4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetPresentationDirectReflexivity4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetPresentationDirectTransitivity4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetSemidirectTransport4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetSemidirectTransportCompatibility4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetDirectTargetUniqueness4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev GaugeJet :=
  FramedSecondOrderJet ThroatCoverCoordinates
    (FramedCovector ThroatCoverCoordinates)

private abbrev GaugePresentationAt
    (current : EffectiveThroat period hPeriod) :=
  ThroatGaugeSecondOrderJetPresentationAt period hPeriod current

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-- Transport from a presentation to itself fixes every raw jet. -/
@[simp]
theorem throatGaugeSecondOrderJetSemidirectTransportAt_self_apply
    {current : EffectiveThroat period hPeriod}
    (presentation : GaugePresentationAt period hPeriod current)
    (jet : GaugeJet) :
    throatGaugeSecondOrderJetSemidirectTransportAt period hPeriod
      presentation presentation jet = jet := by
  let source : GaugePresentationAt period hPeriod current :=
    targetPresentationAt period hPeriod presentation.frameAnchor
      presentation.chartAnchor current presentation.frame_mem
        presentation.chart_mem jet
  have hTransport :=
    throatGaugeSecondOrderJetSemidirectTargetPresentationAt_directCompatible
      period hPeriod source source
  have hRefl := directTransitionCompatible_refl period hPeriod source
  have hUnique := directTransitionCompatible_target_jet_unique period hPeriod
    source source.frameAnchor source.chartAnchor
      source.frame_mem source.frame_mem source.chart_mem source.chart_mem
      (throatGaugeSecondOrderJetSemidirectTransportAt period hPeriod
        source source source.jet) source.jet
      (by
        simpa [targetPresentationAt,
          throatGaugeSecondOrderJetSemidirectTargetPresentationAt] using
            hTransport)
      (by simpa [targetPresentationAt] using hRefl)
  simpa [source, targetPresentationAt,
    throatGaugeSecondOrderJetSemidirectTransportAt,
    throatGaugeSecondOrderJetSemidirectChangeAt,
    throatGaugeCovectorTargetTransitionSecondDerivativeAt] using hUnique

/-- Self-transport is the identity continuous linear map. -/
@[simp]
theorem throatGaugeSecondOrderJetSemidirectTransportAt_self
    {current : EffectiveThroat period hPeriod}
    (presentation : GaugePresentationAt period hPeriod current) :
    throatGaugeSecondOrderJetSemidirectTransportAt period hPeriod
        presentation presentation =
      ContinuousLinearMap.id Real GaugeJet := by
  apply ContinuousLinearMap.ext
  intro jet
  exact throatGaugeSecondOrderJetSemidirectTransportAt_self_apply
    period hPeriod presentation jet

/-- Transport through an intermediate presentation equals direct transport,
pointwise on raw jets. -/
theorem throatGaugeSecondOrderJetSemidirectTransportAt_comp_apply
    {current : EffectiveThroat period hPeriod}
    (first middle last : GaugePresentationAt period hPeriod current)
    (jet : GaugeJet) :
    throatGaugeSecondOrderJetSemidirectTransportAt period hPeriod
        first last jet =
      throatGaugeSecondOrderJetSemidirectTransportAt period hPeriod
        middle last
        (throatGaugeSecondOrderJetSemidirectTransportAt period hPeriod
          first middle jet) := by
  let source : GaugePresentationAt period hPeriod current :=
    targetPresentationAt period hPeriod first.frameAnchor first.chartAnchor
      current first.frame_mem first.chart_mem jet
  let middleTemplate : GaugePresentationAt period hPeriod current :=
    targetPresentationAt period hPeriod middle.frameAnchor middle.chartAnchor
      current middle.frame_mem middle.chart_mem middle.jet
  let lastTemplate : GaugePresentationAt period hPeriod current :=
    targetPresentationAt period hPeriod last.frameAnchor last.chartAnchor
      current last.frame_mem last.chart_mem last.jet
  let middleTransport : GaugePresentationAt period hPeriod current :=
    throatGaugeSecondOrderJetSemidirectTargetPresentationAt period hPeriod
      source middleTemplate
  let iteratedTransport : GaugePresentationAt period hPeriod current :=
    throatGaugeSecondOrderJetSemidirectTargetPresentationAt period hPeriod
      middleTransport lastTemplate
  let directTransport : GaugePresentationAt period hPeriod current :=
    throatGaugeSecondOrderJetSemidirectTargetPresentationAt period hPeriod
      source lastTemplate
  have hSourceMiddle :
      DirectTransitionCompatible period hPeriod source middleTransport := by
    exact
      throatGaugeSecondOrderJetSemidirectTargetPresentationAt_directCompatible
        period hPeriod source middleTemplate
  have hMiddleLast :
      DirectTransitionCompatible period hPeriod middleTransport
        iteratedTransport := by
    exact
      throatGaugeSecondOrderJetSemidirectTargetPresentationAt_directCompatible
        period hPeriod middleTransport lastTemplate
  have hIterated :
      DirectTransitionCompatible period hPeriod source iteratedTransport :=
    directTransitionCompatible_trans period hPeriod hSourceMiddle hMiddleLast
  have hDirect :
      DirectTransitionCompatible period hPeriod source directTransport := by
    exact
      throatGaugeSecondOrderJetSemidirectTargetPresentationAt_directCompatible
        period hPeriod source lastTemplate
  have hUnique := directTransitionCompatible_target_jet_unique period hPeriod
    source lastTemplate.frameAnchor lastTemplate.chartAnchor
      directTransport.frame_mem iteratedTransport.frame_mem
      directTransport.chart_mem iteratedTransport.chart_mem
      directTransport.jet iteratedTransport.jet
      (by
        simpa [directTransport,
          throatGaugeSecondOrderJetSemidirectTargetPresentationAt,
          targetPresentationAt] using hDirect)
      (by
        simpa [iteratedTransport, middleTransport,
          throatGaugeSecondOrderJetSemidirectTargetPresentationAt,
          targetPresentationAt] using hIterated)
  simpa [source, middleTemplate, lastTemplate, middleTransport,
    iteratedTransport, directTransport, targetPresentationAt,
    throatGaugeSecondOrderJetSemidirectTargetPresentationAt,
    throatGaugeSecondOrderJetSemidirectTransportAt,
    throatGaugeSecondOrderJetSemidirectChangeAt,
    throatGaugeCovectorTargetTransitionSecondDerivativeAt] using hUnique

/-- Semidirect transport composes exactly through any intermediate
presentation. -/
theorem throatGaugeSecondOrderJetSemidirectTransportAt_comp
    {current : EffectiveThroat period hPeriod}
    (first middle last : GaugePresentationAt period hPeriod current) :
    throatGaugeSecondOrderJetSemidirectTransportAt period hPeriod
        first last =
      (throatGaugeSecondOrderJetSemidirectTransportAt period hPeriod
        middle last).comp
        (throatGaugeSecondOrderJetSemidirectTransportAt period hPeriod
          first middle) := by
  apply ContinuousLinearMap.ext
  intro jet
  exact throatGaugeSecondOrderJetSemidirectTransportAt_comp_apply
    period hPeriod first middle last jet

/-- Reverse transport is a left inverse. -/
theorem throatGaugeSecondOrderJetSemidirectTransportAt_inverse_comp
    {current : EffectiveThroat period hPeriod}
    (source target : GaugePresentationAt period hPeriod current) :
    (throatGaugeSecondOrderJetSemidirectTransportAt period hPeriod
        target source).comp
        (throatGaugeSecondOrderJetSemidirectTransportAt period hPeriod
          source target) =
      ContinuousLinearMap.id Real GaugeJet := by
  rw [← throatGaugeSecondOrderJetSemidirectTransportAt_comp
    period hPeriod source target source]
  exact throatGaugeSecondOrderJetSemidirectTransportAt_self
    period hPeriod source

/-- Reverse transport is a right inverse. -/
theorem throatGaugeSecondOrderJetSemidirectTransportAt_comp_inverse
    {current : EffectiveThroat period hPeriod}
    (source target : GaugePresentationAt period hPeriod current) :
    (throatGaugeSecondOrderJetSemidirectTransportAt period hPeriod
        source target).comp
        (throatGaugeSecondOrderJetSemidirectTransportAt period hPeriod
          target source) =
      ContinuousLinearMap.id Real GaugeJet := by
  exact throatGaugeSecondOrderJetSemidirectTransportAt_inverse_comp
    period hPeriod target source

end
end P0EFTJanusProgramPActualThroatGaugeSecondOrderJetSemidirectTransportGroupoid4D
end JanusFormal
