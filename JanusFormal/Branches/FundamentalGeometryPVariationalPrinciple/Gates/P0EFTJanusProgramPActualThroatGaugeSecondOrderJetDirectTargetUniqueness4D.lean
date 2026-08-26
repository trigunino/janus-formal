import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeSecondOrderJetPresentationDirectSetoid4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionJacobianEquiv4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFramedSecondOrderJetNormedSpace4D

/-!
# Uniqueness of the target second jet under a direct transition

For a fixed source presentation and fixed target frame and chart anchors, the
value, Jacobian and Hessian transition equations determine the target framed
second jet uniquely.  The proof uses the invertibility of the target base-chart
Jacobian and is independent of the chosen membership proofs.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatGaugeSecondOrderJetDirectTargetUniqueness4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000

noncomputable section

open scoped Manifold ContDiff RealInnerProductSpace Topology
open Bundle
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionGerm4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetPresentationSetoid4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetPresentationDirectSetoid4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionJacobianEquiv4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-! ## Fixed-anchor target template -/

/-- A target presentation with explicit membership witnesses. -/
def targetPresentationAt
    (frameAnchor chartAnchor current : EffectiveThroat period hPeriod)
    (hFrame : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) frameAnchor).baseSet)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source)
    (jet : FramedSecondOrderJet ThroatCoverCoordinates
      (FramedCovector ThroatCoverCoordinates)) :
    ThroatGaugeSecondOrderJetPresentationAt period hPeriod current where
  frameAnchor := frameAnchor
  chartAnchor := chartAnchor
  frame_mem := hFrame
  chart_mem := hChart
  jet := jet

@[simp]
theorem targetPresentationAt_jet
    (frameAnchor chartAnchor current : EffectiveThroat period hPeriod)
    (hFrame : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) frameAnchor).baseSet)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source)
    (jet : FramedSecondOrderJet ThroatCoverCoordinates
      (FramedCovector ThroatCoverCoordinates)) :
    (targetPresentationAt period hPeriod frameAnchor chartAnchor current
      hFrame hChart jet).jet = jet :=
  rfl

/-! ## Target uniqueness -/

/-- A direct transition from a fixed source uniquely determines the target
framed second jet once the target frame and chart anchors are fixed. -/
theorem directTransitionCompatible_target_jet_unique
    {current : EffectiveThroat period hPeriod}
    (source :
      ThroatGaugeSecondOrderJetPresentationAt period hPeriod current)
    (targetFrame targetChart : EffectiveThroat period hPeriod)
    (hFirstFrame hSecondFrame : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) targetFrame).baseSet)
    (hFirstChart hSecondChart : current ∈
      (extChartAt throatCoverModelWithCorners targetChart).source)
    (firstJet secondJet : FramedSecondOrderJet ThroatCoverCoordinates
      (FramedCovector ThroatCoverCoordinates))
    (hFirst : DirectTransitionCompatible period hPeriod source
      (targetPresentationAt period hPeriod targetFrame targetChart current
        hFirstFrame hFirstChart firstJet))
    (hSecond : DirectTransitionCompatible period hPeriod source
      (targetPresentationAt period hPeriod targetFrame targetChart current
        hSecondFrame hSecondChart secondJet)) :
    firstJet = secondJet := by
  let baseFirst : ThroatCoverCoordinates →L[Real] ThroatCoverCoordinates :=
    fderiv Real
      (throatGaugeBaseChartTransition period hPeriod
        source.chartAnchor targetChart)
      (extChartAt throatCoverModelWithCorners source.chartAnchor current)
  have hBaseFirstSurjective : Function.Surjective baseFirst := by
    let baseEquiv :=
      throatGaugeBaseChartTransitionJacobianEquivAt period hPeriod
        source.chartAnchor targetChart current source.chart_mem hFirstChart
    intro direction
    obtain ⟨preimage, hPreimage⟩ := baseEquiv.surjective direction
    refine ⟨preimage, ?_⟩
    simpa only [baseEquiv, baseFirst,
      throatGaugeBaseChartTransitionJacobianEquivAt_apply] using hPreimage
  have hValue : firstJet.value = secondJet.value := by
    exact hFirst.value_transition.trans hSecond.value_transition.symm
  have hFirstComp :
      firstJet.firstDerivative.comp baseFirst =
        secondJet.firstDerivative.comp baseFirst := by
    simpa only [targetPresentationAt, baseFirst] using
      hFirst.firstDerivative_transition.trans
        hSecond.firstDerivative_transition.symm
  have hFirstDerivative :
      firstJet.firstDerivative = secondJet.firstDerivative := by
    apply ContinuousLinearMap.ext
    intro direction
    obtain ⟨preimage, rfl⟩ := hBaseFirstSurjective direction
    exact congrArg
      (fun map : ThroatCoverCoordinates →L[Real]
          FramedCovector ThroatCoverCoordinates => map preimage)
      hFirstComp
  have hSecondDerivative :
      firstJet.secondDerivative = secondJet.secondDerivative := by
    apply ContinuousLinearMap.ext
    intro firstDirection
    apply ContinuousLinearMap.ext
    intro secondDirection
    obtain ⟨firstPreimage, rfl⟩ :=
      hBaseFirstSurjective firstDirection
    obtain ⟨secondPreimage, rfl⟩ :=
      hBaseFirstSurjective secondDirection
    have hAt :=
      (hFirst.secondDerivative_transition firstPreimage secondPreimage).trans
        (hSecond.secondDerivative_transition
          firstPreimage secondPreimage).symm
    change
      firstJet.secondDerivative
          (baseFirst firstPreimage) (baseFirst secondPreimage) +
          firstJet.firstDerivative
            (fderiv Real
              (fderiv Real
                (throatGaugeBaseChartTransition period hPeriod
                  source.chartAnchor targetChart))
              (extChartAt throatCoverModelWithCorners
                source.chartAnchor current) firstPreimage secondPreimage) =
        secondJet.secondDerivative
          (baseFirst firstPreimage) (baseFirst secondPreimage) +
          secondJet.firstDerivative
            (fderiv Real
              (fderiv Real
                (throatGaugeBaseChartTransition period hPeriod
                  source.chartAnchor targetChart))
              (extChartAt throatCoverModelWithCorners
                source.chartAnchor current) firstPreimage secondPreimage)
      at hAt
    rw [hFirstDerivative] at hAt
    exact add_right_cancel hAt
  exact FramedSecondOrderJet.ext_components ThroatCoverCoordinates
    (FramedCovector ThroatCoverCoordinates) hValue hFirstDerivative
      hSecondDerivative

end
end P0EFTJanusProgramPActualThroatGaugeSecondOrderJetDirectTargetUniqueness4D
end JanusFormal
