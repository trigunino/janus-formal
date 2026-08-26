import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatMetricBaseChartSecondOrderJetOverlap4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatCovariantTwoTensorSecondOrderFrameOverlap4D

/-!
# Arbitrary frame and base-chart overlap for throat metric second jets

Both the tangent frame and the extended base chart may change.  The same-chart
covariant rank-two frame law composes with the fixed-frame base-chart chain
rule to give the exact germ and value, first-derivative and second-derivative
laws between arbitrary valid frame--chart pairs.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatMetricArbitraryFrameBaseChartSecondOrderJetOverlap4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 600000

noncomputable section

open Set Filter
open scoped Manifold ContDiff RealInnerProductSpace Topology
open Bundle
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionGerm4D
open P0EFTJanusProgramPActualThroatMetricArbitraryFrameChartSecondOrderJetExtraction4D
open P0EFTJanusProgramPActualThroatMetricBaseChartSecondOrderJetOverlap4D
open P0EFTJanusProgramPActualThroatCovariantTwoTensorSecondOrderFrameOverlap4D

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev TensorModel :=
  FramedCovariantTwoTensor ThroatCoverCoordinates

private abbrev TensorEnd := TensorModel →L[Real] TensorModel

local instance tensorModelNormedAddCommGroup :
    NormedAddCommGroup TensorModel :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance tensorModelNormedSpace : NormedSpace Real TensorModel :=
  ContinuousLinearMap.toNormedSpace

local instance tensorEndNormedAddCommGroup : NormedAddCommGroup TensorEnd :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance tensorEndNormedSpace : NormedSpace Real TensorEnd :=
  ContinuousLinearMap.toNormedSpace

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-! ## Arbitrary frame--chart germ -/

/-- Changing frame in `firstCenter` and then changing base chart gives the
target tensor representative as an exact germ. -/
theorem throatTensorFrameChartRepresentative_arbitraryFrameBaseChartTransition_eventuallyEq
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (firstAnchor secondAnchor firstCenter secondCenter current :
      EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) firstAnchor).baseSet ∩
        (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) secondAnchor).baseSet)
    (hFirst : current ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : current ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source) :
    (fun coordinate ↦
      throatCovariantTwoTensorTransitionCenteredChart period hPeriod
          firstAnchor secondAnchor firstCenter coordinate
        (throatTensorFrameChartRepresentative period hPeriod tensor
          firstAnchor firstCenter coordinate)) =ᶠ[nhds
            (extChartAt throatCoverModelWithCorners firstCenter current)]
      (throatTensorFrameChartRepresentative period hPeriod tensor
          secondAnchor secondCenter) ∘
        throatGaugeBaseChartTransition period hPeriod
          firstCenter secondCenter := by
  exact
    (throatTensorFrameChartRepresentative_frameTransition_eventuallyEq
      period hPeriod tensor firstAnchor secondAnchor firstCenter current
        hCurrent hFirst).trans
    (throatTensorFrameChartRepresentative_baseChartTransition_eventuallyEq
      period hPeriod tensor secondAnchor firstCenter secondCenter current
        hFirst hSecond)

/-! ## Exact arbitrary frame--chart jet laws -/

/-- The target value is the exact covariant rank-two transport of the source
value, independently of the chosen base charts. -/
theorem throatTensorSecondOrderJet_arbitraryFrameBaseChart_value
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (firstAnchor secondAnchor firstCenter secondCenter current :
      EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) firstAnchor).baseSet ∩
        (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) secondAnchor).baseSet)
    (hFirst : current ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : current ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source) :
    (throatTensorSecondOrderJetInFrameChartAt period hPeriod tensor
      secondAnchor secondCenter current hCurrent.2 hSecond).value =
      throatCovariantTwoTensorFrameTransitionAt period hPeriod
        firstAnchor secondAnchor current
        (throatTensorSecondOrderJetInFrameChartAt period hPeriod tensor
          firstAnchor firstCenter current hCurrent.1 hFirst).value := by
  rw [throatTensorSecondOrderJetInFrameChartAt_value,
    throatTensorSecondOrderJetInFrameChartAt_value]
  exact throatTensorCoordinates_eq_frameTransition period hPeriod tensor
    firstAnchor secondAnchor current hCurrent

/-- Arbitrary frame--chart first-order law: the target derivative pulled back
by the base-chart Jacobian equals the varying-frame Leibniz expression. -/
theorem throatTensorSecondOrderJet_arbitraryFrameBaseChart_firstDerivative_transition
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (firstAnchor secondAnchor firstCenter secondCenter current :
      EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) firstAnchor).baseSet ∩
        (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) secondAnchor).baseSet)
    (hFirst : current ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : current ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source) :
    (throatTensorSecondOrderJetInFrameChartAt period hPeriod tensor
      secondAnchor secondCenter current hCurrent.2 hSecond).firstDerivative.comp
        (fderiv Real
          (throatGaugeBaseChartTransition period hPeriod firstCenter secondCenter)
          (extChartAt throatCoverModelWithCorners firstCenter current)) =
      (throatCovariantTwoTensorFrameTransitionAt period hPeriod
          firstAnchor secondAnchor current : TensorEnd).comp
        (throatTensorSecondOrderJetInFrameChartAt period hPeriod tensor
          firstAnchor firstCenter current hCurrent.1 hFirst).firstDerivative +
      (fderiv Real
        (throatCovariantTwoTensorTransitionCenteredChart period hPeriod
          firstAnchor secondAnchor firstCenter)
        (extChartAt throatCoverModelWithCorners firstCenter current)).flip
          (throatTensorSecondOrderJetInFrameChartAt period hPeriod tensor
            firstAnchor firstCenter current hCurrent.1 hFirst).value := by
  have hBase :=
    throatTensorSecondOrderJetInFrameChartAt_firstDerivative_transition
      period hPeriod tensor secondAnchor firstCenter secondCenter current
        hCurrent.2 hFirst hSecond
  exact hBase.symm.trans
    (throatTensorSecondOrderJetInFrameChartAt_firstDerivative_frame_transition
      period hPeriod tensor firstAnchor secondAnchor firstCenter current
        hCurrent hFirst)

/-- Arbitrary frame--chart second-order law. The base-chart Hessian terms on
the left equal the full four-term covariant frame expression on the right. -/
theorem throatTensorSecondOrderJet_arbitraryFrameBaseChart_secondDerivative_transition_apply
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (firstAnchor secondAnchor firstCenter secondCenter current :
      EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) firstAnchor).baseSet ∩
        (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) secondAnchor).baseSet)
    (hFirst : current ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : current ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source)
    (first second : ThroatCoverCoordinates) :
    (throatTensorSecondOrderJetInFrameChartAt period hPeriod tensor
      secondAnchor secondCenter current hCurrent.2 hSecond).secondDerivative
        (fderiv Real
          (throatGaugeBaseChartTransition period hPeriod firstCenter secondCenter)
          (extChartAt throatCoverModelWithCorners firstCenter current) first)
        (fderiv Real
          (throatGaugeBaseChartTransition period hPeriod firstCenter secondCenter)
          (extChartAt throatCoverModelWithCorners firstCenter current) second) +
      (throatTensorSecondOrderJetInFrameChartAt period hPeriod tensor
        secondAnchor secondCenter current hCurrent.2 hSecond).firstDerivative
          (fderiv Real
            (fderiv Real
              (throatGaugeBaseChartTransition period hPeriod
                firstCenter secondCenter))
            (extChartAt throatCoverModelWithCorners firstCenter current)
              first second) =
      throatCovariantTwoTensorFrameTransitionAt period hPeriod
        firstAnchor secondAnchor current
        ((throatTensorSecondOrderJetInFrameChartAt period hPeriod tensor
          firstAnchor firstCenter current hCurrent.1 hFirst).secondDerivative
            first second) +
      fderiv Real
          (throatCovariantTwoTensorTransitionCenteredChart period hPeriod
            firstAnchor secondAnchor firstCenter)
          (extChartAt throatCoverModelWithCorners firstCenter current) first
        ((throatTensorSecondOrderJetInFrameChartAt period hPeriod tensor
          firstAnchor firstCenter current hCurrent.1 hFirst).firstDerivative
            second) +
      fderiv Real
          (throatCovariantTwoTensorTransitionCenteredChart period hPeriod
            firstAnchor secondAnchor firstCenter)
          (extChartAt throatCoverModelWithCorners firstCenter current) second
        ((throatTensorSecondOrderJetInFrameChartAt period hPeriod tensor
          firstAnchor firstCenter current hCurrent.1 hFirst).firstDerivative
            first) +
      fderiv Real
          (fun coordinate ↦
            fderiv Real
              (throatCovariantTwoTensorTransitionCenteredChart period hPeriod
                firstAnchor secondAnchor firstCenter) coordinate second)
          (extChartAt throatCoverModelWithCorners firstCenter current) first
        ((throatTensorSecondOrderJetInFrameChartAt period hPeriod tensor
          firstAnchor firstCenter current hCurrent.1 hFirst).value) := by
  have hBase :=
    throatTensorSecondOrderJetInFrameChartAt_secondDerivative_transition_apply
      period hPeriod tensor secondAnchor firstCenter secondCenter current
        hCurrent.2 hFirst hSecond first second
  exact hBase.symm.trans
    (throatTensorSecondOrderJetInFrameChartAt_secondDerivative_frame_transition_apply
      period hPeriod tensor firstAnchor secondAnchor firstCenter current
        hCurrent hFirst first second)

end
end P0EFTJanusProgramPActualThroatMetricArbitraryFrameBaseChartSecondOrderJetOverlap4D
end JanusFormal
