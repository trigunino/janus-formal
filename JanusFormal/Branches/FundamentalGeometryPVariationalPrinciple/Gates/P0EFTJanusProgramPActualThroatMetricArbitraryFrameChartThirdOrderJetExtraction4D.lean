import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatMetricArbitraryFrameChartSecondOrderJetExtraction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPhysicalThirdOrderJetChartwiseExtraction4D

/-!
# Actual throat metric third jets in arbitrary frames and charts

The existing arbitrary-frame/chart second jet of a genuine smooth throat
tensor is extended by its genuine third Frechet derivative.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatMetricArbitraryFrameChartThirdOrderJetExtraction4D

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
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPFramedThirdOrderJetConstantFiberBaseChange4D
open P0EFTJanusProgramPPhysicalThirdOrderJetChartwiseExtraction4D
open P0EFTJanusProgramPGlobalMetricChartwiseSecondOrderJetExtraction4D
open P0EFTJanusProgramPActualThroatMetricArbitraryFrameChartSecondOrderJetExtraction4D

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev TensorModel :=
  ThroatCovariantTwoTensorModel

local instance tensorModelNormedAddCommGroup :
    NormedAddCommGroup TensorModel :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance tensorModelNormedSpace : NormedSpace Real TensorModel :=
  ContinuousLinearMap.toNormedSpace

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-- The genuine third jet of a smooth intrinsic tensor in arbitrary valid
frame and chart choices. -/
def throatTensorThirdOrderJetInFrameChartAt
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (frameAnchor chartAnchor current : EffectiveThroat period hPeriod)
    (hFrame : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) frameAnchor).baseSet)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source) :
    FramedThirdOrderJet ThroatCoverCoordinates TensorModel :=
  chartwiseThirdOrderJetAt
    (throatTensorFrameChartRepresentative period hPeriod tensor
      frameAnchor chartAnchor)
    (extChartAt throatCoverModelWithCorners chartAnchor current)
    ((throatTensorFrameChartRepresentative_contDiffAt_infty
      period hPeriod tensor frameAnchor chartAnchor current hFrame hChart).of_le
        (by
          change ((3 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
          exact WithTop.coe_le_coe.mpr le_top))

/-- Forgetting the third derivative recovers the existing metric second-jet
extraction definitionally. -/
@[simp]
theorem throatTensorThirdOrderJetInFrameChartAt_truncate
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (frameAnchor chartAnchor current : EffectiveThroat period hPeriod)
    (hFrame : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) frameAnchor).baseSet)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source) :
    (throatTensorThirdOrderJetInFrameChartAt period hPeriod tensor frameAnchor
      chartAnchor current hFrame hChart).toFramedSecondOrderJet =
      throatTensorSecondOrderJetInFrameChartAt period hPeriod tensor frameAnchor
        chartAnchor current hFrame hChart :=
  rfl

@[simp]
theorem throatTensorThirdOrderJetInFrameChartAt_value
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (frameAnchor chartAnchor current : EffectiveThroat period hPeriod)
    (hFrame : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) frameAnchor).baseSet)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source) :
    (throatTensorThirdOrderJetInFrameChartAt period hPeriod tensor frameAnchor
      chartAnchor current hFrame hChart).value =
      throatTensorCoordinates period hPeriod tensor frameAnchor current :=
  throatTensorSecondOrderJetInFrameChartAt_value period hPeriod tensor
    frameAnchor chartAnchor current hFrame hChart

@[simp]
theorem throatTensorThirdOrderJetInFrameChartAt_firstDerivative
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (frameAnchor chartAnchor current : EffectiveThroat period hPeriod)
    (hFrame : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) frameAnchor).baseSet)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source) :
    (throatTensorThirdOrderJetInFrameChartAt period hPeriod tensor frameAnchor
      chartAnchor current hFrame hChart).firstDerivative =
      fderiv Real
        (throatTensorFrameChartRepresentative period hPeriod tensor
          frameAnchor chartAnchor)
        (extChartAt throatCoverModelWithCorners chartAnchor current) :=
  rfl

@[simp]
theorem throatTensorThirdOrderJetInFrameChartAt_secondDerivative
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (frameAnchor chartAnchor current : EffectiveThroat period hPeriod)
    (hFrame : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) frameAnchor).baseSet)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source) :
    (throatTensorThirdOrderJetInFrameChartAt period hPeriod tensor frameAnchor
      chartAnchor current hFrame hChart).secondDerivative =
      fderiv Real
        (fderiv Real
          (throatTensorFrameChartRepresentative period hPeriod tensor
            frameAnchor chartAnchor))
        (extChartAt throatCoverModelWithCorners chartAnchor current) :=
  rfl

@[simp]
theorem throatTensorThirdOrderJetInFrameChartAt_thirdDerivative
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (frameAnchor chartAnchor current : EffectiveThroat period hPeriod)
    (hFrame : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) frameAnchor).baseSet)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source) :
    (throatTensorThirdOrderJetInFrameChartAt period hPeriod tensor frameAnchor
      chartAnchor current hFrame hChart).thirdDerivative =
      fderiv Real
        (fderiv Real
          (fderiv Real
            (throatTensorFrameChartRepresentative period hPeriod tensor
              frameAnchor chartAnchor)))
        (extChartAt throatCoverModelWithCorners chartAnchor current) :=
  rfl

/-- Actual induced metric third jet in arbitrary valid frame and chart
choices. -/
def globalGaugeFixedThroatMetricThirdOrderJetInFrameChartAt
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (sector : Sector)
    (frameAnchor chartAnchor current : EffectiveThroat period hPeriod)
    (hFrame : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) frameAnchor).baseSet)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source) :
    FramedThirdOrderJet ThroatCoverCoordinates TensorModel :=
  throatTensorThirdOrderJetInFrameChartAt period hPeriod
    (globalGaugeFixedInducedMetricBySector period hPeriod configuration sector)
    frameAnchor chartAnchor current hFrame hChart

/-- Physical metric third-jet extraction truncates to the existing physical
second-jet extraction. -/
@[simp]
theorem globalGaugeFixedThroatMetricThirdOrderJetInFrameChartAt_truncate
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (sector : Sector)
    (frameAnchor chartAnchor current : EffectiveThroat period hPeriod)
    (hFrame : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) frameAnchor).baseSet)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source) :
    (globalGaugeFixedThroatMetricThirdOrderJetInFrameChartAt period hPeriod
      configuration sector frameAnchor chartAnchor current hFrame
        hChart).toFramedSecondOrderJet =
      globalGaugeFixedThroatMetricSecondOrderJetInFrameChartAt period hPeriod
        configuration sector frameAnchor chartAnchor current hFrame hChart :=
  rfl

/-- At centered frame and base charts, truncation recovers the previous
centered physical metric second jet. -/
@[simp]
theorem globalGaugeFixedThroatMetricThirdOrderJetInFrameChartAt_diagonal_truncate
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (sector : Sector)
    (anchor : EffectiveThroat period hPeriod) :
    (globalGaugeFixedThroatMetricThirdOrderJetInFrameChartAt period hPeriod
      configuration sector anchor anchor anchor
        (FiberBundle.mem_baseSet_trivializationAt' anchor)
        (mem_extChartAt_source anchor)).toFramedSecondOrderJet =
      globalGaugeFixedThroatMetricSecondOrderJetAt period hPeriod
        configuration sector anchor :=
  rfl

end
end P0EFTJanusProgramPActualThroatMetricArbitraryFrameChartThirdOrderJetExtraction4D
end JanusFormal
