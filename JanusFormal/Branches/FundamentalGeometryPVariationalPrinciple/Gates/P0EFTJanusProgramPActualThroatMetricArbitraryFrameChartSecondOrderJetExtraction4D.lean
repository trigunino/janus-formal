import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalMetricChartwiseSecondOrderJetExtraction4D

/-!
# Actual throat metric second jets in arbitrary frames and charts

An intrinsic smooth throat tensor is read in an independently selected
tangent trivialization and extended base chart.  This supplies its genuine
second jet at every point where both choices are valid.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatMetricArbitraryFrameChartSecondOrderJetExtraction4D

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
open P0EFTJanusProgramPPhysicalSecondOrderJetChartwiseExtraction4D
open P0EFTJanusProgramPGlobalMetricChartwiseSecondOrderJetExtraction4D

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

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

/-- Tensor coefficients in a fixed tangent frame are smooth throughout that
frame's trivialization domain. -/
theorem throatTensorCoordinates_contMDiffOn_frameBaseSet
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (frameAnchor : EffectiveThroat period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      (modelWithCornersSelf Real ThroatCovariantTwoTensorModel) ∞
      (fun current ↦
        ContinuousLinearMap.inCoordinates ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod)
          (ThroatCoverCoordinates →L[Real] Real)
          (ThroatCotangentFiber period hPeriod)
          frameAnchor current frameAnchor current (tensor.tensor current))
      ((trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) frameAnchor).baseSet) := by
  intro current hCurrent
  let tensorTrivialization :=
    trivializationAt ThroatCovariantTwoTensorModel
      (ThroatCovariantTwoTensorFiber period hPeriod) frameAnchor
  have hTensorBase : current ∈ tensorTrivialization.baseSet := by
    simp only [tensorTrivialization, hom_trivializationAt_baseSet]
    exact ⟨hCurrent, ⟨hCurrent, Set.mem_univ current⟩⟩
  have hCoordinates :=
    (tensorTrivialization.contMDiffAt_section_iff hTensorBase).mp
      (tensor.tensor.contMDiff current)
  have hCoordinates' : ContMDiffAt throatCoverModelWithCorners
      (modelWithCornersSelf Real ThroatCovariantTwoTensorModel) ∞
      (fun nearby ↦
        ContinuousLinearMap.inCoordinates ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod)
          (ThroatCoverCoordinates →L[Real] Real)
          (ThroatCotangentFiber period hPeriod)
          frameAnchor nearby frameAnchor nearby (tensor.tensor nearby))
      current := by
    simpa only [tensorTrivialization, hom_trivializationAt_apply] using hCoordinates
  exact hCoordinates'.contMDiffWithinAt

/-- The same `C∞` coefficient family restricted to one frame/chart patch. -/
theorem throatTensorCoordinates_contMDiffOn_frameChartBaseSet
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (frameAnchor chartAnchor : EffectiveThroat period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      (modelWithCornersSelf Real ThroatCovariantTwoTensorModel) ∞
      (fun current ↦
        ContinuousLinearMap.inCoordinates ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod)
          (ThroatCoverCoordinates →L[Real] Real)
          (ThroatCotangentFiber period hPeriod)
          frameAnchor current frameAnchor current (tensor.tensor current))
      ((trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) frameAnchor).baseSet ∩
        (extChartAt throatCoverModelWithCorners chartAnchor).source) :=
  (throatTensorCoordinates_contMDiffOn_frameBaseSet
    period hPeriod tensor frameAnchor).mono inter_subset_left

/-- Tensor coefficients in an independently selected frame and base chart. -/
def throatTensorFrameChartRepresentative
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (frameAnchor chartAnchor : EffectiveThroat period hPeriod) :
    ThroatCoverCoordinates → ThroatCovariantTwoTensorModel :=
  (fun current ↦
    ContinuousLinearMap.inCoordinates ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod)
      (ThroatCoverCoordinates →L[Real] Real)
      (ThroatCotangentFiber period hPeriod)
      frameAnchor current frameAnchor current (tensor.tensor current)) ∘
    (extChartAt throatCoverModelWithCorners chartAnchor).symm

/-- The arbitrary-frame/chart representative is `C∞` at every represented
point where both choices are valid. -/
theorem throatTensorFrameChartRepresentative_contDiffAt_infty
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (frameAnchor chartAnchor current : EffectiveThroat period hPeriod)
    (hFrame : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) frameAnchor).baseSet)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source) :
    ContDiffAt Real ∞
      (throatTensorFrameChartRepresentative period hPeriod tensor
        frameAnchor chartAnchor)
      (extChartAt throatCoverModelWithCorners chartAnchor current) := by
  have hCoordinates : ContMDiffAt throatCoverModelWithCorners
      (modelWithCornersSelf Real ThroatCovariantTwoTensorModel) ∞
      (fun nearby ↦
        ContinuousLinearMap.inCoordinates ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod)
          (ThroatCoverCoordinates →L[Real] Real)
          (ThroatCotangentFiber period hPeriod)
          frameAnchor nearby frameAnchor nearby (tensor.tensor nearby))
      current :=
    ((throatTensorCoordinates_contMDiffOn_frameChartBaseSet
      period hPeriod tensor frameAnchor chartAnchor) current
        ⟨hFrame, hChart⟩).contMDiffAt
      (((trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) frameAnchor).open_baseSet.inter
        (isOpen_extChartAt_source chartAnchor)).mem_nhds
          ⟨hFrame, hChart⟩)
  have hTarget : extChartAt throatCoverModelWithCorners chartAnchor current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).target :=
    (extChartAt throatCoverModelWithCorners chartAnchor).map_source hChart
  have hInverse : ContMDiffAt
      (modelWithCornersSelf Real ThroatCoverCoordinates)
        throatCoverModelWithCorners ∞
      (extChartAt throatCoverModelWithCorners chartAnchor).symm
      (extChartAt throatCoverModelWithCorners chartAnchor current) :=
    (contMDiffOn_extChartAt_symm
      (I := throatCoverModelWithCorners) (n := ∞) chartAnchor).contMDiffAt
        (extChartAt_target_mem_nhds' hTarget)
  have hComposition := hCoordinates.comp_of_eq hInverse
    ((extChartAt throatCoverModelWithCorners chartAnchor).left_inv hChart)
  exact hComposition.contDiffAt

/-- The genuine second jet of a smooth intrinsic tensor in arbitrary valid
frame and chart choices. -/
def throatTensorSecondOrderJetInFrameChartAt
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (frameAnchor chartAnchor current : EffectiveThroat period hPeriod)
    (hFrame : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) frameAnchor).baseSet)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source) :
    FramedSecondOrderJet ThroatCoverCoordinates
      ThroatCovariantTwoTensorModel :=
  chartwiseSecondOrderJetAt
    (throatTensorFrameChartRepresentative period hPeriod tensor
      frameAnchor chartAnchor)
    (extChartAt throatCoverModelWithCorners chartAnchor current)
    ((throatTensorFrameChartRepresentative_contDiffAt_infty
      period hPeriod tensor frameAnchor chartAnchor current hFrame hChart).of_le
        (by
          show (2 : ℕ∞ω) ≤ ∞
          exact WithTop.coe_le_coe.mpr le_top))

@[simp]
theorem throatTensorSecondOrderJetInFrameChartAt_value
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (frameAnchor chartAnchor current : EffectiveThroat period hPeriod)
    (hFrame : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) frameAnchor).baseSet)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source) :
    (throatTensorSecondOrderJetInFrameChartAt period hPeriod tensor
      frameAnchor chartAnchor current hFrame hChart).value =
      throatTensorCoordinates period hPeriod tensor frameAnchor current := by
  rw [throatTensorSecondOrderJetInFrameChartAt,
    chartwiseSecondOrderJetAt_value]
  exact congrArg (throatTensorCoordinates period hPeriod tensor frameAnchor)
    ((extChartAt throatCoverModelWithCorners chartAnchor).left_inv hChart)

@[simp]
theorem throatTensorSecondOrderJetInFrameChartAt_firstDerivative
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (frameAnchor chartAnchor current : EffectiveThroat period hPeriod)
    (hFrame : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) frameAnchor).baseSet)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source) :
    (throatTensorSecondOrderJetInFrameChartAt period hPeriod tensor
      frameAnchor chartAnchor current hFrame hChart).firstDerivative =
      fderiv Real
        (throatTensorFrameChartRepresentative period hPeriod tensor
          frameAnchor chartAnchor)
        (extChartAt throatCoverModelWithCorners chartAnchor current) :=
  rfl

private abbrev TensorModel :=
  FramedCovariantTwoTensor ThroatCoverCoordinates

local instance tensorModelNormedAddCommGroup :
    NormedAddCommGroup TensorModel :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance tensorModelNormedSpace : NormedSpace Real TensorModel :=
  ContinuousLinearMap.toNormedSpace

@[simp]
theorem throatTensorSecondOrderJetInFrameChartAt_secondDerivative
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (frameAnchor chartAnchor current : EffectiveThroat period hPeriod)
    (hFrame : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) frameAnchor).baseSet)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source) :
    (throatTensorSecondOrderJetInFrameChartAt period hPeriod tensor
      frameAnchor chartAnchor current hFrame hChart).secondDerivative =
      fderiv Real
        (fderiv Real
          (throatTensorFrameChartRepresentative period hPeriod tensor
            frameAnchor chartAnchor))
        (extChartAt throatCoverModelWithCorners chartAnchor current) :=
  rfl

theorem throatTensorSecondOrderJetInFrameChartAt_secondDerivative_symmetric
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (frameAnchor chartAnchor current : EffectiveThroat period hPeriod)
    (hFrame : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) frameAnchor).baseSet)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source)
    (first second : ThroatCoverCoordinates) :
    (throatTensorSecondOrderJetInFrameChartAt period hPeriod tensor
      frameAnchor chartAnchor current hFrame hChart).secondDerivative first second =
      (throatTensorSecondOrderJetInFrameChartAt period hPeriod tensor
        frameAnchor chartAnchor current hFrame hChart).secondDerivative second first :=
  (throatTensorSecondOrderJetInFrameChartAt period hPeriod tensor
    frameAnchor chartAnchor current hFrame hChart).secondDerivative_symmetric first second

/-- Actual induced metric jet in arbitrary valid frame and chart choices. -/
def globalGaugeFixedThroatMetricSecondOrderJetInFrameChartAt
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (sector : Sector)
    (frameAnchor chartAnchor current : EffectiveThroat period hPeriod)
    (hFrame : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) frameAnchor).baseSet)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source) :
    FramedSecondOrderJet ThroatCoverCoordinates
      ThroatCovariantTwoTensorModel :=
  throatTensorSecondOrderJetInFrameChartAt period hPeriod
    (globalGaugeFixedInducedMetricBySector
      period hPeriod configuration sector)
    frameAnchor chartAnchor current hFrame hChart

/-- On the diagonal, the arbitrary-frame/chart extraction is exactly the
previous centered actual throat metric jet. -/
@[simp]
theorem globalGaugeFixedThroatMetricSecondOrderJetInFrameChartAt_diagonal
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (sector : Sector)
    (anchor : EffectiveThroat period hPeriod) :
    globalGaugeFixedThroatMetricSecondOrderJetInFrameChartAt period hPeriod
        configuration sector anchor anchor anchor
        (FiberBundle.mem_baseSet_trivializationAt' anchor)
        (mem_extChartAt_source anchor) =
      globalGaugeFixedThroatMetricSecondOrderJetAt period hPeriod
        configuration sector anchor := by
  rfl

end
end P0EFTJanusProgramPActualThroatMetricArbitraryFrameChartSecondOrderJetExtraction4D
end JanusFormal
