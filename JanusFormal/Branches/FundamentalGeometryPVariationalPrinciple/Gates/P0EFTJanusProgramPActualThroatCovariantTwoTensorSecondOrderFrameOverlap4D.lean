import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatMetricArbitraryFrameChartSecondOrderJetExtraction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatCovariantTwoTensorZeroOrderTransition4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPContinuousLinearMapSecondOrderLeibniz4D

/-!
# Second-order same-chart frame overlap for throat covariant two-tensors

The covariant rank-two transition and both tensor representatives are read in
one fixed arbitrary throat chart.  Their exact germ yields the first-order and
full four-term second-order Leibniz laws.  Only the tangent frame changes here;
no independent base-chart transition law is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatCovariantTwoTensorSecondOrderFrameOverlap4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 500000

noncomputable section

open Set Filter
open scoped Manifold ContDiff RealInnerProductSpace Topology
open Bundle
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPGlobalMetricChartwiseSecondOrderJetExtraction4D
open P0EFTJanusProgramPActualThroatAbelianPotentialZeroOrderTrivializationOverlap4D
open P0EFTJanusProgramPActualThroatGaugeZeroOrderTransitionCocycle4D
open P0EFTJanusProgramPActualThroatGaugeZeroOrderTransitionSmoothness4D
open P0EFTJanusProgramPActualThroatGaugeZeroOrderOverlapDataSmoothness4D
open P0EFTJanusProgramPActualThroatMetricArbitraryFrameChartSecondOrderJetExtraction4D
open P0EFTJanusProgramPActualThroatCovariantTwoTensorZeroOrderTransition4D
open P0EFTJanusProgramPContinuousLinearMapSecondOrderLeibniz4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev TensorModel :=
  FramedCovariantTwoTensor ThroatCoverCoordinates

private abbrev TensorEnd := TensorModel →L[Real] TensorModel

private abbrev TensorFirstDerivative :=
  ThroatCoverCoordinates →L[Real] TensorModel

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

local instance tensorModelNormedAddCommGroup :
    NormedAddCommGroup TensorModel :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance tensorModelNormedSpace : NormedSpace Real TensorModel :=
  ContinuousLinearMap.toNormedSpace

local instance tensorEndNormedAddCommGroup : NormedAddCommGroup TensorEnd :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance tensorEndNormedSpace : NormedSpace Real TensorEnd :=
  ContinuousLinearMap.toNormedSpace

local instance tensorFirstDerivativeNormedAddCommGroup :
    NormedAddCommGroup TensorFirstDerivative :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance tensorFirstDerivativeNormedSpace :
    NormedSpace Real TensorFirstDerivative :=
  ContinuousLinearMap.toNormedSpace

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-! ## Transition and exact local germ -/

/-- Instance-normalized covariant rank-two action induced by the same tangent
and covector transitions as the zero-order gate. -/
def throatCovariantTwoTensorFrameTransitionAt
    (firstAnchor secondAnchor current : EffectiveThroat period hPeriod) :
    TensorModel ≃L[Real] TensorModel :=
  (throatGaugeTangentTrivializationTransitionAt period hPeriod
      firstAnchor secondAnchor current).arrowCongr
    (throatGaugeCovectorTrivializationTransitionAt period hPeriod
      firstAnchor secondAnchor current)

/-- The normalized action agrees pointwise with the zero-order transition. -/
theorem throatCovariantTwoTensorFrameTransitionAt_eq_zeroOrder_apply
    (firstAnchor secondAnchor current : EffectiveThroat period hPeriod)
    (tensor : TensorModel) :
    throatCovariantTwoTensorFrameTransitionAt period hPeriod
        firstAnchor secondAnchor current tensor =
      P0EFTJanusProgramPActualThroatCovariantTwoTensorZeroOrderTransition4D.throatCovariantTwoTensorTrivializationTransitionAt
        period hPeriod firstAnchor secondAnchor current tensor := by
  rfl

@[simp]
theorem throatCovariantTwoTensorFrameTransitionAt_apply
    (firstAnchor secondAnchor current : EffectiveThroat period hPeriod)
    (tensor : TensorModel) (first second : ThroatCoverCoordinates) :
    throatCovariantTwoTensorFrameTransitionAt period hPeriod
        firstAnchor secondAnchor current tensor first second =
      tensor
        ((throatGaugeTangentTrivializationTransitionAt period hPeriod
          firstAnchor secondAnchor current).symm first)
        ((throatGaugeTangentTrivializationTransitionAt period hPeriod
          firstAnchor secondAnchor current).symm second) := by
  rfl

/-- The varying covariant rank-two frame transition read in a fixed arbitrary
extended throat chart. -/
def throatCovariantTwoTensorTransitionCenteredChart
    (firstAnchor secondAnchor chartAnchor : EffectiveThroat period hPeriod) :
    ThroatCoverCoordinates → TensorEnd :=
  fun coordinate =>
    (throatCovariantTwoTensorFrameTransitionAt period hPeriod
      firstAnchor secondAnchor
      ((extChartAt throatCoverModelWithCorners chartAnchor).symm coordinate) :
        TensorEnd)

/-- With the tensor-model normed-space instances used by the arbitrary-frame
extraction gate, the rank-two transition remains `C∞` on its frame overlap. -/
private theorem throatCovariantTwoTensorTrivializationTransition_contMDiffOn
    (firstAnchor secondAnchor : EffectiveThroat period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, TensorEnd) ∞
      (fun current : EffectiveThroat period hPeriod =>
        (throatCovariantTwoTensorFrameTransitionAt period hPeriod
          firstAnchor secondAnchor current : TensorEnd))
      ((trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) firstAnchor).baseSet ∩
        (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) secondAnchor).baseSet) := by
  have hTangentInverse :=
    throatGaugeTangentTrivializationTransitionAt_symm_contMDiffOn
      period hPeriod firstAnchor secondAnchor
  have hCovector :=
    throatGaugeCovectorTrivializationTransitionAt_contMDiffOn
      period hPeriod firstAnchor secondAnchor
  simpa only [throatCovariantTwoTensorFrameTransitionAt] using
    hTangentInverse.cle_arrowCongr hCovector

/-- The arbitrary-chart rank-two transition is `C∞` at every point where the
two frames and the selected chart are valid. -/
theorem throatCovariantTwoTensorTransitionCenteredChart_contDiffAt_infty
    (firstAnchor secondAnchor chartAnchor current :
      EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) firstAnchor).baseSet ∩
        (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) secondAnchor).baseSet)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source) :
    ContDiffAt Real ∞
      (throatCovariantTwoTensorTransitionCenteredChart period hPeriod
        firstAnchor secondAnchor chartAnchor)
      (extChartAt throatCoverModelWithCorners chartAnchor current) := by
  let coordinate := extChartAt throatCoverModelWithCorners chartAnchor current
  have hTarget : coordinate ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).target :=
    (extChartAt throatCoverModelWithCorners chartAnchor).map_source hChart
  have hInverse :
      ContMDiffAt (modelWithCornersSelf Real ThroatCoverCoordinates)
        throatCoverModelWithCorners ∞
        (extChartAt throatCoverModelWithCorners chartAnchor).symm coordinate :=
    (contMDiffOn_extChartAt_symm
      (I := throatCoverModelWithCorners) (n := ∞) chartAnchor).contMDiffAt
        (extChartAt_target_mem_nhds' hTarget)
  have hTransition :=
    (throatCovariantTwoTensorTrivializationTransition_contMDiffOn
      period hPeriod firstAnchor secondAnchor).contMDiffAt
        ((trivializationAt ThroatCoverCoordinates
            (ThroatTangentFiber period hPeriod) firstAnchor).open_baseSet.inter
          (trivializationAt ThroatCoverCoordinates
            (ThroatTangentFiber period hPeriod) secondAnchor).open_baseSet
          |>.mem_nhds hCurrent)
  have hComposition := hTransition.comp_of_eq hInverse
    ((extChartAt throatCoverModelWithCorners chartAnchor).left_inv hChart)
  change ContDiffAt Real ∞
    ((fun point : EffectiveThroat period hPeriod =>
        (throatCovariantTwoTensorFrameTransitionAt period hPeriod
          firstAnchor secondAnchor point : TensorEnd)) ∘
      (extChartAt throatCoverModelWithCorners chartAnchor).symm) coordinate
  exact hComposition.contDiffAt

/-- Exact zero-order action of the instance-normalized frame transition on
tensor coefficients. -/
theorem throatTensorCoordinates_eq_frameTransition
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (firstAnchor secondAnchor current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) firstAnchor).baseSet ∩
        (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) secondAnchor).baseSet) :
    throatTensorCoordinates period hPeriod tensor secondAnchor current =
      throatCovariantTwoTensorFrameTransitionAt period hPeriod
        firstAnchor secondAnchor current
        (throatTensorCoordinates period hPeriod tensor firstAnchor current) := by
  apply ContinuousLinearMap.ext
  intro first
  apply ContinuousLinearMap.ext
  intro second
  rw [throatCovariantTwoTensorFrameTransitionAt_apply,
    throatTensorCoordinates_apply_of_mem period hPeriod tensor secondAnchor
      current hCurrent.2,
    throatTensorCoordinates_apply_of_mem period hPeriod tensor firstAnchor
      current hCurrent.1]
  have hVector (vector : ThroatCoverCoordinates) :
      (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) firstAnchor).symm current
          ((throatGaugeTangentTrivializationTransitionAt period hPeriod
            firstAnchor secondAnchor current).symm vector) =
        (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) secondAnchor).symm current
          vector := by
    rw [throatGaugeTangentTrivializationTransitionAt_symm period hPeriod
      firstAnchor secondAnchor current hCurrent]
    unfold throatGaugeTangentTrivializationTransitionAt
    rw [← Bundle.Trivialization.comp_continuousLinearEquivAt_eq_coord_change
      (R := Real) _ _ ⟨hCurrent.2, hCurrent.1⟩]
    exact
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) firstAnchor).symm_apply_apply_mk
          hCurrent.1 _
  rw [hVector first, hVector second]

/-- In one arbitrary common base chart, transporting the first-frame tensor
representative gives the second-frame representative as an exact germ. -/
theorem throatTensorFrameChartRepresentative_frameTransition_eventuallyEq
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (firstAnchor secondAnchor chartAnchor current :
      EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) firstAnchor).baseSet ∩
        (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) secondAnchor).baseSet)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source) :
    (fun coordinate =>
      throatCovariantTwoTensorTransitionCenteredChart period hPeriod
          firstAnchor secondAnchor chartAnchor coordinate
        (throatTensorFrameChartRepresentative period hPeriod tensor
          firstAnchor chartAnchor coordinate)) =ᶠ[𝓝
            (extChartAt throatCoverModelWithCorners chartAnchor current)]
      throatTensorFrameChartRepresentative period hPeriod tensor
        secondAnchor chartAnchor := by
  have hOverlapOpen : IsOpen
      ((trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) firstAnchor).baseSet ∩
        (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) secondAnchor).baseSet) :=
    (trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) firstAnchor).open_baseSet.inter
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) secondAnchor).open_baseSet
  have hOverlapNhds :
      (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) firstAnchor).baseSet ∩
        (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) secondAnchor).baseSet ∈
        𝓝 current :=
    hOverlapOpen.mem_nhds hCurrent
  have hChartInverse : ContinuousAt
      (extChartAt throatCoverModelWithCorners chartAnchor).symm
      (extChartAt throatCoverModelWithCorners chartAnchor current) :=
    continuousAt_extChartAt_symm' hChart
  have hInverseEventually :
      (extChartAt throatCoverModelWithCorners chartAnchor).symm ⁻¹'
          ((trivializationAt ThroatCoverCoordinates
              (ThroatTangentFiber period hPeriod) firstAnchor).baseSet ∩
            (trivializationAt ThroatCoverCoordinates
              (ThroatTangentFiber period hPeriod) secondAnchor).baseSet) ∈
        𝓝 (extChartAt throatCoverModelWithCorners chartAnchor current) :=
    hChartInverse.preimage_mem_nhds (by
      rw [(extChartAt throatCoverModelWithCorners chartAnchor).left_inv hChart]
      exact hOverlapNhds)
  filter_upwards [hInverseEventually] with coordinate hCoordinate
  simpa only [throatCovariantTwoTensorTransitionCenteredChart,
    throatTensorFrameChartRepresentative, throatTensorCoordinates,
    Function.comp_apply,
    ContinuousLinearEquiv.coe_coe] using
    (throatTensorCoordinates_eq_frameTransition period hPeriod tensor
      firstAnchor secondAnchor
      ((extChartAt throatCoverModelWithCorners chartAnchor).symm coordinate)
      hCoordinate).symm

/-! ## Exact value and differentiated frame laws -/

/-- Zero-order component of the same-chart tensor-jet frame law. -/
theorem throatTensorSecondOrderJetInFrameChartAt_value_frame_transition
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (firstAnchor secondAnchor chartAnchor current :
      EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) firstAnchor).baseSet ∩
        (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) secondAnchor).baseSet)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source) :
    (throatTensorSecondOrderJetInFrameChartAt period hPeriod tensor
      secondAnchor chartAnchor current hCurrent.2 hChart).value =
      throatCovariantTwoTensorFrameTransitionAt period hPeriod
        firstAnchor secondAnchor current
        (throatTensorSecondOrderJetInFrameChartAt period hPeriod tensor
          firstAnchor chartAnchor current hCurrent.1 hChart).value := by
  rw [throatTensorSecondOrderJetInFrameChartAt_value,
    throatTensorSecondOrderJetInFrameChartAt_value]
  exact throatTensorCoordinates_eq_frameTransition period hPeriod tensor
    firstAnchor secondAnchor current hCurrent

/-- First-order varying-frame Leibniz law for a covariant rank-two tensor in
one arbitrary fixed base chart. -/
theorem throatTensorSecondOrderJetInFrameChartAt_firstDerivative_frame_transition
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (firstAnchor secondAnchor chartAnchor current :
      EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) firstAnchor).baseSet ∩
        (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) secondAnchor).baseSet)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source) :
    (throatTensorSecondOrderJetInFrameChartAt period hPeriod tensor
      secondAnchor chartAnchor current hCurrent.2 hChart).firstDerivative =
      (throatCovariantTwoTensorFrameTransitionAt period hPeriod
          firstAnchor secondAnchor current : TensorEnd).comp
        (throatTensorSecondOrderJetInFrameChartAt period hPeriod tensor
          firstAnchor chartAnchor current hCurrent.1 hChart).firstDerivative +
      (fderiv Real
        (throatCovariantTwoTensorTransitionCenteredChart period hPeriod
          firstAnchor secondAnchor chartAnchor)
        (extChartAt throatCoverModelWithCorners chartAnchor current)).flip
          (throatTensorSecondOrderJetInFrameChartAt period hPeriod tensor
            firstAnchor chartAnchor current hCurrent.1 hChart).value := by
  let transition :=
    throatCovariantTwoTensorTransitionCenteredChart period hPeriod
      firstAnchor secondAnchor chartAnchor
  let firstRepresentative :=
    throatTensorFrameChartRepresentative period hPeriod tensor
      firstAnchor chartAnchor
  let secondRepresentative :=
    throatTensorFrameChartRepresentative period hPeriod tensor
      secondAnchor chartAnchor
  let coordinate :=
    extChartAt throatCoverModelWithCorners chartAnchor current
  have hTransition : ContDiffAt Real 2 transition coordinate :=
    (throatCovariantTwoTensorTransitionCenteredChart_contDiffAt_infty
      period hPeriod firstAnchor secondAnchor chartAnchor current hCurrent hChart).of_le
        (by
          show (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω)
          exact WithTop.coe_le_coe.mpr le_top)
  have hFirst : ContDiffAt Real 2 firstRepresentative coordinate :=
    (throatTensorFrameChartRepresentative_contDiffAt_infty period hPeriod tensor
      firstAnchor chartAnchor current hCurrent.1 hChart).of_le (by
        show (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω)
        exact WithTop.coe_le_coe.mpr le_top)
  have hGerm :
      (fun point => transition point (firstRepresentative point)) =ᶠ[𝓝 coordinate]
        secondRepresentative := by
    simpa only [transition, firstRepresentative, secondRepresentative,
      coordinate] using
      throatTensorFrameChartRepresentative_frameTransition_eventuallyEq
        period hPeriod tensor firstAnchor secondAnchor chartAnchor current
          hCurrent hChart
  have hProduct := fderiv_clm_apply
    (hTransition.differentiableAt (by norm_num))
    (hFirst.differentiableAt (by norm_num))
  have hCoordinateInverse :
      (extChartAt throatCoverModelWithCorners chartAnchor).symm coordinate =
        current := by
    simpa only [coordinate] using
      (extChartAt throatCoverModelWithCorners chartAnchor).left_inv hChart
  simp only [transition, firstRepresentative,
    throatCovariantTwoTensorTransitionCenteredChart,
    throatTensorFrameChartRepresentative, Function.comp_apply] at hProduct
  rw [hCoordinateInverse] at hProduct
  rw [throatTensorSecondOrderJetInFrameChartAt_firstDerivative,
    throatTensorSecondOrderJetInFrameChartAt_firstDerivative,
    throatTensorSecondOrderJetInFrameChartAt_value]
  rw [show fderiv Real secondRepresentative coordinate =
      fderiv Real (fun point => transition point (firstRepresentative point))
        coordinate by exact hGerm.fderiv_eq.symm]
  simpa only [transition, firstRepresentative, coordinate,
    throatCovariantTwoTensorTransitionCenteredChart,
    throatTensorFrameChartRepresentative, throatTensorCoordinates,
    Function.comp_apply,
    ContinuousLinearEquiv.coe_coe] using hProduct

/-- Full four-term second-order varying-frame law for a covariant rank-two
tensor in one arbitrary fixed base chart. -/
theorem throatTensorSecondOrderJetInFrameChartAt_secondDerivative_frame_transition_apply
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (firstAnchor secondAnchor chartAnchor current :
      EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) firstAnchor).baseSet ∩
        (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) secondAnchor).baseSet)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source)
    (first second : ThroatCoverCoordinates) :
    (throatTensorSecondOrderJetInFrameChartAt period hPeriod tensor
      secondAnchor chartAnchor current hCurrent.2 hChart).secondDerivative
        first second =
      throatCovariantTwoTensorFrameTransitionAt period hPeriod
        firstAnchor secondAnchor current
        ((throatTensorSecondOrderJetInFrameChartAt period hPeriod tensor
          firstAnchor chartAnchor current hCurrent.1 hChart).secondDerivative
            first second) +
      fderiv Real
          (throatCovariantTwoTensorTransitionCenteredChart period hPeriod
            firstAnchor secondAnchor chartAnchor)
          (extChartAt throatCoverModelWithCorners chartAnchor current) first
        ((throatTensorSecondOrderJetInFrameChartAt period hPeriod tensor
          firstAnchor chartAnchor current hCurrent.1 hChart).firstDerivative
            second) +
      fderiv Real
          (throatCovariantTwoTensorTransitionCenteredChart period hPeriod
            firstAnchor secondAnchor chartAnchor)
          (extChartAt throatCoverModelWithCorners chartAnchor current) second
        ((throatTensorSecondOrderJetInFrameChartAt period hPeriod tensor
          firstAnchor chartAnchor current hCurrent.1 hChart).firstDerivative
            first) +
      fderiv Real
          (fun coordinate =>
            fderiv Real
              (throatCovariantTwoTensorTransitionCenteredChart period hPeriod
                firstAnchor secondAnchor chartAnchor) coordinate second)
          (extChartAt throatCoverModelWithCorners chartAnchor current) first
        ((throatTensorSecondOrderJetInFrameChartAt period hPeriod tensor
          firstAnchor chartAnchor current hCurrent.1 hChart).value) := by
  let transition :=
    throatCovariantTwoTensorTransitionCenteredChart period hPeriod
      firstAnchor secondAnchor chartAnchor
  let firstRepresentative :=
    throatTensorFrameChartRepresentative period hPeriod tensor
      firstAnchor chartAnchor
  let secondRepresentative :=
    throatTensorFrameChartRepresentative period hPeriod tensor
      secondAnchor chartAnchor
  let coordinate :=
    extChartAt throatCoverModelWithCorners chartAnchor current
  have hTransition : ContDiffAt Real 2 transition coordinate :=
    (throatCovariantTwoTensorTransitionCenteredChart_contDiffAt_infty
      period hPeriod firstAnchor secondAnchor chartAnchor current hCurrent hChart).of_le
        (by
          show (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω)
          exact WithTop.coe_le_coe.mpr le_top)
  have hFirst : ContDiffAt Real 2 firstRepresentative coordinate :=
    (throatTensorFrameChartRepresentative_contDiffAt_infty period hPeriod tensor
      firstAnchor chartAnchor current hCurrent.1 hChart).of_le (by
        show (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω)
        exact WithTop.coe_le_coe.mpr le_top)
  have hGerm :
      (fun point => transition point (firstRepresentative point)) =ᶠ[𝓝 coordinate]
        secondRepresentative := by
    simpa only [transition, firstRepresentative, secondRepresentative,
      coordinate] using
      throatTensorFrameChartRepresentative_frameTransition_eventuallyEq
        period hPeriod tensor firstAnchor secondAnchor chartAnchor current
          hCurrent hChart
  have hSecondDerivative :
      fderiv Real (fderiv Real
          (fun point => transition point (firstRepresentative point))) coordinate =
        fderiv Real (fderiv Real secondRepresentative) coordinate :=
    (hGerm.fderiv).fderiv_eq
  have hLeibniz := second_fderiv_clm_apply_apply transition
    firstRepresentative coordinate first second hTransition hFirst
  have hCoordinateInverse :
      (extChartAt throatCoverModelWithCorners chartAnchor).symm coordinate =
        current := by
    simpa only [coordinate] using
      (extChartAt throatCoverModelWithCorners chartAnchor).left_inv hChart
  simp only [transition, firstRepresentative,
    throatCovariantTwoTensorTransitionCenteredChart,
    throatTensorFrameChartRepresentative, Function.comp_apply] at hLeibniz
  rw [hCoordinateInverse] at hLeibniz
  rw [P0EFTJanusProgramPActualThroatMetricArbitraryFrameChartSecondOrderJetExtraction4D.throatTensorSecondOrderJetInFrameChartAt_secondDerivative,
    P0EFTJanusProgramPActualThroatMetricArbitraryFrameChartSecondOrderJetExtraction4D.throatTensorSecondOrderJetInFrameChartAt_secondDerivative,
    throatTensorSecondOrderJetInFrameChartAt_firstDerivative,
    throatTensorSecondOrderJetInFrameChartAt_value]
  rw [show fderiv Real (fderiv Real secondRepresentative) coordinate
      first second =
    fderiv Real (fderiv Real
      (fun point => transition point (firstRepresentative point))) coordinate
        first second by
    exact congrArg
      (fun derivative : ThroatCoverCoordinates →L[Real]
          ThroatCoverCoordinates →L[Real] TensorModel =>
        derivative first second) hSecondDerivative.symm]
  simpa only [transition, firstRepresentative, coordinate,
    throatCovariantTwoTensorTransitionCenteredChart,
    throatTensorFrameChartRepresentative, throatTensorCoordinates,
    Function.comp_apply,
    ContinuousLinearEquiv.coe_coe] using hLeibniz

end
end P0EFTJanusProgramPActualThroatCovariantTwoTensorSecondOrderFrameOverlap4D
end JanusFormal
