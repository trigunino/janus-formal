import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralLorentzMetricBVPTCovariance4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralLorentzMetricDirichletPT4D

/-!
# Throat boundary data for the general-metric BV tangent sector

Arbitrary smooth symmetric ambient tensor variations and their shifted
antifields are pulled back through the genuine throat inclusion.  The trace
is proved smooth directly in the dependent Hom bundle.  PT/exchange
naturality, BRST commutation and matched Dirichlet transport are then proved
without postulating an arbitrary intrinsic tensor pullback section.

The existing ambient background-raised pairing and odd bracket remain
pointwise PT covariant through their dedicated gate.  No boundary inverse
metric, functional antibracket or CME is asserted here.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusGeneralLorentzMetricBVThroatBoundary4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped Manifold ContDiff Topology
open Bundle Filter
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusPTInvolution
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothThroatEmbedding
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralLorentzTensorPTSmoothness4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzIndependentFieldPacket4D
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatPTNaturality4D
open P0EFTJanusMappingTorusGeneralLorentzMetricDirichletPT4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFirstLevel4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVPTCovariance4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-! ## Smooth restriction of arbitrary symmetric tensor variations -/

/-- Pointwise covariant pullback of an arbitrary symmetric tensor through
the actual throat inclusion. -/
def smoothSymmetricTensorThroatTraceValue
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    ThroatCovariantTwoTensorFiber period hPeriod point :=
  let derivative :=
    mfderiv throatCoverModelWithCorners coverModelWithCorners
      (fixedThroatQuotientInclusion period hPeriod) point
  (derivative.precomp Real).comp
    ((tensor.tensor (fixedThroatQuotientInclusion period hPeriod point)).comp
      derivative)

@[simp]
theorem smoothSymmetricTensorThroatTraceValue_apply
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveThroat period hPeriod)
    (first second : ThroatTangentFiber period hPeriod point) :
    smoothSymmetricTensorThroatTraceValue period hPeriod tensor point
        first second =
      tensor.tensor (fixedThroatQuotientInclusion period hPeriod point)
        (mfderiv throatCoverModelWithCorners coverModelWithCorners
          (fixedThroatQuotientInclusion period hPeriod) point first)
        (mfderiv throatCoverModelWithCorners coverModelWithCorners
          (fixedThroatQuotientInclusion period hPeriod) point second) :=
  rfl

private def bvInclusionDerivativeCoordinates
    (point current : EffectiveThroat period hPeriod) :
    ThroatCoverCoordinates →L[Real] CoverCoordinates :=
  inTangentCoordinates throatCoverModelWithCorners coverModelWithCorners
    id (fixedThroatQuotientInclusion period hPeriod)
    (mfderiv throatCoverModelWithCorners coverModelWithCorners
      (fixedThroatQuotientInclusion period hPeriod)) point current

private def bvAmbientTensorCoordinates
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point current : EffectiveThroat period hPeriod) :
    CoverCoordinates →L[Real] CoverCoordinates →L[Real] Real :=
  ContinuousLinearMap.inCoordinates CoverCoordinates
    (fun base : EffectiveQuotient period hPeriod =>
      TangentSpace coverModelWithCorners base)
    (CoverCoordinates →L[Real] Real)
    (fun base : EffectiveQuotient period hPeriod =>
      TangentSpace coverModelWithCorners base →L[Real] Real)
    (fixedThroatQuotientInclusion period hPeriod point)
    (fixedThroatQuotientInclusion period hPeriod current)
    (fixedThroatQuotientInclusion period hPeriod point)
    (fixedThroatQuotientInclusion period hPeriod current)
    (tensor.tensor (fixedThroatQuotientInclusion period hPeriod current))

private def bvThroatTraceTensorCoordinates
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point current : EffectiveThroat period hPeriod) :
    ThroatCovariantTwoTensorModel :=
  ContinuousLinearMap.inCoordinates ThroatCoverCoordinates
    (ThroatTangentFiber period hPeriod)
    (ThroatCoverCoordinates →L[Real] Real)
    (ThroatCotangentFiber period hPeriod)
    point current point current
    (smoothSymmetricTensorThroatTraceValue period hPeriod tensor current)

private def bvCoordinateRestriction
    (derivative : ThroatCoverCoordinates →L[Real] CoverCoordinates)
    (tensor : CoverCoordinates →L[Real]
      CoverCoordinates →L[Real] Real) :
    ThroatCovariantTwoTensorModel :=
  (derivative.precomp Real).comp (tensor.comp derivative)

private theorem bvInclusionDerivativeCoordinates_apply
    (point current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) point).baseSet)
    (hImage : fixedThroatQuotientInclusion period hPeriod current ∈
      (trivializationAt CoverCoordinates
        (fun base : EffectiveQuotient period hPeriod =>
          TangentSpace coverModelWithCorners base)
        (fixedThroatQuotientInclusion period hPeriod point)).baseSet)
    (vector : ThroatCoverCoordinates) :
    bvInclusionDerivativeCoordinates period hPeriod point current vector =
      (trivializationAt CoverCoordinates
        (fun base : EffectiveQuotient period hPeriod =>
          TangentSpace coverModelWithCorners base)
        (fixedThroatQuotientInclusion period hPeriod point)).linearMapAt Real
          (fixedThroatQuotientInclusion period hPeriod current)
          (mfderiv throatCoverModelWithCorners coverModelWithCorners
            (fixedThroatQuotientInclusion period hPeriod) current
            ((trivializationAt ThroatCoverCoordinates
              (ThroatTangentFiber period hPeriod) point).symm current
                vector)) := by
  rw [show bvInclusionDerivativeCoordinates period hPeriod point current =
      ContinuousLinearMap.inCoordinates ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) CoverCoordinates
        (fun base : EffectiveQuotient period hPeriod =>
          TangentSpace coverModelWithCorners base)
        point current
        (fixedThroatQuotientInclusion period hPeriod point)
        (fixedThroatQuotientInclusion period hPeriod current)
        (mfderiv throatCoverModelWithCorners coverModelWithCorners
          (fixedThroatQuotientInclusion period hPeriod) current) by rfl]
  rw [ContinuousLinearMap.inCoordinates_eq hCurrent hImage]
  rw [Trivialization.linearMapAt_apply, if_pos hImage]
  rfl

private theorem bvThroatTraceTensorCoordinates_eq
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) point).baseSet)
    (hImage : fixedThroatQuotientInclusion period hPeriod current ∈
      (trivializationAt CoverCoordinates
        (fun base : EffectiveQuotient period hPeriod =>
          TangentSpace coverModelWithCorners base)
        (fixedThroatQuotientInclusion period hPeriod point)).baseSet) :
    bvThroatTraceTensorCoordinates period hPeriod tensor point current =
      bvCoordinateRestriction
        (bvInclusionDerivativeCoordinates period hPeriod point current)
        (bvAmbientTensorCoordinates period hPeriod tensor point current) := by
  apply ContinuousLinearMap.ext
  intro first
  apply ContinuousLinearMap.ext
  intro second
  rw [show bvThroatTraceTensorCoordinates period hPeriod tensor point current
        first second =
      ContinuousLinearMap.inCoordinates ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod)
        (ThroatCoverCoordinates →L[Real] Real)
        (ThroatCotangentFiber period hPeriod)
        point current point current
        (smoothSymmetricTensorThroatTraceValue
          period hPeriod tensor current) first second by rfl]
  rw [inCoordinates_apply_eq₂ hCurrent hCurrent (Set.mem_univ _)]
  simp only [smoothSymmetricTensorThroatTraceValue_apply,
    bvCoordinateRestriction, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.precomp_apply]
  rw [show bvAmbientTensorCoordinates period hPeriod tensor point current
        (bvInclusionDerivativeCoordinates period hPeriod point current first)
        (bvInclusionDerivativeCoordinates period hPeriod point current second) =
      ContinuousLinearMap.inCoordinates CoverCoordinates
        (fun base : EffectiveQuotient period hPeriod =>
          TangentSpace coverModelWithCorners base)
        (CoverCoordinates →L[Real] Real)
        (fun base : EffectiveQuotient period hPeriod =>
          TangentSpace coverModelWithCorners base →L[Real] Real)
        (fixedThroatQuotientInclusion period hPeriod point)
        (fixedThroatQuotientInclusion period hPeriod current)
        (fixedThroatQuotientInclusion period hPeriod point)
        (fixedThroatQuotientInclusion period hPeriod current)
        (tensor.tensor (fixedThroatQuotientInclusion period hPeriod current))
        (bvInclusionDerivativeCoordinates period hPeriod point current first)
        (bvInclusionDerivativeCoordinates period hPeriod point current second)
        by rfl]
  rw [inCoordinates_apply_eq₂ hImage hImage (Set.mem_univ _)]
  rw [bvInclusionDerivativeCoordinates_apply period hPeriod point current
      hCurrent hImage first,
    bvInclusionDerivativeCoordinates_apply period hPeriod point current
      hCurrent hImage second]
  simp only [Trivialization.symm_linearMapAt _ hImage]
  rfl

theorem smoothSymmetricTensorThroatTraceValue_contMDiff
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    ContMDiff throatCoverModelWithCorners
      (throatCoverModelWithCorners.prod
        𝓘(Real, ThroatCovariantTwoTensorModel)) ∞
      (fun point => TotalSpace.mk' ThroatCovariantTwoTensorModel
        (E := ThroatCovariantTwoTensorFiber period hPeriod) point
        (smoothSymmetricTensorThroatTraceValue
          period hPeriod tensor point)) := by
  intro point
  have hD :=
    (fixedThroatQuotientInclusion_contMDiff period hPeriod).contMDiffAt
      |>.mfderiv_const (x₀ := point) (m := ∞) (by simp)
  have hMap :=
    (fixedThroatQuotientInclusion_contMDiff period hPeriod).of_le
      (m := ∞) (by simp)
  have hTensor := tensor.tensor.contMDiff.comp hMap
  have hTensorAt := hTensor point
  rw [contMDiffAt_hom_bundle] at hTensorAt
  have hPre := hD.clm_precomp (F₃ := Real)
  have hOuter := hTensorAt.2.clm_comp hD
  have hFormula := hPre.clm_comp hOuter
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  apply hFormula.congr_of_eventuallyEq
  have hCurrent : ∀ᶠ current in nhds point,
      current ∈
        (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) point).baseSet :=
    (trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) point).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) point)
  have hImage : ∀ᶠ current in nhds point,
      fixedThroatQuotientInclusion period hPeriod current ∈
        (trivializationAt CoverCoordinates
          (fun base : EffectiveQuotient period hPeriod =>
            TangentSpace coverModelWithCorners base)
          (fixedThroatQuotientInclusion period hPeriod point)).baseSet :=
    (fixedThroatQuotientInclusion_contMDiff period hPeriod).continuous.continuousAt
      ((trivializationAt CoverCoordinates
        (fun base : EffectiveQuotient period hPeriod =>
          TangentSpace coverModelWithCorners base)
        (fixedThroatQuotientInclusion period hPeriod point)).open_baseSet.mem_nhds
          (mem_baseSet_trivializationAt CoverCoordinates
            (fun base : EffectiveQuotient period hPeriod =>
              TangentSpace coverModelWithCorners base)
            (fixedThroatQuotientInclusion period hPeriod point)))
  filter_upwards [hCurrent, hImage] with current hCurrent' hImage'
  simpa only [bvThroatTraceTensorCoordinates, bvCoordinateRestriction,
    bvInclusionDerivativeCoordinates, bvAmbientTensorCoordinates,
    Function.comp_apply] using
      (bvThroatTraceTensorCoordinates_eq period hPeriod tensor point current
        hCurrent' hImage')

/-- Genuine smooth symmetric throat trace of an arbitrary ambient symmetric
tensor variation. -/
def smoothSymmetricTensorThroatTrace
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    SmoothSymmetricThroatCovariantTwoTensor period hPeriod where
  tensor :=
    { toFun := smoothSymmetricTensorThroatTraceValue period hPeriod tensor
      contMDiff_toFun :=
        smoothSymmetricTensorThroatTraceValue_contMDiff
          period hPeriod tensor }
  symmetric := by
    intro point first second
    exact tensor.symmetric _ _ _

@[simp]
theorem smoothSymmetricTensorThroatTrace_apply
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveThroat period hPeriod)
    (first second : ThroatTangentFiber period hPeriod point) :
    (smoothSymmetricTensorThroatTrace period hPeriod tensor).tensor point
        first second =
      tensor.tensor (fixedThroatQuotientInclusion period hPeriod point)
        (mfderiv throatCoverModelWithCorners coverModelWithCorners
          (fixedThroatQuotientInclusion period hPeriod) point first)
        (mfderiv throatCoverModelWithCorners coverModelWithCorners
          (fixedThroatQuotientInclusion period hPeriod) point second) :=
  rfl

@[simp]
theorem smoothSymmetricTensorThroatTrace_zero :
    smoothSymmetricTensorThroatTrace period hPeriod
        (zeroSymmetricTensor period hPeriod) =
      { tensor := 0
        symmetric := by intro point first second; rfl } := by
  apply SmoothSymmetricThroatCovariantTwoTensor.ext
  apply ContMDiffSection.ext
  intro point
  apply ContinuousLinearMap.ext
  intro first
  apply ContinuousLinearMap.ext
  intro second
  change (0 : Real) = 0
  rfl

/-! ## BV phase restriction and BRST -/

abbrev SmoothThroatGeneralMetricTensorPair :=
  SmoothSymmetricThroatCovariantTwoTensor period hPeriod ×
    SmoothSymmetricThroatCovariantTwoTensor period hPeriod

abbrev SmoothThroatGeneralMetricBVField :=
  SmoothThroatGeneralMetricTensorPair period hPeriod ×
    SmoothThroatGeneralMetricTensorPair period hPeriod

def smoothThroatGeneralMetricTensorPairZero :
    SmoothThroatGeneralMetricTensorPair period hPeriod :=
  ({ tensor := 0, symmetric := by intro point first second; rfl },
    { tensor := 0, symmetric := by intro point first second; rfl })

def smoothThroatGeneralMetricBVZero :
    SmoothThroatGeneralMetricBVField period hPeriod :=
  (smoothThroatGeneralMetricTensorPairZero period hPeriod,
    smoothThroatGeneralMetricTensorPairZero period hPeriod)

/-- Restriction of both variation and shifted-antifield tensor pairs. -/
def smoothGeneralMetricBVThroatTrace
    (phase : SmoothGeneralMetricBVField period hPeriod) :
    SmoothThroatGeneralMetricBVField period hPeriod :=
  ((smoothSymmetricTensorThroatTrace period hPeriod phase.1.1,
      smoothSymmetricTensorThroatTrace period hPeriod phase.1.2),
    (smoothSymmetricTensorThroatTrace period hPeriod phase.2.1,
      smoothSymmetricTensorThroatTrace period hPeriod phase.2.2))

/-- Boundary BRST doublet `Q(h,h⁺)=(h⁺,0)`. -/
def smoothThroatGeneralMetricBVBRST
    (phase : SmoothThroatGeneralMetricBVField period hPeriod) :
    SmoothThroatGeneralMetricBVField period hPeriod :=
  (phase.2, smoothThroatGeneralMetricTensorPairZero period hPeriod)

@[simp]
theorem smoothThroatGeneralMetricBVBRST_square_zero
    (phase : SmoothThroatGeneralMetricBVField period hPeriod) :
    smoothThroatGeneralMetricBVBRST period hPeriod
        (smoothThroatGeneralMetricBVBRST period hPeriod phase) =
      smoothThroatGeneralMetricBVZero period hPeriod :=
  rfl

/-- Smooth throat restriction commutes exactly with the metric BV BRST
doublet. -/
theorem smoothGeneralMetricBVThroatTrace_commutes_BRST
    (phase : SmoothGeneralMetricBVField period hPeriod) :
    smoothGeneralMetricBVThroatTrace period hPeriod
        (smoothGeneralMetricBVBRST period hPeriod phase) =
      smoothThroatGeneralMetricBVBRST period hPeriod
        (smoothGeneralMetricBVThroatTrace period hPeriod phase) := by
  apply Prod.ext
  · rfl
  · apply Prod.ext <;>
      exact smoothSymmetricTensorThroatTrace_zero period hPeriod

/-! ## PT/exchange naturality -/

theorem smoothSymmetricTensorThroatTrace_pt_natural
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveThroat period hPeriod)
    (first second : ThroatTangentFiber period hPeriod point) :
    (smoothSymmetricTensorThroatTrace period hPeriod
        (smoothPTTensorPullback period hPeriod tensor)).tensor
        point first second =
      throatPTTensorPullbackValue period hPeriod
        (smoothSymmetricTensorThroatTrace period hPeriod tensor)
        point first second := by
  simp only [smoothSymmetricTensorThroatTrace_apply,
    throatPTTensorPullbackValue_apply, smoothPTTensorPullback_apply]
  rw [fixedThroatQuotientInclusion_mfderiv_pt_equivariant
      period hPeriod point first,
    fixedThroatQuotientInclusion_mfderiv_pt_equivariant
      period hPeriod point second,
    fixedThroatQuotientInclusion_pt_equivariant period hPeriod point]

def smoothGeneralMetricTensorPairThroatTrace
    (tensors : SmoothGeneralMetricTensorPair period hPeriod) :
    SmoothThroatGeneralMetricTensorPair period hPeriod :=
  (smoothSymmetricTensorThroatTrace period hPeriod tensors.1,
    smoothSymmetricTensorThroatTrace period hPeriod tensors.2)

theorem smoothGeneralMetricTensorPairThroatTrace_ptExchange_matched
    (tensors : SmoothGeneralMetricTensorPair period hPeriod) :
    MetricThroatDirichletPTExchangeMatched period hPeriod
      (smoothGeneralMetricTensorPairThroatTrace period hPeriod
        (smoothGeneralMetricTensorPairPTExchange period hPeriod tensors))
      (smoothGeneralMetricTensorPairThroatTrace
        period hPeriod tensors) := by
  intro point
  constructor
  · apply ContinuousLinearMap.ext
    intro first
    apply ContinuousLinearMap.ext
    intro second
    exact smoothSymmetricTensorThroatTrace_pt_natural
      period hPeriod tensors.2 point first second
  · apply ContinuousLinearMap.ext
    intro first
    apply ContinuousLinearMap.ext
    intro second
    exact smoothSymmetricTensorThroatTrace_pt_natural
      period hPeriod tensors.1 point first second

/-- Pointwise PT/exchange matching for the restricted variation and
antifield pairs. -/
def SmoothThroatGeneralMetricBVPTExchangeMatched
    (after before : SmoothThroatGeneralMetricBVField period hPeriod) : Prop :=
  MetricThroatDirichletPTExchangeMatched period hPeriod after.1 before.1 ∧
    MetricThroatDirichletPTExchangeMatched period hPeriod after.2 before.2

theorem smoothGeneralMetricBVThroatTrace_ptExchange_matched
    (phase : SmoothGeneralMetricBVField period hPeriod) :
    SmoothThroatGeneralMetricBVPTExchangeMatched period hPeriod
      (smoothGeneralMetricBVThroatTrace period hPeriod
        (smoothGeneralMetricBVPTExchange period hPeriod phase))
      (smoothGeneralMetricBVThroatTrace period hPeriod phase) := by
  exact ⟨
    smoothGeneralMetricTensorPairThroatTrace_ptExchange_matched
      period hPeriod phase.1,
    smoothGeneralMetricTensorPairThroatTrace_ptExchange_matched
      period hPeriod phase.2⟩

theorem smoothThroatGeneralMetricBVPTExchangeMatched_left_unique
    {first second before : SmoothThroatGeneralMetricBVField period hPeriod}
    (hFirst : SmoothThroatGeneralMetricBVPTExchangeMatched
      period hPeriod first before)
    (hSecond : SmoothThroatGeneralMetricBVPTExchangeMatched
      period hPeriod second before) :
    first = second := by
  apply Prod.ext
  · exact metricThroatDirichletPTExchangeMatched_left_unique
      period hPeriod hFirst.1 hSecond.1
  · exact metricThroatDirichletPTExchangeMatched_left_unique
      period hPeriod hFirst.2 hSecond.2

/-! ## Complete boundary packet and Dirichlet transport -/

/-- General independent fields with the PT/exchange action extended to the
first metric BV level. -/
def generalLorentzIndependentFieldsWithMetricBVPTExchange
    (packet : GeneralLorentzIndependentFieldsWithMetricBV period hPeriod) :
    GeneralLorentzIndependentFieldsWithMetricBV period hPeriod where
  independent := generalLorentzIndependentExchange
    period hPeriod packet.independent
  metricBV := smoothGeneralMetricBVPTExchange period hPeriod packet.metricBV

theorem generalLorentzIndependentFieldsWithMetricBVPTExchange_commutes_BRST
    (packet : GeneralLorentzIndependentFieldsWithMetricBV period hPeriod) :
    smoothGeneralMetricBVPTExchange period hPeriod
        (smoothGeneralMetricBVBRST period hPeriod packet.metricBV) =
      smoothGeneralMetricBVBRST period hPeriod
        (generalLorentzIndependentFieldsWithMetricBVPTExchange
          period hPeriod packet).metricBV :=
  smoothGeneralMetricBVPTExchange_commutes_BRST
    period hPeriod packet.metricBV

/-- Metric-extended independent boundary data together with the smooth
variation/antifield throat traces. -/
@[ext]
structure GeneralLorentzIndependentBoundaryDataWithMetricBV where
  independentMetric :
    GeneralLorentzIndependentBoundaryDataWithMetric period hPeriod
  metricBV : SmoothThroatGeneralMetricBVField period hPeriod

def generalLorentzIndependentBoundaryTraceWithMetricBV
    (packet : GeneralLorentzIndependentFieldsWithMetricBV period hPeriod) :
    GeneralLorentzIndependentBoundaryDataWithMetricBV period hPeriod where
  independentMetric :=
    generalLorentzIndependentBoundaryTraceWithMetric
      period hPeriod packet.independent
  metricBV := smoothGeneralMetricBVThroatTrace
    period hPeriod packet.metricBV

/-- Honest matched PT/exchange relation for the complete boundary. -/
def GeneralLorentzMetricBVBoundaryPTExchangeMatched
    (after before :
      GeneralLorentzIndependentBoundaryDataWithMetricBV period hPeriod) : Prop :=
  GeneralLorentzMetricBoundaryPTExchangeMatched period hPeriod
      after.independentMetric before.independentMetric ∧
    SmoothThroatGeneralMetricBVPTExchangeMatched period hPeriod
      after.metricBV before.metricBV

theorem generalLorentzIndependentBoundaryTraceWithMetricBV_exchange_matched
    (packet : GeneralLorentzIndependentFieldsWithMetricBV period hPeriod) :
    GeneralLorentzMetricBVBoundaryPTExchangeMatched period hPeriod
      (generalLorentzIndependentBoundaryTraceWithMetricBV period hPeriod
        (generalLorentzIndependentFieldsWithMetricBVPTExchange
          period hPeriod packet))
      (generalLorentzIndependentBoundaryTraceWithMetricBV
        period hPeriod packet) := by
  exact ⟨
    generalLorentzIndependentBoundaryTraceWithMetric_exchange_matched
      period hPeriod packet.independent,
    smoothGeneralMetricBVThroatTrace_ptExchange_matched
      period hPeriod packet.metricBV⟩

theorem generalLorentzMetricBVBoundaryPTExchangeMatched_left_unique
    {first second before :
      GeneralLorentzIndependentBoundaryDataWithMetricBV period hPeriod}
    (hFirst : GeneralLorentzMetricBVBoundaryPTExchangeMatched
      period hPeriod first before)
    (hSecond : GeneralLorentzMetricBVBoundaryPTExchangeMatched
      period hPeriod second before) :
    first = second := by
  apply GeneralLorentzIndependentBoundaryDataWithMetricBV.ext
  · exact generalLorentzMetricBoundaryPTExchangeMatched_left_unique
      period hPeriod hFirst.1 hSecond.1
  · exact smoothThroatGeneralMetricBVPTExchangeMatched_left_unique
      period hPeriod hFirst.2 hSecond.2

def SatisfiesGeneralLorentzMetricBVBoundary
    (boundary :
      GeneralLorentzIndependentBoundaryDataWithMetricBV period hPeriod)
    (packet : GeneralLorentzIndependentFieldsWithMetricBV period hPeriod) : Prop :=
  generalLorentzIndependentBoundaryTraceWithMetricBV period hPeriod packet =
    boundary

/-- Matched PT/exchange references transport the complete Dirichlet
condition, including metric variations and antifields. -/
theorem satisfiesGeneralLorentzMetricBVBoundary_exchange
    {before after :
      GeneralLorentzIndependentBoundaryDataWithMetricBV period hPeriod}
    {packet : GeneralLorentzIndependentFieldsWithMetricBV period hPeriod}
    (hBoundary : SatisfiesGeneralLorentzMetricBVBoundary
      period hPeriod before packet)
    (hMatched : GeneralLorentzMetricBVBoundaryPTExchangeMatched
      period hPeriod after before) :
    SatisfiesGeneralLorentzMetricBVBoundary period hPeriod after
      (generalLorentzIndependentFieldsWithMetricBVPTExchange
        period hPeriod packet) := by
  unfold SatisfiesGeneralLorentzMetricBVBoundary at hBoundary ⊢
  rw [← hBoundary] at hMatched
  exact generalLorentzMetricBVBoundaryPTExchangeMatched_left_unique
    period hPeriod
    (generalLorentzIndependentBoundaryTraceWithMetricBV_exchange_matched
      period hPeriod packet)
    hMatched

/-! ## Packet-level pointwise bracket covariance -/

theorem generalLorentzPacketMetricBVOddAntibracketAt_ptExchange
    (packet : GeneralLorentzIndependentFieldsWithMetricBV period hPeriod)
    (first second : GeneralMetricBVPointObservable period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    generalLorentzPacketMetricBVOddAntibracketAt period hPeriod
        (generalLorentzIndependentFieldsWithMetricBVPTExchange
          period hPeriod packet)
        (generalMetricBVPointObservablePTExchange period hPeriod first)
        (generalMetricBVPointObservablePTExchange period hPeriod second)
        point =
      generalLorentzPacketMetricBVOddAntibracketAt period hPeriod packet
        first second (reflectedSpherePT period hPeriod point) := by
  exact generalMetricBVOddAntibracketAt_ptExchange period hPeriod
    packet.independent.metrics first second packet.metricBV point

end

end P0EFTJanusMappingTorusGeneralLorentzMetricBVThroatBoundary4D
end JanusFormal
