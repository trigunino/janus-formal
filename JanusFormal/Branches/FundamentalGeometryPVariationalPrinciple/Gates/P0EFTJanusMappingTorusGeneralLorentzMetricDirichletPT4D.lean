import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralLorentzMetricThroatPTRadical4D

/-!
# PT-compatible general-metric Dirichlet data

General throat metric references are kept as genuine smooth tensors.  Since
an arbitrary smooth intrinsic tensor pullback is not yet packaged, PT/exchange
is represented honestly by its exact pointwise values and a matching
relation.  Actual ambient metric traces satisfy that relation by naturality,
which is enough to transport full metric and non-metric Dirichlet data.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusGeneralLorentzMetricDirichletPT4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusPTInvolution
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricPTScalarAction4D
open P0EFTJanusMappingTorusGeneralLorentzIndependentFieldPacket4D
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatPTNaturality4D
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatPTRadical4D

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

/-- Two genuine smooth throat tensors used as metric Dirichlet references. -/
abbrev MetricThroatDirichletReference :=
  SmoothSymmetricThroatCovariantTwoTensor period hPeriod ×
    SmoothSymmetricThroatCovariantTwoTensor period hPeriod

/-- Exact pointwise PT/exchange action on a metric throat reference. -/
def metricThroatDirichletPTExchangeValue
    (reference : MetricThroatDirichletReference period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    ThroatCovariantTwoTensorFiber period hPeriod point ×
      ThroatCovariantTwoTensorFiber period hPeriod point :=
  (throatPTTensorPullbackValue period hPeriod reference.2 point,
    throatPTTensorPullbackValue period hPeriod reference.1 point)

/-- A smooth reference realizes the pointwise PT/exchange of another one.
This relation avoids postulating a missing arbitrary smooth pullback API. -/
def MetricThroatDirichletPTExchangeMatched
    (after before : MetricThroatDirichletReference period hPeriod) : Prop :=
  ∀ point,
    after.1.tensor point =
        (metricThroatDirichletPTExchangeValue
          period hPeriod before point).1 ∧
      after.2.tensor point =
        (metricThroatDirichletPTExchangeValue
          period hPeriod before point).2

/-- Pointwise PT/exchange matching determines a smooth output uniquely. -/
theorem metricThroatDirichletPTExchangeMatched_left_unique
    {first second before : MetricThroatDirichletReference period hPeriod}
    (hFirst : MetricThroatDirichletPTExchangeMatched
      period hPeriod first before)
    (hSecond : MetricThroatDirichletPTExchangeMatched
      period hPeriod second before) :
    first = second := by
  apply Prod.ext
  · apply SmoothSymmetricThroatCovariantTwoTensor.ext
    apply ContMDiffSection.ext
    intro point
    exact (hFirst point).1.trans (hSecond point).1.symm
  · apply SmoothSymmetricThroatCovariantTwoTensor.ext
    apply ContMDiffSection.ext
    intro point
    exact (hFirst point).2.trans (hSecond point).2.symm

/-- Nondegeneracy of both reference tensors is preserved and reflected by
the honest pointwise PT/exchange relation. -/
theorem metricThroatDirichletPTExchangeMatched_nondegenerate_iff
    {after before : MetricThroatDirichletReference period hPeriod}
    (hMatched : MetricThroatDirichletPTExchangeMatched
      period hPeriod after before) :
    (ThroatTensorIsNondegenerate period hPeriod after.1 ∧
        ThroatTensorIsNondegenerate period hPeriod after.2) ↔
      (ThroatTensorIsNondegenerate period hPeriod before.1 ∧
        ThroatTensorIsNondegenerate period hPeriod before.2) := by
  unfold MetricThroatDirichletPTExchangeMatched at hMatched
  simp only [metricThroatDirichletPTExchangeValue] at hMatched
  have hFirst :
      ThroatTensorIsNondegenerate period hPeriod after.1 ↔
        ThroatTensorIsNondegenerate period hPeriod before.2 := by
    have hPointwise :
        ThroatTensorIsNondegenerate period hPeriod after.1 ↔
          ThroatPTPullbackIsNondegenerate period hPeriod before.2 := by
      constructor
      · intro hAfter point
        rw [← (hMatched point).1]
        exact hAfter point
      · intro hPullback point
        rw [(hMatched point).1]
        exact hPullback point
    exact hPointwise.trans
      (throatPTPullbackIsNondegenerate_iff period hPeriod before.2)
  have hSecond :
      ThroatTensorIsNondegenerate period hPeriod after.2 ↔
        ThroatTensorIsNondegenerate period hPeriod before.1 := by
    have hPointwise :
        ThroatTensorIsNondegenerate period hPeriod after.2 ↔
          ThroatPTPullbackIsNondegenerate period hPeriod before.1 := by
      constructor
      · intro hAfter point
        rw [← (hMatched point).2]
        exact hAfter point
      · intro hPullback point
        rw [(hMatched point).2]
        exact hPullback point
    exact hPointwise.trans
      (throatPTPullbackIsNondegenerate_iff period hPeriod before.1)
  constructor
  · rintro ⟨hAfterFirst, hAfterSecond⟩
    exact ⟨hSecond.1 hAfterSecond, hFirst.1 hAfterFirst⟩
  · rintro ⟨hBeforeFirst, hBeforeSecond⟩
    exact ⟨hFirst.2 hBeforeSecond, hSecond.2 hBeforeFirst⟩

/-- PT/exchange matching for the complete metric-extended boundary packet. -/
def GeneralLorentzMetricBoundaryPTExchangeMatched
    (after before :
      GeneralLorentzIndependentBoundaryDataWithMetric period hPeriod) : Prop :=
  MetricThroatDirichletPTExchangeMatched period hPeriod
      after.metrics before.metrics ∧
    after.nonMetric =
      generalLorentzIndependentBoundaryExchange
        period hPeriod before.nonMetric

/-- The complete metric-extended boundary action relation is functional. -/
theorem generalLorentzMetricBoundaryPTExchangeMatched_left_unique
    {first second before :
      GeneralLorentzIndependentBoundaryDataWithMetric period hPeriod}
    (hFirst : GeneralLorentzMetricBoundaryPTExchangeMatched
      period hPeriod first before)
    (hSecond : GeneralLorentzMetricBoundaryPTExchangeMatched
      period hPeriod second before) :
    first = second := by
  apply GeneralLorentzIndependentBoundaryDataWithMetric.ext
  · exact metricThroatDirichletPTExchangeMatched_left_unique
      period hPeriod hFirst.1 hSecond.1
  · exact hFirst.2.trans hSecond.2.symm

/-- The actual full boundary trace intertwines ambient field PT/exchange with
the exact pointwise metric action and the smooth non-metric action. -/
theorem generalLorentzIndependentBoundaryTraceWithMetric_exchange_matched
    (fields : GeneralLorentzIndependentFields period hPeriod) :
    GeneralLorentzMetricBoundaryPTExchangeMatched period hPeriod
      (generalLorentzIndependentBoundaryTraceWithMetric period hPeriod
        (generalLorentzIndependentExchange period hPeriod fields))
      (generalLorentzIndependentBoundaryTraceWithMetric
        period hPeriod fields) := by
  constructor
  · intro point
    constructor
    · apply ContinuousLinearMap.ext
      intro first
      apply ContinuousLinearMap.ext
      intro second
      exact (generalLorentzMetricThroatTrace_ptExchange_natural
        period hPeriod fields.metrics point first second).1
    · apply ContinuousLinearMap.ext
      intro first
      apply ContinuousLinearMap.ext
      intro second
      exact (generalLorentzMetricThroatTrace_ptExchange_natural
        period hPeriod fields.metrics point first second).2
  · exact generalLorentzIndependentBoundaryTrace_exchange
      period hPeriod fields

/-- Exact Dirichlet equality for the complete metric-extended packet. -/
def SatisfiesGeneralLorentzMetricBoundary
    (boundary :
      GeneralLorentzIndependentBoundaryDataWithMetric period hPeriod)
    (fields : GeneralLorentzIndependentFields period hPeriod) : Prop :=
  generalLorentzIndependentBoundaryTraceWithMetric period hPeriod fields =
    boundary

/-- A matched reference transports the full Dirichlet condition exactly
under simultaneous PT and sector exchange. -/
theorem satisfiesGeneralLorentzMetricBoundary_exchange
    {before after :
      GeneralLorentzIndependentBoundaryDataWithMetric period hPeriod}
    {fields : GeneralLorentzIndependentFields period hPeriod}
    (hBoundary : SatisfiesGeneralLorentzMetricBoundary
      period hPeriod before fields)
    (hMatched : GeneralLorentzMetricBoundaryPTExchangeMatched
      period hPeriod after before) :
    SatisfiesGeneralLorentzMetricBoundary period hPeriod after
      (generalLorentzIndependentExchange period hPeriod fields) := by
  unfold SatisfiesGeneralLorentzMetricBoundary at hBoundary ⊢
  rw [← hBoundary] at hMatched
  exact generalLorentzMetricBoundaryPTExchangeMatched_left_unique
    period hPeriod
    (generalLorentzIndependentBoundaryTraceWithMetric_exchange_matched
      period hPeriod fields)
    hMatched

/-- The metric part of the actual exchanged boundary remains nondegenerate
exactly when the original metric boundary was nondegenerate. -/
theorem generalLorentzIndependentBoundaryTraceWithMetric_exchange_nondegenerate_iff
    (fields : GeneralLorentzIndependentFields period hPeriod) :
    (ThroatTensorIsNondegenerate period hPeriod
          (generalLorentzIndependentBoundaryTraceWithMetric period hPeriod
            (generalLorentzIndependentExchange period hPeriod fields)).metrics.1 ∧
        ThroatTensorIsNondegenerate period hPeriod
          (generalLorentzIndependentBoundaryTraceWithMetric period hPeriod
            (generalLorentzIndependentExchange period hPeriod fields)).metrics.2) ↔
      (ThroatTensorIsNondegenerate period hPeriod
          (generalLorentzIndependentBoundaryTraceWithMetric
            period hPeriod fields).metrics.1 ∧
        ThroatTensorIsNondegenerate period hPeriod
          (generalLorentzIndependentBoundaryTraceWithMetric
            period hPeriod fields).metrics.2) :=
  metricThroatDirichletPTExchangeMatched_nondegenerate_iff period hPeriod
    (generalLorentzIndependentBoundaryTraceWithMetric_exchange_matched
      period hPeriod fields).1

end

end P0EFTJanusMappingTorusGeneralLorentzMetricDirichletPT4D
end JanusFormal
