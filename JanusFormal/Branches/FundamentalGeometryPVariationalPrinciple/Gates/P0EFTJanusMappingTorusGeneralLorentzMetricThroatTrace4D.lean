import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusSmoothThroatEmbedding
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralLorentzIndependentFieldPacket4D

/-!
# Restriction of a general Lorentz metric to the D8 throat

The covariant tensor of an arbitrary smooth Lorentz metric is pulled back by
the differential of the actual throat inclusion.  The result is a genuine
smooth symmetric covariant two-tensor on the three-dimensional throat.

Ambient Lorentz nondegeneracy does not imply nondegeneracy of this restriction:
the throat may be null.  Consequently the exact additional condition, absence
of a tangential radical, is kept explicit and proved equivalent to
nondegeneracy of the induced tensor.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 300000

noncomputable section

open scoped Manifold ContDiff Topology
open Bundle Filter
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusPTInvolution
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothThroatEmbedding
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricPTScalarAction4D
open P0EFTJanusMappingTorusGeneralLorentzIndependentFieldPacket4D

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

abbrev ThroatTangentFiber (point : EffectiveThroat period hPeriod) :=
  TangentSpace throatCoverModelWithCorners point

abbrev ThroatCotangentFiber (point : EffectiveThroat period hPeriod) :=
  ThroatTangentFiber period hPeriod point →L[Real] Real

abbrev ThroatCovariantTwoTensorFiber
    (point : EffectiveThroat period hPeriod) :=
  ThroatTangentFiber period hPeriod point →L[Real]
    ThroatCotangentFiber period hPeriod point

abbrev ThroatCovariantTwoTensorModel :=
  ThroatCoverCoordinates →L[Real] ThroatCoverCoordinates →L[Real] Real

/-- Genuine smooth covariant rank-two tensors on the actual D8 throat. -/
abbrev SmoothThroatCovariantTwoTensor :=
  ContMDiffSection throatCoverModelWithCorners
    ThroatCovariantTwoTensorModel ∞
    (ThroatCovariantTwoTensorFiber period hPeriod)

/-- Smooth symmetric covariant rank-two tensors intrinsic to the throat. -/
structure SmoothSymmetricThroatCovariantTwoTensor where
  tensor : SmoothThroatCovariantTwoTensor period hPeriod
  symmetric : ∀ point first second,
    tensor point first second = tensor point second first

@[ext]
theorem SmoothSymmetricThroatCovariantTwoTensor.ext
    {first second : SmoothSymmetricThroatCovariantTwoTensor period hPeriod}
    (hTensor : first.tensor = second.tensor) : first = second := by
  cases first
  cases second
  cases hTensor
  rfl

private abbrev AmbientTangentFiber
    (point : EffectiveThroat period hPeriod) :=
  TangentSpace coverModelWithCorners
    (fixedThroatQuotientInclusion period hPeriod point)

/-- Pointwise covariant pullback through the differential of the actual
throat inclusion. -/
def generalLorentzMetricThroatTraceValue
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    ThroatCovariantTwoTensorFiber period hPeriod point :=
  let derivative :=
    mfderiv throatCoverModelWithCorners coverModelWithCorners
      (fixedThroatQuotientInclusion period hPeriod) point
  (derivative.precomp Real).comp
    ((metric.tensor.tensor
      (fixedThroatQuotientInclusion period hPeriod point)).comp derivative)

@[simp]
theorem generalLorentzMetricThroatTraceValue_apply
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (point : EffectiveThroat period hPeriod)
    (first second : ThroatTangentFiber period hPeriod point) :
    generalLorentzMetricThroatTraceValue period hPeriod metric point first second =
      metric.tensor.tensor (fixedThroatQuotientInclusion period hPeriod point)
        (mfderiv throatCoverModelWithCorners coverModelWithCorners
          (fixedThroatQuotientInclusion period hPeriod) point first)
        (mfderiv throatCoverModelWithCorners coverModelWithCorners
          (fixedThroatQuotientInclusion period hPeriod) point second) :=
  rfl

theorem generalLorentzMetricThroatTraceValue_symmetric
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (point : EffectiveThroat period hPeriod)
    (first second : ThroatTangentFiber period hPeriod point) :
    generalLorentzMetricThroatTraceValue period hPeriod metric point first second =
      generalLorentzMetricThroatTraceValue period hPeriod metric point second first := by
  simp only [generalLorentzMetricThroatTraceValue_apply]
  exact metric.tensor.symmetric _ _ _

private def inclusionDerivativeCoordinates
    (point current : EffectiveThroat period hPeriod) :
    ThroatCoverCoordinates →L[Real] CoverCoordinates :=
  inTangentCoordinates throatCoverModelWithCorners coverModelWithCorners
    id (fixedThroatQuotientInclusion period hPeriod)
    (mfderiv throatCoverModelWithCorners coverModelWithCorners
      (fixedThroatQuotientInclusion period hPeriod)) point current

private def ambientTensorCoordinates
    (metric : SmoothGeneralLorentzMetric period hPeriod)
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
    (metric.tensor.tensor
      (fixedThroatQuotientInclusion period hPeriod current))

private def throatTraceTensorCoordinates
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (point current : EffectiveThroat period hPeriod) :
    ThroatCovariantTwoTensorModel :=
  ContinuousLinearMap.inCoordinates ThroatCoverCoordinates
    (ThroatTangentFiber period hPeriod)
    (ThroatCoverCoordinates →L[Real] Real)
    (ThroatCotangentFiber period hPeriod)
    point current point current
    (generalLorentzMetricThroatTraceValue period hPeriod metric current)

private def coordinateRestriction
    (derivative : ThroatCoverCoordinates →L[Real] CoverCoordinates)
    (tensor : CoverCoordinates →L[Real] CoverCoordinates →L[Real] Real) :
    ThroatCovariantTwoTensorModel :=
  (derivative.precomp Real).comp (tensor.comp derivative)

private theorem inclusionDerivativeCoordinates_apply
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
    inclusionDerivativeCoordinates period hPeriod point current vector =
      (trivializationAt CoverCoordinates
        (fun base : EffectiveQuotient period hPeriod =>
          TangentSpace coverModelWithCorners base)
        (fixedThroatQuotientInclusion period hPeriod point)).linearMapAt Real
          (fixedThroatQuotientInclusion period hPeriod current)
          (mfderiv throatCoverModelWithCorners coverModelWithCorners
            (fixedThroatQuotientInclusion period hPeriod) current
            ((trivializationAt ThroatCoverCoordinates
              (ThroatTangentFiber period hPeriod) point).symm current vector)) := by
  rw [show inclusionDerivativeCoordinates period hPeriod point current =
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

private theorem throatTraceTensorCoordinates_eq
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (point current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) point).baseSet)
    (hImage : fixedThroatQuotientInclusion period hPeriod current ∈
      (trivializationAt CoverCoordinates
        (fun base : EffectiveQuotient period hPeriod =>
          TangentSpace coverModelWithCorners base)
        (fixedThroatQuotientInclusion period hPeriod point)).baseSet) :
    throatTraceTensorCoordinates period hPeriod metric point current =
      coordinateRestriction
        (inclusionDerivativeCoordinates period hPeriod point current)
        (ambientTensorCoordinates period hPeriod metric point current) := by
  apply ContinuousLinearMap.ext
  intro first
  apply ContinuousLinearMap.ext
  intro second
  rw [show throatTraceTensorCoordinates period hPeriod metric point current
        first second =
      ContinuousLinearMap.inCoordinates ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod)
        (ThroatCoverCoordinates →L[Real] Real)
        (ThroatCotangentFiber period hPeriod)
        point current point current
        (generalLorentzMetricThroatTraceValue period hPeriod metric current)
        first second by rfl]
  rw [inCoordinates_apply_eq₂ hCurrent hCurrent (Set.mem_univ _)]
  simp only [generalLorentzMetricThroatTraceValue_apply,
    coordinateRestriction, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.precomp_apply]
  rw [show ambientTensorCoordinates period hPeriod metric point current
        (inclusionDerivativeCoordinates period hPeriod point current first)
        (inclusionDerivativeCoordinates period hPeriod point current second) =
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
        (metric.tensor.tensor
          (fixedThroatQuotientInclusion period hPeriod current))
        (inclusionDerivativeCoordinates period hPeriod point current first)
        (inclusionDerivativeCoordinates period hPeriod point current second) by rfl]
  rw [inCoordinates_apply_eq₂ hImage hImage (Set.mem_univ _)]
  rw [inclusionDerivativeCoordinates_apply period hPeriod point current
      hCurrent hImage first,
    inclusionDerivativeCoordinates_apply period hPeriod point current
      hCurrent hImage second]
  simp only [Trivialization.symm_linearMapAt _ hImage]
  rfl

theorem generalLorentzMetricThroatTraceValue_contMDiff
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    ContMDiff throatCoverModelWithCorners
      (throatCoverModelWithCorners.prod
        𝓘(Real, ThroatCovariantTwoTensorModel)) ∞
      (fun point => TotalSpace.mk' ThroatCovariantTwoTensorModel
        (E := ThroatCovariantTwoTensorFiber period hPeriod) point
        (generalLorentzMetricThroatTraceValue period hPeriod metric point)) := by
  intro point
  have hD :=
    (fixedThroatQuotientInclusion_contMDiff period hPeriod).contMDiffAt
      |>.mfderiv_const (x₀ := point) (m := ∞) (by simp)
  have hMap :=
    (fixedThroatQuotientInclusion_contMDiff period hPeriod).of_le
      (m := ∞) (by simp)
  have hTensor := metric.tensor.tensor.contMDiff.comp hMap
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
  simpa only [throatTraceTensorCoordinates, coordinateRestriction,
    inclusionDerivativeCoordinates, ambientTensorCoordinates,
    Function.comp_apply] using
      (throatTraceTensorCoordinates_eq period hPeriod metric point current
        hCurrent' hImage')

/-- Smooth symmetric tensor induced on the actual throat. -/
def generalLorentzMetricThroatTrace
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    SmoothSymmetricThroatCovariantTwoTensor period hPeriod where
  tensor :=
    { toFun := generalLorentzMetricThroatTraceValue period hPeriod metric
      contMDiff_toFun :=
        generalLorentzMetricThroatTraceValue_contMDiff period hPeriod metric }
  symmetric := generalLorentzMetricThroatTraceValue_symmetric
    period hPeriod metric

@[simp]
theorem generalLorentzMetricThroatTrace_apply
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (point : EffectiveThroat period hPeriod)
    (first second : ThroatTangentFiber period hPeriod point) :
    (generalLorentzMetricThroatTrace period hPeriod metric).tensor point
        first second =
      metric.tensor.tensor (fixedThroatQuotientInclusion period hPeriod point)
        (mfderiv throatCoverModelWithCorners coverModelWithCorners
          (fixedThroatQuotientInclusion period hPeriod) point first)
        (mfderiv throatCoverModelWithCorners coverModelWithCorners
          (fixedThroatQuotientInclusion period hPeriod) point second) :=
  rfl

/-- Exact transversality condition needed for the induced throat tensor to be
nondegenerate: it has no nonzero vector orthogonal to every tangent vector. -/
def HasNoTangentialRadical
    (metric : SmoothGeneralLorentzMetric period hPeriod) : Prop :=
  ∀ (point : EffectiveThroat period hPeriod)
      (first : ThroatTangentFiber period hPeriod point),
    (∀ second : ThroatTangentFiber period hPeriod point,
      metric.tensor.tensor (fixedThroatQuotientInclusion period hPeriod point)
        (mfderiv throatCoverModelWithCorners coverModelWithCorners
          (fixedThroatQuotientInclusion period hPeriod) point first)
        (mfderiv throatCoverModelWithCorners coverModelWithCorners
          (fixedThroatQuotientInclusion period hPeriod) point second) = 0) →
    first = 0

/-- Fiberwise algebraic nondegeneracy for a throat covariant tensor. -/
def ThroatTensorIsNondegenerate
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod) : Prop :=
  ∀ point, Function.Injective (tensor.tensor point)

theorem throatTrace_nondegenerate_iff_no_tangential_radical
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    ThroatTensorIsNondegenerate period hPeriod
        (generalLorentzMetricThroatTrace period hPeriod metric) ↔
      HasNoTangentialRadical period hPeriod metric := by
  constructor
  · intro hNondegenerate point first hRadical
    apply hNondegenerate point
    apply ContinuousLinearMap.ext
    intro second
    simpa using hRadical second
  · intro hRadical point first second hEqual
    have hDifference : ∀ tangent : ThroatTangentFiber period hPeriod point,
        metric.tensor.tensor
            (fixedThroatQuotientInclusion period hPeriod point)
            (mfderiv throatCoverModelWithCorners coverModelWithCorners
              (fixedThroatQuotientInclusion period hPeriod) point
              (first - second))
            (mfderiv throatCoverModelWithCorners coverModelWithCorners
              (fixedThroatQuotientInclusion period hPeriod) point tangent) = 0 := by
      intro tangent
      have hEvaluate := congrArg (fun covector => covector tangent) hEqual
      have hEvaluate' :
          metric.tensor.tensor
              (fixedThroatQuotientInclusion period hPeriod point)
              (mfderiv throatCoverModelWithCorners coverModelWithCorners
                (fixedThroatQuotientInclusion period hPeriod) point first)
              (mfderiv throatCoverModelWithCorners coverModelWithCorners
                (fixedThroatQuotientInclusion period hPeriod) point tangent) =
            metric.tensor.tensor
              (fixedThroatQuotientInclusion period hPeriod point)
              (mfderiv throatCoverModelWithCorners coverModelWithCorners
                (fixedThroatQuotientInclusion period hPeriod) point second)
              (mfderiv throatCoverModelWithCorners coverModelWithCorners
                (fixedThroatQuotientInclusion period hPeriod) point tangent) := by
        simpa only [generalLorentzMetricThroatTrace_apply] using hEvaluate
      simpa only [map_sub, sub_apply] using (sub_eq_zero.mpr hEvaluate')
    exact sub_eq_zero.mp (hRadical point (first - second) hDifference)

/-- The non-null throat-metric domain.  Membership supplies precisely the
extra hypothesis absent for an arbitrary ambient Lorentz metric. -/
def SmoothNondegenerateThroatMetric :=
  {tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod //
    ThroatTensorIsNondegenerate period hPeriod tensor}

def generalLorentzMetricNondegenerateThroatTrace
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (hTransverse : HasNoTangentialRadical period hPeriod metric) :
    SmoothNondegenerateThroatMetric period hPeriod :=
  ⟨generalLorentzMetricThroatTrace period hPeriod metric,
    (throatTrace_nondegenerate_iff_no_tangential_radical
      period hPeriod metric).2 hTransverse⟩

/-- Boundary data extending the previous independent packet by the two actual
general-metric throat tensors.  No nondegeneracy is silently imposed. -/
@[ext]
structure GeneralLorentzIndependentBoundaryDataWithMetric where
  metrics : SmoothSymmetricThroatCovariantTwoTensor period hPeriod ×
    SmoothSymmetricThroatCovariantTwoTensor period hPeriod
  nonMetric : GeneralLorentzIndependentBoundaryData period hPeriod

/-- Complete restriction of the independent packet, now including both
general metric tensors on the throat. -/
def generalLorentzIndependentBoundaryTraceWithMetric
    (fields : GeneralLorentzIndependentFields period hPeriod) :
    GeneralLorentzIndependentBoundaryDataWithMetric period hPeriod where
  metrics :=
    (generalLorentzMetricThroatTrace period hPeriod fields.metrics.1,
      generalLorentzMetricThroatTrace period hPeriod fields.metrics.2)
  nonMetric := generalLorentzIndependentBoundaryTrace period hPeriod fields

@[simp]
theorem generalLorentzIndependentBoundaryTraceWithMetric_metrics
    (fields : GeneralLorentzIndependentFields period hPeriod) :
    (generalLorentzIndependentBoundaryTraceWithMetric
      period hPeriod fields).metrics =
      (generalLorentzMetricThroatTrace period hPeriod fields.metrics.1,
        generalLorentzMetricThroatTrace period hPeriod fields.metrics.2) :=
  rfl

@[simp]
theorem generalLorentzIndependentBoundaryTraceWithMetric_nonMetric
    (fields : GeneralLorentzIndependentFields period hPeriod) :
    (generalLorentzIndependentBoundaryTraceWithMetric
      period hPeriod fields).nonMetric =
      generalLorentzIndependentBoundaryTrace period hPeriod fields :=
  rfl

/-- Both induced boundary tensors are nondegenerate exactly under the two
explicit transversality conditions. -/
theorem generalLorentzIndependentBoundaryTrace_metrics_nondegenerate_iff
    (fields : GeneralLorentzIndependentFields period hPeriod) :
    (ThroatTensorIsNondegenerate period hPeriod
        (generalLorentzIndependentBoundaryTraceWithMetric
          period hPeriod fields).metrics.1 ∧
      ThroatTensorIsNondegenerate period hPeriod
        (generalLorentzIndependentBoundaryTraceWithMetric
          period hPeriod fields).metrics.2) ↔
      (HasNoTangentialRadical period hPeriod fields.metrics.1 ∧
        HasNoTangentialRadical period hPeriod fields.metrics.2) := by
  exact and_congr
    (throatTrace_nondegenerate_iff_no_tangential_radical
      period hPeriod fields.metrics.1)
    (throatTrace_nondegenerate_iff_no_tangential_radical
      period hPeriod fields.metrics.2)

end

end P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
end JanusFormal
