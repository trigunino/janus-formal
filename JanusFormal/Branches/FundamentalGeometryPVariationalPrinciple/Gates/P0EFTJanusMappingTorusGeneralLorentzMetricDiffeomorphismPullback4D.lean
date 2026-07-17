import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralLorentzMetricDiffeomorphismNoether4D

/-!
# Unconditional diffeomorphism pullback of general Lorentz metrics

Tangent and iterated Hom-bundle coordinates prove smoothness of the covariant
two-tensor pullback by any smooth D8 self-diffeomorphism.  The genuine
derivative then transports the musical equivalence and Lorentz inertia,
discharging the pullback contract used by scalar-action covariance.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusGeneralLorentzMetricDiffeomorphismPullback4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 300000

noncomputable section

open scoped Manifold ContDiff Topology
open Bundle Filter
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusDiagonalDiffeomorphismAction4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarDensityFrameCovariance4D
open P0EFTJanusMappingTorusGeneralLorentzMetricPTIntegratedScalarAction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricDiffeomorphismScalarAction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricDiffeomorphismNoether4D
open P0EFTJanusMappingTorusMetricMatterGaugeNoetherOperator4D
open P0EFTJanusMappingTorusLinearizedDiffeomorphismBRST4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

private abbrev TangentFiber (point : EffectiveQuotient period hPeriod) :=
  TangentSpace coverModelWithCorners point

private abbrev CotangentFiber (point : EffectiveQuotient period hPeriod) :=
  TangentFiber period hPeriod point →L[Real] Real

private abbrev CovariantTwoTensorFiber
    (point : EffectiveQuotient period hPeriod) :=
  TangentFiber period hPeriod point →L[Real]
    CotangentFiber period hPeriod point

private abbrev CovariantTwoTensorModel :=
  CoverCoordinates →L[Real] CoverCoordinates →L[Real] Real

def diffeomorphismTensorPullback
    (diffeomorphism : SpacetimeDiffeomorphism period hPeriod)
    (tensor : CovariantTwoTensorField period hPeriod) :
    CovariantTwoTensorField period hPeriod :=
  fun point => pullbackTensorValue period hPeriod diffeomorphism tensor point

@[simp]
theorem diffeomorphismTensorPullback_apply
    (diffeomorphism : SpacetimeDiffeomorphism period hPeriod)
    (tensor : CovariantTwoTensorField period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (first second : TangentFiber period hPeriod point) :
    diffeomorphismTensorPullback period hPeriod diffeomorphism tensor point
        first second =
      tensor (diffeomorphism point)
        (mfderiv coverModelWithCorners coverModelWithCorners diffeomorphism
          point first)
        (mfderiv coverModelWithCorners coverModelWithCorners diffeomorphism
          point second) :=
  rfl

private def derivativeCoordinates
    (diffeomorphism : SpacetimeDiffeomorphism period hPeriod)
    (point current : EffectiveQuotient period hPeriod) :
    CoverCoordinates →L[Real] CoverCoordinates :=
  inTangentCoordinates coverModelWithCorners coverModelWithCorners
    id diffeomorphism
    (mfderiv coverModelWithCorners coverModelWithCorners diffeomorphism)
    point current

private def tensorCoordinates
    (diffeomorphism : SpacetimeDiffeomorphism period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point current : EffectiveQuotient period hPeriod) :
    CovariantTwoTensorModel :=
  ContinuousLinearMap.inCoordinates CoverCoordinates (TangentFiber period hPeriod)
    (CoverCoordinates →L[Real] Real) (CotangentFiber period hPeriod)
    (diffeomorphism point) (diffeomorphism current)
    (diffeomorphism point) (diffeomorphism current)
    (tensor.tensor (diffeomorphism current))

private def pullbackTensorCoordinates
    (diffeomorphism : SpacetimeDiffeomorphism period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point current : EffectiveQuotient period hPeriod) :
    CovariantTwoTensorModel :=
  ContinuousLinearMap.inCoordinates CoverCoordinates (TangentFiber period hPeriod)
    (CoverCoordinates →L[Real] Real) (CotangentFiber period hPeriod)
    point current point current
    (diffeomorphismTensorPullback period hPeriod diffeomorphism
      tensor.tensor.toTensorField current)

private def coordinatePullback
    (derivative : CoverCoordinates →L[Real] CoverCoordinates)
    (tensor : CovariantTwoTensorModel) : CovariantTwoTensorModel :=
  (derivative.precomp Real).comp (tensor.comp derivative)

private theorem derivativeCoordinates_apply
    (diffeomorphism : SpacetimeDiffeomorphism period hPeriod)
    (point current : EffectiveQuotient period hPeriod)
    (hCurrent : current ∈
      (trivializationAt CoverCoordinates (TangentFiber period hPeriod) point).baseSet)
    (hImage : diffeomorphism current ∈
      (trivializationAt CoverCoordinates (TangentFiber period hPeriod)
        (diffeomorphism point)).baseSet)
    (vector : CoverCoordinates) :
    derivativeCoordinates period hPeriod diffeomorphism point current vector =
      (trivializationAt CoverCoordinates (TangentFiber period hPeriod)
        (diffeomorphism point)).linearMapAt Real (diffeomorphism current)
          (mfderiv coverModelWithCorners coverModelWithCorners diffeomorphism
            current
            ((trivializationAt CoverCoordinates (TangentFiber period hPeriod)
              point).symm current vector)) := by
  rw [show derivativeCoordinates period hPeriod diffeomorphism point current =
      ContinuousLinearMap.inCoordinates CoverCoordinates (TangentFiber period hPeriod)
        CoverCoordinates (TangentFiber period hPeriod)
        point current (diffeomorphism point) (diffeomorphism current)
        (mfderiv coverModelWithCorners coverModelWithCorners diffeomorphism
          current) by rfl]
  rw [ContinuousLinearMap.inCoordinates_eq hCurrent hImage]
  rw [Trivialization.linearMapAt_apply, if_pos hImage]
  rfl

private theorem pullbackTensorCoordinates_eq
    (diffeomorphism : SpacetimeDiffeomorphism period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point current : EffectiveQuotient period hPeriod)
    (hCurrent : current ∈
      (trivializationAt CoverCoordinates (TangentFiber period hPeriod) point).baseSet)
    (hImage : diffeomorphism current ∈
      (trivializationAt CoverCoordinates (TangentFiber period hPeriod)
        (diffeomorphism point)).baseSet) :
    pullbackTensorCoordinates period hPeriod diffeomorphism tensor point current =
      coordinatePullback
        (derivativeCoordinates period hPeriod diffeomorphism point current)
        (tensorCoordinates period hPeriod diffeomorphism tensor point current) := by
  apply ContinuousLinearMap.ext
  intro first
  apply ContinuousLinearMap.ext
  intro second
  rw [show pullbackTensorCoordinates period hPeriod diffeomorphism tensor point
      current first second =
      ContinuousLinearMap.inCoordinates CoverCoordinates (TangentFiber period hPeriod)
        (CoverCoordinates →L[Real] Real) (CotangentFiber period hPeriod)
        point current point current
        (diffeomorphismTensorPullback period hPeriod diffeomorphism
          tensor.tensor.toTensorField current) first second by rfl]
  rw [inCoordinates_apply_eq₂ hCurrent hCurrent (Set.mem_univ _)]
  simp only [diffeomorphismTensorPullback_apply, coordinatePullback,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.precomp_apply]
  rw [show tensorCoordinates period hPeriod diffeomorphism tensor point current
        (derivativeCoordinates period hPeriod diffeomorphism point current first)
        (derivativeCoordinates period hPeriod diffeomorphism point current second) =
      ContinuousLinearMap.inCoordinates CoverCoordinates (TangentFiber period hPeriod)
        (CoverCoordinates →L[Real] Real) (CotangentFiber period hPeriod)
        (diffeomorphism point) (diffeomorphism current)
        (diffeomorphism point) (diffeomorphism current)
        (tensor.tensor (diffeomorphism current))
        (derivativeCoordinates period hPeriod diffeomorphism point current first)
        (derivativeCoordinates period hPeriod diffeomorphism point current second) by rfl]
  rw [inCoordinates_apply_eq₂ hImage hImage (Set.mem_univ _)]
  rw [derivativeCoordinates_apply period hPeriod diffeomorphism point current
      hCurrent hImage first,
    derivativeCoordinates_apply period hPeriod diffeomorphism point current
      hCurrent hImage second]
  simp only [Trivialization.symm_linearMapAt _ hImage]
  rfl

theorem diffeomorphismTensorPullback_contMDiff
    (diffeomorphism : SpacetimeDiffeomorphism period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    ContMDiff coverModelWithCorners
      (coverModelWithCorners.prod 𝓘(Real, CovariantTwoTensorModel)) ∞
      (fun point => TotalSpace.mk' CovariantTwoTensorModel
        (E := CovariantTwoTensorFiber period hPeriod) point
        (diffeomorphismTensorPullback period hPeriod diffeomorphism
          tensor.tensor.toTensorField point)) := by
  intro point
  have hD := diffeomorphism.contMDiff.contMDiffAt.mfderiv_const
    (x₀ := point) (m := ∞) (by simp)
  have hMap := diffeomorphism.contMDiff.of_le (m := ∞) (by simp)
  have hTensor := tensor.tensor.contMDiff.comp hMap
  have hTensorAt := hTensor point
  rw [contMDiffAt_hom_bundle] at hTensorAt
  have hPre := hD.clm_precomp (F₃ := Real)
  have hOuter := hTensorAt.2.clm_comp hD
  have hFormula := hPre.clm_comp hOuter
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  apply hFormula.congr_of_eventuallyEq
  have hCurrent : ∀ᶠ current in 𝓝 point,
      current ∈
        (trivializationAt CoverCoordinates (TangentFiber period hPeriod) point).baseSet :=
    (trivializationAt CoverCoordinates (TangentFiber period hPeriod) point).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt CoverCoordinates
        (TangentFiber period hPeriod) point)
  have hImage : ∀ᶠ current in 𝓝 point,
      diffeomorphism current ∈
        (trivializationAt CoverCoordinates (TangentFiber period hPeriod)
          (diffeomorphism point)).baseSet :=
    diffeomorphism.continuous.continuousAt
      ((trivializationAt CoverCoordinates (TangentFiber period hPeriod)
        (diffeomorphism point)).open_baseSet.mem_nhds
          (mem_baseSet_trivializationAt CoverCoordinates
            (TangentFiber period hPeriod) (diffeomorphism point)))
  filter_upwards [hCurrent, hImage] with current hCurrent' hImage'
  simpa only [pullbackTensorCoordinates, coordinatePullback,
    derivativeCoordinates, tensorCoordinates, Function.comp_apply] using
      (pullbackTensorCoordinates_eq period hPeriod diffeomorphism tensor point
        current hCurrent' hImage')

def smoothDiffeomorphismTensorPullback
    (diffeomorphism : SpacetimeDiffeomorphism period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    SmoothSymmetricCovariantTwoTensor period hPeriod where
  tensor :=
    { toFun := diffeomorphismTensorPullback period hPeriod diffeomorphism
        tensor.tensor.toTensorField
      contMDiff_toFun := diffeomorphismTensorPullback_contMDiff
        period hPeriod diffeomorphism tensor }
  symmetric := by
    intro point first second
    exact pullbackTensorValue_symmetric period hPeriod diffeomorphism
      tensor.tensor.toTensorField tensor.symmetric point first second

theorem smoothDiffeomorphismTensorPullback_lorentzian
    (diffeomorphism : SpacetimeDiffeomorphism period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hTensor : IsEverywhereLorentzian period hPeriod tensor) :
    IsEverywhereLorentzian period hPeriod
      (smoothDiffeomorphismTensorPullback period hPeriod diffeomorphism tensor) := by
  intro point
  exact pullbackTensorValue_lorentzian period hPeriod diffeomorphism
    tensor.tensor.toTensorField point (hTensor (diffeomorphism point))

/-- Unconditional pullback of a general Lorentz metric by an arbitrary smooth
self-diffeomorphism. -/
def smoothGeneralLorentzMetricDiffeomorphismPullback
    (diffeomorphism : SpacetimeDiffeomorphism period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    SmoothGeneralLorentzMetric period hPeriod where
  tensor := smoothDiffeomorphismTensorPullback period hPeriod diffeomorphism
    metric.tensor
  musical := fun point =>
    pullbackMusical period hPeriod
      (diffeomorphismDerivative period hPeriod diffeomorphism point)
      (metric.musical (diffeomorphism point))
  musical_eq_tensor := by
    intro point
    apply ContinuousLinearMap.ext
    intro first
    apply ContinuousLinearMap.ext
    intro second
    change metric.musical (diffeomorphism point)
        (diffeomorphismDerivative period hPeriod diffeomorphism point first)
        (diffeomorphismDerivative period hPeriod diffeomorphism point second) =
      metric.tensor.tensor (diffeomorphism point)
        (mfderiv coverModelWithCorners coverModelWithCorners diffeomorphism
          point first)
        (mfderiv coverModelWithCorners coverModelWithCorners diffeomorphism
          point second)
    exact DFunLike.congr_fun
      (DFunLike.congr_fun (metric.musical_eq_tensor (diffeomorphism point)) _)
      _
  lorentzian := smoothDiffeomorphismTensorPullback_lorentzian period hPeriod
    diffeomorphism metric.tensor metric.lorentzian

/-- The residual covariance contract is therefore always inhabited. -/
def smoothGeneralLorentzMetricDiffeomorphismPullbackCertificate
    (diffeomorphism : SpacetimeDiffeomorphism period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    SmoothGeneralLorentzMetricDiffeomorphismPullback period hPeriod
      diffeomorphism metric where
  pulledMetric := smoothGeneralLorentzMetricDiffeomorphismPullback
    period hPeriod diffeomorphism metric
  musical_eq := fun _ => rfl

theorem smoothGeneralLorentzMetricDiffeomorphismPullback_unconditional
    (diffeomorphism : SpacetimeDiffeomorphism period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    Nonempty
      (SmoothGeneralLorentzMetricDiffeomorphismPullback period hPeriod
        diffeomorphism metric) :=
  ⟨smoothGeneralLorentzMetricDiffeomorphismPullbackCertificate
    period hPeriod diffeomorphism metric⟩

/-- Pointwise scalar-density covariance no longer needs an external metric
pullback certificate. -/
theorem generalLorentzHolonomicScalarDensity_diffeomorphism_unconditional
    (diffeomorphism : SpacetimeDiffeomorphism period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (field : SmoothScalarField period hPeriod)
    (frame : OrderedTangentVectorFamily period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    generalLorentzHolonomicScalarDensity period hPeriod
        (smoothGeneralLorentzMetricDiffeomorphismPullback period hPeriod
          diffeomorphism metric)
        massSquared
        (pullbackSmoothField period hPeriod Real diffeomorphism field)
        (diffeomorphismOrderedTangentVectorPullback period hPeriod
          diffeomorphism frame) point =
      generalLorentzHolonomicScalarDensity period hPeriod metric massSquared
        field frame (diffeomorphism point) :=
  generalLorentzHolonomicScalarDensity_diffeomorphism period hPeriod
    diffeomorphism metric
    (smoothGeneralLorentzMetricDiffeomorphismPullbackCertificate
      period hPeriod diffeomorphism metric)
    massSquared field frame point

/-- Integrated finite-diffeomorphism covariance is unconditional after
simultaneously pulling back the measure. -/
theorem measuredGeneralLorentzHolonomicScalarAction_diffeomorphism_unconditional
    (diffeomorphism : SpacetimeDiffeomorphism period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (field : SmoothScalarField period hPeriod)
    (frame : OrderedTangentVectorFamily period hPeriod)
    (measure : MeasureTheory.Measure (EffectiveQuotient period hPeriod)) :
    measuredGeneralLorentzHolonomicScalarAction period hPeriod
        (smoothGeneralLorentzMetricDiffeomorphismPullback period hPeriod
          diffeomorphism metric)
        massSquared
        (pullbackSmoothField period hPeriod Real diffeomorphism field)
        (diffeomorphismOrderedTangentVectorPullback period hPeriod
          diffeomorphism frame)
        (diffeomorphismMeasurePullback period hPeriod diffeomorphism measure) =
      measuredGeneralLorentzHolonomicScalarAction period hPeriod metric
        massSquared field frame measure :=
  measuredGeneralLorentzHolonomicScalarAction_diffeomorphism period hPeriod
    diffeomorphism metric
    (smoothGeneralLorentzMetricDiffeomorphismPullbackCertificate
      period hPeriod diffeomorphism metric)
    massSquared field frame measure

/-- Every supplied smooth diffeomorphism flow acquires its finite-time metric
pullback certificates automatically. -/
def smoothGeneralLorentzScalarDiffeomorphismOrbitOfFlow
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (flow : SmoothMetricPairPullbackFlow period hPeriod metric.tensor
      metric.tensor)
    (ghost : SmoothDiffeomorphismGhost period hPeriod)
    (generatesGhost : ∀ point,
      flow.velocityAt period hPeriod metric.tensor metric.tensor point =
        ghost point) :
    SmoothGeneralLorentzScalarDiffeomorphismOrbit period hPeriod metric where
  flow := flow
  metricPullback := fun parameter =>
    smoothGeneralLorentzMetricDiffeomorphismPullbackCertificate period hPeriod
      (flow.curve parameter) metric
  ghost := ghost
  generatesGhost := generatesGhost

theorem smoothGeneralLorentzScalarDiffeomorphismOrbitOfFlow_action_eq
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (flow : SmoothMetricPairPullbackFlow period hPeriod metric.tensor
      metric.tensor)
    (ghost : SmoothDiffeomorphismGhost period hPeriod)
    (generatesGhost : ∀ point,
      flow.velocityAt period hPeriod metric.tensor metric.tensor point =
        ghost point)
    (massSquared : Real)
    (field : SmoothScalarField period hPeriod)
    (frame : OrderedTangentVectorFamily period hPeriod)
    (measure : MeasureTheory.Measure (EffectiveQuotient period hPeriod))
    (parameter : Real) :
    smoothGeneralLorentzScalarDiffeomorphismOrbitAction period hPeriod metric
        (smoothGeneralLorentzScalarDiffeomorphismOrbitOfFlow period hPeriod
          metric flow ghost generatesGhost)
        massSquared field frame measure parameter =
      measuredGeneralLorentzHolonomicScalarAction period hPeriod metric
        massSquared field frame measure :=
  smoothGeneralLorentzScalarDiffeomorphismOrbitAction_eq period hPeriod metric
    (smoothGeneralLorentzScalarDiffeomorphismOrbitOfFlow period hPeriod metric
      flow ghost generatesGhost)
    massSquared field frame measure parameter

end

end P0EFTJanusMappingTorusGeneralLorentzMetricDiffeomorphismPullback4D
end JanusFormal
