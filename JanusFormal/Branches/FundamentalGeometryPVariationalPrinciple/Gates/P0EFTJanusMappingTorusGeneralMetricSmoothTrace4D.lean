import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralLorentzMetricBVPairingRegularity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusEffectiveD8SmoothInverseMusical4D

/-!
# Smooth global trace of a general metric perturbation

For a genuine smooth nondegenerate Lorentz metric `g` and a genuine smooth
symmetric covariant two-tensor `h` on the effective quotient, this gate
constructs the invariant scalar

`tr_g h = tr(g⁻¹ h)`

as a smooth global field.  Smoothness is proved in arbitrary tangent and
cotangent trivializations.  The local matrix formula is proved equal to the
fiberwise invariant trace, and hence independent of the chosen
trivialization on overlaps.

The global differential `d (tr_g h)` is then obtained as a genuine smooth
one-form.  This is the trace-gradient half of the de Donder operator.  No
divergence of `h`, Levi--Civita connection on arbitrary tensor sections, or
formal-adjoint identity is asserted here.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusGeneralMetricSmoothTrace4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped Manifold ContDiff Topology
open Bundle ContinuousLinearMap Filter
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFirstLevel4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVUltralocalMaster4D
open P0EFTJanusEffectiveD8BackgroundCategory4D
open P0EFTJanusEffectiveD8SmoothVectorFieldFunctor4D
open P0EFTJanusEffectiveD8SmoothCovectorFieldFunctor4D
open P0EFTJanusEffectiveD8HolonomicScalarDifferentialNaturality4D
open P0EFTJanusEffectiveD8SmoothInverseMusical4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

private abbrev ModelTangent := CoverCoordinates

private abbrev ModelCotangent :=
  ModelTangent →L[Real] Real

private abbrev TangentFiber
    (point : EffectiveQuotient period hPeriod) :=
  GeneralMetricTangentFiber period hPeriod point

private abbrev CotangentFiber
    (point : EffectiveQuotient period hPeriod) :=
  TangentFiber period hPeriod point →L[Real] Real

private abbrev ModelEndomorphism :=
  ModelTangent →L[Real] ModelTangent

local instance effectiveTangentFiniteDimensional
    (point : EffectiveQuotient period hPeriod) :
    FiniteDimensional Real (TangentFiber period hPeriod point) := by
  change FiniteDimensional Real CoverCoordinates
  infer_instance

/-- Invariant fiberwise trace `tr(g⁻¹h)`. -/
def generalMetricTensorTraceAt
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) : Real :=
  LinearMap.trace Real (TangentFiber period hPeriod point)
    (raisedGeneralMetricTensorAt period hPeriod metric tensor point).toLinearMap

/-- The trace is the already established invariant symmetric-tensor pairing
against the background metric. -/
theorem generalMetricTensorTraceAt_eq_pairing_metric
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    generalMetricTensorTraceAt period hPeriod metric tensor point =
      generalMetricTensorPairingAt period hPeriod metric
        tensor metric.tensor point := by
  unfold generalMetricTensorTraceAt generalMetricTensorPairingAt
  rw [raisedGeneralMetricTensorAt_metric_tensor]
  congr 1

@[simp]
theorem generalMetricTensorTraceAt_metric_tensor
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    generalMetricTensorTraceAt period hPeriod metric metric.tensor point = 4 := by
  rw [generalMetricTensorTraceAt_eq_pairing_metric,
    generalMetricTensorPairingAt_metric_self]

theorem generalMetricTensorTraceAt_add
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    generalMetricTensorTraceAt period hPeriod metric
        (smoothSymmetricTensorAdd period hPeriod first second) point =
      generalMetricTensorTraceAt period hPeriod metric first point +
        generalMetricTensorTraceAt period hPeriod metric second point := by
  rw [generalMetricTensorTraceAt_eq_pairing_metric,
    generalMetricTensorPairingAt_add_left,
    ← generalMetricTensorTraceAt_eq_pairing_metric,
    ← generalMetricTensorTraceAt_eq_pairing_metric]

theorem generalMetricTensorTraceAt_smul
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (scalar : Real)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    generalMetricTensorTraceAt period hPeriod metric
        (smoothSymmetricTensorSMul period hPeriod scalar tensor) point =
      scalar * generalMetricTensorTraceAt
        period hPeriod metric tensor point := by
  rw [generalMetricTensorTraceAt_eq_pairing_metric,
    generalMetricTensorPairingAt_smul_left,
    ← generalMetricTensorTraceAt_eq_pairing_metric]

private def tensorCoordinates
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (anchor current : EffectiveQuotient period hPeriod) :
    ModelTangent →L[Real] ModelCotangent :=
  ContinuousLinearMap.inCoordinates ModelTangent
    (TangentFiber period hPeriod) ModelCotangent
    (CotangentFiber period hPeriod)
    anchor current anchor current (tensor.tensor current)

private theorem tensorCoordinates_contMDiffAt
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (anchor : EffectiveQuotient period hPeriod) :
    ContMDiffAt coverModelWithCorners
      𝓘(Real, ModelTangent →L[Real] ModelCotangent) ∞
      (tensorCoordinates period hPeriod tensor anchor) anchor := by
  have hSmooth := tensor.tensor.contMDiff anchor
  rw [contMDiffAt_hom_bundle] at hSmooth
  exact hSmooth.2

private def metricCoordinates
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (anchor current : EffectiveQuotient period hPeriod) :
    ModelTangent →L[Real] ModelCotangent :=
  tensorCoordinates period hPeriod metric.tensor anchor current

private theorem metricCoordinates_isInvertible
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (anchor : EffectiveQuotient period hPeriod) :
    (metricCoordinates period hPeriod metric anchor anchor).IsInvertible := by
  have hTangent : anchor ∈
      (trivializationAt ModelTangent
        (TangentFiber period hPeriod) anchor).baseSet :=
    mem_baseSet_trivializationAt ModelTangent
      (TangentFiber period hPeriod) anchor
  have hCotangent : anchor ∈
      (trivializationAt ModelCotangent
        (CotangentFiber period hPeriod) anchor).baseSet :=
    mem_baseSet_trivializationAt ModelCotangent
      (CotangentFiber period hPeriod) anchor
  have hFiber :
      metric.tensor.tensor anchor =
        (metric.musical anchor :
          TangentFiber period hPeriod anchor →L[Real]
            CotangentFiber period hPeriod anchor) :=
    (metric.musical_eq_tensor anchor).symm
  unfold metricCoordinates tensorCoordinates
  rw [ContinuousLinearMap.inCoordinates_eq hTangent hCotangent, hFiber]
  exact isInvertible_equiv.comp
    (isInvertible_equiv.comp isInvertible_equiv)

private def raisedTensorCoordinates
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (anchor current : EffectiveQuotient period hPeriod) :
    ModelEndomorphism :=
  (metricCoordinates period hPeriod metric anchor current).inverse.comp
    (tensorCoordinates period hPeriod tensor anchor current)

private theorem raisedTensorCoordinates_eq_inCoordinates
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (anchor current : EffectiveQuotient period hPeriod)
    (hTangent : current ∈
      (trivializationAt ModelTangent
        (TangentFiber period hPeriod) anchor).baseSet)
    (hCotangent : current ∈
      (trivializationAt ModelCotangent
        (CotangentFiber period hPeriod) anchor).baseSet) :
    raisedTensorCoordinates period hPeriod metric tensor anchor current =
      ContinuousLinearMap.inCoordinates ModelTangent
        (TangentFiber period hPeriod) ModelTangent
        (TangentFiber period hPeriod)
        anchor current anchor current
        (raisedGeneralMetricTensorAt period hPeriod metric tensor current) := by
  have hFiber :
      metric.tensor.tensor current =
        (metric.musical current :
          TangentFiber period hPeriod current →L[Real]
            CotangentFiber period hPeriod current) :=
    (metric.musical_eq_tensor current).symm
  unfold raisedTensorCoordinates metricCoordinates tensorCoordinates
  rw [ContinuousLinearMap.inCoordinates_eq hTangent hCotangent, hFiber,
    ContinuousLinearMap.inCoordinates_eq hTangent hCotangent,
    ContinuousLinearMap.inCoordinates_eq hTangent hTangent]
  simp only [ContinuousLinearMap.inverse_equiv_comp,
    ContinuousLinearMap.inverse_comp_equiv,
    ContinuousLinearEquiv.symm_symm]
  apply ContinuousLinearMap.ext
  intro vector
  simp only [raisedGeneralMetricTensorAt,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearMap.inverse_equiv,
    ContinuousLinearEquiv.symm_apply_apply]

private def modelTraceLinearMap :
    ModelEndomorphism →ₗ[Real] Real :=
  (LinearMap.trace Real ModelTangent).comp
    (ContinuousLinearMap.coeLM Real)

private def modelTrace :
    ModelEndomorphism →L[Real] Real :=
  LinearMap.toContinuousLinearMap modelTraceLinearMap

@[simp]
private theorem modelTrace_apply (endomorphism : ModelEndomorphism) :
    modelTrace endomorphism =
      LinearMap.trace Real ModelTangent endomorphism.toLinearMap :=
  rfl

/-- Coordinate formula for the trace in the trivializations based at
`anchor`. -/
def generalMetricTensorTraceInTrivialization
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (anchor current : EffectiveQuotient period hPeriod) : Real :=
  modelTrace
    (raisedTensorCoordinates period hPeriod metric tensor anchor current)

private theorem
    generalMetricTensorTraceInTrivialization_contMDiffAt
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (anchor : EffectiveQuotient period hPeriod) :
    ContMDiffAt coverModelWithCorners 𝓘(Real, Real) ∞
      (generalMetricTensorTraceInTrivialization
        period hPeriod metric tensor anchor) anchor := by
  have hMetric := tensorCoordinates_contMDiffAt
    period hPeriod metric.tensor anchor
  have hInverse :=
    (metricCoordinates_isInvertible period hPeriod metric anchor
      |>.contDiffAt_map_inverse (n := ∞)).comp_contMDiffAt hMetric
  have hTensor := tensorCoordinates_contMDiffAt
    period hPeriod tensor anchor
  have hRaised := hInverse.clm_comp hTensor
  exact modelTrace.contDiff.contMDiff.contMDiffAt.comp anchor hRaised

/-- The coordinate matrix trace equals the invariant fiber trace wherever
the two chosen trivializations are defined. -/
theorem generalMetricTensorTraceAt_eq_trivialization
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (anchor current : EffectiveQuotient period hPeriod)
    (hTangent : current ∈
      (trivializationAt ModelTangent
        (TangentFiber period hPeriod) anchor).baseSet)
    (hCotangent : current ∈
      (trivializationAt ModelCotangent
        (CotangentFiber period hPeriod) anchor).baseSet) :
    generalMetricTensorTraceAt period hPeriod metric tensor current =
      generalMetricTensorTraceInTrivialization
        period hPeriod metric tensor anchor current := by
  rw [generalMetricTensorTraceInTrivialization,
    raisedTensorCoordinates_eq_inCoordinates period hPeriod
      metric tensor anchor current hTangent hCotangent,
    modelTrace_apply]
  unfold generalMetricTensorTraceAt
  let equivalence :=
    (trivializationAt ModelTangent
      (TangentFiber period hPeriod) anchor).continuousLinearEquivAt
        Real current hTangent
  have hTrace := LinearMap.trace_conj'
    (raisedGeneralMetricTensorAt
      period hPeriod metric tensor current).toLinearMap
    equivalence.toLinearEquiv
  rw [← hTrace]
  congr 1
  apply LinearMap.ext
  intro vector
  rw [ContinuousLinearMap.inCoordinates_eq hTangent hTangent]
  rfl

/-- On an overlap, arbitrary tangent/cotangent trivializations give the same
trace. -/
theorem generalMetricTensorTraceInTrivialization_independent
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (firstAnchor secondAnchor current :
      EffectiveQuotient period hPeriod)
    (hFirstTangent : current ∈
      (trivializationAt ModelTangent
        (TangentFiber period hPeriod) firstAnchor).baseSet)
    (hFirstCotangent : current ∈
      (trivializationAt ModelCotangent
        (CotangentFiber period hPeriod) firstAnchor).baseSet)
    (hSecondTangent : current ∈
      (trivializationAt ModelTangent
        (TangentFiber period hPeriod) secondAnchor).baseSet)
    (hSecondCotangent : current ∈
      (trivializationAt ModelCotangent
        (CotangentFiber period hPeriod) secondAnchor).baseSet) :
    generalMetricTensorTraceInTrivialization
        period hPeriod metric tensor firstAnchor current =
      generalMetricTensorTraceInTrivialization
        period hPeriod metric tensor secondAnchor current := by
  rw [← generalMetricTensorTraceAt_eq_trivialization
      period hPeriod metric tensor firstAnchor current
        hFirstTangent hFirstCotangent,
    ← generalMetricTensorTraceAt_eq_trivialization
      period hPeriod metric tensor secondAnchor current
        hSecondTangent hSecondCotangent]

theorem generalMetricTensorTraceAt_contMDiff
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    ContMDiff coverModelWithCorners 𝓘(Real, Real) ∞
      (generalMetricTensorTraceAt period hPeriod metric tensor) := by
  intro anchor
  have hLocal :=
    generalMetricTensorTraceInTrivialization_contMDiffAt
      period hPeriod metric tensor anchor
  apply hLocal.congr_of_eventuallyEq
  have hTangent : ∀ᶠ current in 𝓝 anchor,
      current ∈ (trivializationAt ModelTangent
        (TangentFiber period hPeriod) anchor).baseSet :=
    (trivializationAt ModelTangent
      (TangentFiber period hPeriod) anchor).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt ModelTangent
          (TangentFiber period hPeriod) anchor)
  have hCotangent : ∀ᶠ current in 𝓝 anchor,
      current ∈ (trivializationAt ModelCotangent
        (CotangentFiber period hPeriod) anchor).baseSet :=
    (trivializationAt ModelCotangent
      (CotangentFiber period hPeriod) anchor).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt ModelCotangent
          (CotangentFiber period hPeriod) anchor)
  filter_upwards [hTangent, hCotangent] with current hTangent' hCotangent'
  exact generalMetricTensorTraceAt_eq_trivialization
    period hPeriod metric tensor anchor current hTangent' hCotangent'

/-- Smooth global scalar `tr_g h`. -/
def generalMetricTensorTrace
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    SmoothQuotientField period hPeriod Real where
  toFun := generalMetricTensorTraceAt period hPeriod metric tensor
  contMDiff_toFun :=
    generalMetricTensorTraceAt_contMDiff
      period hPeriod metric tensor

@[simp]
theorem generalMetricTensorTrace_apply
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    generalMetricTensorTrace period hPeriod metric tensor point =
      generalMetricTensorTraceAt period hPeriod metric tensor point :=
  rfl

private abbrev effectiveBackground : EffectiveD8Background where
  period := period
  period_ne_zero := hPeriod

/-- The smooth global one-form `d (tr_g h)`. -/
def generalMetricTensorTraceDifferential
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    EffectiveD8SmoothCovectorField
      (effectiveBackground period hPeriod) :=
  effectiveD8SmoothScalarDifferential
    (effectiveBackground period hPeriod)
    (generalMetricTensorTrace period hPeriod metric tensor)

@[simp]
theorem generalMetricTensorTraceDifferential_apply
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    generalMetricTensorTraceDifferential
        period hPeriod metric tensor point =
      mfderiv coverModelWithCorners 𝓘(Real, Real)
        (generalMetricTensorTrace period hPeriod metric tensor) point :=
  rfl

/-- The already completed `-1/2 d (tr_g h)` contribution to the de Donder
one-form. -/
def generalMetricDeDonderTraceCorrection
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    EffectiveD8SmoothCovectorField
      (effectiveBackground period hPeriod) :=
  (-1 / 2 : Real) •
    generalMetricTensorTraceDifferential
      period hPeriod metric tensor

@[simp]
theorem generalMetricDeDonderTraceCorrection_apply
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    generalMetricDeDonderTraceCorrection
        period hPeriod metric tensor point =
      (-1 / 2 : Real) •
        generalMetricTensorTraceDifferential
          period hPeriod metric tensor point :=
  rfl

/-- Metric gradient of the trace, as a genuine smooth global
diffeomorphism-ghost vector field. -/
def generalMetricTensorTraceGradient
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    EffectiveD8SmoothVectorField
      (effectiveBackground period hPeriod) :=
  effectiveD8SmoothInverseMusical
    (effectiveBackground period hPeriod) metric
    (generalMetricTensorTraceDifferential
      period hPeriod metric tensor)

@[simp]
theorem generalMetricTensorTraceGradient_apply
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    generalMetricTensorTraceGradient
        period hPeriod metric tensor point =
      inverseMetricSharp period hPeriod metric point
        (generalMetricTensorTraceDifferential
          period hPeriod metric tensor point) :=
  rfl

/-- Lowering the smooth trace gradient recovers its global differential. -/
theorem generalMetricTensorTraceGradient_flat
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    metric.musical point
        (generalMetricTensorTraceGradient
          period hPeriod metric tensor point) =
      generalMetricTensorTraceDifferential
        period hPeriod metric tensor point := by
  exact effectiveD8SmoothInverseMusical_flat
    (effectiveBackground period hPeriod) metric
    (generalMetricTensorTraceDifferential
      period hPeriod metric tensor) point

end
end P0EFTJanusMappingTorusGeneralMetricSmoothTrace4D
end JanusFormal
