import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusEffectiveD8HolonomicScalarGradientPullback4D

/-!
# Smooth inverse musical map on effective D8 backgrounds

In local tangent/cotangent trivializations, the inverse musical map is the
inverse of the smooth matrix-valued metric coefficient map.  Smoothness of
operator inversion therefore promotes pointwise raising of a smooth one-form
to a genuine smooth tangent-vector field.
-/

namespace JanusFormal
namespace P0EFTJanusEffectiveD8SmoothInverseMusical4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped Manifold ContDiff Topology
open Bundle ContinuousLinearMap Filter
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusEffectiveD8BackgroundCategory4D
open P0EFTJanusEffectiveD8SmoothVectorFieldFunctor4D
open P0EFTJanusEffectiveD8SmoothCovectorFieldFunctor4D

private abbrev EffectiveQuotient (background : EffectiveD8Background) :=
  MappingTorus
    (reflectedSphereData background.period background.period_ne_zero)

local instance effectiveQuotientChartedSpace
    (background : EffectiveD8Background) :
    ChartedSpace CoverModel (EffectiveQuotient background) :=
  reflectedSphereQuotientChartedSpace
    background.period background.period_ne_zero

local instance effectiveQuotientIsManifold
    (background : EffectiveD8Background) :
    IsManifold coverModelWithCorners ω (EffectiveQuotient background) :=
  reflectedSphereQuotient_isManifold
    background.period background.period_ne_zero

private abbrev TangentFiber
    (background : EffectiveD8Background)
    (point : EffectiveQuotient background) :=
  TangentSpace coverModelWithCorners point

private abbrev CotangentFiber
    (background : EffectiveD8Background)
    (point : EffectiveQuotient background) :=
  TangentFiber background point →L[Real] Real

private abbrev ModelTangent := CoverCoordinates
private abbrev ModelCotangent := ModelTangent →L[Real] Real

local instance effectiveTangentFiniteDimensional
    (background : EffectiveD8Background)
    (point : EffectiveQuotient background) :
    FiniteDimensional Real (TangentFiber background point) := by
  change FiniteDimensional Real CoverCoordinates
  infer_instance

private def metricCoordinates
    (background : EffectiveD8Background)
    (metric : SmoothGeneralLorentzMetric background.period
      background.period_ne_zero)
    (anchor current : EffectiveQuotient background) :
    ModelTangent →L[Real] ModelCotangent :=
  ContinuousLinearMap.inCoordinates ModelTangent (TangentFiber background)
    ModelCotangent (CotangentFiber background)
    anchor current anchor current (metric.tensor.tensor current)

private def covectorCoordinates
    (background : EffectiveD8Background)
    (covector : EffectiveD8SmoothCovectorField background)
    (anchor current : EffectiveQuotient background) : ModelCotangent :=
  ContinuousLinearMap.inCoordinates ModelTangent (TangentFiber background)
    Real (fun _ : EffectiveQuotient background => Real)
    anchor current anchor current (covector current)

private theorem metricCoordinates_contMDiffAt
    (background : EffectiveD8Background)
    (metric : SmoothGeneralLorentzMetric background.period
      background.period_ne_zero)
    (anchor : EffectiveQuotient background) :
    ContMDiffAt coverModelWithCorners
      𝓘(Real, ModelTangent →L[Real] ModelCotangent) ∞
      (metricCoordinates background metric anchor) anchor := by
  have hMetric := metric.tensor.tensor.contMDiff anchor
  rw [contMDiffAt_hom_bundle] at hMetric
  exact hMetric.2

private theorem covectorCoordinates_contMDiffAt
    (background : EffectiveD8Background)
    (covector : EffectiveD8SmoothCovectorField background)
    (anchor : EffectiveQuotient background) :
    ContMDiffAt coverModelWithCorners 𝓘(Real, ModelCotangent) ∞
      (covectorCoordinates background covector anchor) anchor := by
  have hCovector := covector.contMDiff anchor
  rw [contMDiffAt_hom_bundle] at hCovector
  exact hCovector.2

private theorem metricCoordinates_isInvertible
    (background : EffectiveD8Background)
    (metric : SmoothGeneralLorentzMetric background.period
      background.period_ne_zero)
    (anchor : EffectiveQuotient background) :
    (metricCoordinates background metric anchor anchor).IsInvertible := by
  have hTangent : anchor ∈
      (trivializationAt ModelTangent (TangentFiber background) anchor).baseSet :=
    mem_baseSet_trivializationAt ModelTangent (TangentFiber background) anchor
  have hCotangent : anchor ∈
      (trivializationAt ModelCotangent (CotangentFiber background) anchor).baseSet :=
    mem_baseSet_trivializationAt ModelCotangent
      (CotangentFiber background) anchor
  unfold metricCoordinates
  rw [ContinuousLinearMap.inCoordinates_eq hTangent hCotangent,
    ← metric.musical_eq_tensor anchor]
  exact isInvertible_equiv.comp
    (isInvertible_equiv.comp isInvertible_equiv)

private theorem inverseMetricCoordinates_apply_eq
    (background : EffectiveD8Background)
    (metric : SmoothGeneralLorentzMetric background.period
      background.period_ne_zero)
    (covector : EffectiveD8SmoothCovectorField background)
    (anchor current : EffectiveQuotient background)
    (hTangent : current ∈
      (trivializationAt ModelTangent (TangentFiber background) anchor).baseSet)
    (hCotangent : current ∈
      (trivializationAt ModelCotangent
        (CotangentFiber background) anchor).baseSet) :
    (metricCoordinates background metric anchor current).inverse
        (covectorCoordinates background covector anchor current) =
      ((trivializationAt ModelTangent (TangentFiber background) anchor)
        ⟨current, inverseMetricSharp background.period
          background.period_ne_zero metric current (covector current)⟩).2 := by
  have hCovectorCoordinates :
      covectorCoordinates background covector anchor current =
        (trivializationAt ModelCotangent (CotangentFiber background) anchor
          |>.continuousLinearEquivAt Real current hCotangent)
            (covector current) := by
    rfl
  have hVectorCoordinates :
      ((trivializationAt ModelTangent (TangentFiber background) anchor)
        ⟨current, inverseMetricSharp background.period
          background.period_ne_zero metric current (covector current)⟩).2 =
        (trivializationAt ModelTangent (TangentFiber background) anchor
          |>.continuousLinearEquivAt Real current hTangent)
            (inverseMetricSharp background.period background.period_ne_zero
              metric current (covector current)) := by
    rfl
  unfold metricCoordinates
  rw [ContinuousLinearMap.inCoordinates_eq hTangent hCotangent,
    ← metric.musical_eq_tensor current, hCovectorCoordinates,
    hVectorCoordinates]
  simp only [ContinuousLinearMap.inverse_equiv_comp,
    ContinuousLinearMap.inverse_comp_equiv,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearMap.inverse_equiv,
    inverseMetricSharp, ContinuousLinearEquiv.symm_apply_apply,
    ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.symm_symm]

/-- Raising a smooth one-form with a smooth nondegenerate Lorentz metric gives
a genuine smooth tangent-vector field. -/
def effectiveD8SmoothInverseMusical
    (background : EffectiveD8Background)
    (metric : SmoothGeneralLorentzMetric background.period
      background.period_ne_zero)
    (covector : EffectiveD8SmoothCovectorField background) :
    EffectiveD8SmoothVectorField background where
  toFun := fun point => inverseMetricSharp background.period
    background.period_ne_zero metric point (covector point)
  contMDiff_toFun := by
    intro anchor
    rw [contMDiffAt_section]
    have hMetric := metricCoordinates_contMDiffAt background metric anchor
    have hInverse :=
      (metricCoordinates_isInvertible background metric anchor
        |>.contDiffAt_map_inverse (n := ∞)).comp_contMDiffAt hMetric
    have hCovector := covectorCoordinates_contMDiffAt
      background covector anchor
    have hFormula := hInverse.clm_apply hCovector
    apply hFormula.congr_of_eventuallyEq
    have hTangent : ∀ᶠ current in 𝓝 anchor, current ∈
        (trivializationAt ModelTangent
          (TangentFiber background) anchor).baseSet :=
      (trivializationAt ModelTangent
        (TangentFiber background) anchor).open_baseSet.mem_nhds
          (mem_baseSet_trivializationAt ModelTangent
            (TangentFiber background) anchor)
    have hCotangent : ∀ᶠ current in 𝓝 anchor, current ∈
        (trivializationAt ModelCotangent
          (CotangentFiber background) anchor).baseSet :=
      (trivializationAt ModelCotangent
        (CotangentFiber background) anchor).open_baseSet.mem_nhds
          (mem_baseSet_trivializationAt ModelCotangent
            (CotangentFiber background) anchor)
    filter_upwards [hTangent, hCotangent] with current hTangent' hCotangent'
    exact (inverseMetricCoordinates_apply_eq background metric covector
      anchor current hTangent' hCotangent').symm

@[simp] theorem effectiveD8SmoothInverseMusical_apply
    (background : EffectiveD8Background)
    (metric : SmoothGeneralLorentzMetric background.period
      background.period_ne_zero)
    (covector : EffectiveD8SmoothCovectorField background)
    (point : EffectiveQuotient background) :
    effectiveD8SmoothInverseMusical background metric covector point =
      inverseMetricSharp background.period background.period_ne_zero metric
        point (covector point) :=
  rfl

theorem effectiveD8SmoothInverseMusical_flat
    (background : EffectiveD8Background)
    (metric : SmoothGeneralLorentzMetric background.period
      background.period_ne_zero)
    (covector : EffectiveD8SmoothCovectorField background)
    (point : EffectiveQuotient background) :
    metric.musical point
        (effectiveD8SmoothInverseMusical background metric covector point) =
      covector point := by
  exact metric_flat_inverseMetricSharp background.period
    background.period_ne_zero metric point (covector point)

end

end P0EFTJanusEffectiveD8SmoothInverseMusical4D
end JanusFormal
