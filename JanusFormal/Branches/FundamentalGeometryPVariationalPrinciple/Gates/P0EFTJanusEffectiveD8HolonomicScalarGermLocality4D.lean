import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusEffectiveD8HolonomicScalarDensityNaturality4D

/-!
# Germ locality of the global holonomic scalar sector

The differential depends only on the scalar germ.  This locality propagates
to the smooth inverse-musical gradient and to the complete frame-evaluated
holonomic density.
-/

namespace JanusFormal
namespace P0EFTJanusEffectiveD8HolonomicScalarGermLocality4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff Topology
open Filter
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusEffectiveD8BackgroundCategory4D
open P0EFTJanusEffectiveD8SmoothVectorFieldFunctor4D
open P0EFTJanusEffectiveD8SmoothCovectorFieldFunctor4D
open P0EFTJanusEffectiveD8MetricVolumeDensityNaturality4D
open P0EFTJanusEffectiveD8HolonomicScalarDifferentialNaturality4D
open P0EFTJanusEffectiveD8SmoothInverseMusical4D
open P0EFTJanusEffectiveD8SmoothHolonomicScalarGradient4D
open P0EFTJanusEffectiveD8HolonomicScalarDensityNaturality4D

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

/-- The genuine global differential depends only on the scalar germ. -/
theorem effectiveD8SmoothScalarDifferential_congr_of_eventuallyEq
    (background : EffectiveD8Background)
    (first second : SmoothQuotientField background.period
      background.period_ne_zero Real)
    (point : EffectiveQuotient background)
    (hField : first.toFun =ᶠ[𝓝 point] second.toFun) :
    effectiveD8SmoothScalarDifferential background first point =
      effectiveD8SmoothScalarDifferential background second point := by
  exact hField.mfderiv_eq

/-- Raising a one-form is pointwise local in the supplied covector. -/
theorem effectiveD8SmoothInverseMusical_congr_at
    (background : EffectiveD8Background)
    (metric : SmoothGeneralLorentzMetric background.period
      background.period_ne_zero)
    (first second : EffectiveD8SmoothCovectorField background)
    (point : EffectiveQuotient background)
    (hCovector : first point = second point) :
    effectiveD8SmoothInverseMusical background metric first point =
      effectiveD8SmoothInverseMusical background metric second point := by
  exact congrArg
    (inverseMetricSharp background.period background.period_ne_zero metric
      point) hCovector

/-- The genuine smooth scalar gradient depends only on the scalar germ. -/
theorem effectiveD8SmoothScalarGradient_congr_of_eventuallyEq
    (background : EffectiveD8Background)
    (metric : SmoothGeneralLorentzMetric background.period
      background.period_ne_zero)
    (first second : SmoothQuotientField background.period
      background.period_ne_zero Real)
    (point : EffectiveQuotient background)
    (hField : first.toFun =ᶠ[𝓝 point] second.toFun) :
    effectiveD8SmoothScalarGradient background metric first point =
      effectiveD8SmoothScalarGradient background metric second point := by
  exact effectiveD8SmoothInverseMusical_congr_at background metric
    (effectiveD8SmoothScalarDifferential background first)
    (effectiveD8SmoothScalarDifferential background second) point
    (effectiveD8SmoothScalarDifferential_congr_of_eventuallyEq background
      first second point hField)

/-- The complete holonomic density depends only on the scalar germ. -/
theorem effectiveD8HolonomicScalarFrameDensity_congr_of_eventuallyEq
    (background : EffectiveD8Background)
    (metric : SmoothGeneralLorentzMetric background.period
      background.period_ne_zero)
    (frame : EffectiveD8SmoothVectorFrame background)
    (massSquared : Real)
    (first second : SmoothQuotientField background.period
      background.period_ne_zero Real)
    (point : EffectiveQuotient background)
    (hField : first.toFun =ᶠ[𝓝 point] second.toFun) :
    effectiveD8HolonomicScalarFrameDensity background metric frame
        massSquared first point =
      effectiveD8HolonomicScalarFrameDensity background metric frame
        massSquared second point := by
  unfold effectiveD8HolonomicScalarFrameDensity holonomicScalarDensity
  rw [hField.eq_of_nhds]
  rw [show scalarDifferential background.period background.period_ne_zero
        first point =
      effectiveD8SmoothScalarDifferential background first point by rfl]
  rw [show scalarDifferential background.period background.period_ne_zero
        second point =
      effectiveD8SmoothScalarDifferential background second point by rfl]
  rw [effectiveD8SmoothScalarDifferential_congr_of_eventuallyEq background
    first second point hField]

private theorem eventuallyEq_of_eq_on_open
    (background : EffectiveD8Background)
    (first second : SmoothQuotientField background.period
      background.period_ne_zero Real)
    (region : Set (EffectiveQuotient background))
    (hRegion : IsOpen region)
    (hEqual : ∀ point ∈ region, first point = second point)
    (point : EffectiveQuotient background)
    (hPoint : point ∈ region) :
    first.toFun =ᶠ[𝓝 point] second.toFun := by
  filter_upwards [hRegion.mem_nhds hPoint] with current hCurrent
  exact hEqual current hCurrent

/-- Sheaf locality of the scalar differential on an open region. -/
theorem effectiveD8SmoothScalarDifferential_congr_on_open
    (background : EffectiveD8Background)
    (first second : SmoothQuotientField background.period
      background.period_ne_zero Real)
    (region : Set (EffectiveQuotient background))
    (hRegion : IsOpen region)
    (hEqual : ∀ point ∈ region, first point = second point)
    (point : EffectiveQuotient background)
    (hPoint : point ∈ region) :
    effectiveD8SmoothScalarDifferential background first point =
      effectiveD8SmoothScalarDifferential background second point :=
  effectiveD8SmoothScalarDifferential_congr_of_eventuallyEq background
    first second point
    (eventuallyEq_of_eq_on_open background first second region hRegion hEqual
      point hPoint)

/-- Sheaf locality of `sharp(dφ)` on an open region. -/
theorem effectiveD8SmoothScalarGradient_congr_on_open
    (background : EffectiveD8Background)
    (metric : SmoothGeneralLorentzMetric background.period
      background.period_ne_zero)
    (first second : SmoothQuotientField background.period
      background.period_ne_zero Real)
    (region : Set (EffectiveQuotient background))
    (hRegion : IsOpen region)
    (hEqual : ∀ point ∈ region, first point = second point)
    (point : EffectiveQuotient background)
    (hPoint : point ∈ region) :
    effectiveD8SmoothScalarGradient background metric first point =
      effectiveD8SmoothScalarGradient background metric second point :=
  effectiveD8SmoothScalarGradient_congr_of_eventuallyEq background metric
    first second point
    (eventuallyEq_of_eq_on_open background first second region hRegion hEqual
      point hPoint)

/-- Sheaf locality of the full holonomic density on an open region. -/
theorem effectiveD8HolonomicScalarFrameDensity_congr_on_open
    (background : EffectiveD8Background)
    (metric : SmoothGeneralLorentzMetric background.period
      background.period_ne_zero)
    (frame : EffectiveD8SmoothVectorFrame background)
    (massSquared : Real)
    (first second : SmoothQuotientField background.period
      background.period_ne_zero Real)
    (region : Set (EffectiveQuotient background))
    (hRegion : IsOpen region)
    (hEqual : ∀ point ∈ region, first point = second point)
    (point : EffectiveQuotient background)
    (hPoint : point ∈ region) :
    effectiveD8HolonomicScalarFrameDensity background metric frame
        massSquared first point =
      effectiveD8HolonomicScalarFrameDensity background metric frame
        massSquared second point :=
  effectiveD8HolonomicScalarFrameDensity_congr_of_eventuallyEq background
    metric frame massSquared first second point
    (eventuallyEq_of_eq_on_open background first second region hRegion hEqual
      point hPoint)

end

end P0EFTJanusEffectiveD8HolonomicScalarGermLocality4D
end JanusFormal
