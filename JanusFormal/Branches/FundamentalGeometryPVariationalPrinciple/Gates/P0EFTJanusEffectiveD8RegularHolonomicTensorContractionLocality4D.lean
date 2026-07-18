import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusEffectiveD8RegularHolonomicTensorContraction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusEffectiveD8HolonomicScalarGermLocality4D

/-!
# Sheaf locality of regular holonomic tensor contractions

Agreement of a tensor and both vector arguments on an open region forces
agreement of `T(X,Y)` there.  The canonical holonomic realization then gives
agreement of the true manifold differentials at every point of that region.
-/

namespace JanusFormal
namespace P0EFTJanusEffectiveD8RegularHolonomicTensorContractionLocality4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusEffectiveD8BackgroundCategory4D
open P0EFTJanusEffectiveD8SmoothVectorFieldFunctor4D
open P0EFTJanusEffectiveD8HolonomicScalarDifferentialNaturality4D
open P0EFTJanusEffectiveD8HolonomicScalarGermLocality4D
open P0EFTJanusEffectiveD8SmoothTensorVectorContraction4D
open P0EFTJanusEffectiveD8RegularHolonomicTensorContraction4D

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

/-- Pointwise sheaf locality of a smooth tensor/vector contraction. -/
theorem effectiveD8SmoothTensorVectorContraction_congr_on_open
    (background : EffectiveD8Background)
    (firstTensor secondTensor : SmoothSymmetricCovariantTwoTensor
      background.period background.period_ne_zero)
    (firstVector secondVector firstVector' secondVector' :
      EffectiveD8SmoothVectorField background)
    (region : Set (EffectiveQuotient background))
    (hTensor : ∀ point ∈ region,
      firstTensor.tensor point = secondTensor.tensor point)
    (hFirst : ∀ point ∈ region, firstVector point = firstVector' point)
    (hSecond : ∀ point ∈ region, secondVector point = secondVector' point) :
    ∀ point ∈ region,
      effectiveD8SmoothTensorVectorContraction background firstTensor
          firstVector secondVector point =
        effectiveD8SmoothTensorVectorContraction background secondTensor
          firstVector' secondVector' point := by
  intro point hPoint
  simp only [effectiveD8SmoothTensorVectorContraction_apply]
  rw [hTensor point hPoint, hFirst point hPoint, hSecond point hPoint]

/-- Sheaf locality of the scalar component of the regular realization. -/
theorem effectiveD8RegularHolonomicTensorVectorContraction_field_congr_on_open
    (background : EffectiveD8Background)
    (firstTensor secondTensor : SmoothSymmetricCovariantTwoTensor
      background.period background.period_ne_zero)
    (firstVector secondVector firstVector' secondVector' :
      EffectiveD8SmoothVectorField background)
    (region : Set (EffectiveQuotient background))
    (hTensor : ∀ point ∈ region,
      firstTensor.tensor point = secondTensor.tensor point)
    (hFirst : ∀ point ∈ region, firstVector point = firstVector' point)
    (hSecond : ∀ point ∈ region, secondVector point = secondVector' point) :
    ∀ point ∈ region,
      (effectiveD8RegularHolonomicTensorVectorContraction background firstTensor
          firstVector secondVector).field point =
        (effectiveD8RegularHolonomicTensorVectorContraction background
          secondTensor firstVector' secondVector').field point :=
  effectiveD8SmoothTensorVectorContraction_congr_on_open background
    firstTensor secondTensor firstVector secondVector firstVector'
    secondVector' region hTensor hFirst hSecond

/-- Sheaf locality of the true differential of the regular realization. -/
theorem effectiveD8RegularHolonomicTensorVectorContraction_differential_congr_on_open
    (background : EffectiveD8Background)
    (firstTensor secondTensor : SmoothSymmetricCovariantTwoTensor
      background.period background.period_ne_zero)
    (firstVector secondVector firstVector' secondVector' :
      EffectiveD8SmoothVectorField background)
    (region : Set (EffectiveQuotient background))
    (hRegion : IsOpen region)
    (hTensor : ∀ point ∈ region,
      firstTensor.tensor point = secondTensor.tensor point)
    (hFirst : ∀ point ∈ region, firstVector point = firstVector' point)
    (hSecond : ∀ point ∈ region, secondVector point = secondVector' point)
    (point : EffectiveQuotient background)
    (hPoint : point ∈ region) :
    (effectiveD8RegularHolonomicTensorVectorContraction background firstTensor
        firstVector secondVector).differential point =
      (effectiveD8RegularHolonomicTensorVectorContraction background
        secondTensor firstVector' secondVector').differential point := by
  change effectiveD8SmoothScalarDifferential background
      (effectiveD8SmoothTensorVectorContraction background firstTensor
        firstVector secondVector) point =
    effectiveD8SmoothScalarDifferential background
      (effectiveD8SmoothTensorVectorContraction background secondTensor
        firstVector' secondVector') point
  exact effectiveD8SmoothScalarDifferential_congr_on_open background
    (effectiveD8SmoothTensorVectorContraction background firstTensor
      firstVector secondVector)
    (effectiveD8SmoothTensorVectorContraction background secondTensor
      firstVector' secondVector') region hRegion
    (effectiveD8SmoothTensorVectorContraction_congr_on_open background
      firstTensor secondTensor firstVector secondVector firstVector'
      secondVector' region hTensor hFirst hSecond) point hPoint

/-- The same locality statement for `g(X,Y)`. -/
theorem effectiveD8RegularHolonomicLorentzMetricVectorContraction_differential_congr_on_open
    (background : EffectiveD8Background)
    (firstMetric secondMetric : SmoothGeneralLorentzMetric
      background.period background.period_ne_zero)
    (firstVector secondVector firstVector' secondVector' :
      EffectiveD8SmoothVectorField background)
    (region : Set (EffectiveQuotient background))
    (hRegion : IsOpen region)
    (hMetric : ∀ point ∈ region,
      firstMetric.tensor.tensor point = secondMetric.tensor.tensor point)
    (hFirst : ∀ point ∈ region, firstVector point = firstVector' point)
    (hSecond : ∀ point ∈ region, secondVector point = secondVector' point)
    (point : EffectiveQuotient background)
    (hPoint : point ∈ region) :
    (effectiveD8RegularHolonomicLorentzMetricVectorContraction background
        firstMetric firstVector secondVector).differential point =
      (effectiveD8RegularHolonomicLorentzMetricVectorContraction background
        secondMetric firstVector' secondVector').differential point :=
  effectiveD8RegularHolonomicTensorVectorContraction_differential_congr_on_open
    background firstMetric.tensor secondMetric.tensor firstVector secondVector
    firstVector' secondVector' region hRegion hMetric hFirst hSecond point
    hPoint

end

end P0EFTJanusEffectiveD8RegularHolonomicTensorContractionLocality4D
end JanusFormal
