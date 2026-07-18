import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusEffectiveD8RegularHolonomicScalarRealization4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusEffectiveD8SmoothTensorVectorContraction4D

/-!
# Regular holonomic realizations of smooth tensor contractions

The canonical regular scalar realization promotes the genuine smooth
contractions `T(X,Y)` and `g(X,Y)`.  Their field and differential components
retain the exact effective-D8 pullback laws.
-/

namespace JanusFormal
namespace P0EFTJanusEffectiveD8RegularHolonomicTensorContraction4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusEffectiveD8BackgroundCategory4D
open P0EFTJanusEffectiveD8SmoothVectorFieldFunctor4D
open P0EFTJanusEffectiveD8SmoothCovectorFieldFunctor4D
open P0EFTJanusEffectiveD8SmoothSymmetricTensorFunctor4D
open P0EFTJanusEffectiveD8HolonomicScalarDifferentialNaturality4D
open P0EFTJanusEffectiveD8RegularHolonomicScalarRealization4D
open P0EFTJanusEffectiveD8SmoothTensorVectorContraction4D

/-- Canonical regular holonomic realization of `T(X,Y)`. -/
def effectiveD8RegularHolonomicTensorVectorContraction
    (background : EffectiveD8Background)
    (tensor : SmoothSymmetricCovariantTwoTensor background.period
      background.period_ne_zero)
    (first second : EffectiveD8SmoothVectorField background) :
    RegularHolonomicScalar background.period background.period_ne_zero :=
  effectiveD8RegularHolonomicScalar background
    (effectiveD8SmoothTensorVectorContraction background tensor first second)

@[simp] theorem effectiveD8RegularHolonomicTensorVectorContraction_field
    (background : EffectiveD8Background)
    (tensor : SmoothSymmetricCovariantTwoTensor background.period
      background.period_ne_zero)
    (first second : EffectiveD8SmoothVectorField background) :
    (effectiveD8RegularHolonomicTensorVectorContraction background tensor first
      second).field =
      effectiveD8SmoothTensorVectorContraction background tensor first second :=
  rfl

/-- Exact pullback law for the realized contraction's scalar component. -/
theorem effectiveD8RegularHolonomicTensorVectorContraction_field_pullback
    {source target : EffectiveD8Background}
    (morphism : EffectiveD8BackgroundDiffeomorphism source target)
    (tensor : SmoothSymmetricCovariantTwoTensor target.period
      target.period_ne_zero)
    (first second : EffectiveD8SmoothVectorField target) :
    (effectiveD8RegularHolonomicTensorVectorContraction source
        (effectiveD8SmoothSymmetricTensorPullback morphism tensor)
        (effectiveD8SmoothVectorFieldPullback morphism first)
        (effectiveD8SmoothVectorFieldPullback morphism second)).field =
      pullbackEffectiveD8SmoothField Real morphism
        (effectiveD8RegularHolonomicTensorVectorContraction target tensor first
          second).field := by
  exact effectiveD8SmoothTensorVectorContraction_pullback morphism tensor first
    second

/-- Exact pullback law for the realized contraction's true differential. -/
theorem effectiveD8RegularHolonomicTensorVectorContraction_differential_pullback
    {source target : EffectiveD8Background}
    (morphism : EffectiveD8BackgroundDiffeomorphism source target)
    (tensor : SmoothSymmetricCovariantTwoTensor target.period
      target.period_ne_zero)
    (first second : EffectiveD8SmoothVectorField target) :
    (effectiveD8RegularHolonomicTensorVectorContraction source
        (effectiveD8SmoothSymmetricTensorPullback morphism tensor)
        (effectiveD8SmoothVectorFieldPullback morphism first)
        (effectiveD8SmoothVectorFieldPullback morphism second)).differential =
      effectiveD8SmoothCovectorFieldPullback morphism
        (effectiveD8RegularHolonomicTensorVectorContraction target tensor first
          second).differential := by
  change effectiveD8SmoothScalarDifferential source
      (effectiveD8SmoothTensorVectorContraction source
        (effectiveD8SmoothSymmetricTensorPullback morphism tensor)
        (effectiveD8SmoothVectorFieldPullback morphism first)
        (effectiveD8SmoothVectorFieldPullback morphism second)) = _
  rw [effectiveD8SmoothTensorVectorContraction_pullback]
  exact effectiveD8SmoothScalarDifferential_pullback morphism
    (effectiveD8SmoothTensorVectorContraction target tensor first second)

/-- Canonical regular holonomic realization of the metric scalar `g(X,Y)`. -/
def effectiveD8RegularHolonomicLorentzMetricVectorContraction
    (background : EffectiveD8Background)
    (metric : SmoothGeneralLorentzMetric background.period
      background.period_ne_zero)
    (first second : EffectiveD8SmoothVectorField background) :
    RegularHolonomicScalar background.period background.period_ne_zero :=
  effectiveD8RegularHolonomicTensorVectorContraction background metric.tensor
    first second

@[simp] theorem effectiveD8RegularHolonomicLorentzMetricVectorContraction_field
    (background : EffectiveD8Background)
    (metric : SmoothGeneralLorentzMetric background.period
      background.period_ne_zero)
    (first second : EffectiveD8SmoothVectorField background) :
    (effectiveD8RegularHolonomicLorentzMetricVectorContraction background metric
      first second).field =
      effectiveD8SmoothLorentzMetricVectorContraction background metric first
        second :=
  rfl

/-- Exact pullback law for both components of the realized metric scalar. -/
theorem effectiveD8RegularHolonomicLorentzMetricVectorContraction_field_pullback
    {source target : EffectiveD8Background}
    (morphism : EffectiveD8BackgroundDiffeomorphism source target)
    (metric : SmoothGeneralLorentzMetric target.period target.period_ne_zero)
    (first second : EffectiveD8SmoothVectorField target) :
    (effectiveD8RegularHolonomicLorentzMetricVectorContraction source
        (effectiveD8SmoothGeneralLorentzMetricPullback morphism metric)
        (effectiveD8SmoothVectorFieldPullback morphism first)
        (effectiveD8SmoothVectorFieldPullback morphism second)).field =
      pullbackEffectiveD8SmoothField Real morphism
        (effectiveD8RegularHolonomicLorentzMetricVectorContraction target metric
          first second).field := by
  exact effectiveD8SmoothLorentzMetricVectorContraction_pullback morphism metric
    first second

theorem effectiveD8RegularHolonomicLorentzMetricVectorContraction_differential_pullback
    {source target : EffectiveD8Background}
    (morphism : EffectiveD8BackgroundDiffeomorphism source target)
    (metric : SmoothGeneralLorentzMetric target.period target.period_ne_zero)
    (first second : EffectiveD8SmoothVectorField target) :
    (effectiveD8RegularHolonomicLorentzMetricVectorContraction source
        (effectiveD8SmoothGeneralLorentzMetricPullback morphism metric)
        (effectiveD8SmoothVectorFieldPullback morphism first)
        (effectiveD8SmoothVectorFieldPullback morphism second)).differential =
      effectiveD8SmoothCovectorFieldPullback morphism
        (effectiveD8RegularHolonomicLorentzMetricVectorContraction target metric
          first second).differential := by
  exact effectiveD8RegularHolonomicTensorVectorContraction_differential_pullback
    morphism metric.tensor first second

end

end P0EFTJanusEffectiveD8RegularHolonomicTensorContraction4D
end JanusFormal
