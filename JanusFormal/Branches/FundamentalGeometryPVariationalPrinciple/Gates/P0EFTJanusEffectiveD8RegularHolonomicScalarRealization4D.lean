import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusEffectiveD8HolonomicScalarDifferentialNaturality4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D

/-!
# Regular realization of the genuine holonomic scalar

The global manifold differential supplies the regularity witness required by
the scalar functional-action interface.  Both the scalar and its certified
differential retain their exact effective-D8 pullback laws.
-/

namespace JanusFormal
namespace P0EFTJanusEffectiveD8RegularHolonomicScalarRealization4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusEffectiveD8BackgroundCategory4D
open P0EFTJanusEffectiveD8SmoothCovectorFieldFunctor4D
open P0EFTJanusEffectiveD8HolonomicScalarDifferentialNaturality4D

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

/-- Every genuine smooth scalar on an effective D8 quotient canonically
inhabits the regular holonomic-scalar interface. -/
def effectiveD8RegularHolonomicScalar
    (background : EffectiveD8Background)
    (scalar : SmoothQuotientField background.period
      background.period_ne_zero Real) :
    RegularHolonomicScalar background.period background.period_ne_zero where
  field := scalar
  differential := effectiveD8SmoothScalarDifferential background scalar
  differential_eq := by
    intro point
    rfl

@[simp] theorem effectiveD8RegularHolonomicScalar_field
    (background : EffectiveD8Background)
    (scalar : SmoothQuotientField background.period
      background.period_ne_zero Real) :
    (effectiveD8RegularHolonomicScalar background scalar).field = scalar :=
  rfl

@[simp] theorem effectiveD8RegularHolonomicScalar_differential
    (background : EffectiveD8Background)
    (scalar : SmoothQuotientField background.period
      background.period_ne_zero Real) :
    (effectiveD8RegularHolonomicScalar background scalar).differential =
      effectiveD8SmoothScalarDifferential background scalar :=
  rfl

/-- The field component of the regular realization is exactly natural. -/
theorem effectiveD8RegularHolonomicScalar_field_pullback
    {source target : EffectiveD8Background}
    (morphism : EffectiveD8BackgroundDiffeomorphism source target)
    (scalar : SmoothQuotientField target.period target.period_ne_zero Real) :
    (effectiveD8RegularHolonomicScalar source
        (pullbackEffectiveD8SmoothField Real morphism scalar)).field =
      pullbackEffectiveD8SmoothField Real morphism
        (effectiveD8RegularHolonomicScalar target scalar).field :=
  rfl

/-- The differential component of the regular realization is exactly
natural as a genuine smooth covector field. -/
theorem effectiveD8RegularHolonomicScalar_differential_pullback
    {source target : EffectiveD8Background}
    (morphism : EffectiveD8BackgroundDiffeomorphism source target)
    (scalar : SmoothQuotientField target.period target.period_ne_zero Real) :
    (effectiveD8RegularHolonomicScalar source
        (pullbackEffectiveD8SmoothField Real morphism scalar)).differential =
      effectiveD8SmoothCovectorFieldPullback morphism
        (effectiveD8RegularHolonomicScalar target scalar).differential := by
  exact effectiveD8SmoothScalarDifferential_pullback morphism scalar

end

end P0EFTJanusEffectiveD8RegularHolonomicScalarRealization4D
end JanusFormal
