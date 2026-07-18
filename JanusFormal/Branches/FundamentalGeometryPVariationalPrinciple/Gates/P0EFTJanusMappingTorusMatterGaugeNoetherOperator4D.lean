import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarDiffeomorphismNoetherOperator4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusAbelianGaugeNoetherOperator4D

/-!
# Combined matter and abelian gauge R/B operator on D8

This gate assembles the concrete scalar-diffeomorphism and `U(1)^2` gauge
generators on the same smooth quotient.  The supplied covector is arbitrary;
identifying it with the derivative of one invariant action remains separate.
Metric, LL and nonlinear BRST blocks remain outside this partial global
generator.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusMatterGaugeNoetherOperator4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusLinearizedDiffeomorphismBRST4D
open P0EFTJanusMappingTorusScalarDiffeomorphismNoetherOperator4D
open P0EFTJanusMappingTorusAbelianGaugeNoetherOperator4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- Independent parameters for the matter diffeomorphism and `U(1)^2`
blocks. -/
abbrev MatterGaugeParameterSpace :=
  SmoothDiffeomorphismGhost period hPeriod ×
    (SmoothQuotientField period hPeriod GaugeLieAlgebra ×
      SmoothQuotientField period hPeriod GaugeLieAlgebra)

/-- Simultaneous variations of the eight scalar matter components and the two
abelian gauge potentials. -/
abbrev MatterGaugeVariationSpace :=
  MatterComponentFamily period hPeriod ×
    (SmoothAbelianGaugePotential period hPeriod ×
      SmoothAbelianGaugePotential period hPeriod)

/-- The concrete block generator `R_matter ⊕ R_A` on the actual smooth D8
quotient. -/
def matterGaugeGenerator
    (fields : IndependentFields period hPeriod) :
    MatterGaugeParameterSpace period hPeriod →ₗ[Real]
      MatterGaugeVariationSpace period hPeriod where
  toFun parameters :=
    (matterMultipletDiffeomorphismGaugeGenerator period hPeriod fields
        parameters.1,
      abelianGaugePairGenerator period hPeriod parameters.2)
  map_add' first second := by
    apply Prod.ext
    · exact (matterMultipletDiffeomorphismGaugeGenerator period hPeriod fields).map_add
        first.1 second.1
    · exact (abelianGaugePairGenerator period hPeriod).map_add first.2 second.2
  map_smul' scalar parameters := by
    apply Prod.ext
    · exact (matterMultipletDiffeomorphismGaugeGenerator period hPeriod fields).map_smul
        scalar parameters.1
    · exact (abelianGaugePairGenerator period hPeriod).map_smul scalar parameters.2

@[simp]
theorem matterGaugeGenerator_matter_component
    (fields : IndependentFields period hPeriod)
    (parameters : MatterGaugeParameterSpace period hPeriod)
    (index : MatterComponentIndex) :
    (matterGaugeGenerator period hPeriod fields parameters).1 index =
      scalarLieDerivative period hPeriod parameters.1
        (independentMatterScalar period hPeriod fields index.1 index.2) :=
  rfl

@[simp]
theorem matterGaugeGenerator_gauge_pair
    (fields : IndependentFields period hPeriod)
    (parameters : MatterGaugeParameterSpace period hPeriod) :
    (matterGaugeGenerator period hPeriod fields parameters).2 =
      (exactGaugePotential period hPeriod parameters.2.1,
        exactGaugePotential period hPeriod parameters.2.2) :=
  rfl

/-- The algebraic Noether candidate `B(E) = E ∘ (R_matter ⊕ R_A)`. -/
def matterGaugeNoetherOperator
    (fields : IndependentFields period hPeriod)
    (euler : MatterGaugeVariationSpace period hPeriod →ₗ[Real] Real) :
    MatterGaugeParameterSpace period hPeriod →ₗ[Real] Real :=
  euler.comp (matterGaugeGenerator period hPeriod fields)

@[simp]
theorem matterGaugeNoetherOperator_apply
    (fields : IndependentFields period hPeriod)
    (euler : MatterGaugeVariationSpace period hPeriod →ₗ[Real] Real)
    (parameters : MatterGaugeParameterSpace period hPeriod) :
    matterGaugeNoetherOperator period hPeriod fields euler parameters =
      euler
        (fun index =>
          scalarLieDerivative period hPeriod parameters.1
            (independentMatterScalar period hPeriod fields index.1 index.2),
          (exactGaugePotential period hPeriod parameters.2.1,
            exactGaugePotential period hPeriod parameters.2.2)) :=
  rfl

/-- Vanishing of the combined operator is exactly annihilation of the image
of every concrete matter and abelian gauge direction.  Calling this action
invariance additionally requires a proof that `euler` is the derivative of
that action. -/
theorem matterGaugeNoetherOperator_eq_zero_iff
    (fields : IndependentFields period hPeriod)
    (euler : MatterGaugeVariationSpace period hPeriod →ₗ[Real] Real) :
    matterGaugeNoetherOperator period hPeriod fields euler = 0 ↔
      ∀ parameters : MatterGaugeParameterSpace period hPeriod,
        euler (matterGaugeGenerator period hPeriod fields parameters) = 0 := by
  constructor
  · intro hZero parameters
    have hApply := LinearMap.congr_fun hZero parameters
    exact hApply
  · intro hInvariant
    apply LinearMap.ext
    intro parameters
    exact hInvariant parameters

end

end P0EFTJanusMappingTorusMatterGaugeNoetherOperator4D
end JanusFormal
