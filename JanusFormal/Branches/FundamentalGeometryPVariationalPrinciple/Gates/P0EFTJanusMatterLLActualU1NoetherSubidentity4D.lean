import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCompleteVariationMatterLLActionHessian4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusMatterGaugeActionNoetherBridge4D

/-!
# Actual `U(1)^2` Noether subidentity for the matter--LL action

The existing matter--LL functional is restricted to its genuine global
matter variables while the LL fields are frozen.  Its gauge-potential slots
are the intrinsic one-forms already used by `R_A(c) = dc`; they are inactive
because no Maxwell summand is present.  The resulting Euler covector is
proved to be the actual line derivative, and its concrete Noether operator
vanishes on every pure `U(1)^2` parameter.

This is only the abelian subidentity of the sectorial matter--LL action.  It
does not identify intrinsic one-forms with the unrelated `GaugeFiber`
coefficient fields, and proves neither diagonal-diffeomorphism Noether nor a
global Candidate-A identity.
-/

namespace JanusFormal
namespace P0EFTJanusMatterLLActualU1NoetherSubidentity4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff
open MeasureTheory
open P0EFTJanusReflectionFixedThroat
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusLinearizedDiffeomorphismBRST4D
open P0EFTJanusMappingTorusScalarDiffeomorphismNoetherOperator4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusAbelianGaugeNoetherOperator4D
open P0EFTJanusMappingTorusMatterGaugeNoetherOperator4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarVariation4D
open P0EFTJanusGlobalMatterMultipletActualEulerHessian4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLWeakEquation4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)
private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance : IsManifold coverModelWithCorners ω
    (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance : IsManifold throatCoverModelWithCorners ω
    (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _

local instance : BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

/-- The unchanged global matter action plus the unchanged differential-LL
action, restricted to matter and intrinsic gauge-potential variations.  The
LL background is frozen and the gauge potentials are inactive because this
functional contains no Maxwell term. -/
def frozenLLMatterGaugeAction
    (data : MatterMultipletActionData period hPeriod)
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod))
    (variation : MatterGaugeVariationSpace period hPeriod) : Real :=
  globalMatterMultipletAction period hPeriod data
      (fun index => independentMatterComponentFamily period hPeriod fields index +
        variation.1 index) +
    globalPTSymmetricDifferentialLLAction period hPeriod frame fields mu

/-- The Euler covector of the restricted action at an arbitrary base
variation.  It is bundled as a genuine linear map on the same matter/gauge
variation space used by the concrete generator. -/
def frozenLLMatterGaugeEuler
    (data : MatterMultipletActionData period hPeriod)
    (fields : IndependentFields period hPeriod)
    (base : MatterGaugeVariationSpace period hPeriod) :
    MatterGaugeVariationSpace period hPeriod →ₗ[Real] Real where
  toFun direction :=
    globalMatterMultipletEuler period hPeriod data
      (fun index => independentMatterComponentFamily period hPeriod fields index +
        base.1 index) direction.1
  map_add' first second := by
    change globalMatterMultipletEuler period hPeriod data
        (fun index => independentMatterComponentFamily period hPeriod fields index +
          base.1 index) (first.1 + second.1) =
      globalMatterMultipletEuler period hPeriod data
          (fun index => independentMatterComponentFamily period hPeriod fields index +
            base.1 index) first.1 +
        globalMatterMultipletEuler period hPeriod data
          (fun index => independentMatterComponentFamily period hPeriod fields index +
            base.1 index) second.1
    unfold globalMatterMultipletEuler
    simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' scalar direction := by
    change globalMatterMultipletEuler period hPeriod data
        (fun index => independentMatterComponentFamily period hPeriod fields index +
          base.1 index) (scalar • direction.1) =
      scalar • globalMatterMultipletEuler period hPeriod data
        (fun index => independentMatterComponentFamily period hPeriod fields index +
          base.1 index) direction.1
    unfold globalMatterMultipletEuler
    simp only [Pi.smul_apply, map_smul, RingHom.id_apply, smul_eq_mul,
      Finset.mul_sum]

/-- The preceding Euler covector is the actual derivative of the same
restricted matter--LL action along every affine line. -/
theorem frozenLLMatterGaugeAction_hasDerivAt
    (data : MatterMultipletActionData period hPeriod)
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod))
    (base direction : MatterGaugeVariationSpace period hPeriod) :
    HasDerivAt
      (fun parameter : Real => frozenLLMatterGaugeAction period hPeriod data
        frame fields mu (base + parameter • direction))
      (frozenLLMatterGaugeEuler period hPeriod data fields base direction) 0 := by
  have hMatter := globalMatterMultipletAction_hasDerivAt period hPeriod data
    (fun index => independentMatterComponentFamily period hPeriod fields index +
      base.1 index) direction.1
  have hCurve :
      (fun parameter : Real => frozenLLMatterGaugeAction period hPeriod data
        frame fields mu (base + parameter • direction)) =
      (fun parameter : Real =>
        globalMatterMultipletAction period hPeriod data
          (matterMultipletAffineCurve period hPeriod
            (fun index =>
              independentMatterComponentFamily period hPeriod fields index +
                base.1 index)
            direction.1 parameter) +
        globalPTSymmetricDifferentialLLAction period hPeriod frame fields mu) := by
    funext parameter
    unfold frozenLLMatterGaugeAction
    apply congrArg (fun matter =>
      globalMatterMultipletAction period hPeriod data matter +
        globalPTSymmetricDifferentialLLAction period hPeriod frame fields mu)
    funext index
    apply SmoothQuotientField.ext period hPeriod Real
    intro point
    change _ + (_ + parameter * _) = (_ + _) + parameter * _
    exact (add_assoc _ _ _).symm
  rw [hCurve]
  exact hMatter.add_const
    (globalPTSymmetricDifferentialLLAction period hPeriod frame fields mu)

/-- Inclusion of the true pair of abelian gauge parameters into the combined
parameter space, with zero diffeomorphism ghost. -/
def pureU1Parameter :
    (SmoothQuotientField period hPeriod GaugeLieAlgebra ×
      SmoothQuotientField period hPeriod GaugeLieAlgebra) →
      MatterGaugeParameterSpace period hPeriod :=
  fun parameters => (0, parameters)

/-- The combined concrete generator on a pure abelian parameter is exactly
zero in matter and the genuine pair `(dc₊, dc₋)` in gauge potentials. -/
theorem matterGaugeGenerator_pureU1
    (fields : IndependentFields period hPeriod)
    (parameters : SmoothQuotientField period hPeriod GaugeLieAlgebra ×
      SmoothQuotientField period hPeriod GaugeLieAlgebra) :
    matterGaugeGenerator period hPeriod fields
        (pureU1Parameter period hPeriod parameters) =
      (0, (exactGaugePotential period hPeriod parameters.1,
        exactGaugePotential period hPeriod parameters.2)) := by
  apply Prod.ext
  · funext index
    change scalarLieDerivative period hPeriod
      (0 : SmoothDiffeomorphismGhost period hPeriod)
        (independentMatterScalar period hPeriod fields index.1 index.2) = 0
    exact scalarLieDerivative_zeroGhost period hPeriod
      (independentMatterScalar period hPeriod fields index.1 index.2)
  · rfl

/-- Finite invariance of the same restricted action under every true
`U(1)^2` translation. -/
theorem frozenLLMatterGaugeAction_pureU1_invariant
    (data : MatterMultipletActionData period hPeriod)
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod))
    (base : MatterGaugeVariationSpace period hPeriod)
    (parameters : SmoothQuotientField period hPeriod GaugeLieAlgebra ×
      SmoothQuotientField period hPeriod GaugeLieAlgebra) :
    frozenLLMatterGaugeAction period hPeriod data frame fields mu
        (base + matterGaugeGenerator period hPeriod fields
          (pureU1Parameter period hPeriod parameters)) =
      frozenLLMatterGaugeAction period hPeriod data frame fields mu base := by
  rw [matterGaugeGenerator_pureU1]
  unfold frozenLLMatterGaugeAction
  apply congrArg (fun matter =>
    globalMatterMultipletAction period hPeriod data matter +
      globalPTSymmetricDifferentialLLAction period hPeriod frame fields mu)
  funext index
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  change _ + (_ + 0) = _ + _
  rw [add_zero]

/-- Dynamic abelian Noether subidentity: the concrete `B(dS)` built from the
actual derivative of the same restricted action annihilates every pure
`U(1)^2` parameter. -/
theorem matterGaugeNoetherOperator_actualEuler_pureU1_zero
    (data : MatterMultipletActionData period hPeriod)
    (fields : IndependentFields period hPeriod)
    (base : MatterGaugeVariationSpace period hPeriod)
    (parameters : SmoothQuotientField period hPeriod GaugeLieAlgebra ×
      SmoothQuotientField period hPeriod GaugeLieAlgebra) :
    matterGaugeNoetherOperator period hPeriod fields
        (frozenLLMatterGaugeEuler period hPeriod data fields base)
        (pureU1Parameter period hPeriod parameters) = 0 := by
  change frozenLLMatterGaugeEuler period hPeriod data fields base
    (matterGaugeGenerator period hPeriod fields
      (pureU1Parameter period hPeriod parameters)) = 0
  rw [matterGaugeGenerator_pureU1]
  change globalMatterMultipletEuler period hPeriod data
    (fun index => independentMatterComponentFamily period hPeriod fields index +
      base.1 index) (0 : MatterComponentFamily period hPeriod) = 0
  unfold globalMatterMultipletEuler
  simp only [Pi.zero_apply, map_zero, Finset.sum_const_zero]

end
end P0EFTJanusMatterLLActualU1NoetherSubidentity4D
end JanusFormal
