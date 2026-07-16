import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusMatterGaugeNoetherOperator4D

/-!
# Action derivative bridge for the D8 matter/gauge Noether operator

This gate identifies the covector supplied to the concrete matter and
`U(1)^2` operator with the actual directional first variation of one action.
Finite invariance along every generated line then forces the combined
Noether operator to vanish.  No norm on the infinite-dimensional smooth
field space is postulated: differentiability is required only for each real
one-parameter line.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusMatterGaugeActionNoetherBridge4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusMatterGaugeNoetherOperator4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- The supplied covector is the actual derivative of the action along every
real line through the zero variation. -/
def HasMatterGaugeDirectionalFirstVariationAtZero
    (action : MatterGaugeVariationSpace period hPeriod -> Real)
    (euler : MatterGaugeVariationSpace period hPeriod →ₗ[Real] Real) : Prop :=
  forall variation : MatterGaugeVariationSpace period hPeriod,
    HasDerivAt (fun parameter : Real => action (parameter • variation))
      (euler variation) 0

/-- Finite invariance of the action along every concrete combined
matter/diffeomorphism and abelian-gauge line through zero. -/
def MatterGaugeLineInvariantAtZero
    (fields : IndependentFields period hPeriod)
    (action : MatterGaugeVariationSpace period hPeriod -> Real) : Prop :=
  forall gaugeParameter : MatterGaugeParameterSpace period hPeriod,
    forall lineParameter : Real,
      action
          (lineParameter •
            matterGaugeGenerator period hPeriod fields gaugeParameter) =
        action 0

/-- Once `euler` is identified with the action's true line derivative,
finite invariance yields the concrete Noether identity `B(dS) = 0`. -/
theorem matterGaugeNoetherOperator_eq_zero_of_action_invariant
    (fields : IndependentFields period hPeriod)
    (action : MatterGaugeVariationSpace period hPeriod -> Real)
    (euler : MatterGaugeVariationSpace period hPeriod →ₗ[Real] Real)
    (hFirstVariation :
      HasMatterGaugeDirectionalFirstVariationAtZero period hPeriod action euler)
    (hInvariant : MatterGaugeLineInvariantAtZero period hPeriod fields action) :
    matterGaugeNoetherOperator period hPeriod fields euler = 0 := by
  apply (matterGaugeNoetherOperator_eq_zero_iff period hPeriod fields euler).2
  intro gaugeParameter
  have hActionDerivative :=
    hFirstVariation (matterGaugeGenerator period hPeriod fields gaugeParameter)
  have hCurveConstant :
      (fun lineParameter : Real =>
          action
            (lineParameter •
              matterGaugeGenerator period hPeriod fields gaugeParameter)) =
        fun _ => action 0 := by
    funext lineParameter
    exact hInvariant gaugeParameter lineParameter
  have hZeroDerivative :
      HasDerivAt
        (fun lineParameter : Real =>
          action
            (lineParameter •
              matterGaugeGenerator period hPeriod fields gaugeParameter))
        0 0 := by
    rw [hCurveConstant]
    exact hasDerivAt_const (x := (0 : Real)) (c := action 0)
  exact hActionDerivative.unique hZeroDerivative

/-- Under the same first-variation identification, vanishing of `B(dS)` is
equivalent to infinitesimal stationarity along every generated line.  The
reverse implication to finite invariance would require derivatives at every
point of each line and is deliberately not asserted here. -/
theorem matterGaugeNoetherOperator_eq_zero_iff_line_derivative_zero
    (fields : IndependentFields period hPeriod)
    (action : MatterGaugeVariationSpace period hPeriod -> Real)
    (euler : MatterGaugeVariationSpace period hPeriod →ₗ[Real] Real)
    (hFirstVariation :
      HasMatterGaugeDirectionalFirstVariationAtZero period hPeriod action euler) :
    matterGaugeNoetherOperator period hPeriod fields euler = 0 <->
      forall gaugeParameter : MatterGaugeParameterSpace period hPeriod,
        HasDerivAt
          (fun lineParameter : Real =>
            action
              (lineParameter •
                matterGaugeGenerator period hPeriod fields gaugeParameter))
          0 0 := by
  rw [matterGaugeNoetherOperator_eq_zero_iff]
  constructor
  · intro hZero gaugeParameter
    exact (hFirstVariation
      (matterGaugeGenerator period hPeriod fields gaugeParameter)).congr_deriv
        (hZero gaugeParameter)
  · intro hDerivative gaugeParameter
    exact (hFirstVariation
      (matterGaugeGenerator period hPeriod fields gaugeParameter)).unique
        (hDerivative gaugeParameter)

/-- A linewise Euler one-form for the combined variation space.  This avoids
inventing a Banach topology on global smooth sections while still records the
actual derivative at every point of every real affine line. -/
def HasMatterGaugeLinewiseFirstVariationEverywhere
    (action : MatterGaugeVariationSpace period hPeriod -> Real)
    (euler : MatterGaugeVariationSpace period hPeriod ->
      (MatterGaugeVariationSpace period hPeriod →ₗ[Real] Real)) : Prop :=
  forall base direction : MatterGaugeVariationSpace period hPeriod,
    forall parameter : Real,
      HasDerivAt
        (fun lineParameter : Real => action (base + lineParameter • direction))
        (euler (base + parameter • direction) direction) parameter

/-- Finite invariance under every additive translation generated by the
concrete matter/diffeomorphism and `U(1)^2` block. -/
def MatterGaugeTranslationInvariant
    (fields : IndependentFields period hPeriod)
    (action : MatterGaugeVariationSpace period hPeriod -> Real) : Prop :=
  forall base : MatterGaugeVariationSpace period hPeriod,
    forall gaugeParameter : MatterGaugeParameterSpace period hPeriod,
      action
          (base + matterGaugeGenerator period hPeriod fields gaugeParameter) =
        action base

/-- With the actual linewise first variation supplied everywhere, finite
translation invariance is equivalent to the concrete Noether identity at
every field variation. -/
theorem matterGauge_translation_invariant_iff_noether_everywhere
    (fields : IndependentFields period hPeriod)
    (action : MatterGaugeVariationSpace period hPeriod -> Real)
    (euler : MatterGaugeVariationSpace period hPeriod ->
      (MatterGaugeVariationSpace period hPeriod →ₗ[Real] Real))
    (hFirstVariation :
      HasMatterGaugeLinewiseFirstVariationEverywhere period hPeriod action euler) :
    MatterGaugeTranslationInvariant period hPeriod fields action <->
      forall base : MatterGaugeVariationSpace period hPeriod,
        matterGaugeNoetherOperator period hPeriod fields (euler base) = 0 := by
  constructor
  · intro hInvariant base
    apply (matterGaugeNoetherOperator_eq_zero_iff period hPeriod fields
      (euler base)).2
    intro gaugeParameter
    let direction := matterGaugeGenerator period hPeriod fields gaugeParameter
    let curve : Real -> Real := fun parameter => action (base + parameter • direction)
    have hCurveDerivative : HasDerivAt curve (euler base direction) 0 := by
      simpa [curve, direction] using hFirstVariation base direction 0
    have hCurveConstant : curve = fun _ => action base := by
      funext parameter
      have hTranslated := hInvariant base (parameter • gaugeParameter)
      simpa [curve, direction] using hTranslated
    have hZeroDerivative : HasDerivAt curve 0 0 := by
      rw [hCurveConstant]
      exact hasDerivAt_const (x := (0 : Real)) (c := action base)
    exact hCurveDerivative.unique hZeroDerivative
  · intro hNoether base gaugeParameter
    let direction := matterGaugeGenerator period hPeriod fields gaugeParameter
    let curve : Real -> Real := fun parameter => action (base + parameter • direction)
    have hCurveDerivative (parameter : Real) : HasDerivAt curve 0 parameter := by
      have hDerivative := hFirstVariation base direction parameter
      have hHorizontal :=
        (matterGaugeNoetherOperator_eq_zero_iff period hPeriod fields
          (euler (base + parameter • direction))).1
          (hNoether (base + parameter • direction)) gaugeParameter
      exact (by simpa [curve, direction] using hDerivative.congr_deriv hHorizontal)
    have hCurveDifferentiable : Differentiable Real curve :=
      fun parameter => (hCurveDerivative parameter).differentiableAt
    have hCurveDerivZero (parameter : Real) : deriv curve parameter = 0 :=
      (hCurveDerivative parameter).deriv
    have hConstant :=
      is_const_of_deriv_eq_zero hCurveDifferentiable hCurveDerivZero 1 0
    simpa [curve, direction] using hConstant

end

end P0EFTJanusMappingTorusMatterGaugeActionNoetherBridge4D
end JanusFormal
