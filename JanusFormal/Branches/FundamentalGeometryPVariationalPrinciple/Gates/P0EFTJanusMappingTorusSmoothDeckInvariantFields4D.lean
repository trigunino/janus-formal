import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusSmoothAtlasFrontier

/-!
# Smooth deck-invariant fields on the analytic mapping-torus cover

Until the quotient atlas is promoted from `C⁰` to `C∞`, smooth global fields
can still be defined intrinsically as smooth fields on the analytic cover that
are invariant under every deck iterate.  Such fields descend uniquely and
continuously to the effective quotient.  This gate constructs that field
space for arbitrary finite-dimensional real coefficient fibers and supplies a
nonempty two-metric/two-scalar/root coefficient configuration.

No Lorentz nondegeneracy, Sobolev completion, boundary condition or field
equation is asserted here.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusSmoothDeckInvariantFields4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff ENNReal lp
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier

variable (period : ℝ) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveCover := MappingTorusCover (sphereData period hPeriod)
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance effectiveCoverChartedSpace :
    ChartedSpace CoverModel (EffectiveCover period hPeriod) :=
  reflectedSphereCoverChartedSpace period hPeriod

local instance effectiveCoverIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveCover period hPeriod) :=
  reflectedSphereCover_isManifold period hPeriod

universe u

variable (Fiber : Type u)
  [NormedAddCommGroup Fiber] [NormedSpace ℝ Fiber]

/-- A global smooth coefficient field represented upstairs, with exact deck
invariance rather than a supplied quotient representative. -/
structure SmoothDeckInvariantField where
  toFun : EffectiveCover period hPeriod → Fiber
  contMDiff_toFun : ContMDiff coverModelWithCorners (𝓘(ℝ, Fiber)) ω toFun
  deck_invariant : ∀ (winding : ℤ) (point : EffectiveCover period hPeriod),
    toFun (winding +ᵥ point) = toFun point

instance : CoeFun (SmoothDeckInvariantField period hPeriod Fiber)
    (fun _ => EffectiveCover period hPeriod → Fiber) :=
  ⟨SmoothDeckInvariantField.toFun⟩

@[ext]
theorem SmoothDeckInvariantField.ext
    {first second : SmoothDeckInvariantField period hPeriod Fiber}
    (hEqual : ∀ point, first point = second point) : first = second := by
  cases first with
  | mk firstFun firstSmooth firstInvariant =>
    cases second with
    | mk secondFun secondSmooth secondInvariant =>
      have hFun : firstFun = secondFun := funext hEqual
      subst secondFun
      rfl

/-- Every constant coefficient is a smooth global deck-invariant field. -/
def constantField (value : Fiber) :
    SmoothDeckInvariantField period hPeriod Fiber where
  toFun := fun _ => value
  contMDiff_toFun := contMDiff_const
  deck_invariant := by simp

@[simp]
theorem constantField_apply (value : Fiber)
    (point : EffectiveCover period hPeriod) :
    constantField period hPeriod Fiber value point = value := rfl

/-- Descent to the actual effective quotient. -/
def descend
    (field : SmoothDeckInvariantField period hPeriod Fiber) :
    EffectiveQuotient period hPeriod → Fiber :=
  Quotient.lift field.toFun (fun first second hOrbit => by
    change AddAction.orbitRel ℤ (EffectiveCover period hPeriod)
      first second at hOrbit
    rw [AddAction.orbitRel_apply, AddAction.mem_orbit_iff] at hOrbit
    rcases hOrbit with ⟨winding, hWinding⟩
    rw [← hWinding]
    exact field.deck_invariant winding second)

@[simp]
theorem descend_mk
    (field : SmoothDeckInvariantField period hPeriod Fiber)
    (point : EffectiveCover period hPeriod) :
    descend period hPeriod Fiber field
        (mappingTorusMk (sphereData period hPeriod) point) = field point := rfl

theorem continuous_descend
    (field : SmoothDeckInvariantField period hPeriod Fiber) :
    Continuous (descend period hPeriod Fiber field) := by
  apply field.contMDiff_toFun.continuous.quotient_lift

/-- No information is lost by descending an invariant field. -/
theorem descend_injective :
    Function.Injective
      (descend period hPeriod Fiber :
        SmoothDeckInvariantField period hPeriod Fiber →
          EffectiveQuotient period hPeriod → Fiber) := by
  intro first second hEqual
  apply SmoothDeckInvariantField.ext period hPeriod Fiber
  intro point
  have hPoint := congrFun hEqual
    (mappingTorusMk (sphereData period hPeriod) point)
  simpa using hPoint

/-- The descended constant field is the same constant on the quotient. -/
theorem descend_constantField
    (value : Fiber) :
    descend period hPeriod Fiber (constantField period hPeriod Fiber value) =
      fun _ => value := by
  funext quotientPoint
  induction quotientPoint using Quotient.inductionOn with
  | _ point => rfl

/-- Scalar, vector, metric-coefficient and root-coefficient fibers. -/
abbrev SmoothScalarField := SmoothDeckInvariantField period hPeriod ℝ

abbrev SmoothVectorField :=
  SmoothDeckInvariantField period hPeriod (EuclideanSpace ℝ (Fin 4))

abbrev MetricCoefficientFiber :=
  EuclideanSpace ℝ (Fin 4 × Fin 4)

abbrev SmoothMetricCoefficientField :=
  SmoothDeckInvariantField period hPeriod MetricCoefficientFiber

/-- Flat Lorentz and identity coefficient tensors used only to exhibit a
nonempty smooth field configuration. -/
def minkowskiMetricCoefficients : MetricCoefficientFiber :=
  WithLp.toLp 2 (fun pair =>
    if pair.1 = pair.2 then if pair.1 = 0 then (-1 : ℝ) else 1 else 0)

def identityRootCoefficients : MetricCoefficientFiber :=
  WithLp.toLp 2 (fun pair => if pair.1 = pair.2 then 1 else 0)

/-- Two independent metric fields, two scalar fields and one selected relative
root coefficient field, all on the same analytic cover and quotient. -/
structure SmoothIndependentCoefficientConfiguration where
  gPlus : SmoothMetricCoefficientField period hPeriod
  gMinus : SmoothMetricCoefficientField period hPeriod
  psiPlus : SmoothScalarField period hPeriod
  psiMinus : SmoothScalarField period hPeriod
  root : SmoothMetricCoefficientField period hPeriod

/-- Explicit nonempty PT-flat coefficient witness. -/
def flatSmoothConfiguration :
    SmoothIndependentCoefficientConfiguration period hPeriod where
  gPlus := constantField period hPeriod MetricCoefficientFiber
    minkowskiMetricCoefficients
  gMinus := constantField period hPeriod MetricCoefficientFiber
    minkowskiMetricCoefficients
  psiPlus := constantField period hPeriod ℝ 0
  psiMinus := constantField period hPeriod ℝ 0
  root := constantField period hPeriod MetricCoefficientFiber
    identityRootCoefficients

theorem smooth_deck_invariant_field_gate :
    (∃ configuration : SmoothIndependentCoefficientConfiguration period hPeriod,
      ∀ point : EffectiveCover period hPeriod,
        configuration.gPlus point = minkowskiMetricCoefficients ∧
        configuration.gMinus point = minkowskiMetricCoefficients ∧
        configuration.psiPlus point = 0 ∧
        configuration.psiMinus point = 0 ∧
        configuration.root point = identityRootCoefficients) ∧
    (∀ field : SmoothScalarField period hPeriod,
      Continuous (descend period hPeriod ℝ field)) ∧
    Function.Injective
      (descend period hPeriod ℝ :
        SmoothScalarField period hPeriod →
          EffectiveQuotient period hPeriod → ℝ) := by
  refine ⟨⟨flatSmoothConfiguration period hPeriod, ?_⟩,
    continuous_descend period hPeriod ℝ,
    descend_injective period hPeriod ℝ⟩
  intro point
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

end

end P0EFTJanusMappingTorusSmoothDeckInvariantFields4D
end JanusFormal
