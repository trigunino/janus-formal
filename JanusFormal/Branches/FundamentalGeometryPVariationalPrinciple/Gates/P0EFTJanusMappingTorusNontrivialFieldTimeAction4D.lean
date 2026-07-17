import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCompleteIndependentFieldTimeAction4D

/-!
# A nontrivial smooth field orbit for the D8 time action

The complete time action is geometrically nontrivial.  Here a periodic cosine
mode is descended to the quotient and proves that the induced pullback action
on smooth fields is nontrivial as well.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusNontrivialFieldTimeAction4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothDeckInvariantFields4D
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusDiagonalDiffeomorphismAction4D
open P0EFTJanusMappingTorusCompleteTimeFlow4D
open P0EFTJanusMappingTorusCompleteIndependentFieldTimeAction4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveCover := MappingTorusCover (sphereData period hPeriod)
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance effectiveCoverChartedSpace :
    ChartedSpace CoverModel (EffectiveCover period hPeriod) :=
  reflectedSphereCoverChartedSpace period hPeriod

local instance effectiveCoverIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveCover period hPeriod) :=
  reflectedSphereCover_isManifold period hPeriod

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- The first nonconstant periodic time mode on the mapping-torus cover. -/
def periodicCosineCoverField :
    SmoothDeckInvariantField period hPeriod Real where
  toFun := fun point => Real.cos ((2 * Real.pi / period) * point.time)
  contMDiff_toFun := by
    let productEquiv := coverHomeomorphProd (sphereData period hPeriod)
    have hTo := chartedSpacePullback_toFun_contMDiff coverModelWithCorners ω
      productEquiv
    have hTime : ContMDiff coverModelWithCorners 𝓘(Real, Real) ω
        (fun point : EffectiveCover period hPeriod => point.time) :=
      contMDiff_snd.comp hTo
    exact Real.contDiff_cos.contMDiff.comp (contMDiff_const.mul hTime)
  deck_invariant := by
    intro winding point
    change Real.cos
        ((2 * Real.pi / period) *
          (point.time + (winding : Real) * period)) =
      Real.cos ((2 * Real.pi / period) * point.time)
    have hArgument :
        (2 * Real.pi / period) *
            (point.time + (winding : Real) * period) =
          (2 * Real.pi / period) * point.time +
            (winding : Real) * (2 * Real.pi) := by
      field_simp [hPeriod]
    rw [hArgument]
    exact Real.cos_add_int_mul_two_pi _ winding

/-- The corresponding genuine smooth quotient scalar. -/
def periodicCosineQuotientField :
    SmoothQuotientField period hPeriod Real :=
  descendSmooth period hPeriod Real
    (periodicCosineCoverField period hPeriod)

@[simp]
theorem periodicCosineQuotientField_mk
    (point : EffectiveCover period hPeriod) :
    periodicCosineQuotientField period hPeriod
        (mappingTorusMk (sphereData period hPeriod) point) =
      Real.cos ((2 * Real.pi / period) * point.time) :=
  rfl

private theorem halfPeriodArgument (hPeriod : period ≠ 0) :
    (2 * Real.pi / period) * (period / 2) = Real.pi := by
  field_simp [hPeriod]

private theorem periodicCosine_at_witness :
    periodicCosineQuotientField period hPeriod
        (timeFlowWitnessPoint period hPeriod) = 1 := by
  unfold timeFlowWitnessPoint
  simp

private theorem periodicCosine_at_halfPeriod_witness :
    periodicCosineQuotientField period hPeriod
        (effectiveTimeFlow period hPeriod (period / 2)
          (timeFlowWitnessPoint period hPeriod)) = -1 := by
  unfold timeFlowWitnessPoint
  rw [effectiveTimeFlow_mk, periodicCosineQuotientField_mk]
  change Real.cos ((2 * Real.pi / period) * (0 + period / 2)) = -1
  rw [zero_add, halfPeriodArgument period hPeriod]
  exact Real.cos_pi

/-- The induced pullback representation on smooth quotient fields is itself
nontrivial. -/
theorem smoothSpacetimeTimeAction_halfPeriod_ne :
    smoothSpacetimeTimeAction period hPeriod Real (period / 2)
        (periodicCosineQuotientField period hPeriod) ≠
      periodicCosineQuotientField period hPeriod := by
  intro hEqual
  have hValue := congrArg
    (fun field : SmoothQuotientField period hPeriod Real =>
      field (timeFlowWitnessPoint period hPeriod)) hEqual
  rw [smoothSpacetimeTimeAction_apply,
    periodicCosine_at_halfPeriod_witness,
    periodicCosine_at_witness] at hValue
  norm_num at hValue

/-- Embed the periodic scalar into the first component of the physical matter
fiber used by `IndependentFields`. -/
def periodicCosineMatterField :
    SmoothQuotientField period hPeriod MatterFiber where
  toFun := fun point =>
    periodicCosineQuotientField period hPeriod point •
      EuclideanSpace.single 0 1
  contMDiff_toFun :=
    (periodicCosineQuotientField period hPeriod).contMDiff_toFun.smul
      (I := 𝓘(Real)) contMDiff_const

@[simp]
theorem periodicCosineMatterField_zero
    (point : EffectiveQuotient period hPeriod) :
    periodicCosineMatterField period hPeriod point 0 =
      periodicCosineQuotientField period hPeriod point := by
  simp [periodicCosineMatterField]

/-- A genuine current configuration whose first matter component carries the
periodic quotient mode. -/
def periodicMatterIndependentFields : IndependentFields period hPeriod :=
  { zeroMatchedIndependentFields period hPeriod with
    matter :=
      (periodicCosineMatterField period hPeriod,
        (zeroMatchedIndependentFields period hPeriod).matter.2) }

/-- The complete current field package has a nontrivial time orbit. -/
theorem independentTimeAction_periodicMatter_halfPeriod_ne :
    independentTimeAction period hPeriod (period / 2)
        (periodicMatterIndependentFields period hPeriod) ≠
      periodicMatterIndependentFields period hPeriod := by
  intro hEqual
  have hValue := congrArg
    (fun fields : IndependentFields period hPeriod =>
      fields.matter.1 (timeFlowWitnessPoint period hPeriod) 0) hEqual
  simp only [independentTimeAction, pullbackIndependentFields,
    periodicMatterIndependentFields, pullbackSmoothField,
    diagonalTimeFlowDiffeomorphism] at hValue
  change periodicCosineMatterField period hPeriod
      (effectiveTimeFlowDiffeomorph period hPeriod (period / 2)
        (timeFlowWitnessPoint period hPeriod)) 0 =
    periodicCosineMatterField period hPeriod
      (timeFlowWitnessPoint period hPeriod) 0 at hValue
  rw [periodicCosineMatterField_zero,
    periodicCosineMatterField_zero] at hValue
  change periodicCosineQuotientField period hPeriod
      (effectiveTimeFlow period hPeriod (period / 2)
        (timeFlowWitnessPoint period hPeriod)) =
    periodicCosineQuotientField period hPeriod
      (timeFlowWitnessPoint period hPeriod) at hValue
  rw [periodicCosine_at_halfPeriod_witness,
    periodicCosine_at_witness] at hValue
  norm_num at hValue

theorem nontrivial_field_time_action4D_closed :
    (∃ (shift : Real) (field : SmoothQuotientField period hPeriod Real),
      smoothSpacetimeTimeAction period hPeriod Real shift field ≠ field) ∧
    (∃ (shift : Real) (fields : IndependentFields period hPeriod),
      independentTimeAction period hPeriod shift fields ≠ fields) :=
  ⟨⟨period / 2, periodicCosineQuotientField period hPeriod,
      smoothSpacetimeTimeAction_halfPeriod_ne period hPeriod⟩,
    ⟨period / 2, periodicMatterIndependentFields period hPeriod,
      independentTimeAction_periodicMatter_halfPeriod_ne period hPeriod⟩⟩

end

end P0EFTJanusMappingTorusNontrivialFieldTimeAction4D
end JanusFormal
