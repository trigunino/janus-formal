import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCompleteTimeFlow4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusDiagonalDiffeomorphismAction4D

/-!
# Complete time action on the full independent D8 field package

The mapping-torus translation restricts to the actual smooth throat and its
spacetime and throat slices form a diagonal diffeomorphism preserving the
closed inclusion.  Pullback therefore acts on every component of the current
`IndependentFields` package.  The action has the exact real group law,
inverse slices and PT conjugation, and induction commutes with the action.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCompleteIndependentFieldTimeAction4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff Matrix.Norms.Frobenius
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusPTInvolution
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothPTFieldAction4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothDiagonalLorentzFields4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusDiagonalDiffeomorphismAction4D
open P0EFTJanusMappingTorusCompleteTimeFlow4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev throatData := fixedEquatorData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)
private abbrev EffectiveThroat := MappingTorus (throatData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveThroatCoverChartedSpace :
    ChartedSpace ThroatCoverModel
      (MappingTorusCover (throatData period hPeriod)) :=
  fixedThroatCoverChartedSpace period hPeriod

local instance effectiveThroatCoverIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (MappingTorusCover (throatData period hPeriod)) :=
  fixedThroatCover_isManifold period hPeriod

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-- Translation restricted to the actual three-dimensional throat quotient. -/
def throatTimeFlow (shift : Real) :
    EffectiveThroat period hPeriod → EffectiveThroat period hPeriod :=
  quotientTimeTranslation (throatData period hPeriod) shift

@[simp]
theorem throatTimeFlow_mk (shift : Real)
    (point : MappingTorusCover (throatData period hPeriod)) :
    throatTimeFlow period hPeriod shift
        (mappingTorusMk (throatData period hPeriod) point) =
      mappingTorusMk (throatData period hPeriod)
        (coverTimeTranslation (throatData period hPeriod) shift point) :=
  rfl

@[simp]
theorem throatTimeFlow_zero (point : EffectiveThroat period hPeriod) :
    throatTimeFlow period hPeriod 0 point = point :=
  quotientTimeTranslation_zero _ point

theorem throatTimeFlow_add (first second : Real)
    (point : EffectiveThroat period hPeriod) :
    throatTimeFlow period hPeriod (first + second) point =
      throatTimeFlow period hPeriod first
        (throatTimeFlow period hPeriod second point) :=
  quotientTimeTranslation_add _ first second point

private theorem equatorialProductTimeTranslation_contMDiff (shift : Real) :
    ContMDiff throatCoverModelWithCorners throatCoverModelWithCorners ω
      (fun point : EquatorialTwoSphere × Real => (point.1, point.2 + shift)) := by
  have hTime : ContMDiff 𝓘(Real, Real) 𝓘(Real, Real) ω
      (fun time : Real => time + shift) :=
    (contDiff_id.add contDiff_const).contMDiff
  exact (contMDiff_id.prodMap hTime).congr fun _ => rfl

/-- Every throat translation slice is analytic on the product cover. -/
theorem throatCoverTimeTranslation_contMDiff (shift : Real) :
    ContMDiff throatCoverModelWithCorners throatCoverModelWithCorners ω
      (coverTimeTranslation (throatData period hPeriod) shift) := by
  have hTo := chartedSpacePullback_toFun_contMDiff
    throatCoverModelWithCorners ω
    (coverHomeomorphProd (throatData period hPeriod))
  have hInv := chartedSpacePullback_invFun_contMDiff
    throatCoverModelWithCorners ω
    (coverHomeomorphProd (throatData period hPeriod))
  have hComposite := hInv.comp
    ((equatorialProductTimeTranslation_contMDiff shift).comp hTo)
  exact hComposite.congr fun point => by
    apply MappingTorusCover.ext <;> rfl

/-- Every descended throat translation slice is analytic. -/
theorem throatTimeFlow_contMDiff (shift : Real) :
    ContMDiff throatCoverModelWithCorners throatCoverModelWithCorners ω
      (throatTimeFlow period hPeriod shift) := by
  exact quotientTimeTranslation_contMDiff throatCoverModelWithCorners ω
    (throatData period hPeriod)
    (fixedThroatCover_deck_contMDiff period hPeriod) shift
    (throatCoverTimeTranslation_contMDiff period hPeriod shift)

/-- Analytic throat slice, with inverse given by opposite time. -/
def throatTimeFlowDiffeomorph (shift : Real) :
    EffectiveThroat period hPeriod ≃ₘ^ω⟮
      throatCoverModelWithCorners, throatCoverModelWithCorners⟯
      EffectiveThroat period hPeriod where
  toEquiv :=
    { toFun := throatTimeFlow period hPeriod shift
      invFun := throatTimeFlow period hPeriod (-shift)
      left_inv := quotientTimeTranslation_neg_left _ shift
      right_inv := quotientTimeTranslation_neg_right _ shift }
  contMDiff_toFun := throatTimeFlow_contMDiff period hPeriod shift
  contMDiff_invFun := throatTimeFlow_contMDiff period hPeriod (-shift)

/-- Throat PT conjugates translation to the opposite-time slice. -/
theorem fixedThroatPT_throatTimeFlow (shift : Real)
    (point : EffectiveThroat period hPeriod) :
    fixedThroatPT period hPeriod
        (throatTimeFlow period hPeriod shift point) =
      throatTimeFlow period hPeriod (-shift)
        (fixedThroatPT period hPeriod point) := by
  obtain ⟨representative, rfl⟩ :=
    mappingTorusMk_surjective (throatData period hPeriod) point
  change mappingTorusTimeReversal (throatData period hPeriod)
        (fixedEquatorMonodromy_symm period hPeriod)
        (quotientTimeTranslation (throatData period hPeriod) shift
          (mappingTorusMk (throatData period hPeriod) representative)) =
      quotientTimeTranslation (throatData period hPeriod) (-shift)
        (mappingTorusTimeReversal (throatData period hPeriod)
          (fixedEquatorMonodromy_symm period hPeriod)
          (mappingTorusMk (throatData period hPeriod) representative))
  rw [quotientTimeTranslation_mk, mappingTorusTimeReversal_mk,
    mappingTorusTimeReversal_mk, quotientTimeTranslation_mk]
  apply congrArg (mappingTorusMk (throatData period hPeriod))
  apply MappingTorusCover.ext
  · rfl
  · simp [coverTimeTranslation, timeReverseCover]
    ring

/-- The throat inclusion intertwines the intrinsic and ambient time flows. -/
theorem fixedThroatQuotientInclusion_timeFlow (shift : Real)
    (point : EffectiveThroat period hPeriod) :
    fixedThroatQuotientInclusion period hPeriod
        (throatTimeFlow period hPeriod shift point) =
      effectiveTimeFlow period hPeriod shift
        (fixedThroatQuotientInclusion period hPeriod point) := by
  obtain ⟨representative, rfl⟩ :=
    mappingTorusMk_surjective (throatData period hPeriod) point
  rw [throatTimeFlow_mk, fixedThroatQuotientInclusion_mk,
    fixedThroatQuotientInclusion_mk, effectiveTimeFlow_mk]
  rfl

/-- Each time slice is a diagonal spacetime/throat diffeomorphism preserving
the actual embedded throat. -/
def diagonalTimeFlowDiffeomorphism (shift : Real) :
    DiagonalDiffeomorphism period hPeriod where
  spacetime := effectiveTimeFlowDiffeomorph period hPeriod shift
  throat := throatTimeFlowDiffeomorph period hPeriod shift
  preservesThroat := fixedThroatQuotientInclusion_timeFlow period hPeriod shift

universe u

variable (Fiber : Type u) [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]

/-- Pullback time action on smooth spacetime coefficient fields. -/
def smoothSpacetimeTimeAction (shift : Real)
    (field : SmoothQuotientField period hPeriod Fiber) :
    SmoothQuotientField period hPeriod Fiber :=
  pullbackSmoothField period hPeriod Fiber
    (effectiveTimeFlowDiffeomorph period hPeriod shift) field

@[simp]
theorem smoothSpacetimeTimeAction_apply (shift : Real)
    (field : SmoothQuotientField period hPeriod Fiber)
    (point : EffectiveQuotient period hPeriod) :
    smoothSpacetimeTimeAction period hPeriod Fiber shift field point =
      field (effectiveTimeFlow period hPeriod shift point) :=
  rfl

@[simp]
theorem smoothSpacetimeTimeAction_zero
    (field : SmoothQuotientField period hPeriod Fiber) :
    smoothSpacetimeTimeAction period hPeriod Fiber 0 field = field := by
  apply SmoothQuotientField.ext period hPeriod Fiber
  intro point
  rw [smoothSpacetimeTimeAction_apply, effectiveTimeFlow_zero]

theorem smoothSpacetimeTimeAction_add (first second : Real)
    (field : SmoothQuotientField period hPeriod Fiber) :
    smoothSpacetimeTimeAction period hPeriod Fiber (first + second) field =
      smoothSpacetimeTimeAction period hPeriod Fiber second
        (smoothSpacetimeTimeAction period hPeriod Fiber first field) := by
  apply SmoothQuotientField.ext period hPeriod Fiber
  intro point
  simp only [smoothSpacetimeTimeAction_apply]
  rw [effectiveTimeFlow_add]

@[simp]
theorem smoothSpacetimeTimeAction_neg (shift : Real)
    (field : SmoothQuotientField period hPeriod Fiber) :
    smoothSpacetimeTimeAction period hPeriod Fiber (-shift)
        (smoothSpacetimeTimeAction period hPeriod Fiber shift field) = field := by
  apply SmoothQuotientField.ext period hPeriod Fiber
  intro point
  simp only [smoothSpacetimeTimeAction_apply]
  rw [← effectiveTimeFlow_add]
  simp

/-- Spacetime PT conjugates coefficient pullback to opposite time. -/
theorem ptPullback_time_conjugation (shift : Real)
    (field : SmoothQuotientField period hPeriod Fiber) :
    ptPullback period hPeriod Fiber
        (smoothSpacetimeTimeAction period hPeriod Fiber shift field) =
      smoothSpacetimeTimeAction period hPeriod Fiber (-shift)
        (ptPullback period hPeriod Fiber field) := by
  apply SmoothQuotientField.ext period hPeriod Fiber
  intro point
  simp only [ptPullback_apply, smoothSpacetimeTimeAction_apply]
  simpa only [neg_neg] using congrArg field.toFun
    (reflectedSpherePT_effectiveTimeFlow period hPeriod (-shift) point).symm

/-- Pullback time action on smooth throat coefficient fields. -/
def smoothThroatTimeAction (shift : Real)
    (field : SmoothThroatField period hPeriod Fiber) :
    SmoothThroatField period hPeriod Fiber :=
  pullbackSmoothThroatField period hPeriod Fiber
    (throatTimeFlowDiffeomorph period hPeriod shift) field

@[simp]
theorem smoothThroatTimeAction_apply (shift : Real)
    (field : SmoothThroatField period hPeriod Fiber)
    (point : EffectiveThroat period hPeriod) :
    smoothThroatTimeAction period hPeriod Fiber shift field point =
      field (throatTimeFlow period hPeriod shift point) :=
  rfl

@[simp]
theorem smoothThroatTimeAction_zero
    (field : SmoothThroatField period hPeriod Fiber) :
    smoothThroatTimeAction period hPeriod Fiber 0 field = field := by
  apply SmoothThroatField.ext period hPeriod Fiber
  intro point
  simp

theorem smoothThroatTimeAction_add (first second : Real)
    (field : SmoothThroatField period hPeriod Fiber) :
    smoothThroatTimeAction period hPeriod Fiber (first + second) field =
      smoothThroatTimeAction period hPeriod Fiber second
        (smoothThroatTimeAction period hPeriod Fiber first field) := by
  apply SmoothThroatField.ext period hPeriod Fiber
  intro point
  simp only [smoothThroatTimeAction_apply]
  rw [throatTimeFlow_add]

@[simp]
theorem smoothThroatTimeAction_neg (shift : Real)
    (field : SmoothThroatField period hPeriod Fiber) :
    smoothThroatTimeAction period hPeriod Fiber (-shift)
        (smoothThroatTimeAction period hPeriod Fiber shift field) = field := by
  apply SmoothThroatField.ext period hPeriod Fiber
  intro point
  simp only [smoothThroatTimeAction_apply]
  rw [← throatTimeFlow_add]
  simp

/-- Throat PT conjugates coefficient pullback to opposite time. -/
theorem throatPTPullback_time_conjugation (shift : Real)
    (field : SmoothThroatField period hPeriod Fiber) :
    throatPTPullback period hPeriod Fiber
        (smoothThroatTimeAction period hPeriod Fiber shift field) =
      smoothThroatTimeAction period hPeriod Fiber (-shift)
        (throatPTPullback period hPeriod Fiber field) := by
  apply SmoothThroatField.ext period hPeriod Fiber
  intro point
  simp only [throatPTPullback_apply, smoothThroatTimeAction_apply]
  simpa only [neg_neg] using congrArg field.toFun
    (fixedThroatPT_throatTimeFlow period hPeriod (-shift) point).symm

/-- Pullback of the complete current independent field package by one
diagonal time slice. -/
def independentTimeAction (shift : Real)
    (fields : IndependentFields period hPeriod) :
    IndependentFields period hPeriod :=
  pullbackIndependentFields period hPeriod
    (diagonalTimeFlowDiffeomorphism period hPeriod shift) fields

@[simp]
theorem independentTimeAction_zero
    (fields : IndependentFields period hPeriod) :
    independentTimeAction period hPeriod 0 fields = fields := by
  apply IndependentFields.ext
  · apply SmoothPositiveDiagonalMetricPair.ext <;>
      exact smoothSpacetimeTimeAction_zero period hPeriod _ _
  · apply Prod.ext <;>
      exact smoothSpacetimeTimeAction_zero period hPeriod _ _
  · apply Prod.ext <;>
      exact smoothSpacetimeTimeAction_zero period hPeriod _ _
  · apply Prod.ext <;>
      exact smoothSpacetimeTimeAction_zero period hPeriod _ _
  · apply Prod.ext <;>
      exact smoothSpacetimeTimeAction_zero period hPeriod _ _
  · exact smoothThroatTimeAction_zero period hPeriod _ _
  · exact smoothThroatTimeAction_zero period hPeriod _ _
  · exact smoothThroatTimeAction_zero period hPeriod _ _

/-- Contravariant real group law on the complete independent package. -/
theorem independentTimeAction_add (first second : Real)
    (fields : IndependentFields period hPeriod) :
    independentTimeAction period hPeriod (first + second) fields =
      independentTimeAction period hPeriod second
        (independentTimeAction period hPeriod first fields) := by
  apply IndependentFields.ext
  · apply SmoothPositiveDiagonalMetricPair.ext <;>
      exact smoothSpacetimeTimeAction_add period hPeriod _ first second _
  · apply Prod.ext <;>
      exact smoothSpacetimeTimeAction_add period hPeriod _ first second _
  · apply Prod.ext <;>
      exact smoothSpacetimeTimeAction_add period hPeriod _ first second _
  · apply Prod.ext <;>
      exact smoothSpacetimeTimeAction_add period hPeriod _ first second _
  · apply Prod.ext <;>
      exact smoothSpacetimeTimeAction_add period hPeriod _ first second _
  · exact smoothThroatTimeAction_add period hPeriod _ first second _
  · exact smoothThroatTimeAction_add period hPeriod _ first second _
  · exact smoothThroatTimeAction_add period hPeriod _ first second _

@[simp]
theorem independentTimeAction_neg (shift : Real)
    (fields : IndependentFields period hPeriod) :
    independentTimeAction period hPeriod (-shift)
        (independentTimeAction period hPeriod shift fields) = fields := by
  apply IndependentFields.ext
  · apply SmoothPositiveDiagonalMetricPair.ext <;>
      exact smoothSpacetimeTimeAction_neg period hPeriod _ shift _
  · apply Prod.ext <;>
      exact smoothSpacetimeTimeAction_neg period hPeriod _ shift _
  · apply Prod.ext <;>
      exact smoothSpacetimeTimeAction_neg period hPeriod _ shift _
  · apply Prod.ext <;>
      exact smoothSpacetimeTimeAction_neg period hPeriod _ shift _
  · apply Prod.ext <;>
      exact smoothSpacetimeTimeAction_neg period hPeriod _ shift _
  · exact smoothThroatTimeAction_neg period hPeriod _ shift _
  · exact smoothThroatTimeAction_neg period hPeriod _ shift _
  · exact smoothThroatTimeAction_neg period hPeriod _ shift _

/-- Full PT/exchange conjugates the complete field action to opposite time. -/
theorem independentExchange_time_conjugation (shift : Real)
    (fields : IndependentFields period hPeriod) :
    independentExchange period hPeriod
        (independentTimeAction period hPeriod shift fields) =
      independentTimeAction period hPeriod (-shift)
        (independentExchange period hPeriod fields) := by
  apply IndependentFields.ext
  · apply SmoothPositiveDiagonalMetricPair.ext <;>
      exact ptPullback_time_conjugation period hPeriod _ shift _
  · apply Prod.ext <;>
      exact ptPullback_time_conjugation period hPeriod _ shift _
  · apply Prod.ext <;>
      exact ptPullback_time_conjugation period hPeriod _ shift _
  · apply Prod.ext <;>
      exact ptPullback_time_conjugation period hPeriod _ shift _
  · apply Prod.ext <;>
      exact ptPullback_time_conjugation period hPeriod _ shift _
  · exact throatPTPullback_time_conjugation period hPeriod _ shift _
  · exact throatPTPullback_time_conjugation period hPeriod _ shift _
  · exact throatPTPullback_time_conjugation period hPeriod _ shift _

/-- The time action commutes with construction of the induced plus metric. -/
theorem inducedPlusMetric_timeAction (shift : Real)
    (fields : IndependentFields period hPeriod) :
    (induce period hPeriod
      (independentTimeAction period hPeriod shift fields)).plusMetric =
      smoothSpacetimeTimeAction period hPeriod _ shift
        (induce period hPeriod fields).plusMetric :=
  inducedPlusMetric_pullback period hPeriod
    (diagonalTimeFlowDiffeomorphism period hPeriod shift) fields

theorem inducedMinusMetric_timeAction (shift : Real)
    (fields : IndependentFields period hPeriod) :
    (induce period hPeriod
      (independentTimeAction period hPeriod shift fields)).minusMetric =
      smoothSpacetimeTimeAction period hPeriod _ shift
        (induce period hPeriod fields).minusMetric :=
  inducedMinusMetric_pullback period hPeriod
    (diagonalTimeFlowDiffeomorphism period hPeriod shift) fields

theorem inducedPrincipalRoot_timeAction (shift : Real)
    (fields : IndependentFields period hPeriod) :
    (induce period hPeriod
      (independentTimeAction period hPeriod shift fields)).principalRoot =
      smoothSpacetimeTimeAction period hPeriod _ shift
        (induce period hPeriod fields).principalRoot :=
  inducedPrincipalRoot_pullback period hPeriod
    (diagonalTimeFlowDiffeomorphism period hPeriod shift) fields

theorem inducedPlusMatterTrace_timeAction (shift : Real)
    (fields : IndependentFields period hPeriod) :
    (induce period hPeriod
        (independentTimeAction period hPeriod shift fields)).plusMatterTrace =
      smoothThroatTimeAction period hPeriod _ shift
        (induce period hPeriod fields).plusMatterTrace :=
  inducedPlusMatterTrace_pullback period hPeriod
    (diagonalTimeFlowDiffeomorphism period hPeriod shift) fields

theorem inducedMinusMatterTrace_timeAction (shift : Real)
    (fields : IndependentFields period hPeriod) :
    (induce period hPeriod
        (independentTimeAction period hPeriod shift fields)).minusMatterTrace =
      smoothThroatTimeAction period hPeriod _ shift
        (induce period hPeriod fields).minusMatterTrace :=
  inducedMinusMatterTrace_pullback period hPeriod
    (diagonalTimeFlowDiffeomorphism period hPeriod shift) fields

/-- Packaged complete contravariant real action on all currently installed
independent fields. -/
structure CompleteIndependentFieldTimeAction where
  action : Real → IndependentFields period hPeriod →
    IndependentFields period hPeriod
  action_zero : ∀ fields, action 0 fields = fields
  action_add : ∀ first second fields,
    action (first + second) fields = action second (action first fields)
  action_neg : ∀ shift fields, action (-shift) (action shift fields) = fields
  pt_conjugation : ∀ shift fields,
    independentExchange period hPeriod (action shift fields) =
      action (-shift) (independentExchange period hPeriod fields)

def effectiveCompleteIndependentFieldTimeAction :
    CompleteIndependentFieldTimeAction period hPeriod where
  action := independentTimeAction period hPeriod
  action_zero := independentTimeAction_zero period hPeriod
  action_add := independentTimeAction_add period hPeriod
  action_neg := independentTimeAction_neg period hPeriod
  pt_conjugation := independentExchange_time_conjugation period hPeriod

theorem complete_independent_field_time_action4D_closed :
    Nonempty (CompleteIndependentFieldTimeAction period hPeriod) :=
  ⟨effectiveCompleteIndependentFieldTimeAction period hPeriod⟩

end

end P0EFTJanusMappingTorusCompleteIndependentFieldTimeAction4D
end JanusFormal
