import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPConcreteMatterLineC2Closure4D

/-!
# Realization data for the concrete matter-line C2 criterion

The existing dominated first-variation theorem is based at parameter zero.
This file first transports it to every point of the genuine exponential
metric--matter line.  It then isolates the exact second-order datum not
provided by the arbitrary base action contract.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPConcreteMatterLineC2CriterionRealization4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 600000

noncomputable section

open MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothDiagonalLorentzFields4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusScalarDiffeomorphismNoetherOperator4D
open P0EFTJanusMappingTorusCandidateAFunctionalVariation4D
open P0EFTJanusMappingTorusInducedFieldVariation4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarWeakJacobiRiesz4D
open P0EFTJanusGlobalMatterMultipletActualEulerHessian4D
open P0EFTJanusCommonMatterActionVariation4D
open P0EFTJanusIndependentMatterMetricActionData4D
open P0EFTJanusMappingTorusIndependentMetricMatterIntegratedVariation4D
open P0EFTJanusMappingTorusIndependentMetricMatterIntegratedMixedHessian4D
open P0EFTJanusMappingTorusIndependentMetricMatterIntegratedMetricHessian4D
open P0EFTJanusRobinExtendedCompleteVariationReducedFredholm4D
open P0EFTJanusProgramPConcreteMatterLineC2Closure4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

/-! ## Exact recentering of the common field line -/

theorem positiveScaleCurve_recenter
    (baseScale direction :
      SmoothQuotientField period hPeriod (Fin 4 → Real))
    (first second : Real) :
    positiveScaleCurve period hPeriod
        (positiveScaleCurve period hPeriod baseScale direction first)
        direction second =
      positiveScaleCurve period hPeriod baseScale direction (first + second) := by
  apply SmoothQuotientField.ext period hPeriod (Fin 4 → Real)
  intro point
  funext index
  simp only [positiveScaleCurve]
  rw [add_mul, Real.exp_add]
  ring

theorem metricCurve_recenter
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod)
    (variation : SmoothDiagonalMetricVariation period hPeriod)
    (first second : Real) :
    metricCurve period hPeriod
        (metricCurve period hPeriod metrics variation first)
        variation second =
      metricCurve period hPeriod metrics variation (first + second) := by
  have hPlus :
      plusScaleField period hPeriod
          (metricCurve period hPeriod metrics variation first) =
        positiveScaleCurve period hPeriod
          (plusScaleField period hPeriod metrics)
          variation.plusLogDirection first := by
    apply SmoothQuotientField.ext period hPeriod (Fin 4 → Real)
    intro point
    exact congrArg Prod.fst
      (scalePairField_metricCurve period hPeriod metrics variation first point)
  have hMinus :
      minusScaleField period hPeriod
          (metricCurve period hPeriod metrics variation first) =
        positiveScaleCurve period hPeriod
          (minusScaleField period hPeriod metrics)
          variation.minusLogDirection first := by
    apply SmoothQuotientField.ext period hPeriod (Fin 4 → Real)
    intro point
    exact congrArg Prod.snd
      (scalePairField_metricCurve period hPeriod metrics variation first point)
  apply SmoothPositiveDiagonalMetricPair.ext
  · change squaredMagnitudeField period hPeriod
        (positiveScaleCurve period hPeriod
          (plusScaleField period hPeriod
            (metricCurve period hPeriod metrics variation first))
          variation.plusLogDirection second) =
      squaredMagnitudeField period hPeriod
        (positiveScaleCurve period hPeriod
          (plusScaleField period hPeriod metrics)
          variation.plusLogDirection (first + second))
    rw [hPlus, positiveScaleCurve_recenter]
  · change squaredMagnitudeField period hPeriod
        (positiveScaleCurve period hPeriod
          (minusScaleField period hPeriod
            (metricCurve period hPeriod metrics variation first))
          variation.minusLogDirection second) =
      squaredMagnitudeField period hPeriod
        (positiveScaleCurve period hPeriod
          (minusScaleField period hPeriod metrics)
          variation.minusLogDirection (first + second))
    rw [hMinus, positiveScaleCurve_recenter]

theorem independentFieldCurve_recenter
    (fields : IndependentFields period hPeriod)
    (variation : IndependentFieldVariation period hPeriod)
    (first second : Real) :
    independentFieldCurve period hPeriod
        (independentFieldCurve period hPeriod fields variation first)
        variation second =
      independentFieldCurve period hPeriod fields variation (first + second) := by
  apply IndependentFields.ext
  · exact metricCurve_recenter period hPeriod fields.metrics variation.metrics
      first second
  · apply Prod.ext <;> simp only [independentFieldCurve, add_smul] <;> abel
  · apply Prod.ext <;> simp only [independentFieldCurve, add_smul] <;> abel
  · apply Prod.ext <;> simp only [independentFieldCurve, add_smul] <;> abel
  · apply Prod.ext <;> simp only [independentFieldCurve, add_smul] <;> abel
  · simp only [independentFieldCurve, add_smul]
    abel
  · simp only [independentFieldCurve, add_smul]
    abel
  · simp only [independentFieldCurve, add_smul]
    abel

theorem concreteMatterLineFields_recenter
    (fields : IndependentFields period hPeriod)
    (direction : ProgramPRobinCompleteVariation4D period hPeriod)
    (first second : Real) :
    concreteMatterLineFields period hPeriod
        (concreteMatterLineFields period hPeriod fields direction first)
        direction second =
      concreteMatterLineFields period hPeriod fields direction
        (first + second) := by
  exact independentFieldCurve_recenter period hPeriod fields
    direction.complete.independent first second

theorem concreteMatterLineAction_recenter
    (measure : Measure (EffectiveQuotient period hPeriod))
    (massSquared : MatterComponentIndex → Real)
    (fields : IndependentFields period hPeriod)
    (direction : ProgramPRobinCompleteVariation4D period hPeriod)
    (first second : Real) :
    concreteMatterLineAction period hPeriod measure massSquared
        (concreteMatterLineFields period hPeriod fields direction first)
        direction second =
      concreteMatterLineAction period hPeriod measure massSquared fields direction
        (first + second) := by
  unfold concreteMatterLineAction programPMetricMatterActionCurve
    concreteMatterLineFields
  rw [independentFieldCurve_recenter]

/-! ## Existing dominated first variation at every line parameter -/

theorem concreteMatterLineAction_hasDerivAt_of_parameterwise_domination
    (measure : Measure (EffectiveQuotient period hPeriod))
    (massSquared : MatterComponentIndex → Real)
    (fields : IndependentFields period hPeriod)
    (direction : ProgramPRobinCompleteVariation4D period hPeriod)
    (domination :
      ∀ parameter,
        DominatedIndependentMetricMatterVariationContract period hPeriod
          measure massSquared
          (concreteMatterLineFields period hPeriod fields direction parameter)
          direction) :
    ∀ parameter,
      HasDerivAt
        (concreteMatterLineAction period hPeriod measure massSquared fields
          direction)
        (concreteMatterLineFirstVariation period hPeriod measure massSquared
          fields direction parameter)
        parameter := by
  intro parameter
  let variedFields :=
    concreteMatterLineFields period hPeriod fields direction parameter
  have hZero :=
    programPMetricMatterActionCurve_hasDerivAt period hPeriod measure massSquared
      variedFields direction (domination parameter)
  have hShift : HasDerivAt (fun varied : Real => varied - parameter) 1 parameter :=
    (hasDerivAt_id parameter).sub_const parameter
  have hComposed := hZero.scomp_of_eq parameter hShift (by simp)
  have hEventually :
      concreteMatterLineAction period hPeriod measure massSquared fields
          direction =ᶠ[nhds parameter]
        (concreteMatterLineAction period hPeriod measure massSquared variedFields
          direction ∘ fun varied : Real => varied - parameter) := by
    filter_upwards with varied
    simp only [Function.comp_apply]
    rw [show variedFields =
      concreteMatterLineFields period hPeriod fields direction parameter by rfl]
    rw [concreteMatterLineAction_recenter]
    congr 1
    ring
  refine (hComposed.congr_of_eventuallyEq hEventually).congr_deriv ?_
  simp [variedFields, concreteMatterLineFirstVariation]

/-! ## Exact residual second-order field -/

/-- After parameterwise domination realizes the first derivative, these are
exactly the two fields still needed at second order.  Neither field assumes
`ContDiff` itself. -/
structure ConcreteMatterLineDiagonalSecondOrderData
    (measure : Measure (EffectiveQuotient period hPeriod))
    (massSquared : MatterComponentIndex → Real)
    (fields : IndependentFields period hPeriod)
    (direction : ProgramPRobinCompleteVariation4D period hPeriod)
    (lineContract :
      ∀ parameter,
        IndependentMatterMetricActionContract period hPeriod
          (concreteMatterLineFields period hPeriod fields direction parameter)
          measure) where
  firstVariation_hasDerivAt :
    ∀ parameter,
      HasDerivAt
        (concreteMatterLineFirstVariation period hPeriod measure massSquared
          fields direction)
        (concreteMatterLineHessian period hPeriod measure massSquared fields
          direction lineContract parameter)
        parameter
  hessian_continuous :
    Continuous
      (concreteMatterLineHessian period hPeriod measure massSquared fields
        direction lineContract)

/-- Sufficient analytic extension of one arbitrary base matter contract.
The old `action_hasDerivAt` field is absent: it is derived from
`actionDomination` by the existing differentiation-under-the-integral theorem. -/
structure ConcreteMatterLineC2RealizationData
    (measure : Measure (EffectiveQuotient period hPeriod))
    (fields : IndependentFields period hPeriod)
    (direction : ProgramPRobinCompleteVariation4D period hPeriod)
    (baseContract :
      IndependentMatterMetricActionContract period hPeriod fields measure) where
  lineContract :
    ∀ parameter,
      IndependentMatterMetricActionContract period hPeriod
        (concreteMatterLineFields period hPeriod fields direction parameter)
        measure
  lineContract_massSquared :
    ∀ parameter,
      (lineContract parameter).massSquared = baseContract.massSquared
  actionDomination :
    ∀ parameter,
      DominatedIndependentMetricMatterVariationContract period hPeriod measure
        baseContract.massSquared
        (concreteMatterLineFields period hPeriod fields direction parameter)
        direction
  diagonalSecondOrder :
    ConcreteMatterLineDiagonalSecondOrderData period hPeriod measure
      baseContract.massSquared fields direction lineContract

/-- Genuine construction of the former criterion: its first derivative comes
from the repository's dominated integral theorem at every recentered base. -/
def ConcreteMatterLineC2RealizationData.toCriterion
    (measure : Measure (EffectiveQuotient period hPeriod))
    (fields : IndependentFields period hPeriod)
    (direction : ProgramPRobinCompleteVariation4D period hPeriod)
    (baseContract :
      IndependentMatterMetricActionContract period hPeriod fields measure)
    (data : ConcreteMatterLineC2RealizationData period hPeriod measure fields
      direction baseContract) :
    ConcreteMatterLineC2Criterion period hPeriod measure
      baseContract.massSquared fields direction where
  lineContract := data.lineContract
  lineContract_massSquared := data.lineContract_massSquared
  action_hasDerivAt :=
    concreteMatterLineAction_hasDerivAt_of_parameterwise_domination period
      hPeriod measure baseContract.massSquared fields direction
      data.actionDomination
  firstVariation_hasDerivAt :=
    data.diagonalSecondOrder.firstVariation_hasDerivAt
  hessian_continuous := data.diagonalSecondOrder.hessian_continuous

/-- Relative to a chosen parameterwise contract and the existing dominated
first-variation API, existence of a criterion with that contract is equivalent
to the residual diagonal second-order datum.  This is the exact field
reduction, not an additional physical axiom. -/
theorem criterion_exists_with_lineContract_iff
    (measure : Measure (EffectiveQuotient period hPeriod))
    (massSquared : MatterComponentIndex → Real)
    (fields : IndependentFields period hPeriod)
    (direction : ProgramPRobinCompleteVariation4D period hPeriod)
    (lineContract :
      ∀ parameter,
        IndependentMatterMetricActionContract period hPeriod
          (concreteMatterLineFields period hPeriod fields direction parameter)
          measure)
    (hMass :
      ∀ parameter, (lineContract parameter).massSquared = massSquared)
    (domination :
      ∀ parameter,
        DominatedIndependentMetricMatterVariationContract period hPeriod
          measure massSquared
          (concreteMatterLineFields period hPeriod fields direction parameter)
          direction) :
    (∃ criterion : ConcreteMatterLineC2Criterion period hPeriod measure
        massSquared fields direction,
      criterion.lineContract = lineContract) ↔
      Nonempty
        (ConcreteMatterLineDiagonalSecondOrderData period hPeriod measure
          massSquared fields direction lineContract) := by
  constructor
  · rintro ⟨criterion, hContract⟩
    refine ⟨{
      firstVariation_hasDerivAt := ?_
      hessian_continuous := ?_ }⟩
    · simpa only [hContract] using criterion.firstVariation_hasDerivAt
    · simpa only [hContract] using criterion.hessian_continuous
  · rintro ⟨secondOrder⟩
    let criterion : ConcreteMatterLineC2Criterion period hPeriod measure
        massSquared fields direction :=
      { lineContract := lineContract
        lineContract_massSquared := hMass
        action_hasDerivAt :=
          concreteMatterLineAction_hasDerivAt_of_parameterwise_domination period
            hPeriod measure massSquared fields direction domination
        firstVariation_hasDerivAt :=
          secondOrder.firstVariation_hasDerivAt
        hessian_continuous := secondOrder.hessian_continuous }
    exact ⟨criterion, rfl⟩

/-- A criterion necessarily contains pair integrability for every translated
metric on the line.  The arbitrary base contract only stores the corresponding
statement at the original field, so any unconditional realizer must first
construct this parameterwise family. -/
theorem criterion_requires_parameterwise_pair_integrable
    (measure : Measure (EffectiveQuotient period hPeriod))
    (massSquared : MatterComponentIndex → Real)
    (fields : IndependentFields period hPeriod)
    (direction : ProgramPRobinCompleteVariation4D period hPeriod)
    (criterion : ConcreteMatterLineC2Criterion period hPeriod measure
      massSquared fields direction)
    (parameter : Real) (component : MatterComponentIndex)
    (first second : GlobalScalarTestSpace period hPeriod) :
    Integrable
      (globalHolonomicScalarJacobiDensity period hPeriod
        (massSquared component)
        (independentMatterMagnitude period hPeriod
          (concreteMatterLineFields period hPeriod fields direction parameter)
          component.1)
        first second)
      measure := by
  simpa only [criterion.lineContract_massSquared parameter] using
    (criterion.lineContract parameter).pair_integrable component first second

/-! ## What the existing second-variation contracts already realize -/

/-- The three restricted second derivatives already present in the repository.
They are recorded together to make precise that the remaining field is their
chain-rule assembly along the simultaneous diagonal line. -/
structure ConcreteMatterRestrictedSecondVariationWitness
    (measure : Measure (EffectiveQuotient period hPeriod))
    (massSquared : MatterComponentIndex → Real)
    (fields : IndependentFields period hPeriod)
    (metricDirection : SmoothDiagonalMetricVariation period hPeriod)
    (matterDirection : SmoothQuotientField period hPeriod MatterFiber ×
      SmoothQuotientField period hPeriod MatterFiber)
    (lineContract :
      IndependentMatterMetricActionContract period hPeriod fields measure) where
  matterMatter :
    HasDerivAt
      (fun parameter =>
        globalMatterMultipletEuler period hPeriod
          (independentMatterMetricActionData period hPeriod fields measure
            lineContract)
          (matterMultipletAffineCurve period hPeriod
            (independentMatterComponentFamily period hPeriod fields)
            (matterVariationComponentFamily period hPeriod matterDirection)
            parameter)
          (matterVariationComponentFamily period hPeriod matterDirection))
      (globalMatterMultipletHessian period hPeriod
        (independentMatterMetricActionData period hPeriod fields measure
          lineContract)
        (matterVariationComponentFamily period hPeriod matterDirection)
        (matterVariationComponentFamily period hPeriod matterDirection))
      0
  metricMatter :
    HasDerivAt
      (integratedIndependentMatterEulerCurve period hPeriod measure massSquared
        fields metricDirection matterDirection)
      (integratedIndependentMetricMatterMixedVariation period hPeriod measure
        massSquared fields metricDirection matterDirection)
      0
  metricMetric :
    HasDerivAt
      (integratedIndependentMatterMetricFirstVariationAlongSecond period hPeriod
        measure massSquared fields metricDirection metricDirection)
      (integratedIndependentMatterMetricHessian period hPeriod measure
        massSquared fields metricDirection metricDirection)
      0

/-- Construction of all three restricted witnesses from the existing mixed and
pure-metric domination contracts; matter--matter needs only the line action
contract already used by the scalar Hessian. -/
def restrictedSecondVariationWitness_of_existing_contracts
    (measure : Measure (EffectiveQuotient period hPeriod))
    (massSquared : MatterComponentIndex → Real)
    (fields : IndependentFields period hPeriod)
    (metricDirection : SmoothDiagonalMetricVariation period hPeriod)
    (matterDirection : SmoothQuotientField period hPeriod MatterFiber ×
      SmoothQuotientField period hPeriod MatterFiber)
    (lineContract :
      IndependentMatterMetricActionContract period hPeriod fields measure)
    (mixedContract :
      DominatedIndependentMetricMatterMixedVariationContract period hPeriod
        measure massSquared fields metricDirection matterDirection)
    (metricContract :
      DominatedIndependentMatterMetricSecondVariationContract period hPeriod
        measure massSquared fields metricDirection metricDirection) :
    ConcreteMatterRestrictedSecondVariationWitness period hPeriod measure
      massSquared fields metricDirection matterDirection lineContract where
  matterMatter :=
    globalMatterMultipletEuler_hasDerivAt period hPeriod
      (independentMatterMetricActionData period hPeriod fields measure
        lineContract)
      (independentMatterComponentFamily period hPeriod fields)
      (matterVariationComponentFamily period hPeriod matterDirection)
      (matterVariationComponentFamily period hPeriod matterDirection)
  metricMatter :=
    integratedIndependentMatterEulerCurve_hasDerivAt period hPeriod measure
      massSquared fields metricDirection matterDirection mixedContract
  metricMetric :=
    integratedIndependentMatterMetricFirstVariationAlongSecond_hasDerivAt
      period hPeriod measure massSquared fields metricDirection metricDirection
      metricContract

end
end P0EFTJanusProgramPConcreteMatterLineC2CriterionRealization4D
end JanusFormal
