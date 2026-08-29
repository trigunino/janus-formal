import Mathlib.MeasureTheory.Integral.Bochner.Set
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPConcreteMatterLineC2CriterionRealization4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusAutomaticScalarIntegrability4D

/-!
# Completion frontier for the concrete matter-line C2 criterion

The arbitrary matter contract controls one metric only.  This file gives an
explicit finite-measure completion: fixed-frame continuity constructs the
translated form contracts, while joint continuity and the pointwise diagonal
chain rule produce the required dominated integral derivatives.  No `ContDiff`
conclusion is assumed.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPConcreteMatterLineC2CriterionCompletion4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 600000

noncomputable section

open Filter MeasureTheory Set
open scoped Manifold ContDiff BigOperators Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothDiagonalLorentzFields4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusScalarDiffeomorphismNoetherOperator4D
open P0EFTJanusMappingTorusCandidateAFunctionalVariation4D
open P0EFTJanusMappingTorusInducedFieldVariation4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarAction4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarVariation4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarWeakJacobiRiesz4D
open P0EFTJanusGlobalMatterMultipletActualEulerHessian4D
open P0EFTJanusCommonMatterActionVariation4D
open P0EFTJanusIndependentMatterMetricActionData4D
open P0EFTJanusMappingTorusIndependentMetricMatterPointwiseVariation4D
open P0EFTJanusMappingTorusIndependentMetricMatterPointwiseMixedHessian4D
open P0EFTJanusMappingTorusIndependentMetricMatterPointwiseMetricHessian4D
open P0EFTJanusMappingTorusIndependentMetricMatterIntegratedVariation4D
open P0EFTJanusMappingTorusIndependentMetricMatterIntegratedMixedHessian4D
open P0EFTJanusMappingTorusIndependentMetricMatterIntegratedMetricHessian4D
open P0EFTJanusMappingTorusAutomaticScalarIntegrability4D
open P0EFTJanusRobinExtendedCompleteVariationReducedFredholm4D
open P0EFTJanusProgramPConcreteMatterLineC2Closure4D
open P0EFTJanusProgramPConcreteMatterLineC2CriterionRealization4D

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

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

/-! ## Exact missing regularity of the legacy fixed model frame -/

/-- Contract asserting continuous components in the four fixed model
directions used by the legacy holonomic action.  This need not follow from
intrinsic smoothness: fixed model vectors are not generally global continuous
tangent sections of a quotient atlas. -/
structure GlobalFixedFrameComponentContinuity : Type where
  component_continuous :
    ∀ (field : GlobalScalarTestSpace period hPeriod) (index : Fin 4),
      Continuous (fun point =>
        holonomicCovectorComponent period hPeriod field point index)

def fixedFrameRegularScalar
    (regularity : GlobalFixedFrameComponentContinuity period hPeriod)
    (field : GlobalScalarTestSpace period hPeriod) :
    FixedFrameRegularScalar period hPeriod where
  field := field
  component_continuous := regularity.component_continuous field

/-- For a finite measure, the explicit fixed-frame regularity constructs the
form-domain contract at every translated metric, with unchanged masses. -/
def translatedMatterActionContract
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (massSquared : MatterComponentIndex → Real)
    (fields : IndependentFields period hPeriod)
    (direction : ProgramPRobinCompleteVariation4D period hPeriod)
    (regularity : GlobalFixedFrameComponentContinuity period hPeriod)
    (parameter : Real) :
    IndependentMatterMetricActionContract period hPeriod
      (concreteMatterLineFields period hPeriod fields direction parameter)
      measure where
  massSquared := massSquared
  pair_integrable := by
    intro component first second
    exact
      (globalHolonomicScalarFirstVariationDensity_continuous period hPeriod
        (massSquared component)
        (independentMatterMagnitude period hPeriod
          (concreteMatterLineFields period hPeriod fields direction parameter)
          component.1)
        (independentMatterMagnitude_pos period hPeriod
          (concreteMatterLineFields period hPeriod fields direction parameter)
          component.1)
        (fixedFrameRegularScalar period hPeriod regularity first)
        (fixedFrameRegularScalar period hPeriod regularity second))
      |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

@[simp] theorem translatedMatterActionContract_massSquared
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (massSquared : MatterComponentIndex → Real)
    (fields : IndependentFields period hPeriod)
    (direction : ProgramPRobinCompleteVariation4D period hPeriod)
    (regularity : GlobalFixedFrameComponentContinuity period hPeriod)
    (parameter : Real) :
    (translatedMatterActionContract period hPeriod measure massSquared fields
      direction regularity parameter).massSquared = massSquared :=
  rfl

/-! ## Concrete pointwise diagonal chain -/

def matterLineComponentDensity
    (massSquared : MatterComponentIndex → Real)
    (fields : IndependentFields period hPeriod)
    (direction : ProgramPRobinCompleteVariation4D period hPeriod)
    (component : MatterComponentIndex)
    (input : Real × EffectiveQuotient period hPeriod) : Real :=
  programPMetricMatterDensityCurve period hPeriod (massSquared component)
    fields direction component input.2 input.1

def matterLineComponentFirstDensity
    (massSquared : MatterComponentIndex → Real)
    (fields : IndependentFields period hPeriod)
    (direction : ProgramPRobinCompleteVariation4D period hPeriod)
    (component : MatterComponentIndex)
    (input : Real × EffectiveQuotient period hPeriod) : Real :=
  independentMetricMatterFirstVariationDensity period hPeriod
    (massSquared component)
    (concreteMatterLineFields period hPeriod fields direction input.1)
    direction.complete.independent component input.2

def matterLineComponentMatterHessianDensity
    (massSquared : MatterComponentIndex → Real)
    (fields : IndependentFields period hPeriod)
    (direction : ProgramPRobinCompleteVariation4D period hPeriod)
    (component : MatterComponentIndex)
    (input : Real × EffectiveQuotient period hPeriod) : Real :=
  globalHolonomicScalarJacobiDensity period hPeriod (massSquared component)
    (independentMatterMagnitude period hPeriod
      (concreteMatterLineFields period hPeriod fields direction input.1)
      component.1)
    (matterVariationComponentFamily period hPeriod
      direction.complete.independent.matter component)
    (matterVariationComponentFamily period hPeriod
      direction.complete.independent.matter component)
    input.2

def matterLineComponentMixedHessianDensity
    (massSquared : MatterComponentIndex → Real)
    (fields : IndependentFields period hPeriod)
    (direction : ProgramPRobinCompleteVariation4D period hPeriod)
    (component : MatterComponentIndex)
    (input : Real × EffectiveQuotient period hPeriod) : Real :=
  independentMetricMatterMixedDensity period hPeriod (massSquared component)
    (concreteMatterLineFields period hPeriod fields direction input.1)
    direction.complete.independent.metrics
    direction.complete.independent.matter component input.2

def matterLineComponentMetricHessianDensity
    (massSquared : MatterComponentIndex → Real)
    (fields : IndependentFields period hPeriod)
    (direction : ProgramPRobinCompleteVariation4D period hPeriod)
    (component : MatterComponentIndex)
    (input : Real × EffectiveQuotient period hPeriod) : Real :=
  independentMatterMetricHessianDensity period hPeriod (massSquared component)
    (concreteMatterLineFields period hPeriod fields direction input.1)
    direction.complete.independent.metrics
    direction.complete.independent.metrics component input.2

def matterLineComponentSecondDensity
    (massSquared : MatterComponentIndex → Real)
    (fields : IndependentFields period hPeriod)
    (direction : ProgramPRobinCompleteVariation4D period hPeriod)
    (component : MatterComponentIndex)
    (input : Real × EffectiveQuotient period hPeriod) : Real :=
  matterLineComponentMatterHessianDensity period hPeriod massSquared fields
      direction component input +
    2 * matterLineComponentMixedHessianDensity period hPeriod massSquared fields
      direction component input +
    matterLineComponentMetricHessianDensity period hPeriod massSquared fields
      direction component input

theorem programPMetricMatterDensityCurve_recenter
    (massSquared : Real)
    (fields : IndependentFields period hPeriod)
    (direction : ProgramPRobinCompleteVariation4D period hPeriod)
    (component : MatterComponentIndex)
    (point : EffectiveQuotient period hPeriod)
    (first second : Real) :
    programPMetricMatterDensityCurve period hPeriod massSquared
        (concreteMatterLineFields period hPeriod fields direction first)
        direction component point second =
      programPMetricMatterDensityCurve period hPeriod massSquared fields
        direction component point (first + second) := by
  unfold programPMetricMatterDensityCurve concreteMatterLineFields
  rw [independentFieldCurve_recenter]

/-- The existing pointwise first-variation theorem, transported from zero to
an arbitrary parameter by exact recentering of the common field line. -/
theorem matterLineComponentDensity_hasDerivAt
    (massSquared : MatterComponentIndex → Real)
    (fields : IndependentFields period hPeriod)
    (direction : ProgramPRobinCompleteVariation4D period hPeriod)
    (component : MatterComponentIndex)
    (parameter : Real) (point : EffectiveQuotient period hPeriod) :
    HasDerivAt
      (fun varied =>
        matterLineComponentDensity period hPeriod massSquared fields direction
          component (varied, point))
      (matterLineComponentFirstDensity period hPeriod massSquared fields
        direction component (parameter, point))
      parameter := by
  let variedFields :=
    concreteMatterLineFields period hPeriod fields direction parameter
  have hZero :=
    programPMetricMatterDensityCurve_hasDerivAt period hPeriod
      (massSquared component) variedFields direction component point
  have hShift : HasDerivAt (fun varied : Real => varied - parameter) 1 parameter :=
    (hasDerivAt_id parameter).sub_const parameter
  have hComposed := hZero.scomp_of_eq parameter hShift (by simp)
  have hEventually :
      (fun varied =>
        matterLineComponentDensity period hPeriod massSquared fields direction
          component (varied, point)) =ᶠ[nhds parameter]
        (programPMetricMatterDensityCurve period hPeriod
          (massSquared component) variedFields direction component point ∘
            fun varied : Real => varied - parameter) := by
    filter_upwards with varied
    simp only [Function.comp_apply, matterLineComponentDensity]
    rw [show variedFields =
      concreteMatterLineFields period hPeriod fields direction parameter by rfl]
    rw [programPMetricMatterDensityCurve_recenter]
    congr 1
    ring
  refine (hComposed.congr_of_eventuallyEq hEventually).congr_deriv ?_
  simp [variedFields, matterLineComponentFirstDensity]

/-! ## Compact finite-measure domination generated from joint continuity -/

theorem hasDerivAt_integral_of_jointContinuous
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopologyEither X Real]
    (measure : Measure X) [IsFiniteMeasure measure]
    (density derivative : Real → X → Real)
    (hDensity : Continuous density.uncurry)
    (hDerivative : Continuous derivative.uncurry)
    (hPointwise : ∀ parameter point,
      HasDerivAt (fun varied => density varied point)
        (derivative parameter point) parameter)
    (parameter : Real) :
    HasDerivAt (fun varied => ∫ point, density varied point ∂measure)
      (∫ point, derivative parameter point ∂measure) parameter := by
  have hCompact : IsCompact
      (Set.Icc (parameter - 1) (parameter + 1) ×ˢ
        (Set.univ : Set X)) :=
    isCompact_Icc.prod isCompact_univ
  let hBounded := hCompact.bddAbove_image hDerivative.norm.continuousOn
  let bound : Real := Classical.choose hBounded
  have hBound := Classical.choose_spec hBounded
  have hDensityMeasurable : ∀ᶠ varied in 𝓝 parameter,
      AEStronglyMeasurable (density varied) measure :=
    Filter.Eventually.of_forall fun varied =>
      (hDensity.comp (continuous_const.prodMk continuous_id))
        |>.aestronglyMeasurable
  have hDensityIntegrable : Integrable (density parameter) measure :=
    (hDensity.comp (continuous_const.prodMk continuous_id))
      |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hDerivativeMeasurable :
      AEStronglyMeasurable (derivative parameter) measure :=
    (hDerivative.comp (continuous_const.prodMk continuous_id))
      |>.aestronglyMeasurable
  have hDerivativeBound : ∀ᵐ point ∂measure,
      ∀ varied ∈ Set.Icc (parameter - 1) (parameter + 1),
        ‖derivative varied point‖ ≤ bound := by
    filter_upwards with point
    intro varied hVaried
    exact hBound (Set.mem_image_of_mem _
      (Set.mk_mem_prod hVaried (Set.mem_univ point)))
  have hResult := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := density) (F' := derivative) (bound := fun _ : X => bound)
    (Icc_mem_nhds (sub_lt_self parameter zero_lt_one)
      (lt_add_of_pos_right parameter zero_lt_one))
    hDensityMeasurable hDensityIntegrable hDerivativeMeasurable
    hDerivativeBound (integrable_const bound)
    (Filter.Eventually.of_forall fun point varied _ => hPointwise varied point)
  exact hResult.2

/-! ## Explicit non-circular completion data -/

/-- Joint continuity of the five concrete integrands.  This is enough for all
finite-measure domination, translated integrability, and Hessian continuity;
it contains no derivative conclusion. -/
structure ConcreteMatterLineJointContinuityData
    (massSquared : MatterComponentIndex → Real)
    (fields : IndependentFields period hPeriod)
    (direction : ProgramPRobinCompleteVariation4D period hPeriod) where
  density_continuous :
    ∀ component,
      Continuous
        (matterLineComponentDensity period hPeriod massSquared fields direction
          component)
  firstDensity_continuous :
    ∀ component,
      Continuous
        (matterLineComponentFirstDensity period hPeriod massSquared fields
          direction component)
  matterHessianDensity_continuous :
    ∀ component,
      Continuous
        (matterLineComponentMatterHessianDensity period hPeriod massSquared
          fields direction component)
  mixedHessianDensity_continuous :
    ∀ component,
      Continuous
        (matterLineComponentMixedHessianDensity period hPeriod massSquared
          fields direction component)
  metricHessianDensity_continuous :
    ∀ component,
      Continuous
        (matterLineComponentMetricHessianDensity period hPeriod massSquared
          fields direction component)

/-- The only additional local datum is the explicit pointwise diagonal chain
rule.  No integrated differentiability or `ContDiff` conclusion occurs here. -/
structure ConcreteMatterLinePointwiseCompletionData
    (massSquared : MatterComponentIndex → Real)
    (fields : IndependentFields period hPeriod)
    (direction : ProgramPRobinCompleteVariation4D period hPeriod)
    extends ConcreteMatterLineJointContinuityData period hPeriod massSquared
      fields direction where
  firstDensity_hasDerivAt :
    ∀ component parameter point,
      HasDerivAt
        (fun varied =>
          matterLineComponentFirstDensity period hPeriod massSquared fields
            direction component (varied, point))
        (matterLineComponentSecondDensity period hPeriod massSquared fields
          direction component (parameter, point))
        parameter

theorem ConcreteMatterLineJointContinuityData.secondDensity_continuous
    (massSquared : MatterComponentIndex → Real)
    (fields : IndependentFields period hPeriod)
    (direction : ProgramPRobinCompleteVariation4D period hPeriod)
    (data : ConcreteMatterLineJointContinuityData period hPeriod massSquared
      fields direction)
    (component : MatterComponentIndex) :
    Continuous
      (matterLineComponentSecondDensity period hPeriod massSquared fields
        direction component) := by
  exact
    ((data.matterHessianDensity_continuous component).add
      (continuous_const.mul (data.mixedHessianDensity_continuous component))).add
      (data.metricHessianDensity_continuous component)

def integratedMatterLineSecondDensity
    (measure : Measure (EffectiveQuotient period hPeriod))
    (massSquared : MatterComponentIndex → Real)
    (fields : IndependentFields period hPeriod)
    (direction : ProgramPRobinCompleteVariation4D period hPeriod)
    (parameter : Real) : Real :=
  ∑ component : MatterComponentIndex,
    ∫ point, matterLineComponentSecondDensity period hPeriod massSquared fields
      direction component (parameter, point) ∂measure

theorem integral_matterLineComponentSecondDensity
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (massSquared : MatterComponentIndex → Real)
    (fields : IndependentFields period hPeriod)
    (direction : ProgramPRobinCompleteVariation4D period hPeriod)
    (data : ConcreteMatterLineJointContinuityData period hPeriod massSquared
      fields direction)
    (component : MatterComponentIndex)
    (parameter : Real) :
    (∫ point,
        matterLineComponentSecondDensity period hPeriod massSquared fields
          direction component (parameter, point) ∂measure) =
      (∫ point,
          matterLineComponentMatterHessianDensity period hPeriod massSquared
            fields direction component (parameter, point) ∂measure) +
        2 * (∫ point,
          matterLineComponentMixedHessianDensity period hPeriod massSquared
            fields direction component (parameter, point) ∂measure) +
        ∫ point,
          matterLineComponentMetricHessianDensity period hPeriod massSquared
            fields direction component (parameter, point) ∂measure := by
  have hMatter :
      Integrable
        (fun point =>
          matterLineComponentMatterHessianDensity period hPeriod massSquared
            fields direction component (parameter, point))
        measure :=
    ((data.matterHessianDensity_continuous component).comp
      (continuous_const.prodMk continuous_id))
      |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hMixed :
      Integrable
        (fun point =>
          matterLineComponentMixedHessianDensity period hPeriod massSquared
            fields direction component (parameter, point))
        measure :=
    ((data.mixedHessianDensity_continuous component).comp
      (continuous_const.prodMk continuous_id))
      |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hMetric :
      Integrable
        (fun point =>
          matterLineComponentMetricHessianDensity period hPeriod massSquared
            fields direction component (parameter, point))
        measure :=
    ((data.metricHessianDensity_continuous component).comp
      (continuous_const.prodMk continuous_id))
      |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  unfold matterLineComponentSecondDensity
  calc
    (∫ point,
        matterLineComponentMatterHessianDensity period hPeriod massSquared
              fields direction component (parameter, point) +
            2 * matterLineComponentMixedHessianDensity period hPeriod massSquared
              fields direction component (parameter, point) +
          matterLineComponentMetricHessianDensity period hPeriod massSquared
            fields direction component (parameter, point) ∂measure) =
        (∫ point,
            matterLineComponentMatterHessianDensity period hPeriod massSquared
                fields direction component (parameter, point) +
              2 * matterLineComponentMixedHessianDensity period hPeriod
                massSquared fields direction component (parameter, point)
            ∂measure) +
          ∫ point,
            matterLineComponentMetricHessianDensity period hPeriod massSquared
              fields direction component (parameter, point) ∂measure := by
      apply integral_add (hMatter.add (hMixed.const_mul 2)) hMetric
    _ =
        ((∫ point,
            matterLineComponentMatterHessianDensity period hPeriod massSquared
              fields direction component (parameter, point) ∂measure) +
          ∫ point,
            2 * matterLineComponentMixedHessianDensity period hPeriod
              massSquared fields direction component (parameter, point)
            ∂measure) +
          ∫ point,
            matterLineComponentMetricHessianDensity period hPeriod massSquared
              fields direction component (parameter, point) ∂measure := by
      congr 1
      apply integral_add hMatter (hMixed.const_mul 2)
    _ = _ := by
      rw [integral_const_mul]

theorem concreteMatterLineAction_hasDerivAt_of_jointContinuity
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (massSquared : MatterComponentIndex → Real)
    (fields : IndependentFields period hPeriod)
    (direction : ProgramPRobinCompleteVariation4D period hPeriod)
    (data : ConcreteMatterLineJointContinuityData period hPeriod massSquared
      fields direction)
    (parameter : Real) :
    HasDerivAt
      (concreteMatterLineAction period hPeriod measure massSquared fields
        direction)
      (concreteMatterLineFirstVariation period hPeriod measure massSquared
        fields direction parameter)
      parameter := by
  have hSum :
      HasDerivAt
        (fun varied =>
          ∑ component : MatterComponentIndex,
            ∫ point,
              matterLineComponentDensity period hPeriod massSquared fields
                direction component (varied, point) ∂measure)
        (∑ component : MatterComponentIndex,
          ∫ point,
            matterLineComponentFirstDensity period hPeriod massSquared fields
              direction component (parameter, point) ∂measure)
        parameter := by
    apply HasDerivAt.fun_sum
    intro component _
    exact
      hasDerivAt_integral_of_jointContinuous
        (measure := measure)
        (density := fun varied point =>
          matterLineComponentDensity period hPeriod massSquared fields direction
            component (varied, point))
        (derivative := fun varied point =>
          matterLineComponentFirstDensity period hPeriod massSquared fields
            direction component (varied, point))
        (by
          change Continuous
            (matterLineComponentDensity period hPeriod massSquared fields
              direction component)
          exact data.density_continuous component)
        (by
          change Continuous
            (matterLineComponentFirstDensity period hPeriod massSquared fields
              direction component)
          exact data.firstDensity_continuous component)
        (matterLineComponentDensity_hasDerivAt period hPeriod massSquared fields
          direction component)
        parameter
  convert hSum using 1 <;>
    rfl

theorem concreteMatterLineFirstVariation_hasDerivAt_secondDensity
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (massSquared : MatterComponentIndex → Real)
    (fields : IndependentFields period hPeriod)
    (direction : ProgramPRobinCompleteVariation4D period hPeriod)
    (data : ConcreteMatterLinePointwiseCompletionData period hPeriod massSquared
      fields direction)
    (parameter : Real) :
    HasDerivAt
      (concreteMatterLineFirstVariation period hPeriod measure massSquared fields
        direction)
      (integratedMatterLineSecondDensity period hPeriod measure massSquared
        fields direction parameter)
      parameter := by
  have hSum :
      HasDerivAt
        (fun varied =>
          ∑ component : MatterComponentIndex,
            ∫ point,
              matterLineComponentFirstDensity period hPeriod massSquared fields
                direction component (varied, point) ∂measure)
        (∑ component : MatterComponentIndex,
          ∫ point,
            matterLineComponentSecondDensity period hPeriod massSquared fields
              direction component (parameter, point) ∂measure)
        parameter := by
    apply HasDerivAt.fun_sum
    intro component _
    exact
      hasDerivAt_integral_of_jointContinuous
        (measure := measure)
        (density := fun varied point =>
          matterLineComponentFirstDensity period hPeriod massSquared fields
            direction component (varied, point))
        (derivative := fun varied point =>
          matterLineComponentSecondDensity period hPeriod massSquared fields
            direction component (varied, point))
        (by
          change Continuous
            (matterLineComponentFirstDensity period hPeriod massSquared fields
              direction component)
          exact data.firstDensity_continuous component)
        (by
          change Continuous
            (matterLineComponentSecondDensity period hPeriod massSquared fields
              direction component)
          exact
            ConcreteMatterLineJointContinuityData.secondDensity_continuous
              period hPeriod massSquared fields direction
                data.toConcreteMatterLineJointContinuityData component)
        (data.firstDensity_hasDerivAt component)
        parameter
  convert hSum using 1 <;>
    rfl

theorem integratedMatterLineSecondDensity_continuous
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (massSquared : MatterComponentIndex → Real)
    (fields : IndependentFields period hPeriod)
    (direction : ProgramPRobinCompleteVariation4D period hPeriod)
    (data : ConcreteMatterLineJointContinuityData period hPeriod massSquared
      fields direction) :
    Continuous
      (integratedMatterLineSecondDensity period hPeriod measure massSquared
        fields direction) := by
  unfold integratedMatterLineSecondDensity
  apply continuous_finsetSum
  intro component _
  simpa only [Measure.restrict_univ] using
    (continuous_parametric_integral_of_continuous
      (f := fun parameter point =>
        matterLineComponentSecondDensity period hPeriod massSquared fields
          direction component (parameter, point))
      (ConcreteMatterLineJointContinuityData.secondDensity_continuous
        period hPeriod massSquared fields direction data component)
      (s := (Set.univ : Set (EffectiveQuotient period hPeriod)))
      isCompact_univ)

theorem concreteMatterLineHessian_eq_integratedMatterLineSecondDensity
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (massSquared : MatterComponentIndex → Real)
    (fields : IndependentFields period hPeriod)
    (direction : ProgramPRobinCompleteVariation4D period hPeriod)
    (regularity : GlobalFixedFrameComponentContinuity period hPeriod)
    (data : ConcreteMatterLineJointContinuityData period hPeriod massSquared
      fields direction)
    (parameter : Real) :
    concreteMatterLineHessian period hPeriod measure massSquared fields direction
        (translatedMatterActionContract period hPeriod measure massSquared fields
          direction regularity) parameter =
      integratedMatterLineSecondDensity period hPeriod measure massSquared fields
        direction parameter := by
  unfold concreteMatterLineHessian integratedMatterLineSecondDensity
    globalMatterMultipletHessian
    integratedIndependentMetricMatterMixedVariation
    integratedIndependentMatterMetricHessian
  dsimp only
  rw [Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro component _
  change
    (∫ point,
        matterLineComponentMatterHessianDensity period hPeriod massSquared
          fields direction component (parameter, point) ∂measure) +
        2 * (∫ point,
          matterLineComponentMixedHessianDensity period hPeriod massSquared
            fields direction component (parameter, point) ∂measure) +
        ∫ point,
          matterLineComponentMetricHessianDensity period hPeriod massSquared
            fields direction component (parameter, point) ∂measure =
      ∫ point,
        matterLineComponentSecondDensity period hPeriod massSquared fields
          direction component (parameter, point) ∂measure
  exact
    (integral_matterLineComponentSecondDensity period hPeriod measure massSquared
      fields direction data component parameter).symm

/-- The explicit pointwise chain rule closes the canonical finite-measure
criterion.  The first derivative, the integration bounds, and Hessian
continuity are all derived from joint continuity. -/
def finiteMeasureConcreteMatterLineC2Criterion
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (massSquared : MatterComponentIndex → Real)
    (fields : IndependentFields period hPeriod)
    (direction : ProgramPRobinCompleteVariation4D period hPeriod)
    (regularity : GlobalFixedFrameComponentContinuity period hPeriod)
    (data : ConcreteMatterLinePointwiseCompletionData period hPeriod massSquared
      fields direction) :
    ConcreteMatterLineC2Criterion period hPeriod measure massSquared fields
      direction where
  lineContract :=
    translatedMatterActionContract period hPeriod measure massSquared fields
      direction regularity
  lineContract_massSquared := fun _ => rfl
  action_hasDerivAt :=
    concreteMatterLineAction_hasDerivAt_of_jointContinuity period hPeriod measure
      massSquared fields direction data.toConcreteMatterLineJointContinuityData
  firstVariation_hasDerivAt := by
    intro parameter
    exact
      (concreteMatterLineFirstVariation_hasDerivAt_secondDensity period hPeriod
        measure massSquared fields direction data parameter).congr_deriv
        (concreteMatterLineHessian_eq_integratedMatterLineSecondDensity period
          hPeriod measure massSquared fields direction regularity
          data.toConcreteMatterLineJointContinuityData parameter).symm
  hessian_continuous := by
    have hEquality :
        concreteMatterLineHessian period hPeriod measure massSquared fields
            direction
            (translatedMatterActionContract period hPeriod measure massSquared
              fields direction regularity) =
          integratedMatterLineSecondDensity period hPeriod measure massSquared
            fields direction := by
      funext parameter
      exact
        concreteMatterLineHessian_eq_integratedMatterLineSecondDensity period
          hPeriod measure massSquared fields direction regularity
          data.toConcreteMatterLineJointContinuityData parameter
    rw [hEquality]
    exact
      integratedMatterLineSecondDensity_continuous period hPeriod measure
        massSquared fields direction
        data.toConcreteMatterLineJointContinuityData

theorem concreteMatterLine_contDiff_two_of_pointwiseCompletion
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (massSquared : MatterComponentIndex → Real)
    (fields : IndependentFields period hPeriod)
    (direction : ProgramPRobinCompleteVariation4D period hPeriod)
    (regularity : GlobalFixedFrameComponentContinuity period hPeriod)
    (data : ConcreteMatterLinePointwiseCompletionData period hPeriod massSquared
      fields direction) :
    ContDiff Real 2
      (concreteMatterLineAction period hPeriod measure massSquared fields
        direction) :=
  concreteMatterLine_contDiff_two period hPeriod measure massSquared fields
    direction
    (finiteMeasureConcreteMatterLineC2Criterion period hPeriod measure
      massSquared fields direction regularity data)

/-- With finite measure, fixed-frame regularity, and the five joint
continuities fixed, existence of the canonical criterion is equivalent to one
explicit integrated diagonal chain rule.  Thus no other analytic field is
missing from the current construction. -/
theorem
    criterion_exists_with_translatedContract_iff_integratedDiagonalChain
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (massSquared : MatterComponentIndex → Real)
    (fields : IndependentFields period hPeriod)
    (direction : ProgramPRobinCompleteVariation4D period hPeriod)
    (regularity : GlobalFixedFrameComponentContinuity period hPeriod)
    (data : ConcreteMatterLineJointContinuityData period hPeriod massSquared
      fields direction) :
    (∃ criterion : ConcreteMatterLineC2Criterion period hPeriod measure
        massSquared fields direction,
      criterion.lineContract =
        translatedMatterActionContract period hPeriod measure massSquared fields
          direction regularity) ↔
      ∀ parameter,
        HasDerivAt
          (concreteMatterLineFirstVariation period hPeriod measure massSquared
            fields direction)
          (integratedMatterLineSecondDensity period hPeriod measure massSquared
            fields direction parameter)
          parameter := by
  constructor
  · rintro ⟨criterion, hContract⟩ parameter
    apply (criterion.firstVariation_hasDerivAt parameter).congr_deriv
    rw [hContract]
    exact
      concreteMatterLineHessian_eq_integratedMatterLineSecondDensity period
        hPeriod measure massSquared fields direction regularity data parameter
  · intro hDiagonal
    let criterion : ConcreteMatterLineC2Criterion period hPeriod measure
        massSquared fields direction :=
      { lineContract :=
          translatedMatterActionContract period hPeriod measure massSquared
            fields direction regularity
        lineContract_massSquared := fun _ => rfl
        action_hasDerivAt :=
          concreteMatterLineAction_hasDerivAt_of_jointContinuity period hPeriod
            measure massSquared fields direction data
        firstVariation_hasDerivAt := fun parameter =>
          (hDiagonal parameter).congr_deriv
            (concreteMatterLineHessian_eq_integratedMatterLineSecondDensity
              period hPeriod measure massSquared fields direction regularity data
              parameter).symm
        hessian_continuous := by
          have hEquality :
              concreteMatterLineHessian period hPeriod measure massSquared fields
                  direction
                  (translatedMatterActionContract period hPeriod measure
                    massSquared fields direction regularity) =
                integratedMatterLineSecondDensity period hPeriod measure
                  massSquared fields direction := by
            funext parameter
            exact
              concreteMatterLineHessian_eq_integratedMatterLineSecondDensity
                period hPeriod measure massSquared fields direction regularity
                data parameter
          rw [hEquality]
          exact
            integratedMatterLineSecondDensity_continuous period hPeriod measure
              massSquared fields direction data }
    exact ⟨criterion, rfl⟩

end
end P0EFTJanusProgramPConcreteMatterLineC2CriterionCompletion4D
end JanusFormal
