import Mathlib.Analysis.Calculus.ContDiff.Deriv
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPConcreteFullActionFrechetBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCommonMatterActionVariation4D

/-!
# Concrete linewise C2 closure criterion for the matter block

`IndependentMatterMetricActionContract` supplies pair integrability only at
the base configuration.  It does not control differentiation under the
integral, or Hessian continuity, at every point of the simultaneous
metric--matter line.  Consequently it cannot by itself imply global `C²`.

This file records the exact non-circular closure criterion.  Its first
derivative is the existing integrated metric--matter variation.  Its second
derivative is the sum of the existing matter--matter, two mixed, and pure
metric Hessian slots.  Once both derivative identities hold pointwise on the
line, `C²` is equivalent to continuity of that concrete Hessian curve.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPConcreteMatterLineC2Closure4D

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusScalarDiffeomorphismNoetherOperator4D
open P0EFTJanusMappingTorusInducedFieldVariation4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusGlobalMatterMultipletActualEulerHessian4D
open P0EFTJanusCommonMatterActionVariation4D
open P0EFTJanusIndependentMatterMetricActionData4D
open P0EFTJanusMappingTorusIndependentMetricMatterIntegratedVariation4D
open P0EFTJanusMappingTorusIndependentMetricMatterIntegratedMixedHessian4D
open P0EFTJanusMappingTorusIndependentMetricMatterIntegratedMetricHessian4D
open P0EFTJanusRobinExtendedCompleteVariationReducedFredholm4D
open P0EFTJanusMappingTorusD8NonabelianGhostSmoothSpacetimeBVMaster4D
open P0EFTJanusMappingTorusIntrinsicEinsteinHilbertAction4D
open P0EFTJanusMappingTorusCandidateACoupledEinsteinMaxwellFiniteBVAction4D
open P0EFTJanusMappingTorusCandidateACoupledEinsteinMaxwellFullMetricFiniteBVAction4D
open P0EFTJanusProgramPConcreteFullActionFrechetBridge4D
open P0EFTJanusReciprocalBimetricPotential

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

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

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance effectiveThroatMeasurableSpace :
    MeasurableSpace (EffectiveThroat period hPeriod) := borel _

local instance effectiveThroatBorelSpace :
    BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

/-- Configuration reached at a parameter of the simultaneous matter line. -/
def concreteMatterLineFields
    (fields : IndependentFields period hPeriod)
    (direction : ProgramPRobinCompleteVariation4D period hPeriod)
    (parameter : Real) : IndependentFields period hPeriod :=
  independentFieldCurve period hPeriod fields
    direction.complete.independent parameter

/-- The genuine matter action used by the matter slot of the full line. -/
def concreteMatterLineAction
    (measure : Measure (EffectiveQuotient period hPeriod))
    (massSquared : MatterComponentIndex → Real)
    (fields : IndependentFields period hPeriod)
    (direction : ProgramPRobinCompleteVariation4D period hPeriod)
    (parameter : Real) : Real :=
  programPMetricMatterActionCurve period hPeriod measure massSquared fields
    direction parameter

/-- Existing integrated first variation, based at every point of the line. -/
def concreteMatterLineFirstVariation
    (measure : Measure (EffectiveQuotient period hPeriod))
    (massSquared : MatterComponentIndex → Real)
    (fields : IndependentFields period hPeriod)
    (direction : ProgramPRobinCompleteVariation4D period hPeriod)
    (parameter : Real) : Real :=
  integratedIndependentMetricMatterFirstVariation period hPeriod measure
    massSquared
    (concreteMatterLineFields period hPeriod fields direction parameter)
    direction

/-- Existing full scalar-matter Hessian on the line: matter--matter, both
mixed insertions, and metric--metric. -/
def concreteMatterLineHessian
    (measure : Measure (EffectiveQuotient period hPeriod))
    (massSquared : MatterComponentIndex → Real)
    (fields : IndependentFields period hPeriod)
    (direction : ProgramPRobinCompleteVariation4D period hPeriod)
    (lineContract :
      ∀ parameter : Real,
        IndependentMatterMetricActionContract period hPeriod
          (concreteMatterLineFields period hPeriod fields direction parameter)
          measure)
    (parameter : Real) : Real :=
  let variedFields :=
    concreteMatterLineFields period hPeriod fields direction parameter
  let matterDirection :=
    direction.complete.independent.matter
  let metricDirection :=
    direction.complete.independent.metrics
  globalMatterMultipletHessian period hPeriod
      (independentMatterMetricActionData period hPeriod variedFields measure
        (lineContract parameter))
      (matterVariationComponentFamily period hPeriod matterDirection)
      (matterVariationComponentFamily period hPeriod matterDirection) +
    2 * integratedIndependentMetricMatterMixedVariation period hPeriod measure
      massSquared variedFields metricDirection matterDirection +
    integratedIndependentMatterMetricHessian period hPeriod measure massSquared
      variedFields metricDirection metricDirection

/-- Non-circular analytic data still missing from the arbitrary base matter
contract.  The mass equality ensures that the parameterwise action data
describe the same action, not a replacement action. -/
structure ConcreteMatterLineC2Criterion
    (measure : Measure (EffectiveQuotient period hPeriod))
    (massSquared : MatterComponentIndex → Real)
    (fields : IndependentFields period hPeriod)
    (direction : ProgramPRobinCompleteVariation4D period hPeriod) where
  lineContract :
    ∀ parameter : Real,
      IndependentMatterMetricActionContract period hPeriod
        (concreteMatterLineFields period hPeriod fields direction parameter)
        measure
  lineContract_massSquared :
    ∀ parameter,
      (lineContract parameter).massSquared = massSquared
  action_hasDerivAt :
    ∀ parameter,
      HasDerivAt
        (concreteMatterLineAction period hPeriod measure massSquared fields
          direction)
        (concreteMatterLineFirstVariation period hPeriod measure massSquared
          fields direction parameter)
        parameter
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

/-- With the two genuine derivative identities fixed, continuity of the
concrete Hessian is exactly the remaining condition for linewise `C²`. -/
theorem concreteMatterLine_contDiff_two_iff_hessian_continuous
    (measure : Measure (EffectiveQuotient period hPeriod))
    (massSquared : MatterComponentIndex → Real)
    (fields : IndependentFields period hPeriod)
    (direction : ProgramPRobinCompleteVariation4D period hPeriod)
    (lineContract :
      ∀ parameter : Real,
        IndependentMatterMetricActionContract period hPeriod
          (concreteMatterLineFields period hPeriod fields direction parameter)
          measure)
    (hAction :
      ∀ parameter,
        HasDerivAt
          (concreteMatterLineAction period hPeriod measure massSquared fields
            direction)
          (concreteMatterLineFirstVariation period hPeriod measure massSquared
            fields direction parameter)
          parameter)
    (hFirstVariation :
      ∀ parameter,
        HasDerivAt
          (concreteMatterLineFirstVariation period hPeriod measure massSquared
            fields direction)
          (concreteMatterLineHessian period hPeriod measure massSquared fields
            direction lineContract parameter)
          parameter) :
    ContDiff Real 2
        (concreteMatterLineAction period hPeriod measure massSquared fields
          direction) ↔
      Continuous
        (concreteMatterLineHessian period hPeriod measure massSquared fields
          direction lineContract) := by
  let action :=
    concreteMatterLineAction period hPeriod measure massSquared fields direction
  let firstVariation :=
    concreteMatterLineFirstVariation period hPeriod measure massSquared fields
      direction
  let hessian :=
    concreteMatterLineHessian period hPeriod measure massSquared fields direction
      lineContract
  have hActionDeriv : deriv action = firstVariation := by
    funext parameter
    exact (hAction parameter).deriv
  have hFirstVariationDeriv : deriv firstVariation = hessian := by
    funext parameter
    exact (hFirstVariation parameter).deriv
  constructor
  · intro hC2
    have hFirstVariationC1 : ContDiff Real 1 firstVariation := by
      have hDerivC1 : ContDiff Real 1 (deriv action) := by
        exact hC2.deriv'
      simpa only [hActionDeriv] using hDerivC1
    have hContinuousDeriv : Continuous (deriv firstVariation) :=
      hFirstVariationC1.continuous_deriv_one
    simpa only [hFirstVariationDeriv] using hContinuousDeriv
  · intro hHessian
    have hFirstVariationDifferentiable :
        Differentiable Real firstVariation :=
      fun parameter => (hFirstVariation parameter).differentiableAt
    have hFirstVariationC1 : ContDiff Real 1 firstVariation := by
      rw [contDiff_one_iff_deriv]
      refine ⟨hFirstVariationDifferentiable, ?_⟩
      simpa only [hFirstVariationDeriv] using hHessian
    have hActionDifferentiable : Differentiable Real action :=
      fun parameter => (hAction parameter).differentiableAt
    have hActionC2 : ContDiff Real (1 + 1) action := by
      rw [contDiff_succ_iff_deriv]
      refine ⟨hActionDifferentiable, ?_, ?_⟩
      · simp
      · simpa only [hActionDeriv] using hFirstVariationC1
    (convert hActionC2 using 1; norm_num)

theorem concreteMatterLine_contDiff_two
    (measure : Measure (EffectiveQuotient period hPeriod))
    (massSquared : MatterComponentIndex → Real)
    (fields : IndependentFields period hPeriod)
    (direction : ProgramPRobinCompleteVariation4D period hPeriod)
    (criterion : ConcreteMatterLineC2Criterion period hPeriod measure
      massSquared fields direction) :
    ContDiff Real 2
      (concreteMatterLineAction period hPeriod measure massSquared fields
        direction) := by
  exact
    (concreteMatterLine_contDiff_two_iff_hessian_continuous period hPeriod
      measure massSquared fields direction criterion.lineContract
      criterion.action_hasDerivAt criterion.firstVariation_hasDerivAt).2
      criterion.hessian_continuous

/-- Closure of exactly the `matter` field of
`FullMetricLineMissingC2Slots`; no other missing slot is asserted. -/
theorem fullMetricFiniteBVLineBlocks_matter_contDiff_two
    (candidateMeasure : Measure (EffectiveQuotient period hPeriod))
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (fields : IndependentFields period hPeriod)
    (matterContract : IndependentMatterMetricActionContract period hPeriod
      fields candidateMeasure)
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (junction : SmoothThroatField period hPeriod Real)
    (bvField : SmoothFiniteMetricBVSpacetimeField period hPeriod)
    (couplings : EinsteinHilbertCouplings)
    (completion : CandidateAEinsteinMaxwellCompletion period hPeriod fields)
    (direction :
      CandidateAEinsteinMaxwellFullMetricFiniteBVVariation period hPeriod
        fields completion)
    (criterion : ConcreteMatterLineC2Criterion period hPeriod candidateMeasure
      matterContract.massSquared fields direction.base.physical) :
    ContDiff Real 2
      (fullMetricFiniteBVLineBlocks period hPeriod candidateMeasure
        interactionScale coefficients fields matterContract kPlus kMinus
        bulkPlus bulkMinus robinMeasure frame llMeasure junction bvField
        couplings completion direction).matter := by
  change ContDiff Real 2
    (concreteMatterLineAction period hPeriod candidateMeasure
      matterContract.massSquared fields direction.base.physical)
  exact concreteMatterLine_contDiff_two period hPeriod candidateMeasure
    matterContract.massSquared fields direction.base.physical criterion

end
end P0EFTJanusProgramPConcreteMatterLineC2Closure4D
end JanusFormal
