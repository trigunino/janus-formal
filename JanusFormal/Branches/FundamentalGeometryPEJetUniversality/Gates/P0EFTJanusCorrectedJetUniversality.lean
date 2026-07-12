import Mathlib
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusFiniteJetEquivariance
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusFiniteOrderUniformization
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusSmoothNotPolynomial

namespace JanusFormal
namespace P0EFTJanusCorrectedJetUniversality

set_option autoImplicit false

open P0EFTJanusFiniteJetEquivariance
open P0EFTJanusFiniteOrderUniformization
open P0EFTJanusSmoothNotPolynomial

universe u v w x

/-- Corrected local theorem package.  The geometric/analytic Peetre--Slovak
step supplies `presentation`; the algebraic theorem then supplies the unique
equivariant evaluator. -/
structure CorrectedLocalJetData
    (Symmetry : Type u)
    (Section : Type v)
    (Jet : Type w)
    (Target : Type x) where
  presentation :
    FiniteJetPresentation Symmetry Section Jet Target
  regularLocalSheafMorphism : Prop
  peetreSlovakReductionEstablished : Prop
  finiteJetEvaluatorSmooth : Prop

/-- Corrected local finite-jet universality theorem. -/
theorem corrected_local_jet_universality
    {Symmetry : Type u}
    {Section : Type v}
    {Jet : Type w}
    {Target : Type x}
    (data : CorrectedLocalJetData Symmetry Section Jet Target)
    (hNatural :
      IsNaturalOperator data.presentation.sectionAction
        data.presentation.targetAction
        data.presentation.operator) :
    ∃! evaluator : Jet → Target,
      (∀ sectionValue,
        data.presentation.operator sectionValue =
          evaluator (data.presentation.jet sectionValue)) /\
      IsEquivariant data.presentation.jetAction
        data.presentation.targetAction evaluator :=
  exists_unique_equivariant_evaluator
    data.presentation hNatural

/-- Trivial action used for scalar invariant functions. -/
def trivialAction
    (Symmetry : Type u)
    (Space : Type v) : ActionData Symmetry Space where
  act := fun _ value => value

/-- For a scalar/trivial target, equivariance is precisely invariance of the
evaluator under the jet action. -/
theorem scalar_equivariance_iff_invariance
    {Symmetry : Type u}
    {Jet : Type v}
    (jetAction : ActionData Symmetry Jet)
    (evaluator : Jet → ℝ) :
    IsEquivariant jetAction (trivialAction Symmetry ℝ) evaluator ↔
      ∀ symmetry jetValue,
        evaluator (jetAction.act symmetry jetValue) =
          evaluator jetValue := by
  rfl

/-- Naturality does not imply ellipticity: the zero operator is natural. -/
theorem zero_operator_is_natural
    (Symmetry : Type u) :
    IsNaturalOperator
      (trivialAction Symmetry ℝ)
      (trivialAction Symmetry ℝ)
      (fun _ : ℝ => 0) := by
  intro symmetry value
  rfl

/-- The same zero operator is not injective and hence cannot be an elliptic
principal symbol on a nonzero fiber. -/
theorem zero_operator_not_injective :
    Not (Function.Injective (fun _ : ℝ => 0)) := by
  intro hInjective
  have hEqual : (0 : ℝ) = 1 :=
    hInjective rfl
  norm_num at hEqual

/-- Naturality alone therefore cannot prove ellipticity. -/
theorem naturality_does_not_imply_symbol_injectivity
    (Symmetry : Type u) :
    (IsNaturalOperator
      (trivialAction Symmetry ℝ)
      (trivialAction Symmetry ℝ)
      (fun _ : ℝ => 0)) /\
    Not (Function.Injective (fun _ : ℝ => 0)) := by
  exact ⟨zero_operator_is_natural Symmetry,
    zero_operator_not_injective⟩

/-- Exact logical status of the corrected theorem. -/
structure CorrectedUniversalityStatus where
  decoratedSpinCImmersionCategoryConstructed : Prop
  sourceAndTargetNaturalBundlesFixed : Prop
  regularLocalOperatorSpecified : Prop
  peetreSlovakHypothesesVerified : Prop
  localFiniteJetFactorizationDerived : Prop
  jetRealizationOrSurjectivityDerived : Prop
  finiteJetEvaluatorEquivariant : Prop
  finiteJetEvaluatorUnique : Prop
  smoothRatherThanPolynomialClassificationUsed : Prop
  uniformOrderRegionSpecified : Prop
  ellipticityCheckedSeparately : Prop
  fieldContentSelectionCheckedSeparately : Prop

/-- Closure of the corrected theorem. -/
def correctedUniversalityClosed
    (s : CorrectedUniversalityStatus) : Prop :=
  s.decoratedSpinCImmersionCategoryConstructed /\
  s.sourceAndTargetNaturalBundlesFixed /\
  s.regularLocalOperatorSpecified /\
  s.peetreSlovakHypothesesVerified /\
  s.localFiniteJetFactorizationDerived /\
  s.jetRealizationOrSurjectivityDerived /\
  s.finiteJetEvaluatorEquivariant /\
  s.finiteJetEvaluatorUnique /\
  s.smoothRatherThanPolynomialClassificationUsed /\
  s.uniformOrderRegionSpecified /\
  s.ellipticityCheckedSeparately /\
  s.fieldContentSelectionCheckedSeparately

/-- Missing Peetre--Slovak regularity/locality blocks the finite-jet reduction. -/
theorem missing_peetre_slovak_hypotheses_blocks_closure
    (s : CorrectedUniversalityStatus)
    (hMissing : Not s.peetreSlovakHypothesesVerified) :
    Not (correctedUniversalityClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.1

/-- Missing a bounded region blocks a single global order, even if every local
piece has finite order. -/
theorem missing_uniform_region_blocks_global_order_claim
    (s : CorrectedUniversalityStatus)
    (hMissing : Not s.uniformOrderRegionSpecified) :
    Not (correctedUniversalityClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2.2.2.2.2.1

/-- The polynomial claim is not part of the corrected theorem. -/
theorem polynomial_upgrade_requires_extra_hypothesis :
    Not (HasFiniteDifferencePolynomialCertificate Real.exp) :=
  exp_has_no_finite_difference_polynomial_certificate

/--
Final corrected statement:

* regular local natural operators are locally represented by finite jets once
  the Peetre--Slovak hypotheses are verified;
* after a realizability/surjectivity hypothesis, the representing map is unique
  and naturality is equivalent to equivariance;
* scalar targets give smooth invariant functions, general targets give smooth
  covariants;
* one uniform global order, polynomial dependence, ellipticity and field-content
  selection are additional theorems, not consequences of locality/naturality.
-/
structure CorrectedTheoremVerdict where
  localFiniteJetReduction : Prop
  uniqueEquivariantEvaluator : Prop
  scalarCaseUsesInvariants : Prop
  vectorCaseUsesCovariants : Prop
  polynomialVersionRejectedWithoutExtraHypothesis : Prop
  globalUniformOrderConditional : Prop
  ellipticityIndependent : Prop
  fieldContentIndependent : Prop


def correctedTheoremVerdictClosed
    (s : CorrectedTheoremVerdict) : Prop :=
  s.localFiniteJetReduction /\
  s.uniqueEquivariantEvaluator /\
  s.scalarCaseUsesInvariants /\
  s.vectorCaseUsesCovariants /\
  s.polynomialVersionRejectedWithoutExtraHypothesis /\
  s.globalUniformOrderConditional /\
  s.ellipticityIndependent /\
  s.fieldContentIndependent

end P0EFTJanusCorrectedJetUniversality
end JanusFormal
