import Mathlib

namespace JanusFormal
namespace P0EFTJanusNaturalLowerOrderFreedom

set_option autoImplicit false

/-- Scalar Laplace-type operator model at one point and one covector. -/
structure ScalarLaplaceTypeModel where
  potential : ℝ

/-- Principal symbol, independent of the potential. -/
def principalSymbol
    (_model : ScalarLaplaceTypeModel)
    (normSquared field : ℝ) : ℝ :=
  normSquared * field

/-- Full local operator model including a zero-order potential. -/
def fullOperator
    (model : ScalarLaplaceTypeModel)
    (normSquared field : ℝ) : ℝ :=
  normSquared * field + model.potential * field

/-- Every potential has the same Laplace principal symbol. -/
theorem all_potentials_have_same_principal_symbol
    (first second : ScalarLaplaceTypeModel)
    (normSquared field : ℝ) :
    principalSymbol first normSquared field =
      principalSymbol second normSquared field := by
  rfl

/-- Different potentials define different full operators. -/
theorem distinct_potentials_give_distinct_full_operators
    (first second : ScalarLaplaceTypeModel)
    (hPotential : first.potential ≠ second.potential) :
    fullOperator first 0 1 ≠ fullOperator second 0 1 := by
  unfold fullOperator
  simpa using hPotential

/-- Explicit pair with identical principal symbol and distinct full operators. -/
theorem principal_symbol_does_not_determine_full_operator :
    ∃ first second : ScalarLaplaceTypeModel,
      (∀ normSquared field,
        principalSymbol first normSquared field =
          principalSymbol second normSquared field) /\
      fullOperator first 0 1 ≠ fullOperator second 0 1 := by
  refine ⟨{ potential := 0 }, { potential := 1 }, ?_, ?_⟩
  · intro normSquared field
    rfl
  · norm_num [fullOperator]

/-- Local invariant jet naturally available from an immersed connection geometry. -/
structure ImmersionInvariantJet where
  scalarCurvature : ℝ
  meanCurvatureSquared : ℝ
  secondFundamentalNormSquared : ℝ
  gaugeCurvatureNormSquared : ℝ
  normalCurvaturePotential : ℝ

/-- Couplings multiplying natural zero-order invariants. -/
structure NaturalPotentialCouplings where
  scalarCurvature : ℝ
  meanCurvatureSquared : ℝ
  secondFundamentalNormSquared : ℝ
  gaugeCurvatureNormSquared : ℝ
  normalCurvaturePotential : ℝ
  massSquared : ℝ

/-- General displayed natural zero-order potential. -/
def naturalPotential
    (couplings : NaturalPotentialCouplings)
    (jet : ImmersionInvariantJet) : ℝ :=
  couplings.scalarCurvature * jet.scalarCurvature +
    couplings.meanCurvatureSquared * jet.meanCurvatureSquared +
    couplings.secondFundamentalNormSquared *
      jet.secondFundamentalNormSquared +
    couplings.gaugeCurvatureNormSquared *
      jet.gaugeCurvatureNormSquared +
    couplings.normalCurvaturePotential *
      jet.normalCurvaturePotential +
    couplings.massSquared

/-- Zero coupling package. -/
def zeroNaturalCouplings : NaturalPotentialCouplings :=
  { scalarCurvature := 0
    meanCurvatureSquared := 0
    secondFundamentalNormSquared := 0
    gaugeCurvatureNormSquared := 0
    normalCurvaturePotential := 0
    massSquared := 0 }

/-- Unit scalar-curvature coupling. -/
def unitScalarCurvatureCoupling : NaturalPotentialCouplings :=
  { scalarCurvature := 1
    meanCurvatureSquared := 0
    secondFundamentalNormSquared := 0
    gaugeCurvatureNormSquared := 0
    normalCurvaturePotential := 0
    massSquared := 0 }

/-- Test jet distinguishing the two natural choices. -/
def unitScalarCurvatureJet : ImmersionInvariantJet :=
  { scalarCurvature := 1
    meanCurvatureSquared := 0
    secondFundamentalNormSquared := 0
    gaugeCurvatureNormSquared := 0
    normalCurvaturePotential := 0 }

/-- Natural covariance alone leaves at least the curvature coupling free. -/
theorem natural_invariants_do_not_select_unique_potential :
    naturalPotential zeroNaturalCouplings unitScalarCurvatureJet ≠
      naturalPotential unitScalarCurvatureCoupling
        unitScalarCurvatureJet := by
  norm_num [naturalPotential, zeroNaturalCouplings,
    unitScalarCurvatureCoupling, unitScalarCurvatureJet]

/-- Turn any natural invariant jet and coupling package into a Laplace model. -/
def laplaceModelFromNaturalData
    (couplings : NaturalPotentialCouplings)
    (jet : ImmersionInvariantJet) : ScalarLaplaceTypeModel :=
  { potential := naturalPotential couplings jet }

/-- Two natural operators can have the same principal symbol and different curvature terms. -/
theorem natural_operator_nonuniqueness :
    let first := laplaceModelFromNaturalData
      zeroNaturalCouplings unitScalarCurvatureJet
    let second := laplaceModelFromNaturalData
      unitScalarCurvatureCoupling unitScalarCurvatureJet
    (∀ normSquared field,
      principalSymbol first normSquared field =
        principalSymbol second normSquared field) /\
    fullOperator first 0 1 ≠ fullOperator second 0 1 := by
  dsimp
  constructor
  · intro normSquared field
    rfl
  · norm_num [laplaceModelFromNaturalData, naturalPotential,
      zeroNaturalCouplings, unitScalarCurvatureCoupling,
      unitScalarCurvatureJet, fullOperator]

/-- Overall normalization also remains free at the level of naturality. -/
def rescaleCouplings
    (scale : ℝ)
    (couplings : NaturalPotentialCouplings) :
    NaturalPotentialCouplings :=
  { scalarCurvature := scale * couplings.scalarCurvature
    meanCurvatureSquared := scale * couplings.meanCurvatureSquared
    secondFundamentalNormSquared :=
      scale * couplings.secondFundamentalNormSquared
    gaugeCurvatureNormSquared :=
      scale * couplings.gaugeCurvatureNormSquared
    normalCurvaturePotential :=
      scale * couplings.normalCurvaturePotential
    massSquared := scale * couplings.massSquared }

/-- Natural potentials scale with their coupling package. -/
theorem natural_potential_rescaling
    (scale : ℝ)
    (couplings : NaturalPotentialCouplings)
    (jet : ImmersionInvariantJet) :
    naturalPotential (rescaleCouplings scale couplings) jet =
      scale * naturalPotential couplings jet := by
  unfold naturalPotential rescaleCouplings
  ring

/--
Conclusion: an immersion with metric and connections canonically fixes the
natural bundles and leading symbols.  It does not fix masses, curvature
endomorphisms, relative sector coefficients, action normalization or finite
counterterms.  These require an action or an equivalent microscopic law.
-/
structure LowerOrderSelectionStatus where
  invariantJetAlgebraClassified : Prop
  allowedDerivativeOrderSpecified : Prop
  discreteSymmetriesImposed : Prop
  actionFunctionalDerived : Prop
  relativeCouplingsDerived : Prop
  overallNormalizationDerived : Prop
  finiteCountertermsFixed : Prop
  lowerOrderOperatorsUniquelySelected : Prop


def lowerOrderSelectionClosed
    (s : LowerOrderSelectionStatus) : Prop :=
  s.invariantJetAlgebraClassified /\
  s.allowedDerivativeOrderSpecified /\
  s.discreteSymmetriesImposed /\
  s.actionFunctionalDerived /\
  s.relativeCouplingsDerived /\
  s.overallNormalizationDerived /\
  s.finiteCountertermsFixed /\
  s.lowerOrderOperatorsUniquelySelected

end P0EFTJanusNaturalLowerOrderFreedom
end JanusFormal
