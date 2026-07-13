/-
Program P.E-J: proof program for finite-jet universality of natural operators on
decorated SpinC immersions.

The original strong conjecture is corrected in five ways:

1. Peetre--Slovak gives a local finite-jet factorization under regularity and
   locality hypotheses;
2. naturality is equivalent to equivariance of the unique jet evaluator once
   holonomic jets are realizable/surjective;
3. the evaluator is smooth, not automatically polynomial;
4. a uniform global order, ellipticity and field-content selection require
   independent hypotheses;
5. the categorical morphism law is holonomic jet composition, not ordinary
   composition of maps between unprolonged representation fibers.

The head also contains exact algebraic cores for an action groupoid, orbitwise
descent, the second-immersion-jet normal slice, the abelian connection one-jet
curvature slice, their universal invariant-factorization properties, and
residual symmetry descent to the reduced data. The latest concrete gates derive
the normalized second-jet source action from the second-order chain-rule formula,
classify concrete abelian connection one-jets by curvature, construct the first
combined low-order quotient represented by `(B,F)`, and prove the pointwise
orthogonal splitting of a linear isometric immersion derivative into its tangent
image and orthogonal normal complement. They still do not construct the actual
smooth Janus structured-jet space or its adapted SpinC frame field and bundles.
-/

import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusFiniteJetEquivariance
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusFiniteOrderUniformization
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusSmoothNotPolynomial
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusCorrectedJetUniversality
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusJetOperatorComposition
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusStructuredJetActionGroupoid
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusOrbitwiseDescent
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusSecondJetNormalForm
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusAbelianConnectionJetNormalForm
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusLowOrderJetQuotientUniversality
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusResidualJetSymmetry
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusConcreteSecondJetChainRule
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusConcreteAbelianConnectionJet
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusLowOrderStructuredBackground
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusAdaptedOrthogonalSplitting

namespace JanusFormal
namespace JanusFundamentalGeometryPEJetUniversality

set_option autoImplicit false

structure ProgramStatus where
  regularLocalOperatorSheafDefined : Prop
  peetreSlovakHypothesesVerified : Prop
  localFiniteJetFactorizationDerived : Prop
  finiteJetActionsConstructed : Prop
  holonomicJetRealizationProved : Prop
  naturalityEquivarianceIffProved : Prop
  evaluatorUniquenessProved : Prop
  holonomicJetCompositionProved : Prop
  actionGroupoidLawsProved : Prop
  orbitwiseDescentEquivalenceProved : Prop
  abstractSecondJetNormalFormProved : Prop
  abstractAbelianConnectionNormalFormProved : Prop
  lowOrderInvariantQuotientUniversalityProved : Prop
  abstractResidualEquivariantReductionProved : Prop
  concreteSecondJetChainRuleAndQuotientProved : Prop
  concreteAbelianConnectionOrbitClassificationProved : Prop
  combinedLowOrderStructuredQuotientProved : Prop
  pointwiseAdaptedOrthogonalSplittingProved : Prop
  naiveRepresentationCategoryCorrected : Prop
  smoothNonpolynomialCounterexampleProved : Prop
  polynomialClaimCorrected : Prop
  finiteCoverUniformizationProved : Prop
  unboundedGlobalOrderCounterexampleProved : Prop
  correctedTheoremStated : Prop
  spinCImmersionJetGroupoidConstructed : Prop
  structuredJetNormalFormProved : Prop
  residualFrameActionsConstructed : Prop
  janusOrbitStrataClassified : Prop
  crossStratumExtensionProved : Prop
  actualJanusNaturalBundlesInserted : Prop
  ellipticSymbolsClassified : Prop
  globalUniformOrderRegionDerived : Prop

/-- Formal/logical theorem core, including orbitwise descent, abstract and
concrete low-order orbit reductions, the combined `(B,F)` quotient, pointwise
orthogonal splitting, universal factorization and residual symmetry models. -/
def theoremCoreClosed (s : ProgramStatus) : Prop :=
  s.regularLocalOperatorSheafDefined /\
  s.peetreSlovakHypothesesVerified /\
  s.localFiniteJetFactorizationDerived /\
  s.finiteJetActionsConstructed /\
  s.holonomicJetRealizationProved /\
  s.naturalityEquivarianceIffProved /\
  s.evaluatorUniquenessProved /\
  s.holonomicJetCompositionProved /\
  s.actionGroupoidLawsProved /\
  s.orbitwiseDescentEquivalenceProved /\
  s.abstractSecondJetNormalFormProved /\
  s.abstractAbelianConnectionNormalFormProved /\
  s.lowOrderInvariantQuotientUniversalityProved /\
  s.abstractResidualEquivariantReductionProved /\
  s.concreteSecondJetChainRuleAndQuotientProved /\
  s.concreteAbelianConnectionOrbitClassificationProved /\
  s.combinedLowOrderStructuredQuotientProved /\
  s.pointwiseAdaptedOrthogonalSplittingProved /\
  s.naiveRepresentationCategoryCorrected /\
  s.smoothNonpolynomialCounterexampleProved /\
  s.polynomialClaimCorrected /\
  s.finiteCoverUniformizationProved /\
  s.unboundedGlobalOrderCounterexampleProved /\
  s.correctedTheoremStated

/-- Full Janus specialization. -/
def fullJanusJetUniversalityClosed (s : ProgramStatus) : Prop :=
  theoremCoreClosed s /\
  s.spinCImmersionJetGroupoidConstructed /\
  s.structuredJetNormalFormProved /\
  s.residualFrameActionsConstructed /\
  s.janusOrbitStrataClassified /\
  s.crossStratumExtensionProved /\
  s.actualJanusNaturalBundlesInserted /\
  s.ellipticSymbolsClassified /\
  s.globalUniformOrderRegionDerived

/-- The abstract theorem does not close the Janus specialization without the
actual adapted SpinC structured-jet groupoid. -/
theorem missing_janus_jet_groupoid_blocks_full_specialization
    (s : ProgramStatus)
    (hMissing : Not s.spinCImmersionJetGroupoidConstructed) :
    Not (fullJanusJetUniversalityClosed s) := by
  rintro ⟨hCore, hGroupoid, hNormalForm, hResidual, hStrata,
    hExtension, hBundles, hSymbols, hRegion⟩
  exact hMissing hGroupoid

/-- The low-order chain-rule, curvature and pointwise orthogonal-splitting
results do not replace a geometric jet-isomorphism theorem for the actual
constrained SpinC immersion data. -/
theorem missing_structured_normal_form_blocks_full_specialization
    (s : ProgramStatus)
    (hMissing : Not s.structuredJetNormalFormProved) :
    Not (fullJanusJetUniversalityClosed s) := by
  rintro ⟨hCore, hGroupoid, hNormalForm, hResidual, hStrata,
    hExtension, hBundles, hSymbols, hRegion⟩
  exact hMissing hNormalForm

/-- The pointwise orthogonal factors and generic residual-frame formulas still
require a smooth local frame field and the concrete SpinC lift before invariant
theory can be applied to Janus jets. -/
theorem missing_residual_actions_blocks_full_specialization
    (s : ProgramStatus)
    (hMissing : Not s.residualFrameActionsConstructed) :
    Not (fullJanusJetUniversalityClosed s) := by
  rintro ⟨hCore, hGroupoid, hNormalForm, hResidual, hStrata,
    hExtension, hBundles, hSymbols, hRegion⟩
  exact hMissing hResidual

/-- Orbitwise descent does not solve extension between distinct isotropy strata. -/
theorem missing_cross_stratum_extension_blocks_full_specialization
    (s : ProgramStatus)
    (hMissing : Not s.crossStratumExtensionProved) :
    Not (fullJanusJetUniversalityClosed s) := by
  rintro ⟨hCore, hGroupoid, hNormalForm, hResidual, hStrata,
    hExtension, hBundles, hSymbols, hRegion⟩
  exact hMissing hExtension

/-- Natural finite-jet classification does not imply ellipticity. -/
theorem missing_symbol_classification_blocks_full_specialization
    (s : ProgramStatus)
    (hMissing : Not s.ellipticSymbolsClassified) :
    Not (fullJanusJetUniversalityClosed s) := by
  rintro ⟨hCore, hGroupoid, hNormalForm, hResidual, hStrata,
    hExtension, hBundles, hSymbols, hRegion⟩
  exact hMissing hSymbols

/-- One global jet order still requires a bounded configuration region. -/
theorem missing_uniform_region_blocks_full_specialization
    (s : ProgramStatus)
    (hMissing : Not s.globalUniformOrderRegionDerived) :
    Not (fullJanusJetUniversalityClosed s) := by
  rintro ⟨hCore, hGroupoid, hNormalForm, hResidual, hStrata,
    hExtension, hBundles, hSymbols, hRegion⟩
  exact hMissing hRegion

end JanusFundamentalGeometryPEJetUniversality
end JanusFormal
