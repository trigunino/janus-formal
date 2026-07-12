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
-/

import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusFiniteJetEquivariance
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusFiniteOrderUniformization
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusSmoothNotPolynomial
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusCorrectedJetUniversality
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusJetOperatorComposition

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
  naiveRepresentationCategoryCorrected : Prop
  smoothNonpolynomialCounterexampleProved : Prop
  polynomialClaimCorrected : Prop
  finiteCoverUniformizationProved : Prop
  unboundedGlobalOrderCounterexampleProved : Prop
  correctedTheoremStated : Prop
  spinCImmersionJetGroupoidConstructed : Prop
  actualJanusNaturalBundlesInserted : Prop
  ellipticSymbolsClassified : Prop
  globalUniformOrderRegionDerived : Prop

/-- Formal/logical theorem core. -/
def theoremCoreClosed (s : ProgramStatus) : Prop :=
  s.regularLocalOperatorSheafDefined /\
  s.peetreSlovakHypothesesVerified /\
  s.localFiniteJetFactorizationDerived /\
  s.finiteJetActionsConstructed /\
  s.holonomicJetRealizationProved /\
  s.naturalityEquivarianceIffProved /\
  s.evaluatorUniquenessProved /\
  s.holonomicJetCompositionProved /\
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
  s.actualJanusNaturalBundlesInserted /\
  s.ellipticSymbolsClassified /\
  s.globalUniformOrderRegionDerived

/-- The abstract theorem does not close the Janus specialization without the
actual adapted SpinC structured-jet groupoid. -/
theorem missing_janus_jet_groupoid_blocks_full_specialization
    (s : ProgramStatus)
    (hMissing : Not s.spinCImmersionJetGroupoidConstructed) :
    Not (fullJanusJetUniversalityClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.1

/-- Natural finite-jet classification does not imply ellipticity. -/
theorem missing_symbol_classification_blocks_full_specialization
    (s : ProgramStatus)
    (hMissing : Not s.ellipticSymbolsClassified) :
    Not (fullJanusJetUniversalityClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.1

/-- One global jet order still requires a bounded configuration region. -/
theorem missing_uniform_region_blocks_full_specialization
    (s : ProgramStatus)
    (hMissing : Not s.globalUniformOrderRegionDerived) :
    Not (fullJanusJetUniversalityClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2

end JanusFundamentalGeometryPEJetUniversality
end JanusFormal
