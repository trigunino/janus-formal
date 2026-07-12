/-
Program P.E — five-lemma verification head.

This head records the corrected theorem chain:

1. locality plus parametric regularity gives locally finite-jet dependence
   (written Peetre--Slovak/Whitney proof; analytic kernel formalization open);
2. finite-jet naturality is equivalent to evaluator equivariance under
   holonomic jet realizability;
3. polynomial invariant classification requires an explicit polynomial
   hypothesis; a complete quadratic vector fragment is proved;
4. the core vector/spin-two/discrete-grade pairing spaces are classified, with
   multiplicity freedom explicit;
5. the resulting universality theorem is conditional and smooth-equivariant,
   not automatically polynomial, elliptic or dynamically unique.
-/

import JanusFormal.Branches.FundamentalGeometryPELemmaAudit.Gates.P0EFTJanusFiniteJetOperatorConstruction
import JanusFormal.Branches.FundamentalGeometryPELemmaAudit.Gates.P0EFTJanusQuadraticJetInvariantClassification
import JanusFormal.Branches.FundamentalGeometryPELemmaAudit.Gates.P0EFTJanusCoreInvariantPairingClassification
import JanusFormal.Branches.FundamentalGeometryPELemmaAudit.Gates.P0EFTJanusCorrectedFiveLemmaChain

namespace JanusFormal
namespace JanusFundamentalGeometryPELemmaAudit

set_option autoImplicit false

structure ProgramStatus where
  lemmaOneProofDocumentPresent : Prop
  lemmaOneAnalyticDependenciesExplicit : Prop
  lemmaOneLeanKernelFormalizationComplete : Prop
  lemmaTwoConstructiveEquivalenceLeanChecked : Prop
  lemmaTwoHolonomicRealizationForJanusProved : Prop
  lemmaThreeStrongPolynomialClaimRejected : Prop
  lemmaThreeQuadraticVectorClassificationLeanChecked : Prop
  lemmaThreeFullJanusInvariantAlgebraClassified : Prop
  lemmaFourVectorPairingLeanChecked : Prop
  lemmaFourSpinTwoPairingLeanChecked : Prop
  lemmaFourDiscreteSelectionLeanChecked : Prop
  lemmaFourMultiplicityFreedomLeanChecked : Prop
  lemmaFourSpinorPairingsPythonChecked : Prop
  lemmaFourGlobalBundleClassificationProved : Prop
  lemmaFiveCorrectedConditionalTheoremLeanChecked : Prop
  lemmaFiveActualJanusCategorySpecialized : Prop
  ellipticityCheckedSeparately : Prop
  lowerOrderDynamicsCheckedSeparately : Prop

/-- Results that are presently defensible on the abstract/local models. -/
def verifiedLocalCoreClosed (s : ProgramStatus) : Prop :=
  s.lemmaOneProofDocumentPresent /\
  s.lemmaOneAnalyticDependenciesExplicit /\
  s.lemmaTwoConstructiveEquivalenceLeanChecked /\
  s.lemmaThreeStrongPolynomialClaimRejected /\
  s.lemmaThreeQuadraticVectorClassificationLeanChecked /\
  s.lemmaFourVectorPairingLeanChecked /\
  s.lemmaFourSpinTwoPairingLeanChecked /\
  s.lemmaFourDiscreteSelectionLeanChecked /\
  s.lemmaFourMultiplicityFreedomLeanChecked /\
  s.lemmaFourSpinorPairingsPythonChecked /\
  s.lemmaFiveCorrectedConditionalTheoremLeanChecked /\
  s.ellipticityCheckedSeparately /\
  s.lowerOrderDynamicsCheckedSeparately

/-- Full theorem for the concrete Janus SpinC/PT/Z4/BRST category. -/
def fullJanusLemmaChainClosed (s : ProgramStatus) : Prop :=
  verifiedLocalCoreClosed s /\
  s.lemmaOneLeanKernelFormalizationComplete /\
  s.lemmaTwoHolonomicRealizationForJanusProved /\
  s.lemmaThreeFullJanusInvariantAlgebraClassified /\
  s.lemmaFourGlobalBundleClassificationProved /\
  s.lemmaFiveActualJanusCategorySpecialized

/-- The analytic Peetre--Slovak proof is not silently promoted to a Lean-kernel theorem. -/
theorem missing_lean_peetre_slovak_blocks_full_chain
    (s : ProgramStatus)
    (hMissing : Not s.lemmaOneLeanKernelFormalizationComplete) :
    Not (fullJanusLemmaChainClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.1

/-- Finite local invariant calculations do not replace the full Janus invariant algebra. -/
theorem missing_full_invariant_algebra_blocks_full_chain
    (s : ProgramStatus)
    (hMissing : Not s.lemmaThreeFullJanusInvariantAlgebraClassified) :
    Not (fullJanusLemmaChainClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.1

/-- Pointwise pairing theorems still require globalization to bundle morphisms. -/
theorem missing_global_pairings_blocks_full_chain
    (s : ProgramStatus)
    (hMissing : Not s.lemmaFourGlobalBundleClassificationProved) :
    Not (fullJanusLemmaChainClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.1

end JanusFundamentalGeometryPELemmaAudit
end JanusFormal
