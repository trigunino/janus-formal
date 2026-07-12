import Mathlib
import JanusFormal.Branches.FundamentalGeometryPEInvariantPairings.Gates.P0EFTJanusSectorQuantumNumbers
import JanusFormal.Branches.FundamentalGeometryPEInvariantPairings.Gates.P0EFTJanusVectorInvariantPairing
import JanusFormal.Branches.FundamentalGeometryPEInvariantPairings.Gates.P0EFTJanusSpinTwoInvariantPairing
import JanusFormal.Branches.FundamentalGeometryPEInvariantPairings.Gates.P0EFTJanusMultiplicitySpaceFreedom

namespace JanusFormal
namespace P0EFTJanusCoreInvariantPairingClassification

set_option autoImplicit false

open P0EFTJanusSectorQuantumNumbers
open P0EFTJanusVectorInvariantPairing
open P0EFTJanusSpinTwoInvariantPairing
open P0EFTJanusMultiplicitySpaceFreedom

/-- The local vector pairing has exactly one coefficient. -/
theorem vector_pairing_exists_unique_coefficient
    (pairing : BilinearMatrix3)
    (hInvariant : SignedPermutationInvariant pairing) :
    ∃! coefficient : ℝ,
      pairing = scalarDotPairing coefficient := by
  refine ⟨pairing.xx,
    vector_invariant_pairing_classification pairing hInvariant, ?_⟩
  intro coefficient hCoefficient
  have hXX := congrArg BilinearMatrix3.xx hCoefficient
  simpa [scalarDotPairing] using hXX.symm

/-- The local spin-two pairing has exactly one coefficient. -/
theorem spin_two_pairing_exists_unique_coefficient
    (pairing : SymmetricPairing5)
    (hInvariant : LieGeneratorInvariant pairing) :
    ∃! coefficient : ℝ,
      pairing = canonicalSpinTwoPairing coefficient := by
  refine ⟨pairing.q44,
    spin_two_invariant_pairing_classification pairing hInvariant, ?_⟩
  intro coefficient hCoefficient
  have hQ44 := congrArg SymmetricPairing5.q44 hCoefficient
  simpa [canonicalSpinTwoPairing] using hQ44.symm

/-- The normal and trace scalar sectors cannot mix under the declared normal-root grading. -/
theorem normal_trace_block_is_split :
    PairingAllowed normalMode normalMode /\
    PairingAllowed traceMetricMode traceMetricMode /\
    Not (PairingAllowed normalMode traceMetricMode) := by
  exact ⟨normal_self_pairing_allowed,
    trace_self_pairing_allowed,
    normal_trace_pairing_forbidden⟩

/-- The conjugate quarter-spinor block is allowed while same-quarter blocks are forbidden. -/
theorem quarter_spinor_selection_matrix :
    PairingAllowed positiveQuarterSpinor negativeQuarterSpinor /\
    Not (PairingAllowed positiveQuarterSpinor positiveQuarterSpinor) /\
    Not (PairingAllowed negativeQuarterSpinor negativeQuarterSpinor) := by
  exact ⟨conjugate_spinor_pairing_allowed,
    positive_spinor_self_pairing_forbidden,
    negative_spinor_self_pairing_forbidden⟩

/-- The ghost blocks pair only at opposite ghost number in the displayed core. -/
theorem ghost_selection_matrix :
    PairingAllowed u1Ghost u1Antighost /\
    Not (PairingAllowed u1Ghost u1Ghost) /\
    PairingAllowed diffeomorphismGhost diffeomorphismAntighost := by
  exact ⟨u1_ghost_antighost_pairing_allowed,
    u1_ghost_self_pairing_forbidden,
    diffeomorphism_ghost_antighost_pairing_allowed⟩

/-- Repeated irreducible copies retain a genuine mixing coefficient. -/
theorem multiplicity_two_retains_three_parameter_pairing_space :
    symmetricCoefficientCount 2 = 3 /\
    (∃ first second : SymmetricMultiplicityPairing2,
      first.firstDiagonal = second.firstDiagonal /\
      first.secondDiagonal = second.secondDiagonal /\
      first.mixing ≠ second.mixing) := by
  exact ⟨multiplicity_two_has_three_coefficients,
    multiplicity_two_mixing_not_selected⟩

/-- Complete proved core of Lemma 4. -/
theorem core_pairing_classification_matrix :
    (∀ pairing : BilinearMatrix3,
      SignedPermutationInvariant pairing →
      ∃! coefficient : ℝ,
        pairing = scalarDotPairing coefficient) /\
    (∀ pairing : SymmetricPairing5,
      LieGeneratorInvariant pairing →
      ∃! coefficient : ℝ,
        pairing = canonicalSpinTwoPairing coefficient) /\
    Not (PairingAllowed normalMode traceMetricMode) /\
    PairingAllowed positiveQuarterSpinor negativeQuarterSpinor /\
    Not (PairingAllowed positiveQuarterSpinor positiveQuarterSpinor) /\
    PairingAllowed u1Ghost u1Antighost /\
    symmetricCoefficientCount 2 = 3 := by
  exact ⟨vector_pairing_exists_unique_coefficient,
    spin_two_pairing_exists_unique_coefficient,
    normal_trace_pairing_forbidden,
    conjugate_spinor_pairing_allowed,
    positive_spinor_self_pairing_forbidden,
    u1_ghost_antighost_pairing_allowed,
    multiplicity_two_has_three_coefficients⟩

/--
Lemma 4 is therefore proved for the displayed finite local sectors: zero/one
pairing dimensions and multiplicity freedom are explicit.  The exact global
SpinC/PT/Z4/BRST bundle group, globalization of these pointwise pairings and
normalization of the surviving lines remain separate theorems.
-/
structure CorePairingGlobalizationStatus where
  actualStructureGroupConstructed : Prop
  localRepresentationsIdentified : Prop
  pointwiseClassificationsApplied : Prop
  bundlePairingsGlobalized : Prop
  spinorHermitianAndComplexPairingsFormalized : Prop
  brstSignsAndRealityConditionsFixed : Prop
  multiplicitySpacesComputed : Prop
  survivingNormalizationsDerived : Prop


def corePairingGlobalizationClosed
    (s : CorePairingGlobalizationStatus) : Prop :=
  s.actualStructureGroupConstructed /\
  s.localRepresentationsIdentified /\
  s.pointwiseClassificationsApplied /\
  s.bundlePairingsGlobalized /\
  s.spinorHermitianAndComplexPairingsFormalized /\
  s.brstSignsAndRealityConditionsFixed /\
  s.multiplicitySpacesComputed /\
  s.survivingNormalizationsDerived

end P0EFTJanusCoreInvariantPairingClassification
end JanusFormal
