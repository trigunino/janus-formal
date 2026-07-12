import Mathlib
import JanusFormal.Branches.FundamentalGeometryPEInvariantPairings.Gates.P0EFTJanusSectorQuantumNumbers

namespace JanusFormal
namespace P0EFTJanusMultiplicitySpaceFreedom

set_option autoImplicit false

open P0EFTJanusSectorQuantumNumbers

/-- Number of independent coefficients in a symmetric `m x m` multiplicity matrix. -/
def symmetricCoefficientCount (multiplicity : ℕ) : ℕ :=
  multiplicity * (multiplicity + 1) / 2

@[simp] theorem multiplicity_one_has_one_coefficient :
    symmetricCoefficientCount 1 = 1 := by
  norm_num [symmetricCoefficientCount]

@[simp] theorem multiplicity_two_has_three_coefficients :
    symmetricCoefficientCount 2 = 3 := by
  norm_num [symmetricCoefficientCount]

@[simp] theorem multiplicity_three_has_six_coefficients :
    symmetricCoefficientCount 3 = 6 := by
  norm_num [symmetricCoefficientCount]

/-- Symmetric bilinear form on two copies of one irreducible representation. -/
@[ext] structure SymmetricMultiplicityPairing2 where
  firstDiagonal : ℝ
  mixing : ℝ
  secondDiagonal : ℝ

/-- Evaluation on multiplicity coordinates. -/
def multiplicityPairingValue
    (pairing : SymmetricMultiplicityPairing2)
    (first second : ℝ × ℝ) : ℝ :=
  pairing.firstDiagonal * first.1 * second.1 +
    pairing.mixing * (first.1 * second.2 + first.2 * second.1) +
    pairing.secondDiagonal * first.2 * second.2

/-- Same diagonal coefficients can coexist with distinct invariant mixing. -/
theorem multiplicity_two_mixing_not_selected :
    ∃ first second : SymmetricMultiplicityPairing2,
      first.firstDiagonal = second.firstDiagonal /\
      first.secondDiagonal = second.secondDiagonal /\
      first.mixing ≠ second.mixing := by
  exact ⟨
    { firstDiagonal := 1, mixing := 0, secondDiagonal := 1 },
    { firstDiagonal := 1, mixing := 1, secondDiagonal := 1 },
    rfl, rfl, by norm_num⟩

/-- Distinct mixing changes the quadratic form. -/
theorem distinct_mixing_changes_pairing :
    multiplicityPairingValue
      { firstDiagonal := 1, mixing := 0, secondDiagonal := 1 }
      (1, 0) (0, 1) ≠
    multiplicityPairingValue
      { firstDiagonal := 1, mixing := 1, secondDiagonal := 1 }
      (1, 0) (0, 1) := by
  norm_num [multiplicityPairingValue]

/-- Diagonal pairing when an additional character forbids mixing. -/
@[ext] structure CharacterSeparatedPairing2 where
  firstDiagonal : ℝ
  secondDiagonal : ℝ

/-- Embed a character-separated pairing in the full multiplicity matrix. -/
def separatedEmbedding
    (pairing : CharacterSeparatedPairing2) :
    SymmetricMultiplicityPairing2 :=
  { firstDiagonal := pairing.firstDiagonal
    mixing := 0
    secondDiagonal := pairing.secondDiagonal }

/-- Character separation removes exactly the off-diagonal coefficient. -/
@[simp] theorem separated_embedding_mixing_zero
    (pairing : CharacterSeparatedPairing2) :
    (separatedEmbedding pairing).mixing = 0 := by
  rfl

/-- The normal and trace scalars are rotation-isomorphic but character-separated. -/
theorem normal_trace_are_not_one_isotypic_block :
    normalMode.rotationType = traceMetricMode.rotationType /\
      normalMode.z4Phase ≠ traceMetricMode.z4Phase /\
      Not (PairingAllowed normalMode traceMetricMode) := by
  exact ⟨rfl, by native_decide, normal_trace_pairing_forbidden⟩

/-- A genuine repeated label would retain the full three-coefficient symmetric matrix. -/
def repeatedTraceLabelFirst : SectorLabel := traceMetricMode

def repeatedTraceLabelSecond : SectorLabel := traceMetricMode

@[simp] theorem repeated_trace_labels_pair :
    PairingAllowed repeatedTraceLabelFirst repeatedTraceLabelSecond := by
  native_decide

/-- Multiplicity freedom is not removed by representation invariance alone. -/
structure IsotypicMultiplicityStatus where
  irreduciblePairingSpaceOneDimensional : Prop
  multiplicity : ℕ
  multiplicitySpaceIdentified : Prop
  symmetricMatrixFreedomDerived : Prop
  extraCharacterSplittingDerived : Prop
  relativeCoefficientsSelected : Prop

/-- Physical closure of one isotypic block. -/
def isotypicMultiplicityClosed
    (s : IsotypicMultiplicityStatus) : Prop :=
  s.irreduciblePairingSpaceOneDimensional /\
  s.multiplicitySpaceIdentified /\
  s.symmetricMatrixFreedomDerived /\
  s.extraCharacterSplittingDerived /\
  s.relativeCoefficientsSelected

/-- Missing a relative coefficient law blocks uniqueness whenever multiplicity survives. -/
theorem missing_relative_coefficients_blocks_isotypic_closure
    (s : IsotypicMultiplicityStatus)
    (hMissing : Not s.relativeCoefficientsSelected) :
    Not (isotypicMultiplicityClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2

/--
P.E multiplicity verdict: Schur-type uniqueness applies to one irreducible copy.
For multiplicity `m`, invariant bilinear forms retain a symmetric matrix on the
multiplicity space.  Extra `Z4`, `U(1)`, ghost-number or PT characters can split
that matrix into smaller blocks, but representation theory cannot choose the
remaining diagonal normalizations.
-/
structure MultiplicityAuditPhysicalStatus where
  allSectorLabelsDerived : Prop
  irreducibleDecompositionComputed : Prop
  multiplicitiesComputed : Prop
  dualPairsIdentified : Prop
  characterSplittingsApplied : Prop
  invariantPairingDimensionsComputed : Prop
  residualCoefficientMatricesReported : Prop


def multiplicityAuditPhysicalClosure
    (s : MultiplicityAuditPhysicalStatus) : Prop :=
  s.allSectorLabelsDerived /\
  s.irreducibleDecompositionComputed /\
  s.multiplicitiesComputed /\
  s.dualPairsIdentified /\
  s.characterSplittingsApplied /\
  s.invariantPairingDimensionsComputed /\
  s.residualCoefficientMatricesReported

end P0EFTJanusMultiplicitySpaceFreedom
end JanusFormal
