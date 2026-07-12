import Mathlib

namespace JanusFormal
namespace P0EFTJanusAnomalyObjectDimensionParity

set_option autoImplicit false

/-- Canonical geometric anomaly object attached to a smooth family of Dirac-type operators. -/
inductive AnomalyObjectKind where
  | determinantLine
  | indexGerbe
  deriving DecidableEq, Repr

/--
For the standard families-index package, even-dimensional chiral families carry
`K^0` index data and determinant lines, while odd-dimensional self-adjoint
families carry `K^1` data and an index gerbe.
-/
def canonicalAnomalyObject
    (fiberDimension : ℕ) : AnomalyObjectKind :=
  if fiberDimension % 2 = 0 then
    AnomalyObjectKind.determinantLine
  else
    AnomalyObjectKind.indexGerbe

@[simp] theorem two_dimensional_family_has_determinant_line :
    canonicalAnomalyObject 2 =
      AnomalyObjectKind.determinantLine := by
  native_decide

@[simp] theorem three_dimensional_family_has_index_gerbe :
    canonicalAnomalyObject 3 =
      AnomalyObjectKind.indexGerbe := by
  native_decide

@[simp] theorem four_dimensional_family_has_determinant_line :
    canonicalAnomalyObject 4 =
      AnomalyObjectKind.determinantLine := by
  native_decide

/-- A closed three-dimensional throat family is not directly in the even-dimensional Quillen-line case. -/
theorem closed_three_throat_not_direct_quillen_line :
    canonicalAnomalyObject 3 ≠
      AnomalyObjectKind.determinantLine := by
  native_decide

/-- Auxiliary choices that can reduce or transgress the odd anomaly object to line-valued data. -/
structure OddFamilyLineReductionStatus where
  spectralSectionChosen : Prop
  polarizationChosen : Prop
  boundingBulkOrInflowTheoryConstructed : Prop
  gerbeTrivializationConstructed : Prop
  evenDimensionalCutFamilyConstructed : Prop
  lineReductionActuallyDerived : Prop

/-- At least one genuine reduction mechanism must be present. -/
def oddFamilyReducedToLine
    (s : OddFamilyLineReductionStatus) : Prop :=
  (s.spectralSectionChosen \/
    s.polarizationChosen \/
    s.boundingBulkOrInflowTheoryConstructed \/
    s.gerbeTrivializationConstructed \/
    s.evenDimensionalCutFamilyConstructed) /\
  s.lineReductionActuallyDerived

/-- Without any reduction datum, an odd family cannot be promoted to a line by declaration. -/
theorem no_reduction_data_blocks_line_reduction
    (s : OddFamilyLineReductionStatus)
    (hSpectral : Not s.spectralSectionChosen)
    (hPolarization : Not s.polarizationChosen)
    (hBulk : Not s.boundingBulkOrInflowTheoryConstructed)
    (hTrivialization : Not s.gerbeTrivializationConstructed)
    (hCut : Not s.evenDimensionalCutFamilyConstructed) :
    Not (oddFamilyReducedToLine s) := by
  intro hReduced
  rcases hReduced.1 with h | h | h | h | h
  · exact hSpectral h
  · exact hPolarization h
  · exact hBulk h
  · exact hTrivialization h
  · exact hCut h

/--
The full gauge-fixed bosonic/ghost elliptic complex can still possess its own
determinant line.  The statement above concerns the parity-sensitive
fermionic family and its eta phase, not every determinant magnitude appearing
in the one-loop superdeterminant.
-/
structure MixedAnomalyPackageStatus where
  bosonicEllipticComplexConstructed : Prop
  bosonicDeterminantLineConstructed : Prop
  ghostDeterminantLineConstructed : Prop
  oddFermionIndexGerbeConstructed : Prop
  etaPhaseDefined : Prop
  combinedAnomalyObjectConstructed : Prop
  anomalyCancellationOrTrivializationProved : Prop


def mixedAnomalyPackageClosed
    (s : MixedAnomalyPackageStatus) : Prop :=
  s.bosonicEllipticComplexConstructed /\
  s.bosonicDeterminantLineConstructed /\
  s.ghostDeterminantLineConstructed /\
  s.oddFermionIndexGerbeConstructed /\
  s.etaPhaseDefined /\
  s.combinedAnomalyObjectConstructed /\
  s.anomalyCancellationOrTrivializationProved

end P0EFTJanusAnomalyObjectDimensionParity
end JanusFormal
