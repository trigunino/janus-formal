import Mathlib

/-!
Linear source-mode algebra for Program P Candidate A.

This gate is only a precursor to a post-Newtonian rejection test: it identifies
when Candidate A sources its relative mode.  It derives neither a propagator nor
a PPN parameter or observational bound.
-/

namespace JanusFormal
namespace P0EFTJanusCandidateSourceModeDecomposition

set_option autoImplicit false

/-- Candidate A source coefficient of the diagonal mode. -/
noncomputable def candidateADiagonalSource
    (sourcePlus sourceMinus : ℝ) : ℝ :=
  (sourcePlus + sourceMinus) / 2

/-- Candidate A source coefficient of the relative mode. -/
noncomputable def candidateARelativeSource
    (sourcePlus sourceMinus : ℝ) : ℝ :=
  (sourcePlus - sourceMinus) / 2

/-- Exact diagonal/relative decomposition of Candidate A's linear source coupling. -/
theorem candidateA_source_coupling_mode_decomposition
    (sourcePlus sourceMinus hPlus hMinus : ℝ) :
    sourcePlus * hPlus + sourceMinus * hMinus =
      candidateADiagonalSource sourcePlus sourceMinus * (hPlus + hMinus) +
        candidateARelativeSource sourcePlus sourceMinus * (hPlus - hMinus) := by
  unfold candidateADiagonalSource candidateARelativeSource
  ring

/-- Candidate A leaves the relative mode unsourced exactly for equal sources. -/
theorem candidateA_relative_mode_unsourced_iff_equal_sources
    (sourcePlus sourceMinus : ℝ) :
    candidateARelativeSource sourcePlus sourceMinus = 0 ↔
      sourcePlus = sourceMinus := by
  unfold candidateARelativeSource
  constructor <;> intro h <;> linarith

/-- A nonzero Candidate A source confined to one sheet excites the relative mode. -/
theorem candidateA_single_sheet_source_excites_relative_mode
    (sourcePlus : ℝ) (hSource : sourcePlus ≠ 0) :
    candidateARelativeSource sourcePlus 0 ≠ 0 := by
  unfold candidateARelativeSource
  intro hZero
  apply hSource
  linarith

/-- Opposite PT sources in Candidate A have zero diagonal and pure relative coupling. -/
theorem candidateA_opposite_pt_sources_are_pure_relative
    (source : ℝ) :
    candidateADiagonalSource source (-source) = 0 ∧
      candidateARelativeSource source (-source) = source := by
  constructor
  · unfold candidateADiagonalSource
    ring
  · unfold candidateARelativeSource
    ring

end P0EFTJanusCandidateSourceModeDecomposition
end JanusFormal
