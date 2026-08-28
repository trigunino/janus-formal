import Mathlib.Analysis.InnerProductSpace.Basic
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANamedZeroModeSectors4D

/-!
# Assembly of the five D10-free Candidate-A zero-mode sectors

The terminal Noether frontier previously accepted one opaque finite type
`ZeroMode`.  Physically the modes arise in five different D10-free sectors.
This file replaces the opaque index by a dependent finite family

`Σ sector, Mode sector`.

Each sector supplies its own nonzero orthogonal modes.  Orthogonality between
distinct sector subspaces is stated once, and the global pairwise orthogonality
required by the terminal Hessian packet is derived automatically.  The
physical sector classification is definitionally the first projection.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPCandidateASectorModeAssembly4D

set_option autoImplicit false
noncomputable section

open Set
open scoped InnerProductSpace
open P0EFTJanusProgramPCandidateAZeroModeSector4D
open P0EFTJanusProgramPGlobalCandidateANamedZeroModeSectors4D

/-- One finite mode type for each of the five corrected physical sectors. -/
structure CandidateASectorModeTypes where
  Mode : CandidateAZeroModeSector → Type
  modeFintype : ∀ sector, Fintype (Mode sector)

namespace CandidateASectorModeTypes

/-- The total physical mode type is the dependent disjoint union of sectors. -/
abbrev GlobalMode (types : CandidateASectorModeTypes) :=
  Sigma types.Mode

noncomputable instance globalModeFintype
    (types : CandidateASectorModeTypes) : Fintype types.GlobalMode := by
  letI (sector : CandidateAZeroModeSector) : Fintype (types.Mode sector) :=
    types.modeFintype sector
  infer_instance

/-- Canonical sector assignment of the assembled mode type. -/
def classification (types : CandidateASectorModeTypes) :
    CandidateAZeroModeSectorClassification types.GlobalMode where
  sectorOf mode := mode.1

@[simp]
theorem classification_sector
    (types : CandidateASectorModeTypes)
    (mode : types.GlobalMode) :
    types.classification.sectorOf mode = mode.1 :=
  rfl

end CandidateASectorModeTypes

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace Real E]

/-- Vectors indexed independently inside each physical sector. -/
structure CandidateASectorVectorFamily
    (types : CandidateASectorModeTypes) where
  vector : ∀ sector, types.Mode sector → E

namespace CandidateASectorVectorFamily

/-- Assemble one sector-local vector into the common Hilbert space. -/
def globalVector
    {types : CandidateASectorModeTypes}
    (family : CandidateASectorVectorFamily (E := E) types)
    (mode : types.GlobalMode) : E :=
  family.vector mode.1 mode.2

@[simp]
theorem globalVector_mk
    {types : CandidateASectorModeTypes}
    (family : CandidateASectorVectorFamily (E := E) types)
    (sector : CandidateAZeroModeSector)
    (mode : types.Mode sector) :
    family.globalVector ⟨sector, mode⟩ = family.vector sector mode :=
  rfl

end CandidateASectorVectorFamily

/-- Sector-local nonzero orthogonal families, together with one cross-sector
orthogonality statement. -/
structure CandidateASectorOrthogonalModeFamily
    (types : CandidateASectorModeTypes) where
  vectors : CandidateASectorVectorFamily (E := E) types
  nonzero : ∀ sector mode, vectors.vector sector mode ≠ 0
  within_orthogonal : ∀ sector,
    Pairwise fun first second : types.Mode sector =>
      inner Real (vectors.vector sector first)
        (vectors.vector sector second) = 0
  cross_orthogonal :
    ∀ {firstSector secondSector : CandidateAZeroModeSector},
      firstSector ≠ secondSector →
      ∀ (first : types.Mode firstSector)
        (second : types.Mode secondSector),
        inner Real (vectors.vector firstSector first)
          (vectors.vector secondSector second) = 0

namespace CandidateASectorOrthogonalModeFamily

/-- Every assembled vector is nonzero. -/
theorem global_nonzero
    {types : CandidateASectorModeTypes}
    (family : CandidateASectorOrthogonalModeFamily (E := E) types) :
    ∀ mode : types.GlobalMode, family.vectors.globalVector mode ≠ 0 := by
  rintro ⟨sector, mode⟩
  exact family.nonzero sector mode

/-- Pairwise orthogonality of the complete five-sector family. -/
theorem global_orthogonal
    {types : CandidateASectorModeTypes}
    (family : CandidateASectorOrthogonalModeFamily (E := E) types) :
    Pairwise fun first second : types.GlobalMode =>
      inner Real (family.vectors.globalVector first)
        (family.vectors.globalVector second) = 0 := by
  rintro ⟨firstSector, first⟩ ⟨secondSector, second⟩ hDistinct
  by_cases hSector : firstSector = secondSector
  · subst secondSector
    apply family.within_orthogonal firstSector
    intro hMode
    apply hDistinct
    cases hMode
    rfl
  · exact family.cross_orthogonal hSector first second

/-- Public assembly checkpoint. -/
theorem candidateA_sector_mode_assembly_gate
    {types : CandidateASectorModeTypes}
    (family : CandidateASectorOrthogonalModeFamily (E := E) types) :
    (∀ mode : types.GlobalMode, family.vectors.globalVector mode ≠ 0) ∧
      Pairwise (fun first second : types.GlobalMode =>
        inner Real (family.vectors.globalVector first)
          (family.vectors.globalVector second) = 0) ∧
      Nonempty (CandidateAZeroModeSectorClassification types.GlobalMode) :=
  ⟨family.global_nonzero, family.global_orthogonal,
    ⟨types.classification⟩⟩

end CandidateASectorOrthogonalModeFamily

end
end P0EFTJanusProgramPCandidateASectorModeAssembly4D
end JanusFormal
