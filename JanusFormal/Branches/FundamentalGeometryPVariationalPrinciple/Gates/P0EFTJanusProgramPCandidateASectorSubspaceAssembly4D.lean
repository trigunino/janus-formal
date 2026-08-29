import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPCandidateASectorModeAssembly4D

/-!
# Candidate-A sector modes carried by orthogonal physical subspaces

Cross-sector orthogonality should normally be a property of the Hilbert-space
sector decomposition, not a separate calculation for every pair of modes.
This file packages five sector subspaces and proves that every vector chosen in
them inherits the required cross-sector orthogonality.

Only within-sector orthogonality remains attached to the finite mode families.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPCandidateASectorSubspaceAssembly4D

set_option autoImplicit false
noncomputable section

open Set
open scoped InnerProductSpace
open P0EFTJanusProgramPGlobalCandidateANamedZeroModeSectors4D
open P0EFTJanusProgramPCandidateAZeroModeSector4D
open P0EFTJanusProgramPCandidateASectorModeAssembly4D

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace Real E]

/-- Five physical subspaces which are orthogonal whenever their sector labels
are distinct. -/
structure CandidateASectorOrthogonalSubspaces where
  subspace : CandidateAZeroModeSector → Submodule Real E
  cross_orthogonal :
    ∀ {firstSector secondSector : CandidateAZeroModeSector},
      firstSector ≠ secondSector →
      ∀ (first : E), first ∈ subspace firstSector →
      ∀ (second : E), second ∈ subspace secondSector →
        inner Real first second = 0

/-- Sector-local finite modes living in the prescribed physical subspaces. -/
structure CandidateASectorSubspaceModeFamily
    (types : CandidateASectorModeTypes) where
  subspaces : CandidateASectorOrthogonalSubspaces (E := E)
  vectors : CandidateASectorVectorFamily (E := E) types
  vector_mem : ∀ sector mode,
    vectors.vector sector mode ∈ subspaces.subspace sector
  nonzero : ∀ sector mode, vectors.vector sector mode ≠ 0
  within_orthogonal : ∀ sector,
    Pairwise fun first second : types.Mode sector =>
      inner Real (vectors.vector sector first)
        (vectors.vector sector second) = 0

namespace CandidateASectorSubspaceModeFamily

/-- Forget the carrying subspaces after deriving all cross-sector pairings. -/
def toOrthogonalModeFamily
    {types : CandidateASectorModeTypes}
    (family : CandidateASectorSubspaceModeFamily (E := E) types) :
    CandidateASectorOrthogonalModeFamily (E := E) types where
  vectors := family.vectors
  nonzero := family.nonzero
  within_orthogonal := family.within_orthogonal
  cross_orthogonal := by
    intro firstSector secondSector hSector first second
    exact family.subspaces.cross_orthogonal hSector
      (family.vectors.vector firstSector first)
      (family.vector_mem firstSector first)
      (family.vectors.vector secondSector second)
      (family.vector_mem secondSector second)

/-- Cross-sector orthogonality inherited directly from subspace membership. -/
theorem cross_sector_inner_zero
    {types : CandidateASectorModeTypes}
    (family : CandidateASectorSubspaceModeFamily (E := E) types)
    {firstSector secondSector : CandidateAZeroModeSector}
    (hSector : firstSector ≠ secondSector)
    (first : types.Mode firstSector)
    (second : types.Mode secondSector) :
    inner Real (family.vectors.vector firstSector first)
      (family.vectors.vector secondSector second) = 0 :=
  family.subspaces.cross_orthogonal hSector
    (family.vectors.vector firstSector first)
    (family.vector_mem firstSector first)
    (family.vectors.vector secondSector second)
    (family.vector_mem secondSector second)

/-- Public subspace-carried mode checkpoint. -/
theorem candidateA_sector_subspace_mode_gate
    {types : CandidateASectorModeTypes}
    (family : CandidateASectorSubspaceModeFamily (E := E) types) :
    (∀ mode : types.GlobalMode,
      family.vectors.globalVector mode ≠ 0) ∧
      Pairwise (fun first second : types.GlobalMode =>
        inner Real (family.vectors.globalVector first)
          (family.vectors.globalVector second) = 0) :=
  ⟨family.toOrthogonalModeFamily.global_nonzero,
    family.toOrthogonalModeFamily.global_orthogonal⟩

end CandidateASectorSubspaceModeFamily

end
end P0EFTJanusProgramPCandidateASectorSubspaceAssembly4D
end JanusFormal
