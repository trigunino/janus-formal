import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiveSectorHilbertCoordinates4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPCandidateASectorSubspaceAssembly4D

/-!
# Candidate-A sector subspaces from one five-sector Hilbert coordinate system

The finite mode assembly previously accepted five orthogonal subspaces as an
independent packet.  Once the common Hilbert space has one genuine five-sector
coordinate decomposition, those subspaces are canonical: they are the ranges
of the five coordinate projectors.

This adapter removes both the separate subspace choices and every cross-sector
orthogonality premise from the zero-mode input.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPCandidateASectorCoordinateSubspaces4D

set_option autoImplicit false
noncomputable section

open scoped InnerProductSpace
open P0EFTJanusProgramPFiveSectorHilbertCoordinates4D
open P0EFTJanusProgramPCandidateASectorSubspaceAssembly4D
open P0EFTJanusProgramPGlobalCandidateANamedZeroModeSectors4D

variable {E Metric Abelian Matter Longitudinal Boundary : Type*}
  [NormedAddCommGroup E] [InnerProductSpace Real E]
  [NormedAddCommGroup Metric] [InnerProductSpace Real Metric]
  [NormedAddCommGroup Abelian] [InnerProductSpace Real Abelian]
  [NormedAddCommGroup Matter] [InnerProductSpace Real Matter]
  [NormedAddCommGroup Longitudinal] [InnerProductSpace Real Longitudinal]
  [NormedAddCommGroup Boundary] [InnerProductSpace Real Boundary]

/-- Canonical identification of the two five-sector label types used by the
coordinate and zero-mode layers. -/
def candidateAZeroModeSectorToFivePhysicalSector :
    CandidateAZeroModeSector → FivePhysicalSector
  | .metricDiffeomorphism => .metricDiffeomorphism
  | .abelianGauge => .abelianGauge
  | .primitiveSpinCMatter => .primitiveSpinCMatter
  | .longitudinalLL => .longitudinalLL
  | .boundaryFiniteBV => .boundaryFiniteBV

/-- The five physical subspaces are the ranges of the coordinate projectors. -/
def candidateASectorCoordinateSubspaces
    (coordinates : FiveSectorHilbertCoordinates
      (E := E) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary)) :
    CandidateASectorOrthogonalSubspaces (E := E) where
  subspace := fun sector =>
    coordinates.sectorSubspace (candidateAZeroModeSectorToFivePhysicalSector sector)
  cross_orthogonal := by
    intro firstSector secondSector hDistinct first hFirst second hSecond
    let firstSlot := candidateAZeroModeSectorToFivePhysicalSector firstSector
    let secondSlot := candidateAZeroModeSectorToFivePhysicalSector secondSector
    have hSlot : firstSlot ≠ secondSlot := by
      intro hEq
      cases firstSector <;> cases secondSector <;> simp_all
    rcases hFirst with ⟨firstSource, rfl⟩
    rcases hSecond with ⟨secondSource, rfl⟩
    have hSelf := coordinates.sectorProjector_idempotent firstSlot firstSource
    have hCross := coordinates.sectorProjector_comp_zero hSlot secondSource
    rw [← hSelf]
    rw [← coordinates.decomposition.inner_map]
    rw [hCross]
    simp

/-- A sector-local vector family carried by the canonical coordinate ranges.
Only membership, nonvanishing and within-sector orthogonality remain. -/
structure CandidateASectorCoordinateModeFamily
    (coordinates : FiveSectorHilbertCoordinates
      (E := E) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary))
    (types : CandidateASectorModeTypes) where
  vectors : CandidateASectorVectorFamily (E := E) types
  vector_mem : ∀ sector mode,
    vectors.vector sector mode ∈
      coordinates.sectorSubspace
        (candidateAZeroModeSectorToFivePhysicalSector sector)
  nonzero : ∀ sector mode, vectors.vector sector mode ≠ 0
  within_orthogonal : ∀ sector,
    Pairwise fun first second : types.Mode sector =>
      inner Real (vectors.vector sector first)
        (vectors.vector sector second) = 0

/-- Forget the coordinate implementation after constructing the exact physical
subspace packet. -/
def CandidateASectorCoordinateModeFamily.toSubspaceModeFamily
    {types : CandidateASectorModeTypes}
    {coordinates : FiveSectorHilbertCoordinates
      (E := E) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary)}
    (family : CandidateASectorCoordinateModeFamily coordinates types) :
    CandidateASectorSubspaceModeFamily (E := E) types where
  subspaces := candidateASectorCoordinateSubspaces coordinates
  vectors := family.vectors
  vector_mem := family.vector_mem
  nonzero := family.nonzero
  within_orthogonal := family.within_orthogonal

/-- Public checkpoint: one Hilbert coordinate decomposition carries all five
mode sectors and produces global orthogonality. -/
theorem candidateA_sector_coordinate_mode_gate
    {types : CandidateASectorModeTypes}
    {coordinates : FiveSectorHilbertCoordinates
      (E := E) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary)}
    (family : CandidateASectorCoordinateModeFamily coordinates types) :
    (∀ mode : types.GlobalMode,
      family.vectors.globalVector mode ≠ 0) ∧
      Pairwise (fun first second : types.GlobalMode =>
        inner Real (family.vectors.globalVector first)
          (family.vectors.globalVector second) = 0) :=
  family.toSubspaceModeFamily.candidateA_sector_subspace_mode_gate

end
end P0EFTJanusProgramPCandidateASectorCoordinateSubspaces4D
end JanusFormal
