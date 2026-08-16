import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiveSectorOrthogonalProductResolution4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPCandidateASectorSubspaceAssembly4D

/-!
# Candidate-A sector subspaces from one orthogonal five-sector coordinate system

Once the common Hilbert space carries one effective orthogonal coordinate
decomposition, the five physical subspaces are canonical: they are the ranges
of the transported coordinate projectors.  This adapter therefore removes both
five separately supplied subspaces and every cross-sector mode-pairing premise.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPCandidateASectorCoordinateSubspaces4D

set_option autoImplicit false
noncomputable section

open scoped InnerProductSpace
open P0EFTJanusProgramPFiveSectorOrthogonalProductResolution4D
open P0EFTJanusProgramPCandidateASectorSubspaceAssembly4D
open P0EFTJanusProgramPGlobalCandidateANamedZeroModeSectors4D

variable {E Metric Abelian Matter Longitudinal Boundary : Type*}
  [NormedAddCommGroup E] [InnerProductSpace Real E]
  [NormedAddCommGroup Metric] [InnerProductSpace Real Metric]
  [NormedAddCommGroup Abelian] [InnerProductSpace Real Abelian]
  [NormedAddCommGroup Matter] [InnerProductSpace Real Matter]
  [NormedAddCommGroup Longitudinal] [InnerProductSpace Real Longitudinal]
  [NormedAddCommGroup Boundary] [InnerProductSpace Real Boundary]

/-- Canonical identification of the zero-mode and coordinate sector labels. -/
def candidateAZeroModeSectorToFiveSectorSlot :
    CandidateAZeroModeSector → FiveSectorSlot
  | .metricDiffeomorphism => .metricDiffeomorphism
  | .abelianGauge => .abelianGauge
  | .primitiveSpinCMatter => .primitiveSpinCMatter
  | .longitudinalLL => .longitudinalLL
  | .boundaryFiniteBV => .boundaryFiniteBV

private theorem candidateAZeroModeSectorToFiveSectorSlot_injective :
    Function.Injective candidateAZeroModeSectorToFiveSectorSlot := by
  intro first second h
  cases first <;> cases second <;> simp_all [candidateAZeroModeSectorToFiveSectorSlot]

/-- The five physical subspaces are exactly the five projector ranges generated
by the single orthogonal coordinate decomposition. -/
def candidateASectorCoordinateSubspaces
    (coordinates : FiveSectorOrthogonalProductDecomposition
      (E := E) (MetricDiffeomorphism := Metric) (AbelianGauge := Abelian)
      (PrimitiveSpinCMatter := Matter) (LongitudinalLL := Longitudinal)
      (BoundaryFiniteBV := Boundary)) :
    CandidateASectorOrthogonalSubspaces (E := E) where
  subspace := fun sector =>
    (coordinates.projection
      (candidateAZeroModeSectorToFiveSectorSlot sector)).range
  cross_orthogonal := by
    intro firstSector secondSector hDistinct first hFirst second hSecond
    rcases hFirst with ⟨firstSource, rfl⟩
    rcases hSecond with ⟨secondSource, rfl⟩
    exact coordinates.projection_orthogonal
      (candidateAZeroModeSectorToFiveSectorSlot firstSector)
      (candidateAZeroModeSectorToFiveSectorSlot secondSector)
      (fun h => hDistinct
        (candidateAZeroModeSectorToFiveSectorSlot_injective h))
      firstSource secondSource

/-- Sector-local finite modes carried by the canonical coordinate ranges.  Only
membership, nonvanishing and within-sector orthogonality remain. -/
structure CandidateASectorCoordinateModeFamily
    (coordinates : FiveSectorOrthogonalProductDecomposition
      (E := E) (MetricDiffeomorphism := Metric) (AbelianGauge := Abelian)
      (PrimitiveSpinCMatter := Matter) (LongitudinalLL := Longitudinal)
      (BoundaryFiniteBV := Boundary))
    (types : CandidateASectorModeTypes) where
  vectors : CandidateASectorVectorFamily (E := E) types
  vector_mem : ∀ sector mode,
    vectors.vector sector mode ∈
      (coordinates.projection
        (candidateAZeroModeSectorToFiveSectorSlot sector)).range
  nonzero : ∀ sector mode, vectors.vector sector mode ≠ 0
  within_orthogonal : ∀ sector,
    Pairwise fun first second : types.Mode sector =>
      inner Real (vectors.vector sector first)
        (vectors.vector sector second) = 0

/-- Convert coordinate-carried modes to the established physical-subspace
interface. -/
def CandidateASectorCoordinateModeFamily.toSubspaceModeFamily
    {types : CandidateASectorModeTypes}
    {coordinates : FiveSectorOrthogonalProductDecomposition
      (E := E) (MetricDiffeomorphism := Metric) (AbelianGauge := Abelian)
      (PrimitiveSpinCMatter := Matter) (LongitudinalLL := Longitudinal)
      (BoundaryFiniteBV := Boundary)}
    (family : CandidateASectorCoordinateModeFamily coordinates types) :
    CandidateASectorSubspaceModeFamily (E := E) types where
  subspaces := candidateASectorCoordinateSubspaces coordinates
  vectors := family.vectors
  vector_mem := family.vector_mem
  nonzero := family.nonzero
  within_orthogonal := family.within_orthogonal

/-- Global nonvanishing and orthogonality are now consequences of one Hilbert
coordinate decomposition and within-sector orthogonality. -/
theorem candidateA_sector_coordinate_mode_gate
    {types : CandidateASectorModeTypes}
    {coordinates : FiveSectorOrthogonalProductDecomposition
      (E := E) (MetricDiffeomorphism := Metric) (AbelianGauge := Abelian)
      (PrimitiveSpinCMatter := Matter) (LongitudinalLL := Longitudinal)
      (BoundaryFiniteBV := Boundary)}
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
