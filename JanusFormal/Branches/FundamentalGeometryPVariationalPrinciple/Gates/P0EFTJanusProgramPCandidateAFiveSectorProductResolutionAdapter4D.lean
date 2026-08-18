import Mathlib.Tactic
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiveSectorOrthogonalProductResolution4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteSelfAdjointProjectionResolution4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANamedZeroModeSectors4D

/-!
# Candidate-A projection resolution from one five-factor orthogonal product

The generic Candidate-A Gårding chain consumes a finite self-adjoint projection
resolution indexed by `CandidateAZeroModeSector`.  The more concrete coordinate
layer naturally produces the same five projectors from one right-associated
orthogonal product decomposition.

This adapter identifies the two finite sector labels and converts the one
coordinate decomposition directly into the exact projection-resolution packet.
No dependent Pi-space coordinate reconstruction is required.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPCandidateAFiveSectorProductResolutionAdapter4D

set_option autoImplicit false
noncomputable section

open scoped BigOperators InnerProductSpace
open P0EFTJanusProgramPFiveSectorOrthogonalProductResolution4D
open P0EFTJanusProgramPFiniteSelfAdjointProjectionResolution4D
open P0EFTJanusProgramPGlobalCandidateANamedZeroModeSectors4D
open P0EFTJanusProgramPCandidateAZeroModeSector4D

variable
  {E Metric Abelian Matter Longitudinal Boundary : Type*}
  [NormedAddCommGroup E] [InnerProductSpace Real E]
  [NormedAddCommGroup Metric] [InnerProductSpace Real Metric]
  [NormedAddCommGroup Abelian] [InnerProductSpace Real Abelian]
  [NormedAddCommGroup Matter] [InnerProductSpace Real Matter]
  [NormedAddCommGroup Longitudinal] [InnerProductSpace Real Longitudinal]
  [NormedAddCommGroup Boundary] [InnerProductSpace Real Boundary]

/-- Canonical label identification. -/
def candidateASectorToFiveSlot : CandidateAZeroModeSector → FiveSectorSlot
  | .metricDiffeomorphism => .metricDiffeomorphism
  | .abelianGauge => .abelianGauge
  | .primitiveSpinCMatter => .primitiveSpinCMatter
  | .longitudinalLL => .longitudinalLL
  | .boundaryFiniteBV => .boundaryFiniteBV

private theorem candidateA_sector_univ :
    (Finset.univ : Finset CandidateAZeroModeSector) =
      { .metricDiffeomorphism, .abelianGauge, .primitiveSpinCMatter,
        .longitudinalLL, .boundaryFiniteBV } := by
  decide

private theorem five_slot_univ :
    (Finset.univ : Finset FiveSectorSlot) =
      { .metricDiffeomorphism, .abelianGauge, .primitiveSpinCMatter,
        .longitudinalLL, .boundaryFiniteBV } := by
  decide

/-- Convert the concrete five-factor orthogonal decomposition into the exact
Candidate-A self-adjoint projection resolution. -/
def candidateAFiveSectorSelfAdjointResolutionOfProduct
    (coordinates : FiveSectorOrthogonalProductDecomposition
      (E := E) (MetricDiffeomorphism := Metric) (AbelianGauge := Abelian)
      (PrimitiveSpinCMatter := Matter) (LongitudinalLL := Longitudinal)
      (BoundaryFiniteBV := Boundary)) :
    FiniteSelfAdjointProjectionResolutionData
      (Sector := CandidateAZeroModeSector) (E := E) where
  projection := fun sector => coordinates.projection (candidateASectorToFiveSlot sector)
  sum_projection := by
    intro vector
    rw [candidateA_sector_univ]
    simpa [candidateASectorToFiveSlot, five_slot_univ] using
      coordinates.sum_projection_apply vector
  projection_idempotent := by
    intro sector vector
    exact coordinates.projection_idempotent (candidateASectorToFiveSlot sector)
      vector
  projection_symmetric := by
    intro sector first second
    exact coordinates.projection_selfAdjoint (candidateASectorToFiveSlot sector)
      first second

/-- All Candidate-A projection laws and the Pythagorean norm identity are now
outputs of one five-factor coordinate decomposition. -/
theorem candidateA_five_sector_product_resolution_gate
    (coordinates : FiveSectorOrthogonalProductDecomposition
      (E := E) (MetricDiffeomorphism := Metric) (AbelianGauge := Abelian)
      (PrimitiveSpinCMatter := Matter) (LongitudinalLL := Longitudinal)
      (BoundaryFiniteBV := Boundary)) :
    let resolution := candidateAFiveSectorSelfAdjointResolutionOfProduct coordinates
    (∀ vector,
      (∑ sector : CandidateAZeroModeSector,
        resolution.projection sector vector) = vector) ∧
    (∀ sector vector,
      resolution.projection sector (resolution.projection sector vector) =
        resolution.projection sector vector) ∧
    (∀ sector first second,
      inner Real (resolution.projection sector first) second =
        inner Real first (resolution.projection sector second)) ∧
    (∀ vector,
      ‖vector‖ ^ 2 =
        ∑ sector : CandidateAZeroModeSector,
          ‖resolution.projection sector vector‖ ^ 2) := by
  dsimp only
  let resolution := candidateAFiveSectorSelfAdjointResolutionOfProduct coordinates
  exact
    ⟨resolution.sum_projection,
      resolution.projection_idempotent,
      resolution.projection_symmetric,
      resolution.norm_sq_decomposition⟩

end
end P0EFTJanusProgramPCandidateAFiveSectorProductResolutionAdapter4D
end JanusFormal
