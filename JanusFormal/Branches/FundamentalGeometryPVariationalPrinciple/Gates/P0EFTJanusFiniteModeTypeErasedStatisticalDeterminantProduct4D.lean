import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteModeTypeErasedCommonRegulator4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteModeStatisticalDeterminant4D

/-!
# Type-erased heterogeneous finite determinant product

Every ledger entry retains an actual finite mode type and `WeightedSector`.
The existing weighted cutoff determinant uses its multiplicity and statistics,
with one common cutoff and holonomy for the whole ledger.  The retained
spectrum is not an argument of that existing determinant.  No cutoff limit or
global determinant is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusFiniteModeTypeErasedStatisticalDeterminantProduct4D

open P0EFTJanusFiniteModeTypeErasedCommonRegulator4D
open P0EFTJanusFiniteModeStatisticalDeterminant4D

set_option autoImplicit false

noncomputable section

/-- Weighted cutoff determinant read from one genuine erased sector. -/
def erasedCutoffDeterminantFactor
    (cutoff : ℕ) (z : ℂ) (erased : ErasedWeightedSector) : ℂ :=
  weightedCutoffDeterminant erased.sector.statistics
    erased.sector.multiplicity cutoff z

theorem erasedCutoffDeterminantFactor_pt_invariant
    (cutoff : ℕ) (z : ℂ) (erased : ErasedWeightedSector) :
    erasedCutoffDeterminantFactor cutoff (-z) erased =
      erasedCutoffDeterminantFactor cutoff z erased := by
  exact weightedCutoffDeterminant_pt_invariant
    erased.sector.statistics erased.sector.multiplicity cutoff z

/-- Finite product over sectors whose finite mode types may differ. -/
def heterogeneousWeightedCutoffDeterminantProduct
    (cutoff : ℕ) (z : ℂ) (sectors : List ErasedWeightedSector) : ℂ :=
  (sectors.map (erasedCutoffDeterminantFactor cutoff z)).prod

@[simp] theorem heterogeneousWeightedCutoffDeterminantProduct_nil
    (cutoff : ℕ) (z : ℂ) :
    heterogeneousWeightedCutoffDeterminantProduct cutoff z [] = 1 := rfl

/-- Concatenation is multiplication for the same cutoff and holonomy. -/
theorem heterogeneousWeightedCutoffDeterminantProduct_append
    (cutoff : ℕ) (z : ℂ)
    (first second : List ErasedWeightedSector) :
    heterogeneousWeightedCutoffDeterminantProduct cutoff z (first ++ second) =
      heterogeneousWeightedCutoffDeterminantProduct cutoff z first *
        heterogeneousWeightedCutoffDeterminantProduct cutoff z second := by
  simp [heterogeneousWeightedCutoffDeterminantProduct, List.map_append,
    List.prod_append]

/-- Factorwise PT invariance survives the heterogeneous finite product. -/
theorem heterogeneousWeightedCutoffDeterminantProduct_pt_invariant
    (cutoff : ℕ) (z : ℂ) (sectors : List ErasedWeightedSector) :
    heterogeneousWeightedCutoffDeterminantProduct cutoff (-z) sectors =
      heterogeneousWeightedCutoffDeterminantProduct cutoff z sectors := by
  induction sectors with
  | nil => rfl
  | cons sector sectors inductionHypothesis =>
      change
        erasedCutoffDeterminantFactor cutoff (-z) sector *
            heterogeneousWeightedCutoffDeterminantProduct cutoff (-z) sectors =
          erasedCutoffDeterminantFactor cutoff z sector *
            heterogeneousWeightedCutoffDeterminantProduct cutoff z sectors
      rw [erasedCutoffDeterminantFactor_pt_invariant,
        inductionHypothesis]

/-- The controlled disk makes every genuine sector factor, hence their finite
heterogeneous product, nonzero. -/
theorem heterogeneousWeightedCutoffDeterminantProduct_ne_zero_of_norm_lt_one
    (cutoff : ℕ) {z : ℂ} (sectors : List ErasedWeightedSector)
    (hz : ‖z‖ < 1) :
    heterogeneousWeightedCutoffDeterminantProduct cutoff z sectors ≠ 0 := by
  induction sectors with
  | nil => simp [heterogeneousWeightedCutoffDeterminantProduct]
  | cons sector sectors inductionHypothesis =>
      simp only [heterogeneousWeightedCutoffDeterminantProduct, List.map_cons,
        List.prod_cons]
      exact mul_ne_zero
        (weightedCutoffDeterminant_ne_zero_of_norm_lt_one
          sector.sector.statistics sector.sector.multiplicity cutoff hz)
        inductionHypothesis

end

end P0EFTJanusFiniteModeTypeErasedStatisticalDeterminantProduct4D
end JanusFormal
