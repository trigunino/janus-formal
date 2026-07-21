import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteModeStatisticalDeterminant4D

/-!
# Finite product of weighted cutoff determinants

For one fixed finite mode type, this gate multiplies the already defined
weighted cutoff factor associated with each sector's multiplicity and
statistics.  All factors use the same cutoff and holonomy.  The sector
spectrum is retained in the ledger but the existing cutoff determinant depends
only on the common cutoff.  No cutoff limit or global determinant is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusFiniteModeStatisticalDeterminantProduct4D

open P0EFTJanusFiniteModeCommonPhysicalGhostHeatRegulator4D
open P0EFTJanusFiniteModeStatisticalDeterminant4D

set_option autoImplicit false

noncomputable section

/-- Product of the weighted determinant factors of a finite sector ledger. -/
def weightedCutoffDeterminantProduct
    {Mode : Type*} [Fintype Mode]
    (cutoff : ℕ) (z : ℂ) (sectors : List (WeightedSector Mode)) : ℂ :=
  (sectors.map fun sector =>
    weightedCutoffDeterminant sector.statistics sector.multiplicity cutoff z).prod

@[simp] theorem weightedCutoffDeterminantProduct_nil
    {Mode : Type*} [Fintype Mode] (cutoff : ℕ) (z : ℂ) :
    weightedCutoffDeterminantProduct (Mode := Mode) cutoff z [] = 1 := rfl

/-- Concatenating ledgers multiplies their finite determinant products. -/
theorem weightedCutoffDeterminantProduct_append
    {Mode : Type*} [Fintype Mode]
    (cutoff : ℕ) (z : ℂ)
    (first second : List (WeightedSector Mode)) :
    weightedCutoffDeterminantProduct cutoff z (first ++ second) =
      weightedCutoffDeterminantProduct cutoff z first *
        weightedCutoffDeterminantProduct cutoff z second := by
  simp [weightedCutoffDeterminantProduct, List.map_append, List.prod_append]

/-- PT invariance holds simultaneously for every factor in the ledger. -/
theorem weightedCutoffDeterminantProduct_pt_invariant
    {Mode : Type*} [Fintype Mode]
    (cutoff : ℕ) (z : ℂ) (sectors : List (WeightedSector Mode)) :
    weightedCutoffDeterminantProduct cutoff (-z) sectors =
      weightedCutoffDeterminantProduct cutoff z sectors := by
  simp [weightedCutoffDeterminantProduct,
    weightedCutoffDeterminant_pt_invariant]

/-- On the controlled unit disk every factor, hence the finite product, is
nonzero.  The factorwise certificate is exhibited explicitly in the proof. -/
theorem weightedCutoffDeterminantProduct_ne_zero_of_norm_lt_one
    {Mode : Type*} [Fintype Mode]
    (cutoff : ℕ) {z : ℂ} (sectors : List (WeightedSector Mode))
    (hz : ‖z‖ < 1) :
    weightedCutoffDeterminantProduct cutoff z sectors ≠ 0 := by
  induction sectors with
  | nil => simp [weightedCutoffDeterminantProduct]
  | cons sector sectors inductionHypothesis =>
      simp only [weightedCutoffDeterminantProduct, List.map_cons, List.prod_cons]
      exact mul_ne_zero
        (weightedCutoffDeterminant_ne_zero_of_norm_lt_one
          sector.statistics sector.multiplicity cutoff hz)
        inductionHypothesis

end

end P0EFTJanusFiniteModeStatisticalDeterminantProduct4D
end JanusFormal
