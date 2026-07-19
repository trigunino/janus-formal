import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteModeCommonPhysicalGhostHeatRegulator4D

/-!
# Finite-mode determinant with multiplicity and statistics

This gate applies the finite heat-regulator statistics labels to the existing
finite Fourier determinant.  In the heat-supertrace convention used here,
bosonic labels give a positive determinant power and fermionic or ghost labels
give its reciprocal.  The reciprocal is certified only on the existing
nonvanishing unit holonomy disk.

There is no cutoff limit, global Janus determinant, Quillen identification or
claim about Gaussian half-powers.
-/

namespace JanusFormal
namespace P0EFTJanusFiniteModeStatisticalDeterminant4D

open P0EFTJanusFiniteModeFredholmDeterminantLine
open P0EFTJanusFiniteModeCommonPhysicalGhostHeatRegulator4D

set_option autoImplicit false

noncomputable section

/-- Multiplicity-weighted determinant in the finite heat-supertrace convention. -/
def weightedCutoffDeterminant
    (statistics : FieldStatistics) (multiplicity cutoff : ℕ) (z : ℂ) : ℂ :=
  match statistics with
  | .bosonic => (cutoffDeterminant cutoff z) ^ multiplicity
  | .fermionic => ((cutoffDeterminant cutoff z) ^ multiplicity)⁻¹
  | .ghost => ((cutoffDeterminant cutoff z) ^ multiplicity)⁻¹

@[simp] theorem weightedCutoffDeterminant_bosonic
    (multiplicity cutoff : ℕ) (z : ℂ) :
    weightedCutoffDeterminant .bosonic multiplicity cutoff z =
      (cutoffDeterminant cutoff z) ^ multiplicity := rfl

@[simp] theorem weightedCutoffDeterminant_fermionic
    (multiplicity cutoff : ℕ) (z : ℂ) :
    weightedCutoffDeterminant .fermionic multiplicity cutoff z =
      ((cutoffDeterminant cutoff z) ^ multiplicity)⁻¹ := rfl

@[simp] theorem weightedCutoffDeterminant_ghost
    (multiplicity cutoff : ℕ) (z : ℂ) :
    weightedCutoffDeterminant .ghost multiplicity cutoff z =
      ((cutoffDeterminant cutoff z) ^ multiplicity)⁻¹ := rfl

/-- Multiplicities add by multiplication of their finite determinant factors. -/
theorem weightedCutoffDeterminant_add_multiplicity
    (statistics : FieldStatistics) (first second cutoff : ℕ) (z : ℂ) :
    weightedCutoffDeterminant statistics (first + second) cutoff z =
      weightedCutoffDeterminant statistics first cutoff z *
        weightedCutoffDeterminant statistics second cutoff z := by
  cases statistics <;> simp [weightedCutoffDeterminant, pow_add, mul_comm]

/-- PT invariance survives every finite multiplicity and statistics label. -/
theorem weightedCutoffDeterminant_pt_invariant
    (statistics : FieldStatistics) (multiplicity cutoff : ℕ) (z : ℂ) :
    weightedCutoffDeterminant statistics multiplicity cutoff (-z) =
      weightedCutoffDeterminant statistics multiplicity cutoff z := by
  cases statistics <;>
    simp [weightedCutoffDeterminant, cutoffDeterminant_pt_invariant]

/-- On the existing unit disk, every weighted finite determinant is nonzero. -/
theorem weightedCutoffDeterminant_ne_zero_of_norm_lt_one
    (statistics : FieldStatistics) (multiplicity cutoff : ℕ) {z : ℂ}
    (hz : ‖z‖ < 1) :
    weightedCutoffDeterminant statistics multiplicity cutoff z ≠ 0 := by
  have hDet : cutoffDeterminant cutoff z ≠ 0 :=
    cutoffDeterminant_ne_zero_of_norm_lt_one cutoff hz
  cases statistics
  · exact pow_ne_zero _ hDet
  · exact inv_ne_zero (pow_ne_zero _ hDet)
  · exact inv_ne_zero (pow_ne_zero _ hDet)

end

end P0EFTJanusFiniteModeStatisticalDeterminant4D
end JanusFormal
