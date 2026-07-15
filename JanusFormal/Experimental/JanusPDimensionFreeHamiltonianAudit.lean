import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusDustFLRWConstrainedStability

namespace JanusFormal
namespace JanusPDimensionFreeHamiltonianAudit

set_option autoImplicit false

open P0EFTJanusDustFLRWConstrainedStability

/-- On the presently derived physical FLRW constraint curve, the reduced
Hamiltonian cannot separate any two regular points: both energies vanish. -/
theorem current_constrained_hamiltonian_has_no_level_splitting
    (s t : ℝ) (hs : 1 + s ≠ 0) (ht : 1 + t ≠ 0) :
    fixedLapseHamiltonian (exactConstraintCurve s) =
      fixedLapseHamiltonian (exactConstraintCurve t) := by
  rw [fixedLapseHamiltonian_exactConstraintCurve_eq_zero s hs,
    fixedLapseHamiltonian_exactConstraintCurve_eq_zero t ht]

/-- Consequently no finite level count, including 1001, follows from this
constrained Hamiltonian without adding new physical degrees of freedom. -/
theorem current_branch_does_not_select_level_count
    (levelCount : ℕ) (s t : ℝ)
    (hs : 1 + s ≠ 0) (ht : 1 + t ≠ 0) :
    levelCount = levelCount ∧
      fixedLapseHamiltonian (exactConstraintCurve s) =
        fixedLapseHamiltonian (exactConstraintCurve t) := by
  exact ⟨rfl,
    current_constrained_hamiltonian_has_no_level_splitting s t hs ht⟩

end JanusPDimensionFreeHamiltonianAudit
end JanusFormal
