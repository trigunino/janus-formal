import Mathlib

namespace JanusFormal
namespace P0EFTJanusADMBDConstraintCount

set_option autoImplicit false

/-- Reduced Dirac count for two spatial metrics in four dimensions. -/
def physicalPhaseDimension
    (spatialPhase firstClass secondClass : ℕ) : ℕ :=
  spatialPhase - 2 * firstClass - secondClass

theorem hr_bimetric_phase_dimension :
    physicalPhaseDimension 24 4 2 = 14 := by
  decide

theorem hr_bimetric_configuration_dof :
    physicalPhaseDimension 24 4 2 / 2 = 7 := by
  decide

/-- The conditional bridge deliberately exposes the non-algebraic HR inputs. -/
structure ADMBDInputs where
  realSquareRootBranch : Prop
  shiftRedefinitionLocallyInvertible : Prop
  lapseAffineHamiltonian : Prop
  primaryHamiltonianConstraint : Prop
  independentSecondaryConstraint : Prop
  separateMinimalMatterCoupling : Prop

def bdGhostRemoved (s : ADMBDInputs) : Prop :=
  s.realSquareRootBranch ∧
  s.shiftRedefinitionLocallyInvertible ∧
  s.lapseAffineHamiltonian ∧
  s.primaryHamiltonianConstraint ∧
  s.independentSecondaryConstraint ∧
  s.separateMinimalMatterCoupling

theorem bdGhostRemoved_of_hr_inputs
    (s : ADMBDInputs)
    (hRoot : s.realSquareRootBranch)
    (hShift : s.shiftRedefinitionLocallyInvertible)
    (hAffine : s.lapseAffineHamiltonian)
    (hPrimary : s.primaryHamiltonianConstraint)
    (hSecondary : s.independentSecondaryConstraint)
    (hMatter : s.separateMinimalMatterCoupling) :
    bdGhostRemoved s := by
  exact ⟨hRoot, hShift, hAffine, hPrimary, hSecondary, hMatter⟩

end P0EFTJanusADMBDConstraintCount
end JanusFormal
