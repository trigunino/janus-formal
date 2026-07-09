import JanusFormal.Branches.P0EFTOrbifoldHolstPrototypeProgram.Gates.P0EFTAnisotropicPiScan

namespace JanusFormal
namespace P0EFTSpinorTorsionCoupling

set_option autoImplicit false

structure SpinorTorsionCoupling where
  diracSpinCurrentIncluded : Prop
  cartanEquationSolvedForSpinContorsion : Prop
  sciamaKibbleRhoSquaredTermEncoded : Prop
  spinorBranchesScored : Prop
  physicalSpinorBranchFound : Prop
  unitAmplitudeCriterionPassed : Prop
  spinCoefficientDerivedFromFermionSector : Prop

def spinorTorsionRunStructured (s : SpinorTorsionCoupling) : Prop :=
  s.diracSpinCurrentIncluded /\
  s.cartanEquationSolvedForSpinContorsion /\
  s.sciamaKibbleRhoSquaredTermEncoded /\
  s.spinorBranchesScored

def spinorNoFitCandidateReady (s : SpinorTorsionCoupling) : Prop :=
  spinorTorsionRunStructured s /\
  s.physicalSpinorBranchFound /\
  s.unitAmplitudeCriterionPassed /\
  s.spinCoefficientDerivedFromFermionSector

theorem spinor_torsion_run_is_structured
    (s : SpinorTorsionCoupling)
    (hSpin : s.diracSpinCurrentIncluded)
    (hCartan : s.cartanEquationSolvedForSpinContorsion)
    (hRho2 : s.sciamaKibbleRhoSquaredTermEncoded)
    (hScan : s.spinorBranchesScored) :
    spinorTorsionRunStructured s := by
  exact And.intro hSpin (And.intro hCartan (And.intro hRho2 hScan))

theorem underived_spin_coefficient_blocks_no_fit_candidate
    (s : SpinorTorsionCoupling)
    (hMissing : Not s.spinCoefficientDerivedFromFermionSector) :
    Not (spinorNoFitCandidateReady s) := by
  intro h
  exact hMissing h.right.right.right

end P0EFTSpinorTorsionCoupling
end JanusFormal
