namespace JanusFormal
namespace P0EFTObservationalStatusVerdict

set_option autoImplicit false

structure ObservationalStatusVerdict where
  formalJanusOrbifoldClosed : Prop
  lateTimeGrowthViable : Prop
  cmbSimpleBranchExcluded : Prop
  newCoupledPrimordialSectorDerived : Prop

def formalClosureDoesNotImplyObservationPass (v : ObservationalStatusVerdict) : Prop :=
  v.formalJanusOrbifoldClosed /\
  v.cmbSimpleBranchExcluded

def fullObservationalCosmologyPasses (v : ObservationalStatusVerdict) : Prop :=
  v.formalJanusOrbifoldClosed /\
  v.lateTimeGrowthViable /\
  Not v.cmbSimpleBranchExcluded /\
  v.newCoupledPrimordialSectorDerived

theorem planck_exclusion_blocks_full_observational_pass
    (v : ObservationalStatusVerdict)
    (_hFormal : v.formalJanusOrbifoldClosed)
    (hCMB : v.cmbSimpleBranchExcluded) :
    Not (fullObservationalCosmologyPasses v) := by
  intro h
  exact h.right.right.left hCMB

theorem formal_closure_and_cmb_exclusion_can_coexist
    (v : ObservationalStatusVerdict)
    (hFormal : v.formalJanusOrbifoldClosed)
    (hCMB : v.cmbSimpleBranchExcluded) :
    formalClosureDoesNotImplyObservationPass v := by
  exact And.intro hFormal hCMB

end P0EFTObservationalStatusVerdict
end JanusFormal
