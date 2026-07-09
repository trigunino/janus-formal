import JanusFormal.Branches.Z4HistoricalProgram.Gates.P0EFTJanusZ4TensorOperatorContract

namespace JanusFormal
namespace P0EFTJanusZ4ScalarPerturbationSystem

set_option autoImplicit false

structure ScalarPerturbationSystem where
  rankOneMasterSourceImported : Prop
  backgroundConstraintFromMaster : Prop
  poissonConstraintFromMaster : Prop
  slipEquationDeclared : Prop
  continuityEulerTargetsDeclared : Prop
  bianchiClosureRequired : Prop
  zeroCouplingGRLimitDeclared : Prop
  fullBoltzmannHierarchyDerived : Prop

def scalarSystemScaffoldReady (s : ScalarPerturbationSystem) : Prop :=
  s.rankOneMasterSourceImported /\
  s.backgroundConstraintFromMaster /\
  s.poissonConstraintFromMaster /\
  s.slipEquationDeclared /\
  s.continuityEulerTargetsDeclared /\
  s.bianchiClosureRequired /\
  s.zeroCouplingGRLimitDeclared

def scalarSystemPhysicalReady (s : ScalarPerturbationSystem) : Prop :=
  scalarSystemScaffoldReady s /\
  s.fullBoltzmannHierarchyDerived

theorem scalar_scaffold_does_not_imply_full_boltzmann
    (s : ScalarPerturbationSystem)
    (_h : scalarSystemScaffoldReady s)
    (hMissing : Not s.fullBoltzmannHierarchyDerived) :
    Not (scalarSystemPhysicalReady s) := by
  intro h
  exact hMissing h.right

end P0EFTJanusZ4ScalarPerturbationSystem
end JanusFormal
