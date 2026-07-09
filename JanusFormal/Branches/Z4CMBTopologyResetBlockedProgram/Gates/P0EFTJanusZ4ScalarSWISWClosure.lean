import JanusFormal.Branches.Z4CMBTopologyResetBlockedProgram.Gates.P0EFTJanusZ4ScalarSourceScan
import JanusFormal.Branches.Z4CMBTopologyResetBlockedProgram.Gates.P0EFTJanusZ4ScalarActionDerivation

namespace JanusFormal
namespace P0EFTJanusZ4ScalarSWISWClosure

set_option autoImplicit false

structure ScalarSWISWClosure where
  poissonResidualDeclared : Prop
  momentumResidualDeclared : Prop
  slipResidualDeclared : Prop
  iswSourceDeclared : Prop
  bianchiResidualDeclared : Prop
  conditionalPartialClosureVerified : Prop
  poissonMomentumCoefficientsDerived : Prop
  actionCoefficientsDerived : Prop

def scalarSWISWScaffoldReady (s : ScalarSWISWClosure) : Prop :=
  s.poissonResidualDeclared /\
  s.momentumResidualDeclared /\
  s.slipResidualDeclared /\
  s.iswSourceDeclared /\
  s.bianchiResidualDeclared

def scalarSWISWPartiallyClosed (s : ScalarSWISWClosure) : Prop :=
  scalarSWISWScaffoldReady s /\ s.conditionalPartialClosureVerified

def scalarSWISWPhysicalReady (s : ScalarSWISWClosure) : Prop :=
  scalarSWISWPartiallyClosed s /\
  s.poissonMomentumCoefficientsDerived /\
  s.actionCoefficientsDerived

theorem scalar_swisw_scaffold_does_not_close_physics
    (s : ScalarSWISWClosure)
    (_h : scalarSWISWScaffoldReady s)
    (hMissing : Not s.actionCoefficientsDerived) :
    Not (scalarSWISWPhysicalReady s) := by
  intro h
  exact hMissing h.right.right

theorem scalar_swisw_partial_closure_does_not_close_physics
    (s : ScalarSWISWClosure)
    (_h : scalarSWISWPartiallyClosed s)
    (hMissing : Not s.poissonMomentumCoefficientsDerived) :
    Not (scalarSWISWPhysicalReady s) := by
  intro h
  exact hMissing h.right.left

theorem scalar_action_derivation_feeds_swisw_lock
    (s : ScalarSWISWClosure)
    (a : P0EFTJanusZ4ScalarActionDerivation.ScalarActionDerivation)
    (hPartial : scalarSWISWPartiallyClosed s)
    (hAction : P0EFTJanusZ4ScalarActionDerivation.scalarActionDerivedReady a)
    (hTransport :
      P0EFTJanusZ4ScalarActionDerivation.scalarActionDerivedReady a ->
        s.poissonMomentumCoefficientsDerived /\ s.actionCoefficientsDerived) :
    scalarSWISWPhysicalReady s := by
  exact And.intro hPartial (hTransport hAction)

end P0EFTJanusZ4ScalarSWISWClosure
end JanusFormal
