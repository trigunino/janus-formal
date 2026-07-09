namespace JanusFormal
namespace P0EFTJanusConformalPTBoundaryMatchingAttemptGate

set_option autoImplicit false

structure ConformalPTBoundaryMatchingAttemptGate where
  FiniteSigmaRadiusRemoved : Prop
  C1ThroatMismatchRemoved : Prop
  ConformalBoundaryClassDeclared : Prop
  PTActionOnConformalClassDeclared : Prop
  ConformalClockLawDerived : Prop
  NativeEarlyHJDerived : Prop
  ActiveBaryonNormalizationDerived : Prop

def ConformalPTBoundaryMatchingClosed
    (g : ConformalPTBoundaryMatchingAttemptGate) : Prop :=
  g.FiniteSigmaRadiusRemoved /\
  g.C1ThroatMismatchRemoved /\
  g.ConformalBoundaryClassDeclared /\
  g.PTActionOnConformalClassDeclared /\
  g.ConformalClockLawDerived /\
  g.NativeEarlyHJDerived /\
  g.ActiveBaryonNormalizationDerived

def ConformalPTBoundaryFrontier
    (g : ConformalPTBoundaryMatchingAttemptGate) : Prop :=
  g.FiniteSigmaRadiusRemoved /\
  g.C1ThroatMismatchRemoved /\
  g.ConformalBoundaryClassDeclared /\
  g.PTActionOnConformalClassDeclared /\
  Not g.ConformalClockLawDerived /\
  Not g.NativeEarlyHJDerived /\
  Not g.ActiveBaryonNormalizationDerived

theorem conformal_boundary_removes_throat_but_not_clock
    (g : ConformalPTBoundaryMatchingAttemptGate)
    (hFrontier : ConformalPTBoundaryFrontier g) :
    Not (ConformalPTBoundaryMatchingClosed g) := by
  intro h
  exact hFrontier.2.2.2.2.1 h.2.2.2.2.1

end P0EFTJanusConformalPTBoundaryMatchingAttemptGate
end JanusFormal
