namespace JanusFormal
namespace P0EFTJanusWeylCuspLateSNMatchingBoundaryConditionsGate

set_option autoImplicit false

structure WeylCuspLateSNMatchingBoundaryConditionsGate where
  LateSNBranchPreservedConditionDeclared : Prop
  PTCuspConditionDeclared : Prop
  SmoothClockConditionDeclared : Prop
  BoundaryValueProblemFormulated : Prop
  OmegaDifferentialEquationAvailable : Prop
  OmegaBoundarySolutionDerived : Prop
  LateSNMatchingWithoutExtraLawProved : Prop

def BoundaryProblemClosed
    (g : WeylCuspLateSNMatchingBoundaryConditionsGate) : Prop :=
  g.LateSNBranchPreservedConditionDeclared /\
  g.PTCuspConditionDeclared /\
  g.SmoothClockConditionDeclared /\
  g.BoundaryValueProblemFormulated /\
  g.OmegaDifferentialEquationAvailable

def MatchingSolutionClosed
    (g : WeylCuspLateSNMatchingBoundaryConditionsGate) : Prop :=
  BoundaryProblemClosed g /\
  g.OmegaBoundarySolutionDerived /\
  g.LateSNMatchingWithoutExtraLawProved

def MatchingBoundaryFrontier
    (g : WeylCuspLateSNMatchingBoundaryConditionsGate) : Prop :=
  BoundaryProblemClosed g /\
  Not g.OmegaBoundarySolutionDerived /\
  Not g.LateSNMatchingWithoutExtraLawProved

theorem matching_boundary_problem_still_needs_solution
    (g : WeylCuspLateSNMatchingBoundaryConditionsGate)
    (hFrontier : MatchingBoundaryFrontier g) :
    Not (MatchingSolutionClosed g) := by
  intro h
  exact hFrontier.2.1 h.2.1

end P0EFTJanusWeylCuspLateSNMatchingBoundaryConditionsGate
end JanusFormal
