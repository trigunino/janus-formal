namespace JanusFormal
namespace P0EFTJanusConformalEinsteinTraceReductionGate

set_option autoImplicit false

structure ConformalEinsteinTraceReductionGate where
  ConformalTransformFormulaDeclared : Prop
  PhiDefinedAsLogOmega : Prop
  TraceEquationDeclared : Prop
  OmegaSecondOrderEquationDeclared : Prop
  NoNewScalarFieldAdded : Prop
  HatCurvatureSourceDerived : Prop
  TraceStressSourceDerived : Prop
  BoundaryConditionDerived : Prop

def SymbolicTraceReductionClosed
    (g : ConformalEinsteinTraceReductionGate) : Prop :=
  g.ConformalTransformFormulaDeclared /\
  g.PhiDefinedAsLogOmega /\
  g.TraceEquationDeclared /\
  g.OmegaSecondOrderEquationDeclared /\
  g.NoNewScalarFieldAdded

def ActiveOmegaSolutionClosed
    (g : ConformalEinsteinTraceReductionGate) : Prop :=
  SymbolicTraceReductionClosed g /\
  g.HatCurvatureSourceDerived /\
  g.TraceStressSourceDerived /\
  g.BoundaryConditionDerived

def TraceReductionFrontier
    (g : ConformalEinsteinTraceReductionGate) : Prop :=
  SymbolicTraceReductionClosed g /\
  Not g.HatCurvatureSourceDerived /\
  Not g.TraceStressSourceDerived /\
  Not g.BoundaryConditionDerived

theorem trace_reduction_needs_active_sources
    (g : ConformalEinsteinTraceReductionGate)
    (hFrontier : TraceReductionFrontier g) :
    Not (ActiveOmegaSolutionClosed g) := by
  intro h
  exact hFrontier.2.1 h.2.1

end P0EFTJanusConformalEinsteinTraceReductionGate
end JanusFormal
