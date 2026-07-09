namespace JanusFormal
namespace P0EFTJanusOmega00SolvabilityFrontierGate

set_option autoImplicit false

structure Omega00SolvabilityFrontierGate where
  GPlusWeylKinematicsClosed : Prop
  ProjectiveHatConformalGeometryClosed : Prop
  PlusSectorSourceContractClosed : Prop
  Projection00ChoiceClosed : Prop
  AbsoluteLFixed : Prop
  LorentzianTimeSlicingFixed : Prop
  ObservableHhatFixed : Prop
  PredragRhoPlusComponentsDerived : Prop
  OmegaBoundaryConditionDerived : Prop

def Omega00ContractsClosed
    (g : Omega00SolvabilityFrontierGate) : Prop :=
  g.GPlusWeylKinematicsClosed /\
  g.ProjectiveHatConformalGeometryClosed /\
  g.PlusSectorSourceContractClosed /\
  g.Projection00ChoiceClosed

def Omega00SolutionClosed
    (g : Omega00SolvabilityFrontierGate) : Prop :=
  Omega00ContractsClosed g /\
  g.AbsoluteLFixed /\
  g.LorentzianTimeSlicingFixed /\
  g.ObservableHhatFixed /\
  g.PredragRhoPlusComponentsDerived /\
  g.OmegaBoundaryConditionDerived

def Omega00BottomFrontier
    (g : Omega00SolvabilityFrontierGate) : Prop :=
  Omega00ContractsClosed g /\
  Not g.AbsoluteLFixed /\
  Not g.LorentzianTimeSlicingFixed /\
  Not g.ObservableHhatFixed /\
  Not g.PredragRhoPlusComponentsDerived /\
  Not g.OmegaBoundaryConditionDerived

theorem omega_00_frontier_is_contract_not_solution
    (g : Omega00SolvabilityFrontierGate)
    (hFrontier : Omega00BottomFrontier g) :
    Not (Omega00SolutionClosed g) := by
  intro h
  exact hFrontier.2.1 h.2.1

end P0EFTJanusOmega00SolvabilityFrontierGate
end JanusFormal
