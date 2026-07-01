import JanusFormal.P0EFTBiSectorBoltzmannPrototype
import JanusFormal.P0EFTJanusZ4LinearizedEquation

namespace JanusFormal
namespace P0EFTJanusZ4CMBSolver

set_option autoImplicit false

abbrev Prototype := P0EFTBiSectorBoltzmannPrototype.BiSectorBoltzmannPrototype
abbrev Z4Equation := P0EFTJanusZ4LinearizedEquation.UnifiedZ4LinearizedEquation

def z4ArchitectureReady (p : Prototype) : Prop :=
  P0EFTBiSectorBoltzmannPrototype.prototypeReady p /\
  p.z4UnifiedGeometricOriginEncoded /\
  p.metricSectorsAreZ4Projections /\
  p.independentMetricDynamicsForbidden /\
  p.cmbSolverScaffold95PercentReached

def z4PhysicalPlanckReady (p : Prototype) : Prop :=
  z4ArchitectureReady p /\
  p.fullPhotonBaryonNeutrinoHierarchyValidated /\
  p.planckLikelihoodIntegrated

def z4ArchitectureWithEquationReady (p : Prototype) (e : Z4Equation) : Prop :=
  z4ArchitectureReady p /\
  P0EFTJanusZ4LinearizedEquation.z4ProjectionScaffoldReady e

theorem architecture_does_not_imply_planck_ready
    (p : Prototype)
    (_hArch : z4ArchitectureReady p)
    (hMissing : Not p.planckLikelihoodIntegrated) :
    Not (z4PhysicalPlanckReady p) := by
  intro h
  exact hMissing h.right.right

theorem equation_scaffold_does_not_imply_planck_ready
    (p : Prototype)
    (e : Z4Equation)
    (_hArch : z4ArchitectureWithEquationReady p e)
    (hMissing : Not p.planckLikelihoodIntegrated) :
    Not (z4PhysicalPlanckReady p) := by
  intro h
  exact hMissing h.right.right

end P0EFTJanusZ4CMBSolver
end JanusFormal
