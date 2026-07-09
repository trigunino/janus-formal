import JanusFormal.Branches.Z2SigmaRegularThroat.BoundaryDynamics.Gates.P0EFTJanusZ2SigmaMatterFluxRadialBlockGate
import JanusFormal.Branches.Z2SigmaRegularThroat.GeometryEmbedding.Gates.P0EFTJanusZ2SigmaThroatRadiusVariationalEquationGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaPlugstarEjectionThresholdGate

set_option autoImplicit false

structure PlugstarEjectionThresholdGate where
  coupledRadiusFluxSystemReferenced : Prop
  matterFluxRadialBlockImported : Prop
  throatRadiusVariationalEquationImported : Prop
  plugstarRouteDeclared : Prop
  parallelExplorationOnly : Prop
  noActivePipelineReplacement : Prop
  noObservationalFit : Prop
  concentrationFunctionalDeclared : Prop
  criticalThresholdDeclared : Prop
  ejectionBranchDeclared : Prop
  z2ThresholdInvariant : Prop
  pairedOppositeSheetEjectionDeclared : Prop
  z2TransmissionCompatibilityDeclared : Prop
  curvatureThresholdChannelSelected : Prop
  radiusLowerBoundDeclared : Prop
  thresholdEquationDerived : Prop
  rSigmaMinBoundDerived : Prop
  plugstarConstraintReady : Prop

def plugstarThresholdLedgerDeclared
  (g : PlugstarEjectionThresholdGate) : Prop :=
  g.coupledRadiusFluxSystemReferenced /\
  g.matterFluxRadialBlockImported /\
  g.throatRadiusVariationalEquationImported /\
  g.plugstarRouteDeclared /\
  g.parallelExplorationOnly /\
  g.noActivePipelineReplacement /\
  g.noObservationalFit

def plugstarThresholdReady
    (g : PlugstarEjectionThresholdGate) : Prop :=
  plugstarThresholdLedgerDeclared g /\
  g.concentrationFunctionalDeclared /\
  g.criticalThresholdDeclared /\
  g.ejectionBranchDeclared /\
  g.z2ThresholdInvariant /\
  g.pairedOppositeSheetEjectionDeclared /\
  g.z2TransmissionCompatibilityDeclared /\
  g.curvatureThresholdChannelSelected /\
  g.radiusLowerBoundDeclared /\
  g.thresholdEquationDerived /\
  g.rSigmaMinBoundDerived /\
  g.plugstarConstraintReady

def z2TransmissionReady
    (g : PlugstarEjectionThresholdGate) : Prop :=
  g.z2ThresholdInvariant /\
  g.pairedOppositeSheetEjectionDeclared /\
  g.z2TransmissionCompatibilityDeclared

def thresholdEquationReady
    (g : PlugstarEjectionThresholdGate) : Prop :=
  g.curvatureThresholdChannelSelected /\
  g.radiusLowerBoundDeclared /\
  g.thresholdEquationDerived /\
  g.rSigmaMinBoundDerived

theorem plugstar_constraint_requires_radius_lower_bound
    (g : PlugstarEjectionThresholdGate)
    (hReady : plugstarThresholdReady g) :
    g.rSigmaMinBoundDerived := by
  rcases hReady with
    ⟨_, _, _, _, _, _, _, _, _, _, hRSigmaMin, _⟩
  exact hRSigmaMin

theorem plugstar_constraint_requires_z2_transmission
    (g : PlugstarEjectionThresholdGate)
    (hReady : plugstarThresholdReady g) :
    g.z2TransmissionCompatibilityDeclared := by
  rcases hReady with
    ⟨_, _, _, _, _, _, hZ2Transmission, _, _, _, _, _⟩
  exact hZ2Transmission

theorem plugstar_constraint_gives_z2_transmission_ready
    (g : PlugstarEjectionThresholdGate)
    (hReady : plugstarThresholdReady g) :
    z2TransmissionReady g := by
  rcases hReady with
    ⟨_, _, _, _, hZ2Invariant, hPaired, hZ2Transmission, _, _, _, _, _⟩
  exact ⟨hZ2Invariant, hPaired, hZ2Transmission⟩

theorem plugstar_constraint_gives_threshold_equation_ready
    (g : PlugstarEjectionThresholdGate)
    (hReady : plugstarThresholdReady g) :
    thresholdEquationReady g := by
  rcases hReady with
    ⟨_, _, _, _, _, _, _, hCurvature, hLower, hEquation, hRSigmaMin, _⟩
  exact ⟨hCurvature, hLower, hEquation, hRSigmaMin⟩

theorem missing_threshold_equation_blocks_plugstar_constraint
    (g : PlugstarEjectionThresholdGate)
    (hMissing : Not g.thresholdEquationDerived) :
    Not (plugstarThresholdReady g) := by
  intro hReady
  rcases hReady with
    ⟨_, _, _, _, _, _, _, _, _, hEquation, _, _⟩
  exact hMissing hEquation

theorem missing_radius_lower_bound_blocks_plugstar_constraint
    (g : PlugstarEjectionThresholdGate)
    (hMissing : Not g.rSigmaMinBoundDerived) :
    Not (plugstarThresholdReady g) := by
  intro hReady
  exact hMissing (plugstar_constraint_requires_radius_lower_bound g hReady)

end P0EFTJanusZ2SigmaPlugstarEjectionThresholdGate
end JanusFormal
