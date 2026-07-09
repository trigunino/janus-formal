import JanusFormal.Branches.P0BimetricOrbifoldPrototypeProgram.Gates.P0RadionVielbeinSouriauBridge

namespace JanusFormal
namespace P0AetherGhostObservationConstraints

open P0RadionVielbeinSouriauBridge
open P0VielbeinEnergyResolution
open P0SouriauPoincareEnergyBranch

set_option autoImplicit false

structure GhostFreedomConstraints where
  hassanRosenConstraintStructure : Prop
  generalizedProcaDegeneracy : Prop
  noHigherThanSecondOrderEom : Prop
  hamiltonianConstraintPresent : Prop
  momentumConstraintPresent : Prop
  boulwareDeserModeRemoved : Prop
  positiveKineticSector : Prop

def ghostFreedomClosed (g : GhostFreedomConstraints) : Prop :=
  g.hassanRosenConstraintStructure /\
  g.generalizedProcaDegeneracy /\
  g.noHigherThanSecondOrderEom /\
  g.hamiltonianConstraintPresent /\
  g.momentumConstraintPresent /\
  g.boulwareDeserModeRemoved /\
  g.positiveKineticSector

structure AetherStabilityConstraints where
  timelikeUnitVectorConstraint : Prop
  sectorialLorentzBreakingOnly : Prop
  noTachyonicAetherMode : Prop
  noGradientInstability : Prop
  topologicalCutoffWellPosed : Prop
  boundaryModesControlled : Prop
  vacuumDecayForbidden : Prop

def aetherStabilityClosed (a : AetherStabilityConstraints) : Prop :=
  a.timelikeUnitVectorConstraint /\
  a.sectorialLorentzBreakingOnly /\
  a.noTachyonicAetherMode /\
  a.noGradientInstability /\
  a.topologicalCutoffWellPosed /\
  a.boundaryModesControlled /\
  a.vacuumDecayForbidden

structure ObservationalConstraints where
  gravitationalWaveSpeedLuminal : Prop
  gw170817BoundSatisfied : Prop
  standardMatterLorentzInvariantOnPlusSheet : Prop
  lorentzBreakingGravitationallySuppressed : Prop
  weakBimetricMixing : Prop
  ppnConstraintsSatisfied : Prop
  cosmologyBackgroundViable : Prop

def observationsClosed (o : ObservationalConstraints) : Prop :=
  o.gravitationalWaveSpeedLuminal /\
  o.gw170817BoundSatisfied /\
  o.standardMatterLorentzInvariantOnPlusSheet /\
  o.lorentzBreakingGravitationallySuppressed /\
  o.weakBimetricMixing /\
  o.ppnConstraintsSatisfied /\
  o.cosmologyBackgroundViable

structure AetherViabilityCertificate where
  ghost : GhostFreedomConstraints
  stability : AetherStabilityConstraints
  observation : ObservationalConstraints
  ghostClosed : ghostFreedomClosed ghost
  stabilityClosed : aetherStabilityClosed stability
  observationClosed : observationsClosed observation

def aetherSectorViable (c : AetherViabilityCertificate) : Prop :=
  ghostFreedomClosed c.ghost /\
  aetherStabilityClosed c.stability /\
  observationsClosed c.observation

theorem certificate_gives_aether_viability
    (c : AetherViabilityCertificate) :
    aetherSectorViable c := by
  exact âŸ¨c.ghostClosed, c.stabilityClosed, c.observationClosedâŸ©

theorem topological_cutoff_alone_does_not_remove_bd_ghost :
    Not (forall g : GhostFreedomConstraints,
      g.hassanRosenConstraintStructure ->
      g.boulwareDeserModeRemoved) := by
  intro h
  let bad : GhostFreedomConstraints :=
    { hassanRosenConstraintStructure := True
      generalizedProcaDegeneracy := False
      noHigherThanSecondOrderEom := False
      hamiltonianConstraintPresent := False
      momentumConstraintPresent := False
      boulwareDeserModeRemoved := False
      positiveKineticSector := True }
  exact h bad trivial

theorem second_order_eom_without_hamiltonian_constraint_not_ghost_closed
    (g : GhostFreedomConstraints)
    (hMissing : Not g.hamiltonianConstraintPresent) :
    Not (ghostFreedomClosed g) := by
  intro hClosed
  exact hMissing hClosed.right.right.right.left

theorem luminal_gw_speed_requires_observational_axiom
    (o : ObservationalConstraints)
    (hMissing : Not o.gravitationalWaveSpeedLuminal) :
    Not (observationsClosed o) := by
  intro hClosed
  exact hMissing hClosed.left

theorem gw170817_bound_without_luminal_speed_not_closed
    (o : ObservationalConstraints)
    (hMissing : Not o.gravitationalWaveSpeedLuminal) :
    Not (observationsClosed o) := by
  exact luminal_gw_speed_requires_observational_axiom o hMissing

theorem matter_confinement_without_suppression_not_observation_closed
    (o : ObservationalConstraints)
    (hMissing : Not o.lorentzBreakingGravitationallySuppressed) :
    Not (observationsClosed o) := by
  intro hClosed
  exact hMissing hClosed.right.right.right.left

structure FullAetherRadionSafety
    (c : RadionSouriauBridgeCertificate) where
  aetherViability : AetherViabilityCertificate
  radionSouriauClosed :
    negativeSectorEnergyClosed
      (quantumEnergyFromSouriau (souriauCertificateFromRadionTetrad c))

def fullAetherRadionSafetyClosed
    {c : RadionSouriauBridgeCertificate}
    (s : FullAetherRadionSafety c) : Prop :=
  aetherSectorViable s.aetherViability /\
  negativeSectorEnergyClosed
    (quantumEnergyFromSouriau (souriauCertificateFromRadionTetrad c))

theorem full_safety_certificate_closes_radion_aether_risks
    {c : RadionSouriauBridgeCertificate}
    (s : FullAetherRadionSafety c) :
    fullAetherRadionSafetyClosed s := by
  exact âŸ¨certificate_gives_aether_viability s.aetherViability,
    s.radionSouriauClosedâŸ©

end P0AetherGhostObservationConstraints
end JanusFormal
