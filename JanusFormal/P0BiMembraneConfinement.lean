import JanusFormal.P0ModernJanusViabilityRoadmap

namespace JanusFormal
namespace P0BiMembraneConfinement

open P0OrbifoldActionProgram
open P0SouriauPoincareEnergyBranch

set_option autoImplicit false

structure BiMembraneConfinementMechanism where
  plusSheetExists : Prop
  minusSheetExists : Prop
  orbifoldFixedInterface : Prop
  topologicalSeparation : Prop
  boundaryLeakForbidden : Prop
  noCrossVacuumMixing : Prop
  minusSheetOwnInducedMetric : Prop
  negativeBranchSelectedOnMinusSheet : Prop
  vacuumStabilityControlled : Prop
  defectClassFixed : Prop
  sectorChargeConserved : Prop
  ptFixedSetCompatible : Prop

def biMembraneConfinementClosed
    (m : BiMembraneConfinementMechanism) : Prop :=
  m.plusSheetExists /\
  m.minusSheetExists /\
  m.orbifoldFixedInterface /\
  m.topologicalSeparation /\
  m.boundaryLeakForbidden /\
  m.noCrossVacuumMixing /\
  m.minusSheetOwnInducedMetric /\
  m.negativeBranchSelectedOnMinusSheet /\
  m.vacuumStabilityControlled /\
  m.defectClassFixed /\
  m.sectorChargeConserved /\
  m.ptFixedSetCompatible

def minusSheetConfinementFromBiMembrane
    (m : BiMembraneConfinementMechanism) :
    MinusSheetConfinementData :=
  { minusSheetExists := m.minusSheetExists
    topologicalConfinement := m.topologicalSeparation
    noCrossVacuumMixing := m.noCrossVacuumMixing
    ownInducedMetric := m.minusSheetOwnInducedMetric
    branchSelectedOnMinusSheet := m.negativeBranchSelectedOnMinusSheet
    vacuumStabilityControlled := m.vacuumStabilityControlled }

def topologyFromBiMembrane
    (m : BiMembraneConfinementMechanism) :
    OrbifoldTopologicalInvariants :=
  { defectClassFixed := m.defectClassFixed
    boundaryLeakForbidden := m.boundaryLeakForbidden
    sectorChargeConserved := m.sectorChargeConserved
    ptFixedSetCompatible := m.ptFixedSetCompatible }

theorem closed_bimembrane_gives_minus_confinement
    (m : BiMembraneConfinementMechanism)
    (h : biMembraneConfinementClosed m) :
    confinementClosed (minusSheetConfinementFromBiMembrane m) := by
  rcases h with
    ⟨_hPlus, hMinus, _hInterface, hTopo, _hLeak, hNoMix,
      hMetric, hBranch, hStable, _hDefect, _hCharge, _hPT⟩
  exact ⟨hMinus, hTopo, hNoMix, hMetric, hBranch, hStable⟩

theorem closed_bimembrane_gives_topology_ready
    (m : BiMembraneConfinementMechanism)
    (h : biMembraneConfinementClosed m) :
    topologyConservationReady (topologyFromBiMembrane m) := by
  rcases h with
    ⟨_hPlus, _hMinus, _hInterface, _hTopo, hLeak, _hNoMix,
      _hMetric, _hBranch, _hStable, hDefect, hCharge, hPT⟩
  exact ⟨hDefect, hLeak, hCharge, hPT⟩

theorem topological_separation_alone_does_not_select_negative_branch :
    Not (forall m : BiMembraneConfinementMechanism,
      m.topologicalSeparation -> m.negativeBranchSelectedOnMinusSheet) := by
  intro h
  let bad : BiMembraneConfinementMechanism :=
    { plusSheetExists := True
      minusSheetExists := True
      orbifoldFixedInterface := True
      topologicalSeparation := True
      boundaryLeakForbidden := True
      noCrossVacuumMixing := True
      minusSheetOwnInducedMetric := True
      negativeBranchSelectedOnMinusSheet := False
      vacuumStabilityControlled := True
      defectClassFixed := True
      sectorChargeConserved := True
      ptFixedSetCompatible := True }
  exact h bad trivial

theorem no_cross_mixing_alone_does_not_select_negative_branch :
    Not (forall m : BiMembraneConfinementMechanism,
      m.noCrossVacuumMixing -> m.negativeBranchSelectedOnMinusSheet) := by
  intro h
  let bad : BiMembraneConfinementMechanism :=
    { plusSheetExists := True
      minusSheetExists := True
      orbifoldFixedInterface := True
      topologicalSeparation := True
      boundaryLeakForbidden := True
      noCrossVacuumMixing := True
      minusSheetOwnInducedMetric := True
      negativeBranchSelectedOnMinusSheet := False
      vacuumStabilityControlled := True
      defectClassFixed := True
      sectorChargeConserved := True
      ptFixedSetCompatible := True }
  exact h bad trivial

theorem missing_branch_blocks_bimembrane_closure
    (m : BiMembraneConfinementMechanism)
    (hMissing : Not m.negativeBranchSelectedOnMinusSheet) :
    Not (biMembraneConfinementClosed m) := by
  intro hClosed
  exact hMissing hClosed.right.right.right.right.right.right.right.left

theorem missing_boundary_leak_forbids_topology_ready
    (m : BiMembraneConfinementMechanism)
    (hMissing : Not m.boundaryLeakForbidden) :
    Not (topologyConservationReady (topologyFromBiMembrane m)) := by
  intro hTopology
  exact hMissing hTopology.right.left

end P0BiMembraneConfinement
end JanusFormal
