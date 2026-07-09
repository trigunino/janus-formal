import JanusFormal.Legacy.P0.Gates.P0BiMembraneConfinement

namespace JanusFormal
namespace P0RadionDilatonBranchSelection

open P0BiMembraneConfinement

set_option autoImplicit false

structure RadionDilatonPotential where
  scalarFieldPresent : Prop
  z2OddField : Prop
  doubleWellPotential : Prop
  symmetricHighEnergyPhase : Prop
  phaseTransitionOccurred : Prop
  nonzeroVEV : Prop
  plusMinimumExists : Prop
  minusMinimumExists : Prop

def brokenRadionPhase (p : RadionDilatonPotential) : Prop :=
  p.scalarFieldPresent /\
  p.z2OddField /\
  p.doubleWellPotential /\
  p.symmetricHighEnergyPhase /\
  p.phaseTransitionOccurred /\
  p.nonzeroVEV /\
  p.plusMinimumExists /\
  p.minusMinimumExists

structure YukawaSortingData where
  fermionMatterPresent : Prop
  yukawaCouplingPresent : Prop
  massSignTracksVEV : Prop
  plusVEVSelectsPlusSector : Prop
  minusVEVSelectsMinusSector : Prop
  sheetConfinementCoupled : Prop
  gravitationalEnergyOrientationLinked : Prop

def yukawaSortingClosed (y : YukawaSortingData) : Prop :=
  y.fermionMatterPresent /\
  y.yukawaCouplingPresent /\
  y.massSignTracksVEV /\
  y.plusVEVSelectsPlusSector /\
  y.minusVEVSelectsMinusSector /\
  y.sheetConfinementCoupled /\
  y.gravitationalEnergyOrientationLinked

structure RadionBranchSelectionCertificate where
  potential : RadionDilatonPotential
  yukawa : YukawaSortingData
  brokenPhase : brokenRadionPhase potential
  sortingClosed : yukawaSortingClosed yukawa

def branchSelectedByRadion
    (c : RadionBranchSelectionCertificate) : Prop :=
  c.potential.minusMinimumExists /\
  c.yukawa.minusVEVSelectsMinusSector /\
  c.yukawa.sheetConfinementCoupled /\
  c.yukawa.gravitationalEnergyOrientationLinked

theorem radion_certificate_selects_minus_branch
    (c : RadionBranchSelectionCertificate) :
    branchSelectedByRadion c := by
  rcases c.brokenPhase with
    ⟨_hField, _hOdd, _hPotential, _hHigh, _hTransition,
      _hVEV, _hPlus, hMinus⟩
  rcases c.sortingClosed with
    ⟨_hMatter, _hYukawa, _hTracks, _hPlusSelect,
      hMinusSelect, hConfinement, hEnergy⟩
  exact ⟨hMinus, hMinusSelect, hConfinement, hEnergy⟩

def biMembraneWithRadionSelection
    (m : BiMembraneConfinementMechanism)
    (c : RadionBranchSelectionCertificate) :
    BiMembraneConfinementMechanism :=
  { m with
    negativeBranchSelectedOnMinusSheet := branchSelectedByRadion c
    vacuumStabilityControlled :=
      m.vacuumStabilityControlled /\ c.yukawa.sheetConfinementCoupled }

theorem radion_selection_fills_bimembrane_branch
    (m : BiMembraneConfinementMechanism)
    (c : RadionBranchSelectionCertificate) :
    (biMembraneWithRadionSelection m c).negativeBranchSelectedOnMinusSheet := by
  exact radion_certificate_selects_minus_branch c

theorem double_well_alone_does_not_sort_matter :
    Not (forall (p : RadionDilatonPotential) (y : YukawaSortingData),
      brokenRadionPhase p -> y.minusVEVSelectsMinusSector) := by
  intro h
  let p : RadionDilatonPotential :=
    { scalarFieldPresent := True
      z2OddField := True
      doubleWellPotential := True
      symmetricHighEnergyPhase := True
      phaseTransitionOccurred := True
      nonzeroVEV := True
      plusMinimumExists := True
      minusMinimumExists := True }
  let y : YukawaSortingData :=
    { fermionMatterPresent := True
      yukawaCouplingPresent := False
      massSignTracksVEV := False
      plusVEVSelectsPlusSector := False
      minusVEVSelectsMinusSector := False
      sheetConfinementCoupled := False
      gravitationalEnergyOrientationLinked := False }
  have hBroken : brokenRadionPhase p :=
    ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  have hSort : y.minusVEVSelectsMinusSector := h p y hBroken
  exact hSort

theorem broken_phase_without_yukawa_does_not_sort_matter
    (p : RadionDilatonPotential)
    (y : YukawaSortingData)
    (_hBroken : brokenRadionPhase p)
    (hMissingYukawa : Not y.yukawaCouplingPresent) :
    Not (yukawaSortingClosed y) := by
  intro hSort
  exact hMissingYukawa hSort.right.left

theorem yukawa_mass_sign_without_energy_link_does_not_close_sorting
    (y : YukawaSortingData)
    (hMissingEnergyLink : Not y.gravitationalEnergyOrientationLinked) :
    Not (yukawaSortingClosed y) := by
  intro hSort
  exact hMissingEnergyLink hSort.right.right.right.right.right.right

theorem radion_selected_bimembrane_can_close_if_other_obligations_hold
    (m : BiMembraneConfinementMechanism)
    (c : RadionBranchSelectionCertificate)
    (hBase :
      m.plusSheetExists /\
      m.minusSheetExists /\
      m.orbifoldFixedInterface /\
      m.topologicalSeparation /\
      m.boundaryLeakForbidden /\
      m.noCrossVacuumMixing /\
      m.minusSheetOwnInducedMetric /\
      m.defectClassFixed /\
      m.sectorChargeConserved /\
      m.ptFixedSetCompatible)
    (hStable : m.vacuumStabilityControlled) :
    biMembraneConfinementClosed (biMembraneWithRadionSelection m c) := by
  rcases hBase with
    ⟨hPlus, hMinus, hInterface, hTopo, hLeak, hNoMix,
      hMetric, hDefect, hCharge, hPT⟩
  exact
    ⟨hPlus,
      hMinus,
      hInterface,
      hTopo,
      hLeak,
      hNoMix,
      hMetric,
      radion_certificate_selects_minus_branch c,
      ⟨hStable, c.sortingClosed.right.right.right.right.right.left⟩,
      hDefect,
      hCharge,
      hPT⟩

end P0RadionDilatonBranchSelection
end JanusFormal
