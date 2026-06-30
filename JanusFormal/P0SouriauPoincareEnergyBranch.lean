import JanusFormal.P0VielbeinEnergyResolution

namespace JanusFormal
namespace P0SouriauPoincareEnergyBranch

open P0VielbeinEnergyResolution

set_option autoImplicit false

structure FullPoincareSouriauData where
  fullPoincareGroupUsed : Prop
  coadjointOrbitMethod : Prop
  momentMapEnergyDefined : Prop
  antichronousComponentActs : Prop
  negativeEnergyOrbitExists : Prop
  geometricQuantizationPerformed : Prop
  quantumRepresentationBuilt : Prop

def souriauNegativeOrbitAvailable (d : FullPoincareSouriauData) : Prop :=
  d.fullPoincareGroupUsed /\
  d.coadjointOrbitMethod /\
  d.momentMapEnergyDefined /\
  d.antichronousComponentActs /\
  d.negativeEnergyOrbitExists /\
  d.geometricQuantizationPerformed /\
  d.quantumRepresentationBuilt

structure MinusSheetConfinementData where
  minusSheetExists : Prop
  topologicalConfinement : Prop
  noCrossVacuumMixing : Prop
  ownInducedMetric : Prop
  branchSelectedOnMinusSheet : Prop
  vacuumStabilityControlled : Prop

def confinementClosed (c : MinusSheetConfinementData) : Prop :=
  c.minusSheetExists /\
  c.topologicalConfinement /\
  c.noCrossVacuumMixing /\
  c.ownInducedMetric /\
  c.branchSelectedOnMinusSheet /\
  c.vacuumStabilityControlled

structure SouriauEnergyBranchCertificate where
  souriauData : FullPoincareSouriauData
  confinementData : MinusSheetConfinementData
  negativeOrbitAvailable : souriauNegativeOrbitAvailable souriauData
  confinement : confinementClosed confinementData

def quantumEnergyFromSouriau
    (c : SouriauEnergyBranchCertificate) :
    QuantumEnergyOrientationData :=
  { timeReversalAntiunitary := c.souriauData.antichronousComponentActs
    cptCompatible := c.souriauData.fullPoincareGroupUsed
    extendedPoincareRepresentation := c.souriauData.quantumRepresentationBuilt
    negativeEnergyBranchSelected :=
      c.confinementData.branchSelectedOnMinusSheet
    vacuumStabilityControlled :=
      c.confinementData.vacuumStabilityControlled }

theorem souriau_route_closes_negative_energy_orientation
    (c : SouriauEnergyBranchCertificate) :
    negativeSectorEnergyClosed (quantumEnergyFromSouriau c) := by
  rcases c.negativeOrbitAvailable with
    ⟨hFull, _hOrbit, _hMoment, hAnti, _hNeg, _hQuant, hRep⟩
  rcases c.confinement with
    ⟨_hSheet, _hConfine, _hNoMix, _hMetric, hBranch, hStable⟩
  exact ⟨hAnti, hFull, hRep, hBranch, hStable⟩

theorem negative_orbit_existence_alone_does_not_select_branch :
    Not (forall d : FullPoincareSouriauData,
      d.negativeEnergyOrbitExists -> d.quantumRepresentationBuilt) := by
  intro h
  let bad : FullPoincareSouriauData :=
    { fullPoincareGroupUsed := True
      coadjointOrbitMethod := True
      momentMapEnergyDefined := True
      antichronousComponentActs := True
      negativeEnergyOrbitExists := True
      geometricQuantizationPerformed := False
      quantumRepresentationBuilt := False }
  exact h bad trivial

theorem negative_orbit_without_branch_selection_does_not_close_energy
    (d : FullPoincareSouriauData)
    (c : MinusSheetConfinementData)
    (_hOrbit : souriauNegativeOrbitAvailable d)
    (hMissingBranch : Not c.branchSelectedOnMinusSheet) :
    Not (negativeSectorEnergyClosed
      { timeReversalAntiunitary := d.antichronousComponentActs
        cptCompatible := d.fullPoincareGroupUsed
        extendedPoincareRepresentation := d.quantumRepresentationBuilt
        negativeEnergyBranchSelected := c.branchSelectedOnMinusSheet
        vacuumStabilityControlled := c.vacuumStabilityControlled }) := by
  intro hClosed
  exact hMissingBranch hClosed.right.right.right.left

theorem missing_branch_selection_blocks_souriau_certificate
    (d : FullPoincareSouriauData)
    (c : MinusSheetConfinementData)
    (hMissing : Not c.branchSelectedOnMinusSheet) :
    Not (Nonempty
      { cert : SouriauEnergyBranchCertificate //
        cert.souriauData = d /\ cert.confinementData = c }) := by
  intro hCert
  rcases hCert with ⟨cert, hData⟩
  rcases hData with ⟨_hSource, hConfinement⟩
  have hBranch : c.branchSelectedOnMinusSheet := by
    simpa [hConfinement] using cert.confinement.right.right.right.right.left
  exact hMissing hBranch

end P0SouriauPoincareEnergyBranch
end JanusFormal
