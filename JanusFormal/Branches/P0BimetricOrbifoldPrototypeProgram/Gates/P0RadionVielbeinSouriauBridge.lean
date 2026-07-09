import JanusFormal.Branches.P0BimetricOrbifoldPrototypeProgram.Gates.P0RadionDilatonBranchSelection
import JanusFormal.Branches.P0BimetricOrbifoldPrototypeProgram.Gates.P0SouriauPoincareEnergyBranch

namespace JanusFormal
namespace P0RadionVielbeinSouriauBridge

open P0RadionDilatonBranchSelection
open P0SouriauPoincareEnergyBranch
open P0VielbeinEnergyResolution

set_option autoImplicit false

structure RadionAsVielbeinGeometry where
  radionGeometricNotMatter : Prop
  scalarConformalVielbeinFactor : Prop
  fourDimensionalTetrad : Prop
  determinantScalesAsPhiFourth : Prop
  radionCoupledOnlyToTemporalLeg : Prop
  determinantScalesLinearlyInPhi : Prop
  einsteinAetherTimelikeUnitVector : Prop
  temporalLegSignOperator : Prop
  oddFrameOrientationFlip : Prop
  antichronousLorentzComponentSelected : Prop

def conformalRadionOnly (g : RadionAsVielbeinGeometry) : Prop :=
  g.radionGeometricNotMatter /\
  g.scalarConformalVielbeinFactor /\
  g.fourDimensionalTetrad /\
  g.determinantScalesAsPhiFourth

def radionTetradTimeOrientationClosed
    (g : RadionAsVielbeinGeometry) : Prop :=
  g.radionGeometricNotMatter /\
  g.temporalLegSignOperator /\
  g.radionCoupledOnlyToTemporalLeg /\
  g.determinantScalesLinearlyInPhi /\
  g.einsteinAetherTimelikeUnitVector /\
  g.oddFrameOrientationFlip /\
  g.antichronousLorentzComponentSelected

theorem conformal_phi_four_dimensional_scaling_does_not_force_time_flip :
    Not (forall g : RadionAsVielbeinGeometry,
      conformalRadionOnly g -> g.antichronousLorentzComponentSelected) := by
  intro h
  let bad : RadionAsVielbeinGeometry :=
    { radionGeometricNotMatter := True
      scalarConformalVielbeinFactor := True
      fourDimensionalTetrad := True
      determinantScalesAsPhiFourth := True
      radionCoupledOnlyToTemporalLeg := False
      determinantScalesLinearlyInPhi := False
      einsteinAetherTimelikeUnitVector := False
      temporalLegSignOperator := False
      oddFrameOrientationFlip := False
      antichronousLorentzComponentSelected := False }
  exact h bad âŸ¨trivial, trivial, trivial, trivialâŸ©

theorem temporal_leg_operator_closes_antichronous_selection
    (g : RadionAsVielbeinGeometry)
    (h : radionTetradTimeOrientationClosed g) :
    g.antichronousLorentzComponentSelected := by
  exact h.right.right.right.right.right.right

theorem temporal_leg_radion_geometry_forces_odd_orientation
    (g : RadionAsVielbeinGeometry)
    (h : radionTetradTimeOrientationClosed g) :
    g.radionCoupledOnlyToTemporalLeg /\
    g.determinantScalesLinearlyInPhi /\
    g.oddFrameOrientationFlip := by
  exact âŸ¨h.right.right.left, h.right.right.right.left, h.right.right.right.right.right.leftâŸ©

theorem temporal_leg_without_linear_determinant_not_closed
    (g : RadionAsVielbeinGeometry)
    (hMissing : Not g.determinantScalesLinearlyInPhi) :
    Not (radionTetradTimeOrientationClosed g) := by
  intro h
  exact hMissing h.right.right.right.left

structure RadionSouriauBridgeCertificate where
  radionCertificate : RadionBranchSelectionCertificate
  geometry : RadionAsVielbeinGeometry
  souriauData : FullPoincareSouriauData
  confinementData : MinusSheetConfinementData
  geometryClosed : radionTetradTimeOrientationClosed geometry
  souriauOrbit : souriauNegativeOrbitAvailable souriauData
  confinement : confinementClosed confinementData

def souriauCertificateFromRadionTetrad
    (c : RadionSouriauBridgeCertificate) :
    SouriauEnergyBranchCertificate :=
  { souriauData := c.souriauData
    confinementData :=
      { c.confinementData with
        branchSelectedOnMinusSheet :=
          branchSelectedByRadion c.radionCertificate /\
          c.geometry.antichronousLorentzComponentSelected }
    negativeOrbitAvailable := c.souriauOrbit
    confinement := by
      rcases c.confinement with
        âŸ¨hSheet, hTopo, hNoMix, hMetric, _hBranch, hStableâŸ©
      exact
        âŸ¨hSheet,
          hTopo,
          hNoMix,
          hMetric,
          âŸ¨radion_certificate_selects_minus_branch c.radionCertificate,
            temporal_leg_operator_closes_antichronous_selection c.geometry c.geometryClosedâŸ©,
          hStableâŸ© }

theorem radion_tetrad_bridge_closes_souriau_energy
    (c : RadionSouriauBridgeCertificate) :
    negativeSectorEnergyClosed
      (quantumEnergyFromSouriau (souriauCertificateFromRadionTetrad c)) := by
  exact souriau_route_closes_negative_energy_orientation
    (souriauCertificateFromRadionTetrad c)

theorem radion_branch_without_temporal_leg_does_not_activate_souriau
    (c : RadionBranchSelectionCertificate)
    (g : RadionAsVielbeinGeometry)
    (hMissing : Not g.antichronousLorentzComponentSelected) :
    Not (branchSelectedByRadion c /\ g.antichronousLorentzComponentSelected) := by
  intro h
  exact hMissing h.right

theorem negative_yukawa_sign_without_tetrad_orientation_is_not_enough
    (c : RadionBranchSelectionCertificate)
    (g : RadionAsVielbeinGeometry)
    (hMissing : Not (radionTetradTimeOrientationClosed g)) :
    Not (branchSelectedByRadion c /\ radionTetradTimeOrientationClosed g) := by
  intro h
  exact hMissing h.right

end P0RadionVielbeinSouriauBridge
end JanusFormal
