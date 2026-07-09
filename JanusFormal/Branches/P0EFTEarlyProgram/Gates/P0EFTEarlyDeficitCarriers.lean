namespace JanusFormal
namespace P0EFTEarlyDeficitCarriers

set_option autoImplicit false

structure EarlyDeficitCarriers where
  soundHorizonShortfallComputed : Prop
  torsionVectorRadiationTargetEncoded : Prop
  immirziGeffBoostTargetEncoded : Prop
  carrierGeometryDerived : Prop

def earlyCarrierDiagnosticReady (e : EarlyDeficitCarriers) : Prop :=
  e.soundHorizonShortfallComputed /\
  e.torsionVectorRadiationTargetEncoded /\
  e.immirziGeffBoostTargetEncoded

def earlyCarrierNoFitReady (e : EarlyDeficitCarriers) : Prop :=
  earlyCarrierDiagnosticReady e /\
  e.carrierGeometryDerived

theorem early_deficit_diagnostic_ready_from_targets
    (e : EarlyDeficitCarriers)
    (hShort : e.soundHorizonShortfallComputed)
    (hTorsion : e.torsionVectorRadiationTargetEncoded)
    (hGeff : e.immirziGeffBoostTargetEncoded) :
    earlyCarrierDiagnosticReady e := by
  exact And.intro hShort (And.intro hTorsion hGeff)

theorem missing_carrier_geometry_blocks_no_fit
    (e : EarlyDeficitCarriers)
    (hMissing : Not e.carrierGeometryDerived) :
    Not (earlyCarrierNoFitReady e) := by
  intro h
  exact hMissing h.right

end P0EFTEarlyDeficitCarriers
end JanusFormal
