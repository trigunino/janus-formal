namespace JanusFormal
namespace P0EFTJanusZ2EThroatQuantumTopologyFrontierGate

set_option autoImplicit false

structure EThroatQuantumTopologyFrontier where
  eThroatEqualsEGlobalAllowed : Prop
  chargeQuantizationDerivesE : Prop
  vacuumTopologyDerivesE : Prop
  strongRegularityDerivesE : Prop
  llBraneTensionDerivesE : Prop
  boundaryActionDerivesE : Prop
  candidateQuantumTheoryCanBeProposed : Prop
  candidateTheoryIsCurrentJanusDerivation : Prop

def anyCurrentRouteDerivesE (g : EThroatQuantumTopologyFrontier) : Prop :=
  g.chargeQuantizationDerivesE \/
  g.vacuumTopologyDerivesE \/
  g.strongRegularityDerivesE \/
  g.llBraneTensionDerivesE \/
  g.boundaryActionDerivesE

def strictNoFitEThroatReady (g : EThroatQuantumTopologyFrontier) : Prop :=
  g.eThroatEqualsEGlobalAllowed /\ anyCurrentRouteDerivesE g

theorem no_current_route_blocks_strict_no_fit_EThroat
    (g : EThroatQuantumTopologyFrontier)
    (hNoCharge : Not g.chargeQuantizationDerivesE)
    (hNoVacuum : Not g.vacuumTopologyDerivesE)
    (hNoReg : Not g.strongRegularityDerivesE)
    (hNoLL : Not g.llBraneTensionDerivesE)
    (hNoBoundary : Not g.boundaryActionDerivesE) :
    Not (strictNoFitEThroatReady g) := by
  intro h
  cases h.2 with
  | inl hCharge => exact hNoCharge hCharge
  | inr rest1 =>
      cases rest1 with
      | inl hVacuum => exact hNoVacuum hVacuum
      | inr rest2 =>
          cases rest2 with
          | inl hReg => exact hNoReg hReg
          | inr rest3 =>
              cases rest3 with
              | inl hLL => exact hNoLL hLL
              | inr hBoundary => exact hNoBoundary hBoundary

theorem proposed_quantum_theory_is_not_derivation_without_bridge
    (g : EThroatQuantumTopologyFrontier)
    (_hCan : g.candidateQuantumTheoryCanBeProposed)
    (hNotCurrent : Not g.candidateTheoryIsCurrentJanusDerivation) :
    Not g.candidateTheoryIsCurrentJanusDerivation := hNotCurrent

end P0EFTJanusZ2EThroatQuantumTopologyFrontierGate
end JanusFormal
