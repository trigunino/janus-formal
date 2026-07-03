import JanusFormal.P0EFTJanusZ2SigmaBulkStressOfAGate

namespace JanusFormal
namespace P0EFTJanusZ2SigmaSectorDensityPressureOfAGate

set_option autoImplicit false

structure SectorDensityPressureOfAGate where
  janusBimetricFLRWBibliographyChecked : Prop
  perfectFluidContinuityImported : Prop
  plusSectorRhoPDeclared : Prop
  minusSectorRhoPDeclared : Prop
  z2SignPolicyDeclared : Prop
  equationOfStatePolicyDeclared : Prop
  observationalFitForbidden : Prop
  plusContinuityEquationDeclared : Prop
  minusContinuityEquationDeclared : Prop
  plusEquationOfStateDerived : Prop
  minusEquationOfStateDerived : Prop
  plusInitialNormalizationDerived : Prop
  minusInitialNormalizationDerived : Prop
  plusRhoPOfAReady : Prop
  minusRhoPOfAReady : Prop

def sectorDensityPressureLedgerDeclared
    (g : SectorDensityPressureOfAGate) : Prop :=
  g.janusBimetricFLRWBibliographyChecked /\
  g.perfectFluidContinuityImported /\
  g.plusSectorRhoPDeclared /\
  g.minusSectorRhoPDeclared /\
  g.z2SignPolicyDeclared /\
  g.equationOfStatePolicyDeclared /\
  g.observationalFitForbidden /\
  g.plusContinuityEquationDeclared /\
  g.minusContinuityEquationDeclared

def sectorDensityPressureOfAReady
    (g : SectorDensityPressureOfAGate) : Prop :=
  sectorDensityPressureLedgerDeclared g /\
  g.plusEquationOfStateDerived /\
  g.minusEquationOfStateDerived /\
  g.plusInitialNormalizationDerived /\
  g.minusInitialNormalizationDerived /\
  g.plusRhoPOfAReady /\
  g.minusRhoPOfAReady

theorem sector_rho_p_requires_equations_of_state
    (g : SectorDensityPressureOfAGate)
    (hReady : sectorDensityPressureOfAReady g) :
    g.plusEquationOfStateDerived /\ g.minusEquationOfStateDerived := by
  exact And.intro hReady.2.1 hReady.2.2.1

end P0EFTJanusZ2SigmaSectorDensityPressureOfAGate
end JanusFormal
