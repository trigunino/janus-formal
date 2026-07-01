namespace JanusFormal
namespace P0EFTJanusZ4IonizationHistoryClosure

set_option autoImplicit false

structure IonizationHistoryClosure where
  peeblesEquationDeclared : Prop
  baryonTemperatureEquationDeclared : Prop
  visibilityNormalizationDeclared : Prop
  z4ExpansionRateInputRequired : Prop
  recombinationCoefficientsRequired : Prop
  ionizationHistorySolved : Prop

def ionizationScaffoldReady (i : IonizationHistoryClosure) : Prop :=
  i.peeblesEquationDeclared /\
  i.baryonTemperatureEquationDeclared /\
  i.visibilityNormalizationDeclared /\
  i.z4ExpansionRateInputRequired /\
  i.recombinationCoefficientsRequired

def ionizationPhysicalReady (i : IonizationHistoryClosure) : Prop :=
  ionizationScaffoldReady i /\
  i.ionizationHistorySolved

theorem ionization_scaffold_does_not_solve_history
    (i : IonizationHistoryClosure)
    (_ready : ionizationScaffoldReady i)
    (hMissing : Not i.ionizationHistorySolved) :
    Not (ionizationPhysicalReady i) := by
  intro h
  exact hMissing h.right

end P0EFTJanusZ4IonizationHistoryClosure
end JanusFormal
