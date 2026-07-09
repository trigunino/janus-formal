namespace JanusFormal
namespace P0EFTJanusZ2PTSouriauSymplecticIntegralityGate

set_option autoImplicit false

structure PTSouriauSymplecticIntegralityGate where
  boundaryPhaseSpaceDeclared : Prop
  omegaPTDeclared : Prop
  omegaPTClosed : Prop
  prequantumIntegralityDeclared : Prop
  periodsComputed : Prop
  periodsIntegral : Prop
  massMomentMapPeriodIdentified : Prop
  minimalPositivePeriodNonzero : Prop

def symplecticIntegralityReady (g : PTSouriauSymplecticIntegralityGate) : Prop :=
  g.boundaryPhaseSpaceDeclared /\
  g.omegaPTDeclared /\
  g.omegaPTClosed /\
  g.prequantumIntegralityDeclared /\
  g.periodsComputed /\
  g.periodsIntegral /\
  g.massMomentMapPeriodIdentified /\
  g.minimalPositivePeriodNonzero

theorem missing_periods_blocks_integrality
    (g : PTSouriauSymplecticIntegralityGate)
    (hMissing : Not g.periodsComputed) :
    Not (symplecticIntegralityReady g) := by
  intro h
  exact hMissing h.right.right.right.right.left

theorem missing_mass_period_blocks_integrality
    (g : PTSouriauSymplecticIntegralityGate)
    (hMissing : Not g.massMomentMapPeriodIdentified) :
    Not (symplecticIntegralityReady g) := by
  intro h
  exact hMissing h.right.right.right.right.right.right.left

end P0EFTJanusZ2PTSouriauSymplecticIntegralityGate
end JanusFormal
