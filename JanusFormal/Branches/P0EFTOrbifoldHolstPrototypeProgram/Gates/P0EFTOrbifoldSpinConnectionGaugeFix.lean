import JanusFormal.Branches.P0EFTOrbifoldHolstPrototypeProgram.Gates.P0EFTOrbifoldHolonomyQuantumNormalization
import JanusFormal.Branches.P0EFTOrbifoldHolstPrototypeProgram.Gates.P0EFTOrbifoldFluxQuantizationLaw

namespace JanusFormal
namespace P0EFTOrbifoldSpinConnectionGaugeFix

set_option autoImplicit false

structure SpinConnectionGaugeFix where
  compactCycleLoaded : Prop
  orbifoldRestrictionDefined : Prop
  gaugeRepresentativeChosen : Prop

def spinConnectionGaugeFixedOnCycle (g : SpinConnectionGaugeFix) : Prop :=
  g.compactCycleLoaded /\
  g.orbifoldRestrictionDefined /\
  g.gaugeRepresentativeChosen

theorem gauge_fix_supplies_holonomy_normalization_input
    (g : SpinConnectionGaugeFix)
    (n : P0EFTOrbifoldHolonomyQuantumNormalization.OrbifoldHolonomyQuantumNormalization)
    (_hGauge : spinConnectionGaugeFixedOnCycle g)
    (hCycle : n.compactSingularCycleLoaded)
    (hGaugeFixed : n.spinConnectionGaugeFixedOnCycle)
    (hUnit : n.holonomyUnitChosenByOrbifoldGenerator)
    (hWellDefined : n.fluxDividedByHolonomyUnitWellDefined) :
    P0EFTOrbifoldHolonomyQuantumNormalization.holonomyQuantumNormalizationClosed n := by
  unfold P0EFTOrbifoldHolonomyQuantumNormalization.holonomyQuantumNormalizationClosed
  exact And.intro hCycle (And.intro hGaugeFixed (And.intro hUnit hWellDefined))

theorem gauge_fix_supplies_flux_restriction_input
    (g : SpinConnectionGaugeFix)
    (q : P0EFTOrbifoldFluxQuantizationLaw.OrbifoldFluxQuantizationLaw)
    (_hGauge : spinConnectionGaugeFixedOnCycle g)
    (hCycle : q.singularCycleCompact)
    (hRestrict : q.spinConnectionRestrictsToOrbifoldCycle)
    (hQuantum : q.holonomyQuantumNormalized)
    (hInteger : q.normalizedFluxIsInteger) :
    P0EFTOrbifoldFluxQuantizationLaw.fluxQuantizationLawClosed q := by
  unfold P0EFTOrbifoldFluxQuantizationLaw.fluxQuantizationLawClosed
  exact And.intro hCycle (And.intro hRestrict (And.intro hQuantum hInteger))

theorem missing_gauge_representative_blocks_gauge_fix
    (g : SpinConnectionGaugeFix)
    (hMissing : Not g.gaugeRepresentativeChosen) :
    Not (spinConnectionGaugeFixedOnCycle g) := by
  intro h
  exact hMissing h.right.right

end P0EFTOrbifoldSpinConnectionGaugeFix
end JanusFormal
