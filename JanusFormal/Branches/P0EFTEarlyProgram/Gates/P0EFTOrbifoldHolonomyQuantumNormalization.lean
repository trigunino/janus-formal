import JanusFormal.Branches.P0EFTEarlyProgram.Gates.P0EFTOrbifoldFluxQuantizationLaw

namespace JanusFormal
namespace P0EFTOrbifoldHolonomyQuantumNormalization

set_option autoImplicit false

structure OrbifoldHolonomyQuantumNormalization where
  compactSingularCycleLoaded : Prop
  spinConnectionGaugeFixedOnCycle : Prop
  holonomyUnitChosenByOrbifoldGenerator : Prop
  fluxDividedByHolonomyUnitWellDefined : Prop

def holonomyQuantumNormalizationClosed (n : OrbifoldHolonomyQuantumNormalization) : Prop :=
  n.compactSingularCycleLoaded /\
  n.spinConnectionGaugeFixedOnCycle /\
  n.holonomyUnitChosenByOrbifoldGenerator /\
  n.fluxDividedByHolonomyUnitWellDefined

theorem holonomy_normalization_supplies_flux_law_inputs
    (n : OrbifoldHolonomyQuantumNormalization)
    (q : P0EFTOrbifoldFluxQuantizationLaw.OrbifoldFluxQuantizationLaw)
    (_hNorm : holonomyQuantumNormalizationClosed n)
    (hCycle : q.singularCycleCompact)
    (hRestrict : q.spinConnectionRestrictsToOrbifoldCycle)
    (hQuantum : q.holonomyQuantumNormalized)
    (hInteger : q.normalizedFluxIsInteger) :
    P0EFTOrbifoldFluxQuantizationLaw.fluxQuantizationLawClosed q := by
  unfold P0EFTOrbifoldFluxQuantizationLaw.fluxQuantizationLawClosed
  exact And.intro hCycle
    (And.intro hRestrict (And.intro hQuantum hInteger))

theorem missing_orbifold_holonomy_unit_blocks_normalization
    (n : OrbifoldHolonomyQuantumNormalization)
    (hMissing : Not n.holonomyUnitChosenByOrbifoldGenerator) :
    Not (holonomyQuantumNormalizationClosed n) := by
  intro h
  exact hMissing h.right.right.left

theorem missing_gauge_fix_blocks_normalization
    (n : OrbifoldHolonomyQuantumNormalization)
    (hMissing : Not n.spinConnectionGaugeFixedOnCycle) :
    Not (holonomyQuantumNormalizationClosed n) := by
  intro h
  exact hMissing h.right.left

end P0EFTOrbifoldHolonomyQuantumNormalization
end JanusFormal
