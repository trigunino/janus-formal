import JanusFormal.Branches.P0EFTEarlyProgram.Gates.P0EFTOrbifoldFluxQuantizationLaw
import JanusFormal.Branches.P0EFTEarlyProgram.Gates.P0EFTOrbifoldGeneratorHolonomyUnit
import JanusFormal.Branches.P0EFTEarlyProgram.Gates.P0EFTOrbifoldSpinConnectionGaugeFix

namespace JanusFormal
namespace P0EFTOrbifoldHolonomyQuantumNormalized

set_option autoImplicit false

structure HolonomyQuantumNormalized where
  spinConnectionGaugeFixed : Prop
  generatorHolonomyUnitChosen : Prop
  fluxDividedByHolonomyUnit : Prop

def holonomyQuantumNormalizedDerived (h : HolonomyQuantumNormalized) : Prop :=
  h.spinConnectionGaugeFixed /\
  h.generatorHolonomyUnitChosen /\
  h.fluxDividedByHolonomyUnit

theorem holonomy_quantum_normalization_supplies_flux_law_input
    (h : HolonomyQuantumNormalized)
    (q : P0EFTOrbifoldFluxQuantizationLaw.OrbifoldFluxQuantizationLaw)
    (_hNorm : holonomyQuantumNormalizedDerived h)
    (hCycle : q.singularCycleCompact)
    (hRestrict : q.spinConnectionRestrictsToOrbifoldCycle)
    (hQuantum : q.holonomyQuantumNormalized)
    (hInteger : q.normalizedFluxIsInteger) :
    P0EFTOrbifoldFluxQuantizationLaw.fluxQuantizationLawClosed q := by
  unfold P0EFTOrbifoldFluxQuantizationLaw.fluxQuantizationLawClosed
  exact And.intro hCycle (And.intro hRestrict (And.intro hQuantum hInteger))

theorem missing_flux_division_blocks_holonomy_quantum_normalization
    (h : HolonomyQuantumNormalized)
    (hMissing : Not h.fluxDividedByHolonomyUnit) :
    Not (holonomyQuantumNormalizedDerived h) := by
  intro hClosed
  exact hMissing hClosed.right.right

end P0EFTOrbifoldHolonomyQuantumNormalized
end JanusFormal
