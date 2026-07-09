import JanusFormal.Branches.P0EFTEarlyProgram.Gates.P0EFTOrbifoldFluxQuantizationLaw
import JanusFormal.Branches.P0EFTEarlyProgram.Gates.P0EFTOrbifoldHolonomyQuantumNormalized

namespace JanusFormal
namespace P0EFTOrbifoldNormalizedFluxInteger

set_option autoImplicit false

structure NormalizedFluxInteger where
  holonomyQuantumNormalized : Prop
  fluxRepresentativeDefined : Prop
  normalizedFluxLandsInIntegerLattice : Prop

def normalizedFluxIntegerDerived (n : NormalizedFluxInteger) : Prop :=
  n.holonomyQuantumNormalized /\
  n.fluxRepresentativeDefined /\
  n.normalizedFluxLandsInIntegerLattice

theorem normalized_flux_integer_supplies_flux_law_input
    (n : NormalizedFluxInteger)
    (q : P0EFTOrbifoldFluxQuantizationLaw.OrbifoldFluxQuantizationLaw)
    (_hInteger : normalizedFluxIntegerDerived n)
    (hCycle : q.singularCycleCompact)
    (hRestrict : q.spinConnectionRestrictsToOrbifoldCycle)
    (hQuantum : q.holonomyQuantumNormalized)
    (hInteger : q.normalizedFluxIsInteger) :
    P0EFTOrbifoldFluxQuantizationLaw.fluxQuantizationLawClosed q := by
  unfold P0EFTOrbifoldFluxQuantizationLaw.fluxQuantizationLawClosed
  exact And.intro hCycle (And.intro hRestrict (And.intro hQuantum hInteger))

theorem missing_integer_lattice_blocks_normalized_flux_integer
    (n : NormalizedFluxInteger)
    (hMissing : Not n.normalizedFluxLandsInIntegerLattice) :
    Not (normalizedFluxIntegerDerived n) := by
  intro h
  exact hMissing h.right.right

end P0EFTOrbifoldNormalizedFluxInteger
end JanusFormal
