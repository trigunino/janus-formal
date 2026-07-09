import JanusFormal.Branches.P0EFTEarlyProgram.Gates.P0EFTOrbifoldFluxIntegerTheorem

namespace JanusFormal
namespace P0EFTOrbifoldFluxQuantizationLaw

set_option autoImplicit false

structure OrbifoldFluxQuantizationLaw where
  singularCycleCompact : Prop
  spinConnectionRestrictsToOrbifoldCycle : Prop
  holonomyQuantumNormalized : Prop
  normalizedFluxIsInteger : Prop

def fluxQuantizationLawClosed (q : OrbifoldFluxQuantizationLaw) : Prop :=
  q.singularCycleCompact /\
  q.spinConnectionRestrictsToOrbifoldCycle /\
  q.holonomyQuantumNormalized /\
  q.normalizedFluxIsInteger

theorem quantization_law_supplies_integer_flux_data
    (q : OrbifoldFluxQuantizationLaw)
    (t : P0EFTOrbifoldFluxIntegerTheorem.OrbifoldFluxIntegerTheorem)
    (_hLaw : fluxQuantizationLawClosed q)
    (hCycle : t.singularCycleDefined)
    (hFlux : t.normalizedSpinConnectionFluxDefined)
    (hInteger : t.integerFluxLawProved) :
    P0EFTOrbifoldFluxIntegerTheorem.integerFluxDataClosed t := by
  unfold P0EFTOrbifoldFluxIntegerTheorem.integerFluxDataClosed
  exact And.intro hCycle (And.intro hFlux hInteger)

theorem missing_normalized_flux_integer_blocks_quantization_law
    (q : OrbifoldFluxQuantizationLaw)
    (hMissing : Not q.normalizedFluxIsInteger) :
    Not (fluxQuantizationLawClosed q) := by
  intro h
  exact hMissing h.right.right.right

theorem missing_holonomy_quantum_blocks_quantization_law
    (q : OrbifoldFluxQuantizationLaw)
    (hMissing : Not q.holonomyQuantumNormalized) :
    Not (fluxQuantizationLawClosed q) := by
  intro h
  exact hMissing h.right.right.left

end P0EFTOrbifoldFluxQuantizationLaw
end JanusFormal
