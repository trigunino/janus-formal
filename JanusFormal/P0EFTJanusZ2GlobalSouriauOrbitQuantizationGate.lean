namespace JanusFormal
namespace P0EFTJanusZ2GlobalSouriauOrbitQuantizationGate

set_option autoImplicit false

structure GlobalSouriauOrbitQuantizationGate where
  globalStateSpaceDeclared : Prop
  coadjointOrbitsDeclared : Prop
  massCasimirIdentified : Prop
  ptPairingDeclared : Prop
  geometricQuantizationPerformed : Prop
  integralityConditionOnOrbit : Prop
  massOrbitLatticeDerived : Prop
  minimalMassUnitAvailable : Prop

def globalOrbitQuantized (g : GlobalSouriauOrbitQuantizationGate) : Prop :=
  g.globalStateSpaceDeclared /\
  g.coadjointOrbitsDeclared /\
  g.massCasimirIdentified /\
  g.ptPairingDeclared /\
  g.geometricQuantizationPerformed /\
  g.integralityConditionOnOrbit /\
  g.massOrbitLatticeDerived /\
  g.minimalMassUnitAvailable

theorem mass_casimir_without_lattice_does_not_quantize_alpha
    (g : GlobalSouriauOrbitQuantizationGate)
    (hMissing : Not g.massOrbitLatticeDerived) :
    Not (globalOrbitQuantized g) := by
  intro h
  exact hMissing h.right.right.right.right.right.right.left

theorem missing_minimal_unit_blocks_global_quantization
    (g : GlobalSouriauOrbitQuantizationGate)
    (hMissing : Not g.minimalMassUnitAvailable) :
    Not (globalOrbitQuantized g) := by
  intro h
  exact hMissing h.right.right.right.right.right.right.right

end P0EFTJanusZ2GlobalSouriauOrbitQuantizationGate
end JanusFormal
