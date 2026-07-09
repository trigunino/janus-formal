import JanusFormal.Branches.P0EFTOrbifoldHolstPrototypeProgram.Gates.P0EFTSpinlessIsotropicAlphaBranch

namespace JanusFormal
namespace P0EFTTorsionEnergyNormalization

set_option autoImplicit false

structure TorsionEnergyNormalization where
  torsionEnergyScalingEncoded : Prop
  hSquaredScaleSelected : Prop
  omegaTorsionDefined : Prop
  normalizationReducedToCTorsion : Prop
  cTorsionDerived : Prop
  alphaIsoFullyDerived : Prop

def torsionEnergyReduced (t : TorsionEnergyNormalization) : Prop :=
  t.torsionEnergyScalingEncoded /\
  t.hSquaredScaleSelected /\
  t.omegaTorsionDefined /\
  t.normalizationReducedToCTorsion

def torsionEnergyClosed (t : TorsionEnergyNormalization) : Prop :=
  torsionEnergyReduced t /\
  t.cTorsionDerived /\
  t.alphaIsoFullyDerived

theorem torsion_energy_reduces_to_ctorsion
    (t : TorsionEnergyNormalization)
    (hScale : t.torsionEnergyScalingEncoded)
    (hH : t.hSquaredScaleSelected)
    (hOmega : t.omegaTorsionDefined)
    (hC : t.normalizationReducedToCTorsion) :
    torsionEnergyReduced t := by
  exact And.intro hScale (And.intro hH (And.intro hOmega hC))

theorem missing_ctorsion_blocks_alpha_iso
    (t : TorsionEnergyNormalization)
    (hMissing : Not t.cTorsionDerived) :
    Not (torsionEnergyClosed t) := by
  intro h
  exact hMissing h.right.left

end P0EFTTorsionEnergyNormalization
end JanusFormal
