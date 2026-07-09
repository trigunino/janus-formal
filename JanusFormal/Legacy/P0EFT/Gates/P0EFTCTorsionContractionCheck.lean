import JanusFormal.Legacy.P0EFT.Gates.P0EFTTorsionEnergyNormalization

namespace JanusFormal
namespace P0EFTCTorsionContractionCheck

set_option autoImplicit false

structure CTorsionContractionCheck where
  traceAxialAnsatzLoaded : Prop
  contractionTargetEncoded : Prop
  ecNormalizationFixed : Prop
  cTorsionDerived : Prop
  alphaIsoFullyDerived : Prop

def cTorsionContractionReady (c : CTorsionContractionCheck) : Prop :=
  c.traceAxialAnsatzLoaded /\
  c.contractionTargetEncoded /\
  c.ecNormalizationFixed

def cTorsionClosed (c : CTorsionContractionCheck) : Prop :=
  cTorsionContractionReady c /\
  c.cTorsionDerived /\
  c.alphaIsoFullyDerived

theorem missing_ec_normalization_blocks_ctorsion
    (c : CTorsionContractionCheck)
    (hMissing : Not c.ecNormalizationFixed) :
    Not (cTorsionClosed c) := by
  intro h
  exact hMissing h.left.right.right

end P0EFTCTorsionContractionCheck
end JanusFormal
