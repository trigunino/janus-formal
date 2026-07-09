import JanusFormal.Branches.AsymptoticNullBoundaryCharges.Gates.P0EFTJanusAsymptoticNullBoundaryCandidateMatrixGate

namespace JanusFormal
namespace P0EFTJanusAsymptoticNullBoundaryChargeDerivationGate

set_option autoImplicit false

structure AsymptoticNullBoundaryChargesChargeDerivationGate where
  asymptoticSymmetryAlgebraDerived : Prop
  surfaceChargeFormulaDerived : Prop
  integrabilityAndFluxBalanceDerived : Prop
  timeTranslationGeneratorSelected : Prop
  bondiOrNullMassChargeDerived : Prop
  chargeMappedToMBridge : Prop

def boundaryMassChargeReady (g : AsymptoticNullBoundaryChargesChargeDerivationGate) : Prop :=
  g.asymptoticSymmetryAlgebraDerived /\
  g.surfaceChargeFormulaDerived /\
  g.integrabilityAndFluxBalanceDerived /\
  g.timeTranslationGeneratorSelected /\
  g.bondiOrNullMassChargeDerived /\
  g.chargeMappedToMBridge

theorem missing_time_generator_blocks_boundary_mass
    (g : AsymptoticNullBoundaryChargesChargeDerivationGate)
    (hMissing : Not g.timeTranslationGeneratorSelected) :
    Not (boundaryMassChargeReady g) := by
  intro h
  exact hMissing h.right.right.right.left

end P0EFTJanusAsymptoticNullBoundaryChargeDerivationGate
end JanusFormal
