namespace JanusFormal
namespace P0EFTEarlyHolstPlasmaStressTensor

set_option autoImplicit false

structure EarlyHolstPlasmaStressTensor where
  niehYanHolstTraceWeightDerived : Prop
  comovingMatterSpinChargeConserved : Prop
  deltaNeffEqualsEtaTimesOmegaM : Prop
  fullCMBTransferFunctionsDerived : Prop

def earlyStressTensorRelationReady (e : EarlyHolstPlasmaStressTensor) : Prop :=
  e.niehYanHolstTraceWeightDerived /\
  e.comovingMatterSpinChargeConserved /\
  e.deltaNeffEqualsEtaTimesOmegaM

def directCMBNoFitReady (e : EarlyHolstPlasmaStressTensor) : Prop :=
  earlyStressTensorRelationReady e /\
  e.fullCMBTransferFunctionsDerived

theorem holst_plasma_stress_tensor_closes_delta_neff_relation
    (e : EarlyHolstPlasmaStressTensor)
    (hTrace : e.niehYanHolstTraceWeightDerived)
    (hCharge : e.comovingMatterSpinChargeConserved)
    (hRelation : e.deltaNeffEqualsEtaTimesOmegaM) :
    earlyStressTensorRelationReady e := by
  exact And.intro hTrace (And.intro hCharge hRelation)

theorem missing_transfer_functions_blocks_direct_cmb
    (e : EarlyHolstPlasmaStressTensor)
    (hMissing : Not e.fullCMBTransferFunctionsDerived) :
    Not (directCMBNoFitReady e) := by
  intro h
  exact hMissing h.right

end P0EFTEarlyHolstPlasmaStressTensor
end JanusFormal
