namespace JanusFormal
namespace P0EFTPrimordialLowESectorGate

set_option autoImplicit false

structure PrimordialLowESectorGate where
  reionizationLowEOnlyTested : Prop
  perfectLowEStillRejected : Prop
  highLTransferDominatesResidual : Prop
  perfectHighLStillRejected : Prop
  primordialHighLTransferDerived : Prop
  lowEReionizationDerived : Prop

def reionizationOnlyExcluded (g : PrimordialLowESectorGate) : Prop :=
  g.reionizationLowEOnlyTested /\
  g.perfectLowEStillRejected

def highLOnlyExcluded (g : PrimordialLowESectorGate) : Prop :=
  g.highLTransferDominatesResidual /\
  g.perfectHighLStillRejected

def requiresCombinedPrimordialLowESector (g : PrimordialLowESectorGate) : Prop :=
  reionizationOnlyExcluded g /\
  highLOnlyExcluded g

def cmbNoFitReadyAfterLowEGate (g : PrimordialLowESectorGate) : Prop :=
  requiresCombinedPrimordialLowESector g /\
  g.primordialHighLTransferDerived /\
  g.lowEReionizationDerived

theorem lowe_only_cannot_rescue_branch
    (g : PrimordialLowESectorGate)
    (hTested : g.reionizationLowEOnlyTested)
    (hRejected : g.perfectLowEStillRejected) :
    reionizationOnlyExcluded g := by
  exact And.intro hTested hRejected

theorem highl_transfer_required
    (g : PrimordialLowESectorGate)
    (hLowE : reionizationOnlyExcluded g)
    (hHighL : g.highLTransferDominatesResidual) :
    g.perfectHighLStillRejected ->
    requiresCombinedPrimordialLowESector g := by
  intro hHighLRejected
  exact And.intro hLowE (And.intro hHighL hHighLRejected)

theorem missing_primordial_transfer_blocks_no_fit
    (g : PrimordialLowESectorGate)
    (_hReq : requiresCombinedPrimordialLowESector g)
    (hMissing : Not g.primordialHighLTransferDerived) :
    Not (cmbNoFitReadyAfterLowEGate g) := by
  intro h
  exact hMissing h.right.left

end P0EFTPrimordialLowESectorGate
end JanusFormal
