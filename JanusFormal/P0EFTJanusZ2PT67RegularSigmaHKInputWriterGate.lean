namespace JanusFormal
namespace P0EFTJanusZ2PT67RegularSigmaHKInputWriterGate

set_option autoImplicit false

structure PT67RegularSigmaHKInputWriterGate where
  hAbNondegenerate : Prop
  unitNormalReady : Prop
  localKAbReady : Prop
  deltaKPTTransportReady : Prop
  cartanGHYJumpReadyUnderPTTransport : Prop
  usesObservationalFit : Prop
  usesFreeOrientationSign : Prop
  regularSigmaPipelineInputsReady : Prop

def strictPT67HKInputsReady
    (g : PT67RegularSigmaHKInputWriterGate) : Prop :=
  g.hAbNondegenerate /\
  g.unitNormalReady /\
  g.localKAbReady /\
  g.deltaKPTTransportReady /\
  g.cartanGHYJumpReadyUnderPTTransport /\
  Not g.usesObservationalFit /\
  Not g.usesFreeOrientationSign

theorem strict_inputs_enable_regular_sigma_pipeline
    (g : PT67RegularSigmaHKInputWriterGate)
    (hReady : strictPT67HKInputsReady g)
    (hNeeds : strictPT67HKInputsReady g -> g.regularSigmaPipelineInputsReady) :
    g.regularSigmaPipelineInputsReady := by
  exact hNeeds hReady

end P0EFTJanusZ2PT67RegularSigmaHKInputWriterGate
end JanusFormal
