namespace JanusFormal
namespace P0EFTJanusZ2PT67CartanGHYDeltaKInputWriterGate

set_option autoImplicit false

structure PT67CartanGHYDeltaKInputWriterGate where
  activeCoreZ2Sigma : Prop
  pt67RegularSigmaHKInputsReady : Prop
  ptTransportRuleFixed : Prop
  deltaKTTZero : Prop
  deltaKScreenTraceZero : Prop
  deltaKsOfAZero : Prop
  deltaKtauOfAZero : Prop
  ptTransportNotOutwardIsraelConvention : Prop
  freeOrientationSignForbidden : Prop
  observationalFitForbidden : Prop
  archivedZ4ReuseForbidden : Prop
  cartanGHYDeltaKInputsReady : Prop

def canWritePT67CartanDeltaKInputs
    (g : PT67CartanGHYDeltaKInputWriterGate) : Prop :=
  g.activeCoreZ2Sigma /\
  g.pt67RegularSigmaHKInputsReady /\
  g.ptTransportRuleFixed /\
  g.deltaKTTZero /\
  g.deltaKScreenTraceZero /\
  g.deltaKsOfAZero /\
  g.deltaKtauOfAZero /\
  g.ptTransportNotOutwardIsraelConvention /\
  g.freeOrientationSignForbidden /\
  g.observationalFitForbidden /\
  g.archivedZ4ReuseForbidden

theorem pt67_deltaK_inputs_are_zero
    (g : PT67CartanGHYDeltaKInputWriterGate)
    (h : canWritePT67CartanDeltaKInputs g) :
    g.deltaKsOfAZero /\ g.deltaKtauOfAZero := by
  rcases h with ⟨_, _, _, _, _, hKs, hKtau, _, _, _, _⟩
  exact ⟨hKs, hKtau⟩

theorem pt67_deltaK_inputs_forbid_free_orientation_and_fit
    (g : PT67CartanGHYDeltaKInputWriterGate)
    (h : canWritePT67CartanDeltaKInputs g) :
    g.freeOrientationSignForbidden /\ g.observationalFitForbidden := by
  rcases h with ⟨_, _, _, _, _, _, _, _, hOrient, hFit, _⟩
  exact ⟨hOrient, hFit⟩

theorem pt67_deltaK_inputs_keep_PT_convention_explicit
    (g : PT67CartanGHYDeltaKInputWriterGate)
    (h : canWritePT67CartanDeltaKInputs g) :
    g.ptTransportNotOutwardIsraelConvention := by
  rcases h with ⟨_, _, _, _, _, _, _, hConvention, _, _, _⟩
  exact hConvention

end P0EFTJanusZ2PT67CartanGHYDeltaKInputWriterGate
end JanusFormal
