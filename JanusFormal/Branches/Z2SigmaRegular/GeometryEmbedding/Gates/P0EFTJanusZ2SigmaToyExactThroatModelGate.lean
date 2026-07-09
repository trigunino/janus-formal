namespace JanusFormal
namespace P0EFTJanusZ2SigmaToyExactThroatModelGate

set_option autoImplicit false

structure ToyExactThroatModelGate where
  toyDiagnosticOnly : Prop
  finiteRoundThroatDeclared : Prop
  hAbEven : Prop
  kAbOdd : Prop
  kTraceOdd : Prop
  kSquaredEven : Prop
  intrinsicCurvatureEven : Prop
  notPromotedToActiveCountertermProof : Prop
  notPromotedToTransportBianchiProof : Prop
  notPromotedToSCrossSourceProof : Prop

def toyModelReady (g : ToyExactThroatModelGate) : Prop :=
  g.toyDiagnosticOnly /\
  g.finiteRoundThroatDeclared /\
  g.hAbEven /\
  g.kAbOdd /\
  g.kTraceOdd /\
  g.kSquaredEven /\
  g.intrinsicCurvatureEven /\
  g.notPromotedToActiveCountertermProof /\
  g.notPromotedToTransportBianchiProof /\
  g.notPromotedToSCrossSourceProof

theorem toy_model_does_not_prove_active_counterterm
    (g : ToyExactThroatModelGate)
    (hReady : toyModelReady g) :
    g.notPromotedToActiveCountertermProof := by
  exact hReady.2.2.2.2.2.2.2.1

theorem toy_model_does_not_prove_transport_bianchi
    (g : ToyExactThroatModelGate)
    (hReady : toyModelReady g) :
    g.notPromotedToTransportBianchiProof := by
  exact hReady.2.2.2.2.2.2.2.2.1

theorem toy_model_does_not_prove_s_cross_source
    (g : ToyExactThroatModelGate)
    (hReady : toyModelReady g) :
    g.notPromotedToSCrossSourceProof := by
  exact hReady.2.2.2.2.2.2.2.2.2

theorem linear_k_terms_are_odd_in_toy_model
    (g : ToyExactThroatModelGate)
    (hReady : toyModelReady g) :
    g.kTraceOdd := by
  exact hReady.2.2.2.2.1

theorem quadratic_k_terms_are_even_in_toy_model
    (g : ToyExactThroatModelGate)
    (hReady : toyModelReady g) :
    g.kSquaredEven := by
  exact hReady.2.2.2.2.2.1

end P0EFTJanusZ2SigmaToyExactThroatModelGate
end JanusFormal
