namespace JanusFormal
namespace P0EFTJanusZ2SigmaCountertermTetradMetricResidualCoefficientInputWriterGate

set_option autoImplicit false

structure CountertermTetradMetricResidualCoefficientInputWriterGate where
  activeCoreZ2TunnelSigma : Prop
  metricResidualInputValid : Prop
  coframeTraceInputValid : Prop
  formulaDeclared : Prop
  noCompressedPlanckLCDM : Prop
  noArchivedZ4Reuse : Prop
  noPhenomenologicalHolstBAOScan : Prop
  noFittedCountertermCoefficient : Prop
  coefficientOutputWritten : Prop

def writerReady
    (g : CountertermTetradMetricResidualCoefficientInputWriterGate) : Prop :=
  g.activeCoreZ2TunnelSigma /\
  g.metricResidualInputValid /\
  g.coframeTraceInputValid /\
  g.formulaDeclared /\
  g.noCompressedPlanckLCDM /\
  g.noArchivedZ4Reuse /\
  g.noPhenomenologicalHolstBAOScan /\
  g.noFittedCountertermCoefficient /\
  g.coefficientOutputWritten

theorem writer_requires_metric_and_coframe_inputs
    (g : CountertermTetradMetricResidualCoefficientInputWriterGate)
    (h : writerReady g) :
    g.metricResidualInputValid /\ g.coframeTraceInputValid := by
  exact And.intro h.2.1 h.2.2.1

theorem writer_forbids_fitted_counterterm_coefficient
    (g : CountertermTetradMetricResidualCoefficientInputWriterGate)
    (h : writerReady g) :
    g.noFittedCountertermCoefficient := by
  rcases h with ⟨_, _, _, _, _, _, _, hNoFit, _⟩
  exact hNoFit

end P0EFTJanusZ2SigmaCountertermTetradMetricResidualCoefficientInputWriterGate
end JanusFormal
