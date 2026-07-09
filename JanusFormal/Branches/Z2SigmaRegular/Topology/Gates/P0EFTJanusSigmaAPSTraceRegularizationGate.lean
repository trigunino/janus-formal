namespace JanusFormal
namespace P0EFTJanusSigmaAPSTraceRegularizationGate

set_option autoImplicit false

structure SigmaAPSTraceRegularizationGate where
  sigmaApsBoundaryPinLiftClosed : Prop
  cliffordTraceNormalizationDeclared : Prop
  apsHeatKernelRegularizationDeclared : Prop
  traceRegularizationStandardGlobal : Prop

def sigmaApsTraceRegularizationClosed
    (g : SigmaAPSTraceRegularizationGate) : Prop :=
  g.sigmaApsBoundaryPinLiftClosed /\
  g.cliffordTraceNormalizationDeclared /\
  g.apsHeatKernelRegularizationDeclared /\
  g.traceRegularizationStandardGlobal

theorem trace_regularization_follows_closed_sigma_aps_package
    (g : SigmaAPSTraceRegularizationGate)
    (h : sigmaApsTraceRegularizationClosed g) :
    g.traceRegularizationStandardGlobal := by
  exact h.2.2.2

end P0EFTJanusSigmaAPSTraceRegularizationGate
end JanusFormal
