namespace JanusFormal
namespace P0EFTJanusZ2SigmaSurfaceActionOrNoGoGate

set_option autoImplicit false

structure SurfaceActionOrNoGoGate where
  mplaLocalThroatReady : Prop
  projectiveRatioReady : Prop
  souriauGlobalChargeReady : Prop
  souriauLocalDensityReady : Prop
  countertermChainPassed : Prop
  surfaceHKCoefficientsAvailable : Prop
  countertermTraceInputsAvailable : Prop
  eCountertermClosed : Prop
  sigmaAlphaHClosed : Prop
  noObservationFitForCoefficients : Prop
  noGlobalChargeAsLocalDensityShortcut : Prop
  noArchivedZ4CoefficientReuse : Prop

def positiveNoExtensionInputsReady
    (g : SurfaceActionOrNoGoGate) : Prop :=
  g.mplaLocalThroatReady /\
  g.projectiveRatioReady /\
  g.souriauGlobalChargeReady /\
  g.noObservationFitForCoefficients /\
  g.noGlobalChargeAsLocalDensityShortcut /\
  g.noArchivedZ4CoefficientReuse

theorem missing_local_density_and_coefficients_blocks_counterterm
    (g : SurfaceActionOrNoGoGate)
    (_hPositive : positiveNoExtensionInputsReady g)
    (hNoDensity : Not g.souriauLocalDensityReady)
    (hNoHK : Not g.surfaceHKCoefficientsAvailable)
    (hNoTrace : Not g.countertermTraceInputsAvailable)
    (hCountertermNeedsOne :
      g.eCountertermClosed ->
        g.souriauLocalDensityReady \/
        g.surfaceHKCoefficientsAvailable \/
        g.countertermTraceInputsAvailable) :
    Not g.eCountertermClosed := by
  intro hClosed
  rcases hCountertermNeedsOne hClosed with hDensity | hRest
  · exact hNoDensity hDensity
  · rcases hRest with hHK | hTrace
    · exact hNoHK hHK
    · exact hNoTrace hTrace

theorem missing_counterterm_trace_blocks_sigma_alpha_h
    (g : SurfaceActionOrNoGoGate)
    (hNoTrace : Not g.countertermTraceInputsAvailable)
    (hSigmaNeedsTrace : g.sigmaAlphaHClosed -> g.countertermTraceInputsAvailable) :
    Not g.sigmaAlphaHClosed := by
  intro hSigma
  exact hNoTrace (hSigmaNeedsTrace hSigma)

end P0EFTJanusZ2SigmaSurfaceActionOrNoGoGate
end JanusFormal
