import JanusFormal.Basic

namespace JanusFormal
namespace P0EFTJanusZ2SigmaResolvedThroatBoundaryTraceTargetsGate

set_option autoImplicit false

structure ResolvedThroatBoundaryTraceTargetsGate where
  sigmaIsGeometricBoundaryInterface : Prop
  projectiveZ2IdentificationDeclared : Prop
  inducedMetricEquivariant : Prop
  normalOrientationReversal : Prop
  extrinsicCurvatureReversal : Prop
  stationaryThroatConditionDeclared : Prop
  fluxTransparencyTargetDeclared : Prop
  noFreeBoundaryStressDeclared : Prop
  junctionConditionAvailable : Prop
  normalFluxCancellationLedgerAvailable : Prop
  minimalDensityBasisAvailable : Prop
  rSigmaSolutionCertificateSupported : Prop
  rHTraceRequired : Prop
  rKTraceRequired : Prop
  rHTraceDerived : Prop
  rKTraceDerived : Prop
  localActionVariationTraceValuesAvailable : Prop

def resolvedThroatTraceTargetLedgerDeclared
    (g : ResolvedThroatBoundaryTraceTargetsGate) : Prop :=
  g.sigmaIsGeometricBoundaryInterface /\
  g.projectiveZ2IdentificationDeclared /\
  g.inducedMetricEquivariant /\
  g.normalOrientationReversal /\
  g.extrinsicCurvatureReversal /\
  g.stationaryThroatConditionDeclared /\
  g.fluxTransparencyTargetDeclared /\
  g.noFreeBoundaryStressDeclared /\
  g.junctionConditionAvailable /\
  g.normalFluxCancellationLedgerAvailable /\
  g.minimalDensityBasisAvailable /\
  g.rSigmaSolutionCertificateSupported /\
  g.rHTraceRequired /\
  g.rKTraceRequired

def resolvedThroatTraceValuesReady
    (g : ResolvedThroatBoundaryTraceTargetsGate) : Prop :=
  resolvedThroatTraceTargetLedgerDeclared g /\
  g.rHTraceDerived /\
  g.rKTraceDerived /\
  g.localActionVariationTraceValuesAvailable

theorem trace_values_require_local_action_variation
    (g : ResolvedThroatBoundaryTraceTargetsGate)
    (hReady : resolvedThroatTraceValuesReady g) :
    g.localActionVariationTraceValuesAvailable := by
  exact hReady.2.2.2

end P0EFTJanusZ2SigmaResolvedThroatBoundaryTraceTargetsGate
end JanusFormal
