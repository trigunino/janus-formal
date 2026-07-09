namespace JanusFormal
namespace P0EFTJanusZ4Local2DCarrierProfilingGate

set_option autoImplicit false

structure Local2DCarrierProfilingGate where
  lambdaFrozen : Prop
  noLambdaRetuning : Prop
  noNewPhysics : Prop
  sameGridForGRAndCandidate : Prop
  nonOverlapAccountingOnly : Prop
  referenceCombinedGainFavorable : Prop
  referenceDecomposedGainFavorable : Prop
  omegaCDMAsPairSurvives : Prop
  omegaCDMNsPairSurvives : Prop
  omegaCDMH0PairSurvives : Prop
  omegaCDMOmegaBPairSurvives : Prop
  local2DCarrierProfiledEffectiveCandidate : Prop
  local2DCarrierDegeneracyDetected : Prop
  profiledPlanckCandidate : Prop
  fullPlanckValidation : Prop

def local2DDegeneracyDiagnostic (g : Local2DCarrierProfilingGate) : Prop :=
  g.lambdaFrozen /\
  g.noLambdaRetuning /\
  g.noNewPhysics /\
  g.sameGridForGRAndCandidate /\
  g.nonOverlapAccountingOnly /\
  g.referenceCombinedGainFavorable /\
  g.referenceDecomposedGainFavorable /\
  Not g.omegaCDMAsPairSurvives /\
  Not g.omegaCDMNsPairSurvives /\
  Not g.omegaCDMH0PairSurvives /\
  Not g.omegaCDMOmegaBPairSurvives /\
  Not g.local2DCarrierProfiledEffectiveCandidate /\
  Not g.profiledPlanckCandidate /\
  Not g.fullPlanckValidation

theorem local_2d_carrier_profiles_detect_degeneracy
    (g : Local2DCarrierProfilingGate)
    (hPolicy : local2DDegeneracyDiagnostic g -> g.local2DCarrierDegeneracyDetected)
    (h : local2DDegeneracyDiagnostic g) :
    g.local2DCarrierDegeneracyDetected := by
  exact hPolicy h

end P0EFTJanusZ4Local2DCarrierProfilingGate
end JanusFormal
