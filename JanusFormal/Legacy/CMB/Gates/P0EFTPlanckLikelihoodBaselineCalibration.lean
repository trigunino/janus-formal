namespace JanusFormal
namespace P0EFTPlanckLikelihoodBaselineCalibration

set_option autoImplicit false

structure PlanckLikelihoodCalibration where
  referencePointEvaluated : Prop
  janusPointEvaluated : Prop
  lcdmReferenceUsedOnlyAsNumericalOffset : Prop
  rawPlanckLikelihoodUsed : Prop
  lowEAbsoluteOffsetCalibrated : Prop
  deltaChi2PrimaryBlockerIdentified : Prop

def calibratedDiagnosticsReady (c : PlanckLikelihoodCalibration) : Prop :=
  c.referencePointEvaluated /\
  c.janusPointEvaluated /\
  c.lcdmReferenceUsedOnlyAsNumericalOffset /\
  c.rawPlanckLikelihoodUsed /\
  c.lowEAbsoluteOffsetCalibrated /\
  c.deltaChi2PrimaryBlockerIdentified

theorem calibration_requires_reference_and_janus
    (c : PlanckLikelihoodCalibration)
    (hRef : c.referencePointEvaluated)
    (hJanus : c.janusPointEvaluated)
    (hOffsetOnly : c.lcdmReferenceUsedOnlyAsNumericalOffset)
    (hRaw : c.rawPlanckLikelihoodUsed)
    (hLowE : c.lowEAbsoluteOffsetCalibrated)
    (hDelta : c.deltaChi2PrimaryBlockerIdentified) :
    calibratedDiagnosticsReady c := by
  exact And.intro hRef (And.intro hJanus (And.intro hOffsetOnly (And.intro hRaw (And.intro hLowE hDelta))))

end P0EFTPlanckLikelihoodBaselineCalibration
end JanusFormal
