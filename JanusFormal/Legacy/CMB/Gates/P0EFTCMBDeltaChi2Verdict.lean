namespace JanusFormal
namespace P0EFTCMBDeltaChi2Verdict

set_option autoImplicit false

structure CMBDeltaChi2Verdict where
  rawPlanckLikelihoodUsed : Prop
  lcdmUsedOnlyAsOffsetCalibration : Prop
  lowENotBlockingAfterCalibration : Prop
  highLResidualBlocker : Prop
  lensingResidualBlocker : Prop

def calibratedCMBVerdictReady (v : CMBDeltaChi2Verdict) : Prop :=
  v.rawPlanckLikelihoodUsed /\
  v.lcdmUsedOnlyAsOffsetCalibration /\
  v.lowENotBlockingAfterCalibration /\
  v.highLResidualBlocker /\
  v.lensingResidualBlocker

theorem delta_chi2_verdict_separates_data_from_offset
    (v : CMBDeltaChi2Verdict)
    (hRaw : v.rawPlanckLikelihoodUsed)
    (hOffset : v.lcdmUsedOnlyAsOffsetCalibration)
    (hLowE : v.lowENotBlockingAfterCalibration)
    (hHighL : v.highLResidualBlocker)
    (hLensing : v.lensingResidualBlocker) :
    calibratedCMBVerdictReady v := by
  exact And.intro hRaw (And.intro hOffset (And.intro hLowE (And.intro hHighL hLensing)))

end P0EFTCMBDeltaChi2Verdict
end JanusFormal
