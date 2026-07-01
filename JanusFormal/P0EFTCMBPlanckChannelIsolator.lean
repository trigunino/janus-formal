namespace JanusFormal
namespace P0EFTCMBPlanckChannelIsolator

set_option autoImplicit false

structure PlanckChannelIsolator where
  highTTGateRun : Prop
  highTEGateRun : Prop
  highEEGateRun : Prop
  lowTTGateRun : Prop
  lowEEGateRun : Prop
  lensingGateRun : Prop
  worstChannelRecorded : Prop

def channelIsolatorReady (c : PlanckChannelIsolator) : Prop :=
  c.highTTGateRun /\
  c.highTEGateRun /\
  c.highEEGateRun /\
  c.lowTTGateRun /\
  c.lowEEGateRun /\
  c.lensingGateRun /\
  c.worstChannelRecorded

theorem channel_isolator_ready_from_all_gates
    (c : PlanckChannelIsolator)
    (hTT : c.highTTGateRun)
    (hTE : c.highTEGateRun)
    (hEE : c.highEEGateRun)
    (hLowTT : c.lowTTGateRun)
    (hLowEE : c.lowEEGateRun)
    (hLens : c.lensingGateRun)
    (hWorst : c.worstChannelRecorded) :
    channelIsolatorReady c := by
  exact And.intro hTT
    (And.intro hTE
      (And.intro hEE
        (And.intro hLowTT
          (And.intro hLowEE
            (And.intro hLens hWorst)))))

end P0EFTCMBPlanckChannelIsolator
end JanusFormal
