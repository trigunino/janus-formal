namespace JanusFormal
namespace P0EFTJanusProjectiveHhatFromS4RP4LimitGate

set_option autoImplicit false

structure ProjectiveHhatFromS4RP4LimitGate where
  ConformalHatMetricAvailable : Prop
  PTCuspCoordinateAvailable : Prop
  OmegaS4FactorAvailable : Prop
  HatCurvatureScaleDependsOnL : Prop
  AbsoluteLFixed : Prop
  LorentzianTimeSlicingFixed : Prop
  HatHAsObservableClockFixed : Prop

def HhatGeometryClosed
    (g : ProjectiveHhatFromS4RP4LimitGate) : Prop :=
  g.ConformalHatMetricAvailable /\
  g.PTCuspCoordinateAvailable /\
  g.OmegaS4FactorAvailable /\
  g.HatCurvatureScaleDependsOnL

def HhatDynamicsClosed
    (g : ProjectiveHhatFromS4RP4LimitGate) : Prop :=
  HhatGeometryClosed g /\
  g.AbsoluteLFixed /\
  g.LorentzianTimeSlicingFixed /\
  g.HatHAsObservableClockFixed

def HhatFrontier
    (g : ProjectiveHhatFromS4RP4LimitGate) : Prop :=
  HhatGeometryClosed g /\
  Not g.AbsoluteLFixed /\
  Not g.LorentzianTimeSlicingFixed /\
  Not g.HatHAsObservableClockFixed

theorem projective_hhat_geometry_does_not_fix_clock
    (g : ProjectiveHhatFromS4RP4LimitGate)
    (hFrontier : HhatFrontier g) :
    Not (HhatDynamicsClosed g) := by
  intro h
  exact hFrontier.2.1 h.2.1

end P0EFTJanusProjectiveHhatFromS4RP4LimitGate
end JanusFormal
