namespace JanusFormal
namespace P0EFTJanusProjectiveS4RP4ConformalBackgroundGate

set_option autoImplicit false

structure ProjectiveS4RP4ConformalBackgroundGate where
  S4LCoverDeclared : Prop
  RP4AntipodalQuotientDeclared : Prop
  StereographicChartDeclared : Prop
  FlatHatMetricAvailableOnPuncturedChart : Prop
  PTPointAsConformalInfinityDeclared : Prop
  OmegaS4ConformalFactorDeclared : Prop
  Z2ProjectiveIdentificationDeclared : Prop
  AbsoluteLFixedByGeometry : Prop
  LorentzianFLRWTimeDerived : Prop
  RhoEffPlusDerived : Prop

def HatBackgroundGeometryClosed
    (g : ProjectiveS4RP4ConformalBackgroundGate) : Prop :=
  g.S4LCoverDeclared /\
  g.RP4AntipodalQuotientDeclared /\
  g.StereographicChartDeclared /\
  g.FlatHatMetricAvailableOnPuncturedChart /\
  g.PTPointAsConformalInfinityDeclared /\
  g.OmegaS4ConformalFactorDeclared /\
  g.Z2ProjectiveIdentificationDeclared

def PredictiveCosmologyClosed
    (g : ProjectiveS4RP4ConformalBackgroundGate) : Prop :=
  HatBackgroundGeometryClosed g /\
  g.AbsoluteLFixedByGeometry /\
  g.LorentzianFLRWTimeDerived /\
  g.RhoEffPlusDerived

def ProjectiveConformalBackgroundFrontier
    (g : ProjectiveS4RP4ConformalBackgroundGate) : Prop :=
  HatBackgroundGeometryClosed g /\
  Not g.AbsoluteLFixedByGeometry /\
  Not g.LorentzianFLRWTimeDerived /\
  Not g.RhoEffPlusDerived

theorem projective_background_is_geometry_not_cosmology
    (g : ProjectiveS4RP4ConformalBackgroundGate)
    (hFrontier : ProjectiveConformalBackgroundFrontier g) :
    Not (PredictiveCosmologyClosed g) := by
  intro h
  exact hFrontier.2.1 h.2.1

end P0EFTJanusProjectiveS4RP4ConformalBackgroundGate
end JanusFormal
