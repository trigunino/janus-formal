namespace JanusFormal
namespace P0EFTJanusGPlusWeylCuspKinematicPullbackGate

set_option autoImplicit false

structure GPlusWeylCuspKinematicPullbackGate where
  GPlusConformalDecompositionDeclared : Prop
  VisibleProperTimeRelationDeclared : Prop
  VisibleScaleFactorRelationDeclared : Prop
  VisibleRedshiftRelationDeclared : Prop
  VisibleHubbleRelationDeclared : Prop
  PTCuspRedshiftDomainAvailable : Prop
  OmegaDynamicsDerived : Prop
  SourceTermsInConformalFrameDerived : Prop

def KinematicPullbackClosed
    (g : GPlusWeylCuspKinematicPullbackGate) : Prop :=
  g.GPlusConformalDecompositionDeclared /\
  g.VisibleProperTimeRelationDeclared /\
  g.VisibleScaleFactorRelationDeclared /\
  g.VisibleRedshiftRelationDeclared /\
  g.VisibleHubbleRelationDeclared /\
  g.PTCuspRedshiftDomainAvailable

def PredictiveDynamicsClosed
    (g : GPlusWeylCuspKinematicPullbackGate) : Prop :=
  KinematicPullbackClosed g /\
  g.OmegaDynamicsDerived /\
  g.SourceTermsInConformalFrameDerived

def KinematicButNotDynamicFrontier
    (g : GPlusWeylCuspKinematicPullbackGate) : Prop :=
  KinematicPullbackClosed g /\
  Not g.OmegaDynamicsDerived /\
  Not g.SourceTermsInConformalFrameDerived

theorem kinematic_pullback_does_not_predict_without_omega
    (g : GPlusWeylCuspKinematicPullbackGate)
    (hFrontier : KinematicButNotDynamicFrontier g) :
    Not (PredictiveDynamicsClosed g) := by
  intro h
  exact hFrontier.2.1 h.2.1

end P0EFTJanusGPlusWeylCuspKinematicPullbackGate
end JanusFormal
