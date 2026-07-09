namespace JanusFormal
namespace P0EFTJanusZ2SigmaStressEquivarianceGate

set_option autoImplicit false

structure StressEquivarianceGate where
  janusZ2StressTransportDeclared : Prop
  perfectFluidStressTransportDeclared : Prop
  holstTorsionStressTransportDeclared : Prop
  thermodynamicDensityNotSignedByHand : Prop
  gravitationalZ2SignPolicyDeclared : Prop
  observationalFitForbidden : Prop
  plusRhoPReady : Prop
  minusRhoPReady : Prop
  rhoPressureZ2TransportDerived : Prop
  fourVelocityZ2TransportDerived : Prop
  metricZ2TransportDerived : Prop
  matterStressZ2EquivarianceDerived : Prop
  holstTorsionStressReady : Prop
  holstTorsionStressZ2EquivarianceDerived : Prop
  totalStressZ2EquivarianceDerived : Prop

def stressEquivarianceReady (g : StressEquivarianceGate) : Prop :=
  g.janusZ2StressTransportDeclared /\
  g.perfectFluidStressTransportDeclared /\
  g.holstTorsionStressTransportDeclared /\
  g.thermodynamicDensityNotSignedByHand /\
  g.gravitationalZ2SignPolicyDeclared /\
  g.observationalFitForbidden /\
  g.plusRhoPReady /\
  g.minusRhoPReady /\
  g.rhoPressureZ2TransportDerived /\
  g.fourVelocityZ2TransportDerived /\
  g.metricZ2TransportDerived /\
  g.matterStressZ2EquivarianceDerived /\
  g.holstTorsionStressReady /\
  g.holstTorsionStressZ2EquivarianceDerived /\
  g.totalStressZ2EquivarianceDerived

theorem stress_equivariance_requires_density_sign_policy
    (g : StressEquivarianceGate)
    (h : stressEquivarianceReady g) :
    g.thermodynamicDensityNotSignedByHand := by
  exact h.2.2.2.1

theorem total_stress_equivariance_requires_matter_and_holst_routes
    (g : StressEquivarianceGate)
    (h : stressEquivarianceReady g) :
    g.matterStressZ2EquivarianceDerived /\
      g.holstTorsionStressZ2EquivarianceDerived := by
  exact And.intro h.2.2.2.2.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.2.2.2.2.2.1

end P0EFTJanusZ2SigmaStressEquivarianceGate
end JanusFormal
