import JanusFormal.P0CoreGaugeLikeJanusClosure

namespace JanusFormal
namespace P0TensorParameterDerivations

open P0LinearTensorPerturbationStability
open P0GaugeLikeAetherTopology

set_option autoImplicit false

structure QuadraticTensorParameters where
  alpha : Rat
  beta : Rat
  plusSpeedSquared : Rat
  minusSpeedSquared : Rat
  massSquared : Rat
  visibleSpeedUnmodified : Prop

def noGhostFromParams (p : QuadraticTensorParameters) : Prop :=
  0 < p.alpha

def noGradientFromParams (p : QuadraticTensorParameters) : Prop :=
  0 < p.beta /\ 0 < p.plusSpeedSquared /\ 0 < p.minusSpeedSquared

def massMatrixStableFromParams (p : QuadraticTensorParameters) : Prop :=
  0 <= p.massSquared

def hyperbolicMinusFromParams (p : QuadraticTensorParameters) : Prop :=
  0 < p.alpha /\ 0 < p.beta /\ 0 < p.minusSpeedSquared

def tensorCoefficientsFromParams
    (p : QuadraticTensorParameters)
    (g : GaugeLikeAetherTopology) :
    TensorQuadraticCoefficients :=
  { alphaPositive := noGhostFromParams p
    betaPositive := 0 < p.beta
    plusSpeedSquaredPositive := 0 < p.plusSpeedSquared
    massMatrixPositive := massMatrixStableFromParams p
    c1PlusC3Zero := c1PlusC3Zero (coefficientsFromGaugeLikeAether g)
    visibleTensorLuminal := p.visibleSpeedUnmodified
    minusSectorHyperbolic := hyperbolicMinusFromParams p }

structure QuadraticTensorParameterCertificate where
  params : QuadraticTensorParameters
  gaugeAether : GaugeLikeAetherTopology
  gaugeClosed : gaugeLikeAetherClosed gaugeAether
  visibleSpeed : params.visibleSpeedUnmodified
  alphaPositive : 0 < params.alpha
  betaPositive : 0 < params.beta
  plusSpeedPositive : 0 < params.plusSpeedSquared
  minusSpeedPositive : 0 < params.minusSpeedSquared
  massNonnegative : 0 <= params.massSquared

def tensorCoefficientsFromCertificate
    (c : QuadraticTensorParameterCertificate) :
    TensorQuadraticCoefficients :=
  tensorCoefficientsFromParams c.params c.gaugeAether

theorem certificate_derives_no_ghost
    (c : QuadraticTensorParameterCertificate) :
    (tensorCoefficientsFromCertificate c).alphaPositive := by
  exact c.alphaPositive

theorem certificate_derives_no_gradient
    (c : QuadraticTensorParameterCertificate) :
    noTensorGradientInstability (tensorCoefficientsFromCertificate c) := by
  exact ⟨c.betaPositive, c.plusSpeedPositive,
    ⟨c.alphaPositive, c.betaPositive, c.minusSpeedPositive⟩⟩

theorem certificate_derives_mass_stability
    (c : QuadraticTensorParameterCertificate) :
    (tensorCoefficientsFromCertificate c).massMatrixPositive := by
  exact c.massNonnegative

theorem certificate_derives_gauge_luminality
    (c : QuadraticTensorParameterCertificate) :
    visibleGravitationalWaveLuminal (tensorCoefficientsFromCertificate c) := by
  exact ⟨gauge_like_aether_forces_luminal_combination c.gaugeAether c.gaugeClosed,
    c.visibleSpeed⟩

theorem certificate_derives_tensor_stability
    (c : QuadraticTensorParameterCertificate) :
    tensorPerturbationsStable (tensorCoefficientsFromCertificate c) := by
  exact ⟨certificate_derives_no_ghost c,
    certificate_derives_no_gradient c,
    certificate_derives_gauge_luminality c,
    certificate_derives_mass_stability c⟩

def linearTensorCertificateFromParams
    (setup : TensorPerturbationSetup)
    (hSetup : tensorSetupClosed setup)
    (c : QuadraticTensorParameterCertificate) :
    LinearTensorPerturbationCertificate :=
  { setup := setup
    coeffs := tensorCoefficientsFromCertificate c
    setupClosed := hSetup
    stable := certificate_derives_tensor_stability c }

theorem alpha_zero_or_negative_blocks_certificate
    (p : QuadraticTensorParameters)
    (hMissing : Not (0 < p.alpha)) :
    Not (Nonempty
      { c : QuadraticTensorParameterCertificate // c.params = p }) := by
  intro hCert
  rcases hCert with ⟨c, hc⟩
  have hAlpha : 0 < p.alpha := by
    simpa [hc] using c.alphaPositive
  exact hMissing hAlpha

theorem beta_zero_or_negative_blocks_certificate
    (p : QuadraticTensorParameters)
    (hMissing : Not (0 < p.beta)) :
    Not (Nonempty
      { c : QuadraticTensorParameterCertificate // c.params = p }) := by
  intro hCert
  rcases hCert with ⟨c, hc⟩
  have hBeta : 0 < p.beta := by
    simpa [hc] using c.betaPositive
  exact hMissing hBeta

theorem negative_mass_squared_blocks_certificate
    (p : QuadraticTensorParameters)
    (hMissing : Not (0 <= p.massSquared)) :
    Not (Nonempty
      { c : QuadraticTensorParameterCertificate // c.params = p }) := by
  intro hCert
  rcases hCert with ⟨c, hc⟩
  have hMass : 0 <= p.massSquared := by
    simpa [hc] using c.massNonnegative
  exact hMissing hMass

end P0TensorParameterDerivations
end JanusFormal
