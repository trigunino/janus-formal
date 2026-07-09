import JanusFormal.Branches.P0BimetricOrbifoldPrototypeProgram.Gates.P0TensorParameterDerivations

namespace JanusFormal
namespace P0SymbolicTensorCoefficientMap

open P0TensorParameterDerivations
open P0GaugeLikeAetherTopology
open P0LinearTensorPerturbationStability

set_option autoImplicit false

structure SymbolicOrbifoldActionParams where
  plusPlanckMassSquared : Rat
  minusPlanckMassSquared : Rat
  radionVev : Rat
  aetherKineticScale : Rat
  membraneTension : Rat
  hassanRosenMassSquared : Rat
  visibleSpeedUnmodified : Prop

def alphaFromAction (p : SymbolicOrbifoldActionParams) : Rat :=
  p.radionVev * (p.minusPlanckMassSquared - p.aetherKineticScale)

def betaFromAction (p : SymbolicOrbifoldActionParams) : Rat :=
  p.minusPlanckMassSquared + p.membraneTension

def plusSpeedSquaredFromAction (_p : SymbolicOrbifoldActionParams) : Rat :=
  1

def minusSpeedSquaredFromAction (p : SymbolicOrbifoldActionParams) : Rat :=
  betaFromAction p / alphaFromAction p

def massSquaredFromAction (p : SymbolicOrbifoldActionParams) : Rat :=
  p.hassanRosenMassSquared

def tensorParamsFromAction
    (p : SymbolicOrbifoldActionParams) :
    QuadraticTensorParameters :=
  { alpha := alphaFromAction p
    beta := betaFromAction p
    plusSpeedSquared := plusSpeedSquaredFromAction p
    minusSpeedSquared := minusSpeedSquaredFromAction p
    massSquared := massSquaredFromAction p
    visibleSpeedUnmodified := p.visibleSpeedUnmodified }

structure SymbolicActionSignCertificate where
  params : SymbolicOrbifoldActionParams
  gaugeAether : GaugeLikeAetherTopology
  gaugeClosed : gaugeLikeAetherClosed gaugeAether
  visibleSpeed : params.visibleSpeedUnmodified
  alphaPositive : 0 < alphaFromAction params
  betaPositive : 0 < betaFromAction params
  massNonnegative : 0 <= massSquaredFromAction params

theorem plus_speed_squared_positive_from_action
    (p : SymbolicOrbifoldActionParams) :
    0 < plusSpeedSquaredFromAction p := by
  norm_num [plusSpeedSquaredFromAction]

theorem minus_speed_positive_from_alpha_beta
    (p : SymbolicOrbifoldActionParams)
    (hAlpha : 0 < alphaFromAction p)
    (hBeta : 0 < betaFromAction p) :
    0 < minusSpeedSquaredFromAction p := by
  unfold minusSpeedSquaredFromAction
  exact div_pos hBeta hAlpha

def parameterCertificateFromSymbolicAction
    (c : SymbolicActionSignCertificate) :
    QuadraticTensorParameterCertificate :=
  { params := tensorParamsFromAction c.params
    gaugeAether := c.gaugeAether
    gaugeClosed := c.gaugeClosed
    visibleSpeed := c.visibleSpeed
    alphaPositive := c.alphaPositive
    betaPositive := c.betaPositive
    plusSpeedPositive := plus_speed_squared_positive_from_action c.params
    minusSpeedPositive :=
      minus_speed_positive_from_alpha_beta c.params c.alphaPositive c.betaPositive
    massNonnegative := c.massNonnegative }

theorem symbolic_action_certificate_derives_tensor_stability
    (c : SymbolicActionSignCertificate) :
    tensorPerturbationsStable
      (tensorCoefficientsFromCertificate
        (parameterCertificateFromSymbolicAction c)) := by
  exact certificate_derives_tensor_stability
    (parameterCertificateFromSymbolicAction c)

theorem symbolic_action_certificate_derives_luminality
    (c : SymbolicActionSignCertificate) :
    visibleGravitationalWaveLuminal
      (tensorCoefficientsFromCertificate
        (parameterCertificateFromSymbolicAction c)) := by
  exact certificate_derives_gauge_luminality
    (parameterCertificateFromSymbolicAction c)

theorem alpha_condition_is_planck_minus_aether_load
    (p : SymbolicOrbifoldActionParams) :
    alphaFromAction p =
      p.radionVev * (p.minusPlanckMassSquared - p.aetherKineticScale) := by
  rfl

theorem beta_condition_is_planck_plus_membrane_tension
    (p : SymbolicOrbifoldActionParams) :
    betaFromAction p = p.minusPlanckMassSquared + p.membraneTension := by
  rfl

theorem alpha_nonpositive_blocks_symbolic_certificate
    (p : SymbolicOrbifoldActionParams)
    (hMissing : Not (0 < alphaFromAction p)) :
    Not (Nonempty
      { c : SymbolicActionSignCertificate // c.params = p }) := by
  intro hCert
  rcases hCert with âŸ¨c, hcâŸ©
  have hAlpha : 0 < alphaFromAction p := by
    simpa [hc] using c.alphaPositive
  exact hMissing hAlpha

theorem beta_nonpositive_blocks_symbolic_certificate
    (p : SymbolicOrbifoldActionParams)
    (hMissing : Not (0 < betaFromAction p)) :
    Not (Nonempty
      { c : SymbolicActionSignCertificate // c.params = p }) := by
  intro hCert
  rcases hCert with âŸ¨c, hcâŸ©
  have hBeta : 0 < betaFromAction p := by
    simpa [hc] using c.betaPositive
  exact hMissing hBeta

theorem negative_hassan_rosen_mass_blocks_symbolic_certificate
    (p : SymbolicOrbifoldActionParams)
    (hMissing : Not (0 <= massSquaredFromAction p)) :
    Not (Nonempty
      { c : SymbolicActionSignCertificate // c.params = p }) := by
  intro hCert
  rcases hCert with âŸ¨c, hcâŸ©
  have hMass : 0 <= massSquaredFromAction p := by
    simpa [hc] using c.massNonnegative
  exact hMissing hMass

end P0SymbolicTensorCoefficientMap
end JanusFormal
