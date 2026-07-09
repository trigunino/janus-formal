import JanusFormal.Legacy.P0.Gates.P0SymbolicTensorCoefficientMap

namespace JanusFormal
namespace P0ActionTermCoefficientDerivation

open P0SymbolicTensorCoefficientMap

set_option autoImplicit false

structure MinusEinsteinHilbertTerm where
  planckMassSquared : Rat
  contributesKineticAlpha : Rat
  contributesGradientBeta : Rat

def minusEHClosed (t : MinusEinsteinHilbertTerm) : Prop :=
  t.contributesKineticAlpha = t.planckMassSquared /\
  t.contributesGradientBeta = t.planckMassSquared

structure GaugeAetherRadionTerm where
  kineticScale : Rat
  radionVev : Rat
  contributesKineticLoad : Rat

def gaugeAetherRadionClosed (t : GaugeAetherRadionTerm) : Prop :=
  t.contributesKineticLoad = t.radionVev * t.kineticScale

structure MembraneTensionTerm where
  tension : Rat
  contributesGradientStiffness : Rat

def membraneTensionClosed (t : MembraneTensionTerm) : Prop :=
  t.contributesGradientStiffness = t.tension

structure HassanRosenTensorMassTerm where
  massSquared : Rat
  contributesTensorMassSquared : Rat

def hassanRosenMassClosed (t : HassanRosenTensorMassTerm) : Prop :=
  t.contributesTensorMassSquared = t.massSquared

structure TensorActionTermSystem where
  minusEH : MinusEinsteinHilbertTerm
  aetherRadion : GaugeAetherRadionTerm
  membrane : MembraneTensionTerm
  hassanRosen : HassanRosenTensorMassTerm
  visibleSpeedUnmodified : Prop

def termSystemClosed (s : TensorActionTermSystem) : Prop :=
  minusEHClosed s.minusEH /\
  gaugeAetherRadionClosed s.aetherRadion /\
  membraneTensionClosed s.membrane /\
  hassanRosenMassClosed s.hassanRosen

def symbolicParamsFromTerms
    (s : TensorActionTermSystem) :
    SymbolicOrbifoldActionParams :=
  { plusPlanckMassSquared := s.minusEH.planckMassSquared
    minusPlanckMassSquared := s.minusEH.planckMassSquared
    radionVev := s.aetherRadion.radionVev
    aetherKineticScale := s.aetherRadion.kineticScale
    membraneTension := s.membrane.tension
    hassanRosenMassSquared := s.hassanRosen.massSquared
    visibleSpeedUnmodified := s.visibleSpeedUnmodified }

def alphaFromTerms (s : TensorActionTermSystem) : Rat :=
  s.aetherRadion.radionVev *
    (s.minusEH.contributesKineticAlpha - s.aetherRadion.kineticScale)

def betaFromTerms (s : TensorActionTermSystem) : Rat :=
  s.minusEH.contributesGradientBeta + s.membrane.contributesGradientStiffness

def massSquaredFromTerms (s : TensorActionTermSystem) : Rat :=
  s.hassanRosen.contributesTensorMassSquared

theorem closed_terms_alpha_matches_symbolic_action
    (s : TensorActionTermSystem)
    (h : termSystemClosed s) :
    alphaFromTerms s = alphaFromAction (symbolicParamsFromTerms s) := by
  rcases h with ⟨hEH, hAether, _hMembrane, _hMass⟩
  unfold alphaFromTerms alphaFromAction symbolicParamsFromTerms
  rw [hEH.left]

theorem closed_terms_beta_matches_symbolic_action
    (s : TensorActionTermSystem)
    (h : termSystemClosed s) :
    betaFromTerms s = betaFromAction (symbolicParamsFromTerms s) := by
  rcases h with ⟨hEH, _hAether, hMembrane, _hMass⟩
  unfold betaFromTerms betaFromAction symbolicParamsFromTerms
  rw [hEH.right, hMembrane]

theorem closed_terms_mass_matches_symbolic_action
    (s : TensorActionTermSystem)
    (h : termSystemClosed s) :
    massSquaredFromTerms s = massSquaredFromAction (symbolicParamsFromTerms s) := by
  rcases h with ⟨_hEH, _hAether, _hMembrane, hMass⟩
  unfold massSquaredFromTerms massSquaredFromAction symbolicParamsFromTerms
  rw [hMass]

structure ActionTermSignCertificate where
  system : TensorActionTermSystem
  gaugeAether : P0GaugeLikeAetherTopology.GaugeLikeAetherTopology
  gaugeClosed : P0GaugeLikeAetherTopology.gaugeLikeAetherClosed gaugeAether
  termsClosed : termSystemClosed system
  visibleSpeed : system.visibleSpeedUnmodified
  alphaPositive : 0 < alphaFromTerms system
  betaPositive : 0 < betaFromTerms system
  massNonnegative : 0 <= massSquaredFromTerms system

def symbolicCertificateFromActionTerms
    (c : ActionTermSignCertificate) :
    SymbolicActionSignCertificate :=
  { params := symbolicParamsFromTerms c.system
    gaugeAether := c.gaugeAether
    gaugeClosed := c.gaugeClosed
    visibleSpeed := c.visibleSpeed
    alphaPositive := by
      rw [← closed_terms_alpha_matches_symbolic_action c.system c.termsClosed]
      exact c.alphaPositive
    betaPositive := by
      rw [← closed_terms_beta_matches_symbolic_action c.system c.termsClosed]
      exact c.betaPositive
    massNonnegative := by
      rw [← closed_terms_mass_matches_symbolic_action c.system c.termsClosed]
      exact c.massNonnegative }

theorem action_terms_derive_tensor_stability
    (c : ActionTermSignCertificate) :
    P0LinearTensorPerturbationStability.tensorPerturbationsStable
      (P0TensorParameterDerivations.tensorCoefficientsFromCertificate
        (parameterCertificateFromSymbolicAction
          (symbolicCertificateFromActionTerms c))) := by
  exact symbolic_action_certificate_derives_tensor_stability
    (symbolicCertificateFromActionTerms c)

theorem action_terms_derive_visible_luminality
    (c : ActionTermSignCertificate) :
    P0LinearTensorPerturbationStability.visibleGravitationalWaveLuminal
      (P0TensorParameterDerivations.tensorCoefficientsFromCertificate
        (parameterCertificateFromSymbolicAction
          (symbolicCertificateFromActionTerms c))) := by
  exact symbolic_action_certificate_derives_luminality
    (symbolicCertificateFromActionTerms c)

theorem missing_closed_terms_blocks_action_certificate
    (s : TensorActionTermSystem)
    (hMissing : Not (termSystemClosed s)) :
    Not (Nonempty { c : ActionTermSignCertificate // c.system = s }) := by
  intro hCert
  rcases hCert with ⟨c, hc⟩
  have hClosed : termSystemClosed s := by
    simpa [hc] using c.termsClosed
  exact hMissing hClosed

end P0ActionTermCoefficientDerivation
end JanusFormal
