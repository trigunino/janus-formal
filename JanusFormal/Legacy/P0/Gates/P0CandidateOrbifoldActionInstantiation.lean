import JanusFormal.Legacy.P0.Gates.P0ActionTermCoefficientDerivation
import JanusFormal.Legacy.P0.Gates.P0RadionVielbeinSouriauBridge

namespace JanusFormal
namespace P0CandidateOrbifoldActionInstantiation

open P0ActionTermCoefficientDerivation
open P0GaugeLikeAetherTopology
open P0RadionVielbeinSouriauBridge

set_option autoImplicit false

structure CandidateOrbifoldActionConstants where
  planckMassSquared : Rat
  radionVev : Rat
  aetherKineticScale : Rat
  membraneTension : Rat
  hassanRosenMassSquared : Rat
  visibleSpeedUnmodified : Prop

structure CandidateOrbifoldActionStructure where
  cartanTetradFormalism : Prop
  plusEinsteinHilbertMatter : Prop
  minusTemporalRadionTetrad : Prop
  radionDoubleWellPotential : Prop
  gaugeLikeAetherFEqualsDA : Prop
  noAetherMultiplierGeometricNormal : Prop
  hassanRosenBoundaryMass : Prop
  hassanRosenDgrtCoefficients : Prop
  ghyJumpTermsPresent : Prop
  israelJunctionConditions : Prop
  minkowskiTwinBackground : Prop
  minusMetricDependsOnVevSquared : Prop
  minusTetradOrientationDependsOnVevSign : Prop

def candidateActionStructureClosed
    (s : CandidateOrbifoldActionStructure) : Prop :=
  s.cartanTetradFormalism /\
  s.plusEinsteinHilbertMatter /\
  s.minusTemporalRadionTetrad /\
  s.radionDoubleWellPotential /\
  s.gaugeLikeAetherFEqualsDA /\
  s.noAetherMultiplierGeometricNormal /\
  s.hassanRosenBoundaryMass /\
  s.hassanRosenDgrtCoefficients /\
  s.ghyJumpTermsPresent /\
  s.israelJunctionConditions /\
  s.minkowskiTwinBackground /\
  s.minusMetricDependsOnVevSquared /\
  s.minusTetradOrientationDependsOnVevSign

def gaugeLikeAetherFromCandidate
    (s : CandidateOrbifoldActionStructure) :
    GaugeLikeAetherTopology :=
  { aetherFromOneFormPotential := s.gaugeLikeAetherFEqualsDA
    fieldStrengthExact := s.gaugeLikeAetherFEqualsDA
    fieldStrengthClosedByD2Zero := s.gaugeLikeAetherFEqualsDA
    gaugeInvariantKineticTerm := s.gaugeLikeAetherFEqualsDA
    antisymmetricDerivativeOnly := s.gaugeLikeAetherFEqualsDA
    maxwellLorentzKineticStructure := s.gaugeLikeAetherFEqualsDA
    orbifoldFoldSource := s.noAetherMultiplierGeometricNormal }

theorem closed_candidate_gives_gauge_like_aether
    (s : CandidateOrbifoldActionStructure)
    (h : candidateActionStructureClosed s) :
    gaugeLikeAetherClosed (gaugeLikeAetherFromCandidate s) := by
  rcases h with
    ⟨_hCartan, _hPlus, _hMinus, _hPotential, hGauge,
      hNormal, _hHR, _hDgrt, _hGHY, _hIsrael, _hBg, _hMetric, _hOrient⟩
  exact ⟨hGauge, hGauge, hGauge, hGauge, hGauge, hGauge, hNormal⟩

def radionGeometryFromCandidate
    (s : CandidateOrbifoldActionStructure) :
    RadionAsVielbeinGeometry :=
  { radionGeometricNotMatter := s.minusTemporalRadionTetrad
    scalarConformalVielbeinFactor := False
    fourDimensionalTetrad := s.cartanTetradFormalism
    determinantScalesAsPhiFourth := False
    radionCoupledOnlyToTemporalLeg := s.minusTemporalRadionTetrad
    determinantScalesLinearlyInPhi := s.minusTetradOrientationDependsOnVevSign
    einsteinAetherTimelikeUnitVector := s.noAetherMultiplierGeometricNormal
    temporalLegSignOperator := s.minusTemporalRadionTetrad
    oddFrameOrientationFlip := s.minusTetradOrientationDependsOnVevSign
    antichronousLorentzComponentSelected := s.minusTetradOrientationDependsOnVevSign }

theorem closed_candidate_gives_radion_tetrad_orientation
    (s : CandidateOrbifoldActionStructure)
    (h : candidateActionStructureClosed s) :
    radionTetradTimeOrientationClosed (radionGeometryFromCandidate s) := by
  rcases h with
    ⟨hCartan, _hPlus, hMinus, _hPotential, _hGauge,
      hNormal, _hHR, _hDgrt, _hGHY, _hIsrael, _hBg, _hMetric, hOrient⟩
  exact ⟨hMinus, hMinus, hMinus, hOrient, hNormal, hOrient, hOrient⟩

def termSystemFromCandidate
    (k : CandidateOrbifoldActionConstants) :
    TensorActionTermSystem :=
  { minusEH :=
      { planckMassSquared := k.planckMassSquared
        contributesKineticAlpha := k.planckMassSquared
        contributesGradientBeta := k.planckMassSquared }
    aetherRadion :=
      { kineticScale := k.aetherKineticScale
        radionVev := k.radionVev
        contributesKineticLoad := k.radionVev * k.aetherKineticScale }
    membrane :=
      { tension := k.membraneTension
        contributesGradientStiffness := k.membraneTension }
    hassanRosen :=
      { massSquared := k.hassanRosenMassSquared
        contributesTensorMassSquared := k.hassanRosenMassSquared }
    visibleSpeedUnmodified := k.visibleSpeedUnmodified }

theorem candidate_term_system_closed
    (k : CandidateOrbifoldActionConstants) :
    termSystemClosed (termSystemFromCandidate k) := by
  exact ⟨⟨rfl, rfl⟩, rfl, rfl, rfl⟩

structure CandidateOrbifoldActionCertificate where
  constants : CandidateOrbifoldActionConstants
  actionStructure : CandidateOrbifoldActionStructure
  structureClosed : candidateActionStructureClosed actionStructure
  visibleSpeed : constants.visibleSpeedUnmodified
  alphaPositive :
    0 < alphaFromTerms (termSystemFromCandidate constants)
  betaPositive :
    0 < betaFromTerms (termSystemFromCandidate constants)
  massNonnegative :
    0 <= massSquaredFromTerms (termSystemFromCandidate constants)

def actionTermCertificateFromCandidate
    (c : CandidateOrbifoldActionCertificate) :
    ActionTermSignCertificate :=
  { system := termSystemFromCandidate c.constants
    gaugeAether := gaugeLikeAetherFromCandidate c.actionStructure
    gaugeClosed :=
      closed_candidate_gives_gauge_like_aether c.actionStructure c.structureClosed
    termsClosed := candidate_term_system_closed c.constants
    visibleSpeed := c.visibleSpeed
    alphaPositive := c.alphaPositive
    betaPositive := c.betaPositive
    massNonnegative := c.massNonnegative }

theorem candidate_action_derives_tensor_stability
    (c : CandidateOrbifoldActionCertificate) :
    P0LinearTensorPerturbationStability.tensorPerturbationsStable
      (P0TensorParameterDerivations.tensorCoefficientsFromCertificate
        (P0SymbolicTensorCoefficientMap.parameterCertificateFromSymbolicAction
          (symbolicCertificateFromActionTerms
            (actionTermCertificateFromCandidate c)))) := by
  exact action_terms_derive_tensor_stability
    (actionTermCertificateFromCandidate c)

theorem candidate_action_derives_visible_luminality
    (c : CandidateOrbifoldActionCertificate) :
    P0LinearTensorPerturbationStability.visibleGravitationalWaveLuminal
      (P0TensorParameterDerivations.tensorCoefficientsFromCertificate
        (P0SymbolicTensorCoefficientMap.parameterCertificateFromSymbolicAction
          (symbolicCertificateFromActionTerms
            (actionTermCertificateFromCandidate c)))) := by
  exact action_terms_derive_visible_luminality
    (actionTermCertificateFromCandidate c)

theorem candidate_metric_sign_note
    (s : CandidateOrbifoldActionStructure)
    (h : candidateActionStructureClosed s) :
    s.minusMetricDependsOnVevSquared /\
    s.minusTetradOrientationDependsOnVevSign := by
  exact ⟨h.right.right.right.right.right.right.right.right.right.right.right.left,
    h.right.right.right.right.right.right.right.right.right.right.right.right⟩

theorem missing_temporal_radion_blocks_candidate_closure
    (s : CandidateOrbifoldActionStructure)
    (hMissing : Not s.minusTemporalRadionTetrad) :
    Not (candidateActionStructureClosed s) := by
  intro h
  exact hMissing h.right.right.left

theorem missing_gauge_aether_blocks_candidate_closure
    (s : CandidateOrbifoldActionStructure)
    (hMissing : Not s.gaugeLikeAetherFEqualsDA) :
    Not (candidateActionStructureClosed s) := by
  intro h
  exact hMissing h.right.right.right.right.left

theorem missing_hr_boundary_mass_blocks_candidate_closure
    (s : CandidateOrbifoldActionStructure)
    (hMissing : Not s.hassanRosenBoundaryMass) :
    Not (candidateActionStructureClosed s) := by
  intro h
  exact hMissing h.right.right.right.right.right.right.left

end P0CandidateOrbifoldActionInstantiation
end JanusFormal
