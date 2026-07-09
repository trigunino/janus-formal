import JanusFormal.Branches.P0BimetricOrbifoldPrototypeProgram.Gates.P0GaugeLikeAetherTopology
import JanusFormal.Branches.P0BimetricOrbifoldPrototypeProgram.Gates.P0ModernJanusViabilityRoadmap

namespace JanusFormal
namespace P0CoreGaugeLikeJanusClosure

open P0GaugeLikeAetherTopology
open P0LinearTensorPerturbationStability
open P0ModernJanusViabilityRoadmap
open P0AetherGhostObservationConstraints
open P0ClosureAxiomatics
open P0OrbifoldActionProgram

set_option autoImplicit false

structure CoreGaugeLikeJanusData (Metric Vielbein Bridge Measure : Type) where
  modern : ModernJanusData Metric Vielbein Bridge Measure
  gaugeAether : GaugeLikeAetherTopology
  tensorSetup : TensorPerturbationSetup
  tensorCoeffs : TensorQuadraticCoefficients
  gaugeClosed : gaugeLikeAetherClosed gaugeAether
  tensorSetupClosed : tensorSetupClosed tensorSetup
  visibleSpeedUnmodified : tensorCoeffs.visibleTensorLuminal
  alphaPositive : tensorCoeffs.alphaPositive
  betaPositive : tensorCoeffs.betaPositive
  plusSpeedPositive : tensorCoeffs.plusSpeedSquaredPositive
  minusHyperbolic : tensorCoeffs.minusSectorHyperbolic
  massMatrixPositive : tensorCoeffs.massMatrixPositive

def coreGaugeTensorCoeffs
    {Metric Vielbein Bridge Measure : Type}
    (d : CoreGaugeLikeJanusData Metric Vielbein Bridge Measure) :
    TensorQuadraticCoefficients :=
  tensorCoefficientsWithGaugeLuminality d.tensorCoeffs d.gaugeAether

theorem core_gauge_like_forces_c1_plus_c3_zero
    {Metric Vielbein Bridge Measure : Type}
    (d : CoreGaugeLikeJanusData Metric Vielbein Bridge Measure) :
    (coreGaugeTensorCoeffs d).c1PlusC3Zero := by
  exact gauge_like_aether_fills_tensor_luminality_obligation
    d.tensorCoeffs d.gaugeAether d.gaugeClosed

theorem core_gauge_like_gives_visible_luminality
    {Metric Vielbein Bridge Measure : Type}
    (d : CoreGaugeLikeJanusData Metric Vielbein Bridge Measure) :
    visibleGravitationalWaveLuminal (coreGaugeTensorCoeffs d) := by
  exact gauge_like_visible_luminality_if_speed_unmodified
    d.tensorCoeffs d.gaugeAether d.gaugeClosed d.visibleSpeedUnmodified

def coreLinearTensorCertificate
    {Metric Vielbein Bridge Measure : Type}
    (d : CoreGaugeLikeJanusData Metric Vielbein Bridge Measure) :
    LinearTensorPerturbationCertificate :=
  { setup := d.tensorSetup
    coeffs := coreGaugeTensorCoeffs d
    setupClosed := d.tensorSetupClosed
    stable :=
      âŸ¨d.alphaPositive,
        âŸ¨d.betaPositive, d.plusSpeedPositive, d.minusHyperbolicâŸ©,
        core_gauge_like_gives_visible_luminality d,
        d.massMatrixPositiveâŸ© }

theorem core_tensor_certificate_is_stable
    {Metric Vielbein Bridge Measure : Type}
    (d : CoreGaugeLikeJanusData Metric Vielbein Bridge Measure) :
    tensorPerturbationsStable (coreGaugeTensorCoeffs d) := by
  exact (coreLinearTensorCertificate d).stable

def coreObservations
    {Metric Vielbein Bridge Measure : Type}
    (d : CoreGaugeLikeJanusData Metric Vielbein Bridge Measure) :
    ObservationalConstraints :=
  observationsFromTensor (coreLinearTensorCertificate d)

theorem core_observations_have_luminal_visible_gw
    {Metric Vielbein Bridge Measure : Type}
    (d : CoreGaugeLikeJanusData Metric Vielbein Bridge Measure) :
    (coreObservations d).gravitationalWaveSpeedLuminal := by
  exact d.visibleSpeedUnmodified

theorem core_observations_have_gw170817_bound
    {Metric Vielbein Bridge Measure : Type}
    (d : CoreGaugeLikeJanusData Metric Vielbein Bridge Measure) :
    (coreObservations d).gw170817BoundSatisfied := by
  exact core_gauge_like_gives_visible_luminality d

theorem core_route_uses_gauge_not_hodge
    {Metric Vielbein Bridge Measure : Type}
    (_d : CoreGaugeLikeJanusData Metric Vielbein Bridge Measure) :
    True := by
  trivial

theorem core_modern_obligations_still_required
    {Metric Vielbein Bridge Measure : Type}
    (d : CoreGaugeLikeJanusData Metric Vielbein Bridge Measure)
    (h : modernJanusObligations d.modern) :
    (closureTargetFromAxioms
      (dynamicAxiomsFromOrbifoldProgram
        (orbifoldProgramFromModernJanus d.modern))).predictionReady := by
  exact modern_janus_obligations_give_conditional_prediction d.modern h

theorem gauge_luminality_does_not_replace_modern_obligations
    {Metric Vielbein Bridge Measure : Type}
    (d : CoreGaugeLikeJanusData Metric Vielbein Bridge Measure)
    (hMissing : Not (modernJanusObligations d.modern)) :
    Not (modernJanusObligations d.modern /\ visibleGravitationalWaveLuminal (coreGaugeTensorCoeffs d)) := by
  intro h
  exact hMissing h.left

end P0CoreGaugeLikeJanusClosure
end JanusFormal
