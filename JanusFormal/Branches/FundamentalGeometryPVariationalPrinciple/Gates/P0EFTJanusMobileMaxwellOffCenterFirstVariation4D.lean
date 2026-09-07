import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusSmoothMaxwellRecenterGaugeVelocity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusStrongMaxwellMetricResidual4D

/-! # Actual Maxwell first variation away from the metric chart centre

The joint centred derivative splits into its metric and gauge parts. Recentring
therefore retains the canonical gauge residual paired with the exact smooth
transition velocity, without any Maxwell stationarity assumption.
-/

namespace JanusFormal
namespace P0EFTJanusMobileMaxwellOffCenterFirstVariation4D

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 600000

noncomputable section
open MeasureTheory
open scoped Manifold ContDiff

/-- A joint derivative is the sum of its two actual partial derivatives. -/
private theorem fderiv_prod_eq_partial_add
    {E G : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [NormedAddCommGroup G] [NormedSpace Real G]
    (action : E → G → Real) (coefficients : G)
    (hJoint : DifferentiableAt Real
      (fun input : E × G => action input.1 input.2) (0, coefficients))
    (metricDirection : E) (gaugeDirection : G) :
    fderiv Real (fun input : E × G => action input.1 input.2)
        (0, coefficients) (metricDirection, gaugeDirection) =
      fderiv Real (fun variation => action variation coefficients) 0 metricDirection +
        fderiv Real (action 0) coefficients gaugeDirection := by
  let joint := fun input : E × G => action input.1 input.2
  let derivative := fderiv Real joint (0, coefficients)
  have hJoint' : HasFDerivAt joint derivative (0, coefficients) := hJoint.hasFDerivAt
  have hMetric : HasFDerivAt (fun variation => action variation coefficients)
      (derivative.comp (ContinuousLinearMap.inl Real E G)) 0 := by
    simpa only [Function.comp_def, joint] using
      hJoint'.comp (0 : E) (hasFDerivAt_prodMk_left (𝕜 := Real) (0 : E) coefficients)
  have hGauge : HasFDerivAt (action 0)
      (derivative.comp (ContinuousLinearMap.inr Real E G)) coefficients := by
    simpa only [Function.comp_def, joint] using
      hJoint'.comp coefficients (hasFDerivAt_prodMk_right (0 : E) coefficients)
  rw [hMetric.fderiv, hGauge.fderiv]
  change derivative (metricDirection, gaugeDirection) =
    derivative (metricDirection, 0) + derivative (0, gaugeDirection)
  have hPair : (metricDirection, gaugeDirection) =
      (metricDirection, (0 : G)) + ((0 : E), gaugeDirection) := by
    ext <;> simp
  rw [hPair, map_add]

open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFirstLevel4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVUltralocalMaster4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusProgramPGlobalGaugeTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPRegularFrameGaugePotentialReconstruction4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartRegularMetric4D
open P0EFTJanusProgramPRegularGeneralMetricC2MaxwellStressDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalMetricGaugeCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2GaugeCoefficientFrameTransport4D
open P0EFTJanusProgramPRegularGeneralMetricC2GaugeCoefficientMaxwellAction4D
open P0EFTJanusProgramPRegularFrameMaxwellSmoothGaugeTestSeparation4D
open P0EFTJanusProgramPRegularFrameCanonicalMaxwellVariationalResidual4D
open P0EFTJanusStrongMaxwellMetricCenterFirstVariation4D
open P0EFTJanusGaugeCoefficientMaxwellIntrinsicFirstVariation4D
open P0EFTJanusStrongMaxwellMetricResidual4D
open P0EFTJanusMobileMaxwellDerivativeRecenter4D
open P0EFTJanusSmoothMaxwellRecenterGaugeVelocity4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev C2Scalar := CanonicalPhysicalScalarC2JetCore period hPeriod
private abbrev GaugeC2Core := RegularGeneralMetricC2GaugeCoefficientCore period hPeriod

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _
local instance : BorelSpace (EffectiveQuotient period hPeriod) where measurable_eq := rfl
local instance : IsFiniteMeasure (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod
local instance : NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (C2Scalar period hPeriod) := inferInstance
local instance : CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod

attribute [local irreducible]
  regularGeneralMetricC0MobileGaugeCoefficientFixedVolumeMaxwellAction
  regularGeneralMetricC0GaugeCoefficientFixedVolumeMaxwellAction
  regularGeneralMetricC2LorentzChartDomain

/-- At zero metric coordinate, the gauge partial is the genuine fixed-frame
coefficient derivative, while the metric partial retains the moving frame. -/
theorem mobileMaxwellJointAction_fderiv_zero_split
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure measure]
    (coefficients : GaugeC2Core period hPeriod)
    (metricDirection : RegularGeneralMetricC2Core period hPeriod metric)
    (gaugeDirection : GaugeC2Core period hPeriod) :
    fderiv Real
        (fun input : RegularGeneralMetricC2Core period hPeriod metric × GaugeC2Core period hPeriod =>
          regularGeneralMetricC0MobileGaugeCoefficientFixedVolumeMaxwellAction
            period hPeriod metric measure input.1 input.2)
        (0, coefficients) (metricDirection, gaugeDirection) =
      fderiv Real
          (fun variation => regularGeneralMetricC0MobileGaugeCoefficientFixedVolumeMaxwellAction
            period hPeriod metric measure variation coefficients) 0 metricDirection +
        fderiv Real
          (regularGeneralMetricC0GaugeCoefficientFixedVolumeMaxwellAction
            period hPeriod metric measure 0) coefficients gaugeDirection := by
  have hSplit := fderiv_prod_eq_partial_add
    (regularGeneralMetricC0MobileGaugeCoefficientFixedVolumeMaxwellAction
      period hPeriod metric measure) coefficients
    (mobileMaxwellJointAction_differentiableAt period hPeriod metric measure 0 coefficients
      (zero_mem_regularGeneralMetricC2LorentzChartDomain period hPeriod metric))
    metricDirection gaugeDirection
  have hGauge :
      regularGeneralMetricC0MobileGaugeCoefficientFixedVolumeMaxwellAction
        period hPeriod metric measure 0 =
      regularGeneralMetricC0GaugeCoefficientFixedVolumeMaxwellAction
        period hPeriod metric measure 0 := by
    funext packet
    simp only [regularGeneralMetricC0MobileGaugeCoefficientFixedVolumeMaxwellAction,
      regularGeneralMetricC2MobileGaugeCoefficientTransport_zero]
  rw [hGauge] at hSplit
  exact hSplit

/-- Both parts of the joint derivative have their actual canonical residual
representatives on smooth metric and intrinsic gauge directions. -/
theorem mobileMaxwellJointAction_fderiv_zero_eq_residualIntegral_add_gaugePairing
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (gaugeVariation : SmoothAbelianGaugePotential period hPeriod) :
    let coefficients := smoothGaugeCoefficientC2CoreLinearMap period hPeriod
      (gaugePotentialFrameCoefficients period hPeriod metric potential)
    fderiv Real
        (fun input : RegularGeneralMetricC2Core period hPeriod metric × GaugeC2Core period hPeriod =>
          regularGeneralMetricC0MobileGaugeCoefficientFixedVolumeMaxwellAction period hPeriod
            metric (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) input.1 input.2)
        (0, coefficients)
        (regularGeneralMetricC2SmoothDirection period hPeriod metric tensor,
          smoothGaugeCoefficientC2CoreLinearMap period hPeriod
            (gaugePotentialFrameCoefficients period hPeriod metric gaugeVariation)) =
      (∫ point, generalMetricTensorPairingAt period hPeriod metric.metric
        (strongMaxwellMetricResidual period hPeriod metric potential) tensor point
        ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod) +
      canonicalRegularFrameIntrinsicGaugeResidualPairing period hPeriod metric
        (regularFrameCanonicalMaxwellVariationalResidual period hPeriod metric potential)
        gaugeVariation := by
  dsimp only
  rw [mobileMaxwellJointAction_fderiv_zero_split,
    strongMaxwellMetricCenterFirstVariation_eq_residualIntegral,
    gaugeCoefficientMaxwellAction_fderiv_zeroMetric_eq_canonicalResidualPairing]

/-- The original off-centre metric derivative is the centred metric residual
plus the exact smooth gauge-transition contribution. -/
theorem mobileMaxwellAction_fderiv_recenter_eq_residualIntegral_add_gaugePairing
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (shift direction : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hShift : regularGeneralMetricSmoothC2Variation period hPeriod metric shift ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric)
    (coefficients : SmoothQuotientField period hPeriod GaugeFiber) :
    let shifted := regularGeneralMetricC2LorentzChartRegularMetric period hPeriod metric shift hShift
    let potential := regularFrameGaugePotentialFromCoefficients period hPeriod shifted coefficients
    let packet := smoothGaugeCoefficientC2CoreLinearMap period hPeriod coefficients
    fderiv Real
        (fun variation => regularGeneralMetricC0MobileGaugeCoefficientFixedVolumeMaxwellAction
          period hPeriod metric (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
          variation packet)
        (regularGeneralMetricSmoothC2Variation period hPeriod metric shift)
        (regularGeneralMetricSmoothC2Variation period hPeriod metric direction) =
      (∫ point, generalMetricTensorPairingAt period hPeriod shifted.metric
        (strongMaxwellMetricResidual period hPeriod shifted potential) direction point
        ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod) +
      canonicalRegularFrameIntrinsicGaugeResidualPairing period hPeriod shifted
        (regularFrameCanonicalMaxwellVariationalResidual period hPeriod shifted potential)
        (smoothMobileMaxwellRecenterGaugePotential period hPeriod metric shift direction hShift
          coefficients) := by
  let shifted := regularGeneralMetricC2LorentzChartRegularMetric period hPeriod metric shift hShift
  let potential := regularFrameGaugePotentialFromCoefficients period hPeriod shifted coefficients
  let gaugeVariation := smoothMobileMaxwellRecenterGaugePotential period hPeriod
    metric shift direction hShift coefficients
  have hCenter := mobileMaxwellJointAction_fderiv_zero_eq_residualIntegral_add_gaugePairing
    period hPeriod shifted potential direction gaugeVariation
  have hCoefficients : gaugePotentialFrameCoefficients period hPeriod shifted potential =
      coefficients := gaugePotentialFrameCoefficients_reconstructed period hPeriod shifted coefficients
  have hVelocity : smoothGaugeCoefficientC2CoreLinearMap period hPeriod
      (gaugePotentialFrameCoefficients period hPeriod shifted gaugeVariation) =
      mobileMaxwellRecenterGaugeVelocity period hPeriod metric shift direction hShift
        (smoothGaugeCoefficientC2CoreLinearMap period hPeriod coefficients) :=
    smoothMobileMaxwellRecenterGaugePotential_toC2 period hPeriod metric shift direction hShift coefficients
  dsimp only at hCenter
  rw [hCoefficients, hVelocity] at hCenter
  exact (mobileMaxwellAction_fderiv_recenter_joint period hPeriod metric shift direction hShift
    (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) coefficients).trans hCenter

end
end P0EFTJanusMobileMaxwellOffCenterFirstVariation4D
end JanusFormal
