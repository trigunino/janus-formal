import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMobileMaxwellOffCenterFirstVariation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMaxwellRecenterGaugeMetricResidual4D

/-! # Complete smooth Maxwell metric residual away from the chart centre

The centred Maxwell metric residual and the exact recentering gauge residual
are both represented at the reconstructed metric. Their sum represents the
original native metric derivative, without a Maxwell stationarity premise.
-/

namespace JanusFormal
namespace P0EFTJanusMobileMaxwellOffCenterMetricResidual4D
set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 600000
noncomputable section
open MeasureTheory
open scoped Manifold ContDiff
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
open P0EFTJanusMappingTorusGeneralLorentzMetricBVPairingRegularity4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusProgramPGlobalGaugeTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPRegularFrameGaugePotentialReconstruction4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartRegularMetric4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalMetricGaugeCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2GaugeCoefficientMaxwellAction4D
open P0EFTJanusProgramPRegularFrameCanonicalMaxwellVariationalResidual4D
open P0EFTJanusStrongMaxwellMetricResidual4D
open P0EFTJanusMobileMaxwellOffCenterFirstVariation4D
open P0EFTJanusMaxwellRecenterGaugeMetricResidual4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev C2Scalar := CanonicalPhysicalScalarC2JetCore period hPeriod
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

variable (metric : RegularGeneralLorentzMetric period hPeriod)
  (shift : SmoothSymmetricCovariantTwoTensor period hPeriod)
  (hShift : regularGeneralMetricSmoothC2Variation period hPeriod metric shift ∈
    regularGeneralMetricC2LorentzChartDomain period hPeriod metric)
  (coefficients : SmoothQuotientField period hPeriod GaugeFiber)

local notation "shifted" => regularGeneralMetricC2LorentzChartRegularMetric period hPeriod metric shift hShift
local notation "potential" => regularFrameGaugePotentialFromCoefficients period hPeriod shifted coefficients

/-- The full off-centre tensor retains both the moving-frame centre response
and the exact gauge contribution from the change of centre. -/
def mobileMaxwellOffCenterMetricResidual : SmoothSymmetricCovariantTwoTensor period hPeriod :=
  smoothSymmetricTensorAdd period hPeriod
    (strongMaxwellMetricResidual period hPeriod shifted potential)
    (maxwellRecenterGaugeMetricResidual period hPeriod metric shift hShift coefficients)

/-- Both summands are integrable smooth tensor pairings for the canonical
measure, so their sum is the pairing with the complete residual. -/
theorem mobileMaxwellOffCenterMetricResidual_integral
    (direction : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    (∫ point, generalMetricTensorPairingAt period hPeriod (shifted).metric
      (strongMaxwellMetricResidual period hPeriod shifted potential) direction point
      ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod) +
    (∫ point, generalMetricTensorPairingAt period hPeriod (shifted).metric
      (maxwellRecenterGaugeMetricResidual period hPeriod metric shift hShift coefficients) direction point
      ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod) =
    ∫ point, generalMetricTensorPairingAt period hPeriod (shifted).metric
      (mobileMaxwellOffCenterMetricResidual period hPeriod metric shift hShift coefficients) direction point
      ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod := by
  have hFirst := generalMetricTensorPairingAt_continuous period hPeriod (shifted).metric
    (strongMaxwellMetricResidual period hPeriod shifted potential) direction
  have hSecond := generalMetricTensorPairingAt_continuous period hPeriod (shifted).metric
    (maxwellRecenterGaugeMetricResidual period hPeriod metric shift hShift coefficients) direction
  rw [← integral_add (μ := intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
    (hFirst.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (hSecond.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  apply congrArg (fun density : EffectiveQuotient period hPeriod → Real =>
    ∫ point, density point ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
  funext point
  exact (generalMetricTensorPairingAt_add_left period hPeriod (shifted).metric
    (strongMaxwellMetricResidual period hPeriod shifted potential)
    (maxwellRecenterGaugeMetricResidual period hPeriod metric shift hShift coefficients) direction point).symm

attribute [local irreducible]
  regularGeneralMetricC0MobileGaugeCoefficientFixedVolumeMaxwellAction
  regularGeneralMetricC2LorentzChartDomain

/-- The actual native derivative at an arbitrary admissible smooth metric
shift is the canonical integral of its complete smooth metric residual. -/
theorem mobileMaxwellAction_fderiv_recenter_eq_metricResidualIntegral
    (direction : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    fderiv Real
        (fun variation => regularGeneralMetricC0MobileGaugeCoefficientFixedVolumeMaxwellAction
          period hPeriod metric (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
          variation (smoothGaugeCoefficientC2CoreLinearMap period hPeriod coefficients))
        (regularGeneralMetricSmoothC2Variation period hPeriod metric shift)
        (regularGeneralMetricSmoothC2Variation period hPeriod metric direction) =
      ∫ point, generalMetricTensorPairingAt period hPeriod (shifted).metric
        (mobileMaxwellOffCenterMetricResidual period hPeriod metric shift hShift coefficients) direction point
        ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod := by
  have hGauge := canonicalMaxwellResidualPairing_recenterGaugePotential_eq_metricIntegral
    period hPeriod metric shift hShift coefficients direction
  exact (mobileMaxwellAction_fderiv_recenter_eq_residualIntegral_add_gaugePairing
    period hPeriod metric shift direction hShift coefficients).trans
      ((congrArg (fun gaugePairing : Real =>
        (∫ point, generalMetricTensorPairingAt period hPeriod (shifted).metric
          (strongMaxwellMetricResidual period hPeriod shifted potential) direction point
          ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod) + gaugePairing) hGauge).trans
        (mobileMaxwellOffCenterMetricResidual_integral period hPeriod metric shift hShift coefficients direction))

end
end P0EFTJanusMobileMaxwellOffCenterMetricResidual4D
end JanusFormal
