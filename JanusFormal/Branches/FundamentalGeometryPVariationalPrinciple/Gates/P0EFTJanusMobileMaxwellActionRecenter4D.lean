import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusStrongMaxwellMetricResidual4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusLorentzChartAffineRecenterGeometry4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusRegularFrameGaugeCoefficientTransition4D

/-! # Exact Maxwell action recentering with the true moving-frame gauge transition -/

namespace JanusFormal
namespace P0EFTJanusMobileMaxwellActionRecenter4D

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
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFirstLevel4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVUltralocalMaster4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVPairingRegularity4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusProgramPGlobalGaugeTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2MaxwellStressDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalMetricGaugeCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2GaugeCoefficientFrameTransport4D
open P0EFTJanusProgramPRegularGeneralMetricC2GaugeCoefficientMaxwellAction4D
open P0EFTJanusProgramPRegularFrameMaxwellSmoothGaugeTestSeparation4D
open P0EFTJanusProgramPRegularFrameCanonicalMaxwellVariationalResidual4D
open P0EFTJanusStrongMaxwellMetricCenterFirstVariation4D
open P0EFTJanusFixedVolumeMaxwellStressResidual4D
open P0EFTJanusMetricInducedSmoothGaugeVelocity4D
open P0EFTJanusGaugeCoefficientMaxwellIntrinsicFirstVariation4D
open P0EFTJanusMetricInducedMaxwellResidual4D

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

open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusIntrinsicAbelianMaxwellAction4D
open P0EFTJanusMappingTorusConformalFrameFreeMaxwellHessian4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartRegularMetric4D
open P0EFTJanusProgramPRegularFrameGaugePotentialReconstruction4D
open P0EFTJanusLorentzChartAffineRecenterGeometry4D
open P0EFTJanusRegularFrameGaugeCoefficientTransition4D

/-- Maxwell depends on the metric, stored density and actual potential, not its frame coordinates. -/
theorem intrinsicMaxwellAction_eq_of_metric_volume_eq
    (first second : RegularGeneralLorentzMetric period hPeriod)
    (hMetric : first.metric = second.metric) (hVolume : first.volume = second.volume)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod)) :
    intrinsicMaxwellAction period hPeriod first
      (globalSmoothMaxwellPairing period hPeriod first.metric potential potential) measure =
    intrinsicMaxwellAction period hPeriod second
      (globalSmoothMaxwellPairing period hPeriod second.metric potential potential) measure := by
  unfold intrinsicMaxwellAction
  rw [hMetric, hVolume]

/-- A coefficient transition preserves Maxwell whenever metric and stored volume agree. -/
theorem intrinsicMaxwellAction_coefficientTransition
    (first second : RegularGeneralLorentzMetric period hPeriod)
    (hMetric : first.metric = second.metric) (hVolume : first.volume = second.volume)
    (coefficients : SmoothQuotientField period hPeriod GaugeFiber)
    (measure : Measure (EffectiveQuotient period hPeriod)) :
    intrinsicMaxwellAction period hPeriod first
      (globalSmoothMaxwellPairing period hPeriod first.metric
        (regularFrameGaugePotentialFromCoefficients period hPeriod first coefficients)
        (regularFrameGaugePotentialFromCoefficients period hPeriod first coefficients)) measure =
    intrinsicMaxwellAction period hPeriod second
      (globalSmoothMaxwellPairing period hPeriod second.metric
        (regularFrameGaugePotentialFromCoefficients period hPeriod second
          (regularFrameGaugeCoefficientTransition period hPeriod first second coefficients))
        (regularFrameGaugePotentialFromCoefficients period hPeriod second
          (regularFrameGaugeCoefficientTransition period hPeriod first second coefficients))) measure := by
  rw [regularFrameGaugeCoefficientTransition_preserves_potential]
  exact intrinsicMaxwellAction_eq_of_metric_volume_eq period hPeriod
    first second hMetric hVolume _ measure

/-- The genuine coefficient action evaluates on the potential reconstructed in its moving frame. -/
theorem mobileMaxwellAction_smoothCoefficients
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variation : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation : regularGeneralMetricSmoothC2Variation period hPeriod metric variation ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric)
    (measure : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure measure]
    (coefficients : SmoothQuotientField period hPeriod GaugeFiber) :
    let finalMetric := regularGeneralMetricC2LorentzChartRegularMetric
      period hPeriod metric variation hVariation
    let potential := regularFrameGaugePotentialFromCoefficients period hPeriod finalMetric coefficients
    regularGeneralMetricC0MobileGaugeCoefficientFixedVolumeMaxwellAction period hPeriod metric measure
      (regularGeneralMetricSmoothC2Variation period hPeriod metric variation)
      (smoothGaugeCoefficientC2CoreLinearMap period hPeriod coefficients) =
    intrinsicMaxwellAction period hPeriod finalMetric
      (globalSmoothMaxwellPairing period hPeriod finalMetric.metric potential potential) measure := by
  dsimp only
  simpa only [gaugePotentialFrameCoefficients_reconstructed] using
    regularGeneralMetricC0MobileGaugeCoefficientFixedVolumeMaxwellAction_smooth period hPeriod
      metric variation hVariation measure
      (regularFrameGaugePotentialFromCoefficients period hPeriod
        (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod metric variation hVariation) coefficients)

/-- Exact action equality for neighbouring smooth points after the genuine coefficient transition.
The transition depends on the metric increment and must also be differentiated. -/
theorem mobileMaxwellAction_recenter
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (shift increment : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hShift : regularGeneralMetricSmoothC2Variation period hPeriod metric shift ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric)
    (hTotal : regularGeneralMetricSmoothC2Variation period hPeriod metric (shift + increment) ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric)
    (hIncrement : regularGeneralMetricSmoothC2Variation period hPeriod
        (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod metric shift hShift) increment ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod
        (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod metric shift hShift))
    (measure : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure measure]
    (coefficients : SmoothQuotientField period hPeriod GaugeFiber) :
    let shifted := regularGeneralMetricC2LorentzChartRegularMetric period hPeriod metric shift hShift
    let originalFinal := regularGeneralMetricC2LorentzChartRegularMetric period hPeriod
      metric (shift + increment) hTotal
    let recenteredFinal := regularGeneralMetricC2LorentzChartRegularMetric period hPeriod
      shifted increment hIncrement
    regularGeneralMetricC0MobileGaugeCoefficientFixedVolumeMaxwellAction period hPeriod metric measure
      (regularGeneralMetricSmoothC2Variation period hPeriod metric (shift + increment))
      (smoothGaugeCoefficientC2CoreLinearMap period hPeriod coefficients) =
    regularGeneralMetricC0MobileGaugeCoefficientFixedVolumeMaxwellAction period hPeriod shifted measure
      (regularGeneralMetricSmoothC2Variation period hPeriod shifted increment)
      (smoothGaugeCoefficientC2CoreLinearMap period hPeriod
        (regularFrameGaugeCoefficientTransition period hPeriod originalFinal recenteredFinal coefficients)) := by
  let shifted := regularGeneralMetricC2LorentzChartRegularMetric period hPeriod metric shift hShift
  let originalFinal := regularGeneralMetricC2LorentzChartRegularMetric period hPeriod
    metric (shift + increment) hTotal
  let recenteredFinal := regularGeneralMetricC2LorentzChartRegularMetric period hPeriod
    shifted increment hIncrement
  let transported := regularFrameGaugeCoefficientTransition period hPeriod
    originalFinal recenteredFinal coefficients
  have hOld := mobileMaxwellAction_smoothCoefficients period hPeriod metric
    (shift + increment) hTotal measure coefficients
  have hNew := mobileMaxwellAction_smoothCoefficients period hPeriod shifted
    increment hIncrement measure transported
  have hVolume : originalFinal.volume = recenteredFinal.volume :=
    (lorentzChart_stored_volume period hPeriod metric (shift + increment) hTotal).trans
      ((lorentzChart_stored_volume period hPeriod shifted increment hIncrement).trans
        (lorentzChart_stored_volume period hPeriod metric shift hShift)).symm
  have hMetric := intrinsicMaxwellAction_coefficientTransition period hPeriod
    originalFinal recenteredFinal
    (lorentzChartRecenter_metric period hPeriod metric shift increment hShift hTotal hIncrement).symm
    hVolume coefficients measure
  exact hOld.trans (hMetric.trans hNew.symm)

end
end P0EFTJanusMobileMaxwellActionRecenter4D
end JanusFormal
