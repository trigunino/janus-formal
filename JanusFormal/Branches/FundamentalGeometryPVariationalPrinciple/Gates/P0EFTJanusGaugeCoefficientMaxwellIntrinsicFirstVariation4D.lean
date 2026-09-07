import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusStrongMaxwellMetricCenterFirstVariation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularFrameCanonicalMaxwellVariationalTestSeparation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusFrameFreeMaxwellPotentialHessian4D

/-! # Native coefficient Maxwell derivative as the intrinsic first variation

At the fixed metric centre, smooth coefficient directions differentiate to the
intrinsic Maxwell variation, hence to its canonical variational residual pairing.
-/

namespace JanusFormal
namespace P0EFTJanusGaugeCoefficientMaxwellIntrinsicFirstVariation4D

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
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusIntrinsicAbelianMaxwellAction4D
open P0EFTJanusMappingTorusConformalFrameFreeMaxwellHessian4D
open P0EFTJanusMappingTorusFrameFreeMaxwellPotentialHessian4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0Space4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
open P0EFTJanusProgramPGlobalGaugeTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D
open P0EFTJanusProgramPRegularGeneralMetricC2Maxwell4D
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothMaxwell4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartMaxwell4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalMetricGaugeCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2FixedVolumeMaxwellActionBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2GaugeCoefficientMaxwellAction4D
open P0EFTJanusProgramPRegularFrameMaxwellSmoothGaugeTestSeparation4D
open P0EFTJanusProgramPRegularFrameCanonicalMaxwellVariationalResidual4D
open P0EFTJanusProgramPRegularFrameCanonicalMaxwellVariationalTestSeparation4D
open P0EFTJanusStrongMaxwellMetricCenterFirstVariation4D

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
local instance : NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (C2Scalar period hPeriod) := inferInstance
local instance : CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod
local instance : IsFiniteMeasure (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

/-- Exact value of the native coefficient action on a smooth potential at the centre. -/
theorem gaugeCoefficientMaxwellAction_zeroMetric_eq_intrinsicAction
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure measure]
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    regularGeneralMetricC0GaugeCoefficientFixedVolumeMaxwellAction
        period hPeriod metric measure 0
        (smoothGaugeCoefficientC2CoreLinearMap period hPeriod
          (gaugePotentialFrameCoefficients period hPeriod metric potential)) =
      intrinsicMaxwellAction period hPeriod metric
        (globalSmoothMaxwellPairing period hPeriod metric.metric potential potential) measure := by
  rw [regularGeneralMetricC0GaugeCoefficientFixedVolumeMaxwellAction_frameCoefficients]
  have hPairing : regularGeneralMetricC0MaxwellPairing
      period hPeriod metric potential potential 0 =
      smoothToCanonicalPhysicalContinuousScalar period hPeriod
        (globalSmoothMaxwellPairing period hPeriod metric.metric potential potential) := by
    rw [regularGeneralMetricC0MaxwellPairing, regularGeneralMetricC2MaxwellPairing_zero,
      canonicalPhysicalScalarC2JetCoreToContinuous_smooth]
  unfold regularGeneralMetricC0FixedVolumeMaxwellAction
    regularGeneralMetricC0FixedVolumeMaxwellDensity
  rw [hPairing, regularGeneralMetricC0IntegralCLM_apply]
  rfl

private theorem gaugePotentialC2Coefficients_line
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod) (t : Real) :
    smoothGaugeCoefficientC2CoreLinearMap period hPeriod
        (gaugePotentialFrameCoefficients period hPeriod metric
          (gaugePotentialLine period hPeriod potential variation t)) =
      smoothGaugeCoefficientC2CoreLinearMap period hPeriod
        (gaugePotentialFrameCoefficients period hPeriod metric potential) +
      t • smoothGaugeCoefficientC2CoreLinearMap period hPeriod
        (gaugePotentialFrameCoefficients period hPeriod metric variation) := by
  let coefficients := (smoothGaugeCoefficientC2CoreLinearMap period hPeriod).comp
    (gaugePotentialFrameCoefficientsLinearMap period hPeriod metric)
  change coefficients (potential + t • variation) =
    coefficients potential + t • coefficients variation
  simp only [map_add, map_smul]

private def intrinsicPairingLine
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (data : RegularIntrinsicMaxwellLine period hPeriod metric)
    (t : Real) : SmoothQuotientField period hPeriod Real where
  toFun := fun point =>
    data.basePairing point + t * data.mixedPairing point + t ^ 2 * data.variationPairing point
  contMDiff_toFun :=
    data.basePairing.contMDiff_toFun.add
      (contMDiff_const.mul data.mixedPairing.contMDiff_toFun) |>.add
      (contMDiff_const.mul data.variationPairing.contMDiff_toFun)

private theorem maxwellPairing_gaugePotentialLine
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod) (t : Real) :
    globalSmoothMaxwellPairing period hPeriod metric.metric
        (gaugePotentialLine period hPeriod potential variation t)
        (gaugePotentialLine period hPeriod potential variation t) =
      intrinsicPairingLine period hPeriod metric
        (regularIntrinsicMaxwellLineOfPotentials period hPeriod metric potential variation) t := by
  apply SmoothQuotientField.ext
  intro point
  change globalMaxwellPairing period hPeriod metric.metric
    (potential + t • variation) (potential + t • variation) point = _
  rw [globalMaxwellPairing_add_left, globalMaxwellPairing_add_right,
    globalMaxwellPairing_add_right, globalMaxwellPairing_smul_left,
    globalMaxwellPairing_smul_right, globalMaxwellPairing_smul_right,
    globalMaxwellPairing_smul_left]
  simp only [intrinsicPairingLine, regularIntrinsicMaxwellLineOfPotentials,
    globalSmoothMaxwellPairing]
  change _ =
    globalMaxwellPairing period hPeriod metric.metric potential potential point +
      t * (globalMaxwellPairing period hPeriod metric.metric variation potential point +
        globalMaxwellPairing period hPeriod metric.metric potential variation point) +
      t ^ 2 * globalMaxwellPairing period hPeriod metric.metric variation variation point
  ring

attribute [local irreducible] regularGeneralMetricC0GaugeCoefficientFixedVolumeMaxwellAction

theorem gaugeCoefficientMaxwellAction_zeroMetric_differentiableAt
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure measure]
    (coefficients : GaugeC2Core period hPeriod) :
    DifferentiableAt Real
      (regularGeneralMetricC0GaugeCoefficientFixedVolumeMaxwellAction
        period hPeriod metric measure 0) coefficients := by
  exact (regularGeneralMetricC0GaugeCoefficientFixedVolumeMaxwellAction_differentiableAt_center
    period hPeriod metric measure coefficients).comp coefficients
      (hasFDerivAt_prodMk_right
        (0 : RegularGeneralMetricC2Core period hPeriod metric) coefficients).differentiableAt

/-- The native coefficient Fréchet derivative is the actual intrinsic gauge variation. -/
theorem gaugeCoefficientMaxwellAction_fderiv_zeroMetric_eq_intrinsicFirstVariation
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure measure]
    (potential variation : SmoothAbelianGaugePotential period hPeriod) :
    fderiv Real (regularGeneralMetricC0GaugeCoefficientFixedVolumeMaxwellAction
        period hPeriod metric measure 0)
      (smoothGaugeCoefficientC2CoreLinearMap period hPeriod
        (gaugePotentialFrameCoefficients period hPeriod metric potential))
      (smoothGaugeCoefficientC2CoreLinearMap period hPeriod
        (gaugePotentialFrameCoefficients period hPeriod metric variation)) =
      intrinsicMaxwellFirstVariation period hPeriod metric
        (regularIntrinsicMaxwellLineOfPotentials period hPeriod metric potential variation)
        measure := by
  let action := regularGeneralMetricC0GaugeCoefficientFixedVolumeMaxwellAction
    period hPeriod metric measure 0
  let base := smoothGaugeCoefficientC2CoreLinearMap period hPeriod
    (gaugePotentialFrameCoefficients period hPeriod metric potential)
  let direction := smoothGaugeCoefficientC2CoreLinearMap period hPeriod
    (gaugePotentialFrameCoefficients period hPeriod metric variation)
  let line := regularIntrinsicMaxwellLineOfPotentials period hPeriod metric potential variation
  have hAction : HasFDerivAt action (fderiv Real action base) base :=
    (gaugeCoefficientMaxwellAction_zeroMetric_differentiableAt
      period hPeriod metric measure base).hasFDerivAt
  have hAffine : HasDerivAt (fun t : Real => base + t • direction) direction 0 := by
    exact ((hasDerivAt_const (x := (0 : Real)) (c := base)).add
      ((hasDerivAt_id (0 : Real)).smul_const direction)).congr_deriv (by simp)
  have hFrechet := hAction.comp_hasDerivAt_of_eq 0 hAffine (by simp)
  have hIntrinsic : HasDerivAt
      (fun t : Real => intrinsicMaxwellAction period hPeriod metric
        (intrinsicPairingLine period hPeriod metric line t) measure)
      (intrinsicMaxwellFirstVariation period hPeriod metric line measure) 0 := by
    simpa only [intrinsicPairingLine] using
      intrinsicMaxwellAction_line_hasDerivAt period hPeriod metric line measure
  have hFunctions :
      (fun t : Real => action (base + t • direction)) =
      (fun t : Real => intrinsicMaxwellAction period hPeriod metric
        (intrinsicPairingLine period hPeriod metric line t) measure) := by
    funext t
    change regularGeneralMetricC0GaugeCoefficientFixedVolumeMaxwellAction
      period hPeriod metric measure 0 (base + t • direction) = _
    rw [show base + t • direction =
      smoothGaugeCoefficientC2CoreLinearMap period hPeriod
        (gaugePotentialFrameCoefficients period hPeriod metric
          (gaugePotentialLine period hPeriod potential variation t)) from
        (gaugePotentialC2Coefficients_line period hPeriod metric potential variation t).symm]
    rw [gaugeCoefficientMaxwellAction_zeroMetric_eq_intrinsicAction,
      maxwellPairing_gaugePotentialLine]
  have hFrechet' : HasDerivAt (fun t : Real => action (base + t • direction))
      (fderiv Real action base direction) 0 := by
    simpa only [Function.comp_def] using hFrechet
  rw [hFunctions] at hFrechet'
  exact hFrechet'.unique hIntrinsic

/-- The canonical residual retains the exact action normalization and sign. -/
theorem gaugeCoefficientMaxwellAction_fderiv_zeroMetric_eq_canonicalResidualPairing
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod) :
    fderiv Real (regularGeneralMetricC0GaugeCoefficientFixedVolumeMaxwellAction
        period hPeriod metric (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) 0)
      (smoothGaugeCoefficientC2CoreLinearMap period hPeriod
        (gaugePotentialFrameCoefficients period hPeriod metric potential))
      (smoothGaugeCoefficientC2CoreLinearMap period hPeriod
        (gaugePotentialFrameCoefficients period hPeriod metric variation)) =
      canonicalRegularFrameIntrinsicGaugeResidualPairing period hPeriod metric
        (regularFrameCanonicalMaxwellVariationalResidual period hPeriod metric potential)
        variation := by
  rw [gaugeCoefficientMaxwellAction_fderiv_zeroMetric_eq_intrinsicFirstVariation,
    intrinsicMaxwellFirstVariation_eq_variationalResidualPairing]

end
end P0EFTJanusGaugeCoefficientMaxwellIntrinsicFirstVariation4D
end JanusFormal
