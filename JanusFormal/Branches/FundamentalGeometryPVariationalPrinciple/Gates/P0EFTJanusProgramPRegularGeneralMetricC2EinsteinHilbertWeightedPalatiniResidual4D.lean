import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbertInvariantResidual4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2SmoothPalatiniCurrent4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularFrameEinsteinHilbertFrameFreeActionMeasureBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalMetricVolumeDivergenceStokes4D

/-!
# Weighted global Palatini residual

The legacy stored-frame action is a scalar-weighted frame-free action.  This
file rewrites its Einstein--Hilbert derivative against the intrinsic metric
volume.  Global Stokes removes the canonical metric divergence and leaves two
honest terms: the derivative of the stored-frame weight and the pointwise
defect between the regular-frame Palatini divergence and the canonical
metric-volume divergence.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbertWeightedPalatiniResidual4D

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

open MeasureTheory
open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFirstLevel4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVPairingRegularity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusIntrinsicEinsteinHilbertAction4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusMappingTorusCanonicalMetricVolumeDivergenceStokes4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbertDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2MaxwellStressDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothPalatiniCurrent4D
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothPalatiniDivergence4D
open P0EFTJanusProgramPRegularGeneralMetricGlobalSmoothSymmetricEinsteinTensor4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbertInvariantResidual4D
open P0EFTJanusProgramPRegularFrameEinsteinHilbertFrameFreeActionMeasureBridge4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance intrinsicCanonicalLorentzVolumeMeasureIsFinite :
    IsFiniteMeasure (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

/-- Pointwise defect between the already constructed regular-frame Palatini
divergence and the canonical divergence for the intrinsic metric volume. -/
def regularGeneralMetricC2PalatiniCanonicalDivergenceDefect
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    SmoothQuotientField period hPeriod Real where
  toFun := fun point =>
    regularFrameSmoothPalatiniCovariantDivergence period hPeriod metric tensor
        point -
      canonicalMetricVolumeDivergence period hPeriod metric
        (regularGeneralMetricC2SmoothPalatiniVector period hPeriod metric tensor)
        point
  contMDiff_toFun :=
    (regularFrameSmoothPalatiniCovariantDivergence period hPeriod metric tensor
      ).contMDiff_toFun.sub
      (canonicalMetricVolumeDivergence period hPeriod metric
        (regularGeneralMetricC2SmoothPalatiniVector period hPeriod metric tensor)
        ).contMDiff_toFun

@[simp]
theorem regularFrameSmoothPalatiniCovariantDivergence_eq_canonical_add_defect
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    regularFrameSmoothPalatiniCovariantDivergence period hPeriod metric tensor
        point =
      canonicalMetricVolumeDivergence period hPeriod metric
          (regularGeneralMetricC2SmoothPalatiniVector period hPeriod metric tensor)
          point +
        regularGeneralMetricC2PalatiniCanonicalDivergenceDefect period hPeriod
          metric tensor point := by
  unfold regularGeneralMetricC2PalatiniCanonicalDivergenceDefect
  ring

/-- Exact global derivative of the stored-frame EH action after passing to
the intrinsic metric volume and applying weak Stokes. -/
theorem regularGeneralMetricC0EinsteinHilbertActionDerivative_smooth_weightedPalatiniResidual
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (couplings : EinsteinHilbertCouplings)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    regularGeneralMetricC0EinsteinHilbertActionDerivativeAtZero
        period hPeriod metric
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) couplings
        (regularGeneralMetricC2SmoothDirection period hPeriod metric tensor) =
      (∫ point,
        (-(regularFrameEinsteinHilbertActionWeight period hPeriod metric point /
              (2 * couplings.gravitationalCoupling)) *
            generalMetricTensorPairingAt period hPeriod metric.metric
              (regularGeneralMetricSymmetricEinsteinTensor period hPeriod metric
                couplings.cosmologicalConstant) tensor point +
          (regularFrameEinsteinHilbertActionWeight period hPeriod metric point /
              (2 * couplings.gravitationalCoupling)) *
            regularGeneralMetricC2PalatiniCanonicalDivergenceDefect period
              hPeriod metric tensor point)
        ∂generalLorentzVolumeMeasure period hPeriod metric.metric) -
      (1 / (2 * couplings.gravitationalCoupling)) *
        ∫ point,
          mvfderiv coverModelWithCorners
            (regularFrameEinsteinHilbertActionWeight period hPeriod metric).toFun
            point
            (regularGeneralMetricC2SmoothPalatiniVector period hPeriod metric
              tensor point)
          ∂generalLorentzVolumeMeasure period hPeriod metric.metric := by
  let weight := regularFrameEinsteinHilbertActionWeight period hPeriod metric
  let current := regularGeneralMetricC2SmoothPalatiniVector period hPeriod
    metric tensor
  let canonicalDivergence :=
    canonicalMetricVolumeDivergence period hPeriod metric current
  let defect := regularGeneralMetricC2PalatiniCanonicalDivergenceDefect
    period hPeriod metric tensor
  let pairing := fun point =>
    generalMetricTensorPairingAt period hPeriod metric.metric
      (regularGeneralMetricSymmetricEinsteinTensor period hPeriod metric
        couplings.cosmologicalConstant) tensor point
  let metricMeasure := generalLorentzVolumeMeasure period hPeriod metric.metric
  letI : IsFiniteMeasure metricMeasure :=
    generalLorentzVolumeMeasure_isFinite period hPeriod metric.metric
  have hMain : Integrable
      (fun point =>
        -(weight point / (2 * couplings.gravitationalCoupling)) * pairing point +
          (weight point / (2 * couplings.gravitationalCoupling)) * defect point)
      metricMeasure := by
    have hWeight := weight.contMDiff_toFun.continuous
    have hPairing :=
      generalMetricTensorPairingAt_continuous period hPeriod metric.metric
        (regularGeneralMetricSymmetricEinsteinTensor period hPeriod metric
          couplings.cosmologicalConstant) tensor
    have hDefect := defect.contMDiff_toFun.continuous
    exact (((hWeight.div_const _).neg.mul hPairing).add
      ((hWeight.div_const _).mul hDefect)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hCanonical : Integrable
      (fun point => weight point * canonicalDivergence point) metricMeasure := by
    exact (weight.contMDiff_toFun.continuous.mul
      canonicalDivergence.contMDiff_toFun.continuous
      ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [regularGeneralMetricC0EinsteinHilbertActionDerivative_smooth_invariantResidual]
  calc
    (∫ point,
        (-(metric.volume point / (2 * couplings.gravitationalCoupling)) *
            pairing point +
          (metric.volume point / (2 * couplings.gravitationalCoupling)) *
            regularFrameSmoothPalatiniCovariantDivergence period hPeriod metric
              tensor point)
        ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod) =
      ∫ point,
        (-(weight point / (2 * couplings.gravitationalCoupling)) * pairing point +
          (weight point / (2 * couplings.gravitationalCoupling)) *
            regularFrameSmoothPalatiniCovariantDivergence period hPeriod metric
              tensor point) ∂metricMeasure := by
        rw [integral_generalLorentzVolumeMeasure_eq_reference]
        apply integral_congr_ae
        filter_upwards [] with point
        have hWeight :=
          regularFrameEinsteinHilbertActionWeight_mul_volumeRatio
            period hPeriod metric point
        dsimp only [weight, pairing, metricMeasure]
        rw [← hWeight]
        ring
    _ = (∫ point,
          (-(weight point / (2 * couplings.gravitationalCoupling)) *
              pairing point +
            (weight point / (2 * couplings.gravitationalCoupling)) *
              defect point) ∂metricMeasure) +
        (1 / (2 * couplings.gravitationalCoupling)) *
          ∫ point, weight point * canonicalDivergence point
            ∂metricMeasure := by
      calc
        _ = ∫ point,
            ((-(weight point / (2 * couplings.gravitationalCoupling)) *
                pairing point +
              (weight point / (2 * couplings.gravitationalCoupling)) *
                defect point) +
              (1 / (2 * couplings.gravitationalCoupling)) *
                (weight point * canonicalDivergence point)) ∂metricMeasure := by
          apply integral_congr_ae
          filter_upwards [] with point
          rw [regularFrameSmoothPalatiniCovariantDivergence_eq_canonical_add_defect]
          dsimp only [canonicalDivergence, defect, current]
          ring
        _ = _ := by
          rw [integral_add hMain (hCanonical.const_mul _), integral_const_mul]
    _ = (∫ point,
          (-(weight point / (2 * couplings.gravitationalCoupling)) *
              pairing point +
            (weight point / (2 * couplings.gravitationalCoupling)) *
              defect point) ∂metricMeasure) -
        (1 / (2 * couplings.gravitationalCoupling)) *
          ∫ point,
            mvfderiv coverModelWithCorners weight.toFun point (current point)
            ∂metricMeasure := by
      rw [canonicalMetricVolumeDivergence_weak_stokes period hPeriod metric
        current weight]
      ring
    _ = _ := by
      rfl

/-- In canonical-volume gauge, vanishing of the concrete divergence defect
reduces the EH derivative to the pure invariant Einstein bulk pairing. -/
theorem regularGeneralMetricC0EinsteinHilbertActionDerivative_smooth_invariantBulk_of_canonicalVolumeGauge
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (couplings : EinsteinHilbertCouplings)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hGauge : RegularGeneralMetricInCanonicalVolumeGauge period hPeriod metric)
    (hDefect : regularGeneralMetricC2PalatiniCanonicalDivergenceDefect
      period hPeriod metric tensor = 0) :
    regularGeneralMetricC0EinsteinHilbertActionDerivativeAtZero
        period hPeriod metric
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) couplings
        (regularGeneralMetricC2SmoothDirection period hPeriod metric tensor) =
      ∫ point,
        -(1 / (2 * couplings.gravitationalCoupling)) *
          generalMetricTensorPairingAt period hPeriod metric.metric
            (regularGeneralMetricSymmetricEinsteinTensor period hPeriod metric
              couplings.cosmologicalConstant) tensor point
        ∂generalLorentzVolumeMeasure period hPeriod metric.metric := by
  rw [regularGeneralMetricC0EinsteinHilbertActionDerivative_smooth_weightedPalatiniResidual
    period hPeriod metric couplings tensor]
  have hWeightFun :
      (regularFrameEinsteinHilbertActionWeight period hPeriod metric).toFun =
        fun _ => 1 := by
    funext point
    exact regularFrameEinsteinHilbertActionWeight_eq_one_of_canonicalVolumeGauge
      period hPeriod metric hGauge point
  have hMain :
      (∫ point,
        (-(regularFrameEinsteinHilbertActionWeight period hPeriod metric point /
              (2 * couplings.gravitationalCoupling)) *
            generalMetricTensorPairingAt period hPeriod metric.metric
              (regularGeneralMetricSymmetricEinsteinTensor period hPeriod metric
                couplings.cosmologicalConstant) tensor point +
          (regularFrameEinsteinHilbertActionWeight period hPeriod metric point /
              (2 * couplings.gravitationalCoupling)) *
            regularGeneralMetricC2PalatiniCanonicalDivergenceDefect period
              hPeriod metric tensor point)
        ∂generalLorentzVolumeMeasure period hPeriod metric.metric) =
      ∫ point,
        -(1 / (2 * couplings.gravitationalCoupling)) *
          generalMetricTensorPairingAt period hPeriod metric.metric
            (regularGeneralMetricSymmetricEinsteinTensor period hPeriod metric
              couplings.cosmologicalConstant) tensor point
        ∂generalLorentzVolumeMeasure period hPeriod metric.metric := by
    apply integral_congr_ae
    filter_upwards [] with point
    have hWeight := congrFun hWeightFun point
    have hDefectPoint := congrArg
      (fun field : SmoothQuotientField period hPeriod Real => field point)
      hDefect
    change regularGeneralMetricC2PalatiniCanonicalDivergenceDefect
      period hPeriod metric tensor point = (0 : Real) at hDefectPoint
    rw [hWeight, hDefectPoint]
    ring
  have hDerivative :
      (∫ point,
        mvfderiv coverModelWithCorners
          (regularFrameEinsteinHilbertActionWeight period hPeriod metric).toFun
          point
          (regularGeneralMetricC2SmoothPalatiniVector period hPeriod metric
            tensor point)
        ∂generalLorentzVolumeMeasure period hPeriod metric.metric) = 0 := by
    simp_rw [hWeightFun, mvfderiv_const]
    change (∫ _point, (0 : Real)
      ∂generalLorentzVolumeMeasure period hPeriod metric.metric) = 0
    simp
  calc
    _ = (
        ∫ point,
          -(1 / (2 * couplings.gravitationalCoupling)) *
            generalMetricTensorPairingAt period hPeriod metric.metric
              (regularGeneralMetricSymmetricEinsteinTensor period hPeriod metric
                couplings.cosmologicalConstant) tensor point
          ∂generalLorentzVolumeMeasure period hPeriod metric.metric) -
        (1 / (2 * couplings.gravitationalCoupling)) * 0 := by
      rw [hMain, hDerivative]
    _ = _ := by ring

/-- Gate marker: the complete weighted Palatini remainder is explicit, and
canonical-volume gauge plus the single geometric divergence identification
gives the pure Einstein residual. -/
theorem regular_general_metric_c2_einstein_hilbert_weighted_palatini_residual_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (couplings : EinsteinHilbertCouplings)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hGauge : RegularGeneralMetricInCanonicalVolumeGauge period hPeriod metric)
    (hDefect : regularGeneralMetricC2PalatiniCanonicalDivergenceDefect
      period hPeriod metric tensor = 0) :
    regularGeneralMetricC0EinsteinHilbertActionDerivativeAtZero
        period hPeriod metric
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) couplings
        (regularGeneralMetricC2SmoothDirection period hPeriod metric tensor) =
      ∫ point,
        -(1 / (2 * couplings.gravitationalCoupling)) *
          generalMetricTensorPairingAt period hPeriod metric.metric
            (regularGeneralMetricSymmetricEinsteinTensor period hPeriod metric
              couplings.cosmologicalConstant) tensor point
        ∂generalLorentzVolumeMeasure period hPeriod metric.metric :=
  regularGeneralMetricC0EinsteinHilbertActionDerivative_smooth_invariantBulk_of_canonicalVolumeGauge
    period hPeriod metric couplings tensor hGauge hDefect

end
end P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbertWeightedPalatiniResidual4D
end JanusFormal
