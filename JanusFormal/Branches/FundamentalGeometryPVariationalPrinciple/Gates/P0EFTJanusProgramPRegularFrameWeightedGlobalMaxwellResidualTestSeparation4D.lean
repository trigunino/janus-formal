import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularFrameMaxwellFrameFreeActionMeasureBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularFrameMaxwellSmoothGaugeTestSeparation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricGlobalMaxwellDivergence4D

/-! # Global weighted Maxwell residual selected by the stored-frame action -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularFrameWeightedGlobalMaxwellResidualTestSeparation4D

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 800000

noncomputable section

open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusProgramPGlobalGaugeTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPGeneralMetricPositiveDualizer4D
open P0EFTJanusProgramPRegularGeneralMetricGlobalMaxwellDivergence4D
open P0EFTJanusProgramPRegularFrameMaxwellFrameFreeActionMeasureBridge4D
open P0EFTJanusProgramPRegularFrameMaxwellSmoothGaugeTestSeparation4D
open P0EFTJanusMappingTorusGlobalGeneralMetricSymmetricTensorDivergence4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- Curvature multiplied by the intrinsic scalar weight carried by the stored
regular frame. -/
def regularFrameWeightedGlobalGaugeCurvatureTensor
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2) :=
  smoothBulkScalarSMulCovariantTensor period hPeriod
    (regularFrameMaxwellActionWeight period hPeriod metric)
    (regularGlobalGaugeCurvatureTensor period hPeriod metric potential
      component)

/-- Genuine global Euler covector `∇ᵘ(w Fᵘᵥ)` of the weighted frame-free
Maxwell action. -/
def regularFrameWeightedGlobalMaxwellDivergence
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2) :=
  globalGeneralMetricSymmetricTensorDivergence period hPeriod metric.metric
    (regularFrameWeightedGlobalGaugeCurvatureTensor period hPeriod metric
      potential component)

/-- Eight smooth regular-frame coefficients of the weighted global Euler
covectors. -/
def regularFrameWeightedGlobalMaxwellResidual
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    SmoothQuotientField period hPeriod GaugeFiber where
  toFun := fun point =>
    (EuclideanSpace.equiv (Fin 4 × Fin 2) Real).symm (fun index =>
      regularFrameWeightedGlobalMaxwellDivergence period hPeriod metric
        potential index.2 point (metric.frame index.1 point))
  contMDiff_toFun := by
    apply
      (EuclideanSpace.equiv (Fin 4 × Fin 2) Real).symm.toContinuousLinearMap
        |>.contMDiff.comp
    rw [contMDiff_pi_space]
    intro index
    have hApplied :=
      (regularFrameWeightedGlobalMaxwellDivergence period hPeriod metric
        potential index.2).contMDiff.clm_bundle_apply
          (metric.frame index.1).contMDiff
    intro point
    have hAppliedAt := hApplied point
    rw [Bundle.contMDiffAt_section] at hAppliedAt
    simpa using hAppliedAt

@[simp]
theorem regularFrameWeightedGlobalMaxwellResidual_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (index : Fin 4) (component : Fin 2) :
    regularFrameWeightedGlobalMaxwellResidual period hPeriod metric potential
        point (index, component) =
      regularFrameWeightedGlobalMaxwellDivergence period hPeriod metric
        potential component point (metric.frame index point) :=
  rfl

/-- Chart-free strong equation selected by the stored-frame Maxwell action. -/
def RegularFrameWeightedGlobalMaxwellEquation
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod) : Prop :=
  ∀ component : Fin 2,
    regularFrameWeightedGlobalMaxwellDivergence period hPeriod metric
      potential component = 0

/-- Vanishing of all smooth frame coefficients is equivalent to the weighted
global strong equation. -/
theorem regularFrameWeightedGlobalMaxwellResidual_pointwise_zero_iff
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    (∀ point : EffectiveQuotient period hPeriod,
        regularFrameWeightedGlobalMaxwellResidual period hPeriod metric
          potential point = 0) ↔
      RegularFrameWeightedGlobalMaxwellEquation period hPeriod metric
        potential := by
  constructor
  · intro hResidual component
    apply ContMDiffSection.ext
    intro point
    apply ContinuousLinearMap.ext
    intro vector
    obtain ⟨coordinates, rfl⟩ := (metric.frameEquiv point).surjective vector
    have hExpansion :
        metric.frameEquiv point coordinates =
          ∑ index : Fin 4, coordinates index • metric.frame index point := by
      calc
        metric.frameEquiv point coordinates =
            metric.frameEquiv point
              (∑ index : Fin 4,
                coordinates index • (Pi.basisFun Real (Fin 4)) index) := by
          congr 1
          exact ((Pi.basisFun Real (Fin 4)).sum_repr coordinates).symm
        _ = ∑ index : Fin 4,
            coordinates index •
              metric.frameEquiv point ((Pi.basisFun Real (Fin 4)) index) := by
          simp only [map_sum, map_smul]
        _ = ∑ index : Fin 4,
            coordinates index • metric.frame index point := by
          apply Finset.sum_congr rfl
          intro index _
          rw [RegularGeneralLorentzMetric.frame_eq_basisFun]
    rw [hExpansion, map_sum]
    apply Finset.sum_eq_zero
    intro index _
    rw [map_smul]
    have hEntry := congrArg
      (fun value : GaugeFiber => value (index, component)) (hResidual point)
    have hFrame :
        regularFrameWeightedGlobalMaxwellDivergence period hPeriod metric
          potential component point (metric.frame index point) = 0 := by
      simpa using hEntry
    rw [hFrame, smul_zero]
  · intro hStrong point
    apply (EuclideanSpace.equiv (Fin 4 × Fin 2) Real).injective
    funext index
    change regularFrameWeightedGlobalMaxwellDivergence period hPeriod metric
      potential index.2 point (metric.frame index.1 point) = 0
    have hAt := congrArg (fun field => field point) (hStrong index.2)
    change regularFrameWeightedGlobalMaxwellDivergence period hPeriod metric
      potential index.2 point = 0 at hAt
    rw [hAt]
    rfl

/-- Nonzero coupling and all intrinsic smooth tests separate the weighted
global Maxwell PDE. -/
theorem regularFrameWeightedGlobalMaxwell_coupledWeak_iff_strong
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (coupling : Real) (hCoupling : coupling ≠ 0) :
    (∀ variation : SmoothAbelianGaugePotential period hPeriod,
        coupling * canonicalRegularFrameIntrinsicGaugeResidualPairing period
          hPeriod metric
            (regularFrameWeightedGlobalMaxwellResidual period hPeriod metric
              potential) variation = 0) ↔
      RegularFrameWeightedGlobalMaxwellEquation period hPeriod metric
        potential := by
  calc
    _ ↔ ∀ point : EffectiveQuotient period hPeriod,
        regularFrameWeightedGlobalMaxwellResidual period hPeriod metric
          potential point = 0 :=
      regular_frame_maxwell_smooth_gauge_test_separation_gate period hPeriod
        metric
          (regularFrameWeightedGlobalMaxwellResidual period hPeriod metric
            potential) coupling hCoupling
    _ ↔ _ :=
      regularFrameWeightedGlobalMaxwellResidual_pointwise_zero_iff period
        hPeriod metric potential

/-- Independent paired weak equation for the two action-weighted sectors. -/
def PairedRegularFrameWeightedGlobalMaxwellWeakEquation
    (plusMetric minusMetric : RegularGeneralLorentzMetric period hPeriod)
    (plusPotential minusPotential : SmoothAbelianGaugePotential period hPeriod)
    (plusCoupling minusCoupling : Real) : Prop :=
  ∀ variations : SmoothAbelianGaugePotential period hPeriod ×
      SmoothAbelianGaugePotential period hPeriod,
    plusCoupling * canonicalRegularFrameIntrinsicGaugeResidualPairing period
        hPeriod plusMetric
          (regularFrameWeightedGlobalMaxwellResidual period hPeriod plusMetric
            plusPotential) variations.1 +
      minusCoupling * canonicalRegularFrameIntrinsicGaugeResidualPairing period
        hPeriod minusMetric
          (regularFrameWeightedGlobalMaxwellResidual period hPeriod minusMetric
            minusPotential) variations.2 = 0

@[simp] private theorem canonicalResidualPairing_zero
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (residual : SmoothQuotientField period hPeriod GaugeFiber) :
    canonicalRegularFrameIntrinsicGaugeResidualPairing period hPeriod metric
        residual (0 : SmoothAbelianGaugePotential period hPeriod) = 0 := by
  unfold canonicalRegularFrameIntrinsicGaugeResidualPairing
  unfold regularFrameIntrinsicGaugeResidualPairing
  rw [show gaugePotentialFrameCoefficients period hPeriod metric
        (0 : SmoothAbelianGaugePotential period hPeriod) = 0 from
      (gaugePotentialFrameCoefficientsLinearMap period hPeriod metric).map_zero]
  change (∫ point, inner Real (residual point) (0 : GaugeFiber) ∂
    intrinsicCanonicalLorentzVolumeMeasure period hPeriod) = 0
  simp

/-- Gate: nonzero physical couplings and independent smooth tests split the
paired weak equation into both global weighted Maxwell PDEs. -/
theorem regular_frame_weighted_global_maxwell_residual_test_separation_gate
    (plusMetric minusMetric : RegularGeneralLorentzMetric period hPeriod)
    (plusPotential minusPotential : SmoothAbelianGaugePotential period hPeriod)
    (plusCoupling minusCoupling : Real)
    (hPlusCoupling : plusCoupling ≠ 0)
    (hMinusCoupling : minusCoupling ≠ 0) :
    PairedRegularFrameWeightedGlobalMaxwellWeakEquation period hPeriod
        plusMetric minusMetric plusPotential minusPotential plusCoupling
          minusCoupling ↔
      RegularFrameWeightedGlobalMaxwellEquation period hPeriod plusMetric
          plusPotential ∧
        RegularFrameWeightedGlobalMaxwellEquation period hPeriod minusMetric
          minusPotential := by
  constructor
  · intro hWeak
    have hPlusWeak :
        ∀ variation : SmoothAbelianGaugePotential period hPeriod,
          plusCoupling * canonicalRegularFrameIntrinsicGaugeResidualPairing
            period hPeriod plusMetric
              (regularFrameWeightedGlobalMaxwellResidual period hPeriod
                plusMetric plusPotential) variation = 0 := by
      intro variation
      simpa only [canonicalResidualPairing_zero, mul_zero, add_zero] using
        hWeak (variation, 0)
    have hMinusWeak :
        ∀ variation : SmoothAbelianGaugePotential period hPeriod,
          minusCoupling * canonicalRegularFrameIntrinsicGaugeResidualPairing
            period hPeriod minusMetric
              (regularFrameWeightedGlobalMaxwellResidual period hPeriod
                minusMetric minusPotential) variation = 0 := by
      intro variation
      simpa only [canonicalResidualPairing_zero, mul_zero, zero_add] using
        hWeak (0, variation)
    exact
      ⟨(regularFrameWeightedGlobalMaxwell_coupledWeak_iff_strong period
          hPeriod plusMetric plusPotential plusCoupling hPlusCoupling).mp
            hPlusWeak,
        (regularFrameWeightedGlobalMaxwell_coupledWeak_iff_strong period
          hPeriod minusMetric minusPotential minusCoupling hMinusCoupling).mp
            hMinusWeak⟩
  · rintro ⟨hPlus, hMinus⟩ variations
    have hPlusZero :=
      (regularFrameWeightedGlobalMaxwell_coupledWeak_iff_strong period hPeriod
        plusMetric plusPotential plusCoupling hPlusCoupling).mpr hPlus
          variations.1
    have hMinusZero :=
      (regularFrameWeightedGlobalMaxwell_coupledWeak_iff_strong period hPeriod
        minusMetric minusPotential minusCoupling hMinusCoupling).mpr hMinus
          variations.2
    rw [hPlusZero, hMinusZero, zero_add]

end

end P0EFTJanusProgramPRegularFrameWeightedGlobalMaxwellResidualTestSeparation4D
end JanusFormal
