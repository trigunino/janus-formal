import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricStrongMaxwellPDE4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularFrameMaxwellSmoothGaugeTestSeparation4D

/-! # Global Maxwell residual and paired test separation -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricMaxwellGlobalResidualTestSeparation4D

set_option autoImplicit false

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
open P0EFTJanusProgramPRegularGeneralMetricGlobalMaxwellDivergence4D
open P0EFTJanusProgramPRegularGeneralMetricStrongMaxwellPDE4D
open P0EFTJanusProgramPRegularFrameMaxwellSmoothGaugeTestSeparation4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- The eight regular-frame coefficients of the genuine smooth global
Maxwell-divergence covectors. -/
def regularGlobalMaxwellDivergenceFrameResidual
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    SmoothQuotientField period hPeriod GaugeFiber where
  toFun := fun point =>
    (EuclideanSpace.equiv (Fin 4 × Fin 2) Real).symm (fun index =>
      regularGlobalMaxwellDivergence period hPeriod metric potential index.2
        point (metric.frame index.1 point))
  contMDiff_toFun := by
    apply
      (EuclideanSpace.equiv (Fin 4 × Fin 2) Real).symm.toContinuousLinearMap
        |>.contMDiff.comp
    rw [contMDiff_pi_space]
    intro index
    have hApplied :=
      (regularGlobalMaxwellDivergence period hPeriod metric potential index.2
        ).contMDiff.clm_bundle_apply (metric.frame index.1).contMDiff
    intro point
    have hAppliedAt := hApplied point
    rw [Bundle.contMDiffAt_section] at hAppliedAt
    simpa using hAppliedAt

@[simp]
theorem regularGlobalMaxwellDivergenceFrameResidual_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (index : Fin 4) (component : Fin 2) :
    regularGlobalMaxwellDivergenceFrameResidual period hPeriod metric potential
        point (index, component) =
      regularGlobalMaxwellDivergence period hPeriod metric potential component
        point (metric.frame index point) :=
  rfl

/-- Vanishing of the eight smooth frame coefficients is exactly the
chart-free source-free Maxwell equation. -/
theorem regularGlobalMaxwellDivergenceFrameResidual_pointwise_zero_iff_strong
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    (∀ point : EffectiveQuotient period hPeriod,
        regularGlobalMaxwellDivergenceFrameResidual period hPeriod metric
          potential point = 0) ↔
      RegularGeneralMetricStrongMaxwellEquation period hPeriod metric
        potential := by
  constructor
  · intro hResidual component
    apply ContMDiffSection.ext
    intro point
    apply ContinuousLinearMap.ext
    intro vector
    change regularGlobalMaxwellDivergence period hPeriod metric potential
      component point vector = 0
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
        regularGlobalMaxwellDivergence period hPeriod metric potential component
          point (metric.frame index point) = 0 := by
      simpa using hEntry
    rw [hFrame, smul_zero]
  · intro hStrong point
    apply (EuclideanSpace.equiv (Fin 4 × Fin 2) Real).injective
    funext index
    change regularGlobalMaxwellDivergence period hPeriod metric potential
      index.2 point (metric.frame index.1 point) = 0
    have hAt := congrArg (fun field => field point) (hStrong index.2)
    change regularGlobalMaxwellDivergence period hPeriod metric potential
      index.2 point = 0 at hAt
    rw [hAt]
    rfl

/-- With nonzero coupling, the canonical weak pairing of the genuine global
Maxwell residual is equivalent to the chart-free strong PDE. -/
theorem regularGlobalMaxwellDivergence_coupledWeak_iff_strong
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (coupling : Real) (hCoupling : coupling ≠ 0) :
    (∀ variation : SmoothAbelianGaugePotential period hPeriod,
        coupling * canonicalRegularFrameIntrinsicGaugeResidualPairing period
          hPeriod metric
            (regularGlobalMaxwellDivergenceFrameResidual period hPeriod metric
              potential) variation = 0) ↔
      RegularGeneralMetricStrongMaxwellEquation period hPeriod metric
        potential := by
  calc
    _ ↔ ∀ point : EffectiveQuotient period hPeriod,
        regularGlobalMaxwellDivergenceFrameResidual period hPeriod metric
          potential point = 0 :=
      regular_frame_maxwell_smooth_gauge_test_separation_gate period hPeriod
        metric
          (regularGlobalMaxwellDivergenceFrameResidual period hPeriod metric
            potential) coupling hCoupling
    _ ↔ _ :=
      regularGlobalMaxwellDivergenceFrameResidual_pointwise_zero_iff_strong
        period hPeriod metric potential

/-- Independent paired Maxwell weak equation for the two genuine global
residuals. -/
def PairedRegularGlobalMaxwellCoupledWeakEquation
    (plusMetric minusMetric : RegularGeneralLorentzMetric period hPeriod)
    (plusPotential minusPotential : SmoothAbelianGaugePotential period hPeriod)
    (plusCoupling minusCoupling : Real) : Prop :=
  ∀ variations : SmoothAbelianGaugePotential period hPeriod ×
      SmoothAbelianGaugePotential period hPeriod,
    plusCoupling * canonicalRegularFrameIntrinsicGaugeResidualPairing period
        hPeriod plusMetric
          (regularGlobalMaxwellDivergenceFrameResidual period hPeriod plusMetric
            plusPotential) variations.1 +
      minusCoupling * canonicalRegularFrameIntrinsicGaugeResidualPairing period
        hPeriod minusMetric
          (regularGlobalMaxwellDivergenceFrameResidual period hPeriod minusMetric
            minusPotential) variations.2 = 0

@[simp] private theorem canonicalRegularFrameIntrinsicGaugeResidualPairing_zero
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

/-- Gate: independent smooth intrinsic tests split the paired weak equation
into both pointwise Maxwell PDEs when both physical couplings are nonzero. -/
theorem regular_general_metric_paired_maxwell_global_residual_test_separation_gate
    (plusMetric minusMetric : RegularGeneralLorentzMetric period hPeriod)
    (plusPotential minusPotential : SmoothAbelianGaugePotential period hPeriod)
    (plusCoupling minusCoupling : Real)
    (hPlusCoupling : plusCoupling ≠ 0)
    (hMinusCoupling : minusCoupling ≠ 0) :
    PairedRegularGlobalMaxwellCoupledWeakEquation period hPeriod plusMetric
        minusMetric plusPotential minusPotential plusCoupling minusCoupling ↔
      RegularGeneralMetricStrongMaxwellEquation period hPeriod plusMetric
          plusPotential ∧
        RegularGeneralMetricStrongMaxwellEquation period hPeriod minusMetric
          minusPotential := by
  constructor
  · intro hWeak
    have hPlusWeak :
        ∀ variation : SmoothAbelianGaugePotential period hPeriod,
          plusCoupling *
            canonicalRegularFrameIntrinsicGaugeResidualPairing period hPeriod
              plusMetric
                (regularGlobalMaxwellDivergenceFrameResidual period hPeriod
                  plusMetric plusPotential) variation = 0 := by
      intro variation
      have hTest := hWeak (variation, 0)
      simpa only [canonicalRegularFrameIntrinsicGaugeResidualPairing_zero,
        mul_zero, add_zero] using hTest
    have hMinusWeak :
        ∀ variation : SmoothAbelianGaugePotential period hPeriod,
          minusCoupling *
            canonicalRegularFrameIntrinsicGaugeResidualPairing period hPeriod
              minusMetric
                (regularGlobalMaxwellDivergenceFrameResidual period hPeriod
                  minusMetric minusPotential) variation = 0 := by
      intro variation
      have hTest := hWeak (0, variation)
      simpa only [canonicalRegularFrameIntrinsicGaugeResidualPairing_zero,
        mul_zero, zero_add] using hTest
    exact
      ⟨(regularGlobalMaxwellDivergence_coupledWeak_iff_strong period hPeriod
          plusMetric plusPotential plusCoupling hPlusCoupling).mp hPlusWeak,
        (regularGlobalMaxwellDivergence_coupledWeak_iff_strong period hPeriod
          minusMetric minusPotential minusCoupling hMinusCoupling).mp
            hMinusWeak⟩
  · rintro ⟨hPlus, hMinus⟩ variations
    have hPlusZero :=
      (regularGlobalMaxwellDivergence_coupledWeak_iff_strong period hPeriod
        plusMetric plusPotential plusCoupling hPlusCoupling).mpr hPlus
          variations.1
    have hMinusZero :=
      (regularGlobalMaxwellDivergence_coupledWeak_iff_strong period hPeriod
        minusMetric minusPotential minusCoupling hMinusCoupling).mpr hMinus
          variations.2
    rw [hPlusZero, hMinusZero, zero_add]

end

end P0EFTJanusProgramPRegularGeneralMetricMaxwellGlobalResidualTestSeparation4D
end JanusFormal
