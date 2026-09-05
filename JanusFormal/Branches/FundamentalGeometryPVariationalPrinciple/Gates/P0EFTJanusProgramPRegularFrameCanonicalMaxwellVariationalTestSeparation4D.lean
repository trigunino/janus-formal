import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularFrameCanonicalMaxwellVariationalResidual4D

/-! # Test separation for the authentic Maxwell first variation -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularFrameCanonicalMaxwellVariationalTestSeparation4D

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusIntrinsicAbelianMaxwellAction4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartMaxwell4D
open P0EFTJanusProgramPRegularFrameMaxwellSmoothGaugeTestSeparation4D
open P0EFTJanusProgramPRegularFrameCanonicalMaxwellVariationalStokes4D
open P0EFTJanusProgramPRegularFrameCanonicalMaxwellVariationalResidual4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- The authentic first variation is the canonical pairing with the derived
smooth variational residual. -/
theorem intrinsicMaxwellFirstVariation_eq_variationalResidualPairing
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod) :
    intrinsicMaxwellFirstVariation period hPeriod metric
        (regularIntrinsicMaxwellLineOfPotentials period hPeriod metric
          potential variation)
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) =
      canonicalRegularFrameIntrinsicGaugeResidualPairing period hPeriod metric
        (regularFrameCanonicalMaxwellVariationalResidual period hPeriod metric
          potential) variation := by
  rw [intrinsicMaxwellFirstVariation_eq_integral_variationalEuler]
  unfold canonicalRegularFrameIntrinsicGaugeResidualPairing
    regularFrameIntrinsicGaugeResidualPairing smoothGaugeResidualPairing
  apply integral_congr_ae
  filter_upwards [] with point
  exact (inner_variationalMaxwellResidual_frameCoefficients period hPeriod
    metric potential variation point).symm

/-- With a nonzero Maxwell coupling, stationarity against all genuine smooth
gauge variations is equivalent to pointwise vanishing of the derived Euler
residual. -/
theorem regularFrameCanonicalMaxwell_coupledStationary_iff_variationalResidual
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (coupling : Real) (hCoupling : coupling ≠ 0) :
    (∀ variation : SmoothAbelianGaugePotential period hPeriod,
        coupling *
          intrinsicMaxwellFirstVariation period hPeriod metric
            (regularIntrinsicMaxwellLineOfPotentials period hPeriod metric
              potential variation)
            (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) = 0) ↔
      ∀ point : EffectiveQuotient period hPeriod,
        regularFrameCanonicalMaxwellVariationalResidual period hPeriod metric
          potential point = 0 := by
  simp_rw [intrinsicMaxwellFirstVariation_eq_variationalResidualPairing]
  exact regular_frame_maxwell_smooth_gauge_test_separation_gate period hPeriod
    metric
      (regularFrameCanonicalMaxwellVariationalResidual period hPeriod metric
        potential) coupling hCoupling

/-- Gate marker: Maxwell stationarity now separates to an explicit smooth
pointwise residual without any abstract Stokes datum. -/
theorem regular_frame_canonical_maxwell_variational_test_separation_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (coupling : Real) (hCoupling : coupling ≠ 0) :
    (∀ variation : SmoothAbelianGaugePotential period hPeriod,
        coupling *
          intrinsicMaxwellFirstVariation period hPeriod metric
            (regularIntrinsicMaxwellLineOfPotentials period hPeriod metric
              potential variation)
            (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) = 0) ↔
      ∀ point : EffectiveQuotient period hPeriod,
        regularFrameCanonicalMaxwellVariationalResidual period hPeriod metric
          potential point = 0 :=
  regularFrameCanonicalMaxwell_coupledStationary_iff_variationalResidual period
    hPeriod metric potential coupling hCoupling

end
end P0EFTJanusProgramPRegularFrameCanonicalMaxwellVariationalTestSeparation4D
end JanusFormal
