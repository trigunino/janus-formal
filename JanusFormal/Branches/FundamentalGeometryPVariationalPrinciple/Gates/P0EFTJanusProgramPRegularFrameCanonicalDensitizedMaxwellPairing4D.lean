import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularFrameCanonicalDensitizedMaxwellResidual4D

/-! # Pairing formula for the canonically densitized Maxwell residual -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularFrameCanonicalDensitizedMaxwellPairing4D

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusProgramPGlobalGaugeTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPRegularFrameMaxwellSmoothGaugeTestSeparation4D
open P0EFTJanusProgramPRegularFrameWeightedGlobalMaxwellResidualTestSeparation4D
open P0EFTJanusProgramPRegularFrameGlobalMaxwellBoundaryCurrent4D
open P0EFTJanusProgramPRegularFrameCanonicalDensitizedMaxwellResidual4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

/-- Explicit canonical-volume strong Maxwell pairing density. -/
def regularFrameCanonicalDensitizedMaxwellStrongPairing
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (point : EffectiveQuotient period hPeriod) : Real :=
  ∑ index : Fin 4, ∑ component : Fin 2,
    globalMetricVolumeRatio period hPeriod metric.metric point *
      regularFrameWeightedGlobalMaxwellDivergence period hPeriod metric
        potential component point
          (regularFrameSmoothDualVector period hPeriod metric index point) *
      variation.toFun component point (metric.frame index point)

/-- The Euclidean coefficient pairing is exactly contraction of the
canonically densitized Euler covector with the intrinsic gauge variation. -/
theorem inner_densitizedMaxwellResidual_frameCoefficients
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    inner Real
        (regularFrameCanonicalDensitizedMaxwellResidual period hPeriod metric
          potential point)
        (gaugePotentialFrameCoefficients period hPeriod metric variation point) =
      regularFrameCanonicalDensitizedMaxwellStrongPairing period hPeriod metric
        potential variation point := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type]
  unfold regularFrameCanonicalDensitizedMaxwellStrongPairing
  apply Finset.sum_congr rfl
  intro index _
  apply Finset.sum_congr rfl
  intro component _
  rw [Real.inner_apply,
    regularFrameCanonicalDensitizedMaxwellResidual_apply,
    gaugePotentialFrameCoefficients_apply]

/-- The canonical intrinsic residual functional is the integral of the
explicit densitized strong pairing. -/
theorem canonicalDensitizedMaxwellResidualPairing_eq_integral_strong
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod) :
    canonicalRegularFrameIntrinsicGaugeResidualPairing period hPeriod metric
        (regularFrameCanonicalDensitizedMaxwellResidual period hPeriod metric
          potential) variation =
      ∫ point,
        regularFrameCanonicalDensitizedMaxwellStrongPairing period hPeriod metric
          potential variation point
        ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
  unfold canonicalRegularFrameIntrinsicGaugeResidualPairing
    regularFrameIntrinsicGaugeResidualPairing smoothGaugeResidualPairing
  apply integral_congr_ae
  filter_upwards [] with point
  exact inner_densitizedMaxwellResidual_frameCoefficients period hPeriod metric
    potential variation point

/-- Gate marker: the corrected canonical weak residual is now an explicit
intrinsic contraction, not only an abstract Euclidean coefficient pairing. -/
theorem regular_frame_canonical_densitized_maxwell_pairing_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod) :
    canonicalRegularFrameIntrinsicGaugeResidualPairing period hPeriod metric
        (regularFrameCanonicalDensitizedMaxwellResidual period hPeriod metric
          potential) variation =
      ∫ point,
        regularFrameCanonicalDensitizedMaxwellStrongPairing period hPeriod metric
          potential variation point
        ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  canonicalDensitizedMaxwellResidualPairing_eq_integral_strong period hPeriod
    metric potential variation

end
end P0EFTJanusProgramPRegularFrameCanonicalDensitizedMaxwellPairing4D
end JanusFormal
