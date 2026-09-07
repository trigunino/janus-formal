import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCovariantAction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularFrameEinsteinHilbertFrameFreeActionMeasureBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularFrameMaxwellFrameFreeActionMeasureBridge4D

/-!
# Frame-free covariant EH--Maxwell action data

The bulk datum contains smooth metrics, potentials and explicit volume weights.
It requires no global tangent frame. The conversion retains the legacy weights
and proves equality for its stored curvature and Maxwell representatives.
The final identity replaces this bulk in the same complete legacy action;
interaction, matter, LL and boundary data are not migrated here.
-/

namespace JanusFormal
namespace P0EFTJanusFrameFreeCovariantActionData4D

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusIntrinsicEinsteinHilbertAction4D
open P0EFTJanusMappingTorusIntrinsicAbelianMaxwellAction4D
open P0EFTJanusMappingTorusGlobalSmoothScalarCurvatureGluing4D
open P0EFTJanusMappingTorusCanonicalTotalR4BallParametrization4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusMappingTorusFrameFreeIntrinsicEinsteinHilbertAction4D
open P0EFTJanusMappingTorusConformalFrameFreeMaxwellHessian4D
open P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPRegularFrameEinsteinHilbertFrameFreeActionMeasureBridge4D
open P0EFTJanusProgramPRegularFrameMaxwellFrameFreeActionMeasureBridge4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- Independently constructible from a smooth metric, potential and scalar
weight, with no choice of a tangent frame or stored curvature. -/
structure FrameFreeCovariantBulkSectorData where
  metric : SmoothGeneralLorentzMetric period hPeriod
  potential : SmoothAbelianGaugePotential period hPeriod
  volumeWeight : SmoothScalarField period hPeriod

/-- The two physical bulk sectors with their independent volume weights. -/
structure FrameFreeCovariantBulkActionData where
  plus : FrameFreeCovariantBulkSectorData period hPeriod
  minus : FrameFreeCovariantBulkSectorData period hPeriod

/-- Reuse the two metrics of the existing intrinsic Candidate-A geometry. -/
def frameFreeCovariantBulkActionDataOfGeometry
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (plusPotential minusPotential : SmoothAbelianGaugePotential period hPeriod)
    (plusWeight minusWeight : SmoothScalarField period hPeriod) :
    FrameFreeCovariantBulkActionData period hPeriod where
  plus := ⟨geometry.plusMetric, plusPotential, plusWeight⟩
  minus := ⟨geometry.minusMetric, minusPotential, minusWeight⟩

def frameFreeCovariantSectorEinsteinHilbertAction
    (data : FrameFreeCovariantBulkSectorData period hPeriod)
    (couplings : EinsteinHilbertCouplings) : Real :=
  ∫ point, data.volumeWeight point *
      frameFreeEinsteinHilbertDensity period hPeriod data.metric couplings point
    ∂generalLorentzVolumeMeasure period hPeriod data.metric

def frameFreeCovariantSectorMaxwellAction
    (data : FrameFreeCovariantBulkSectorData period hPeriod) : Real :=
  ∫ point, data.volumeWeight point *
      frameFreeMaxwellDensity period hPeriod data.metric data.potential point
    ∂generalLorentzVolumeMeasure period hPeriod data.metric

def frameFreeCovariantEinsteinHilbertAction
    (data : FrameFreeCovariantBulkActionData period hPeriod)
    (couplings : GlobalCandidateAActionCouplings) : Real :=
  frameFreeCovariantSectorEinsteinHilbertAction period hPeriod data.plus
      couplings.plusEinstein +
    frameFreeCovariantSectorEinsteinHilbertAction period hPeriod data.minus
      couplings.minusEinstein

def frameFreeCovariantMaxwellAction
    (data : FrameFreeCovariantBulkActionData period hPeriod)
    (couplings : GlobalCandidateAActionCouplings) : Real :=
  couplings.plusMaxwellScale *
      frameFreeCovariantSectorMaxwellAction period hPeriod data.plus +
    couplings.minusMaxwellScale *
      frameFreeCovariantSectorMaxwellAction period hPeriod data.minus

def frameFreeCovariantBulkAction
    (data : FrameFreeCovariantBulkActionData period hPeriod)
    (couplings : GlobalCandidateAActionCouplings) : Real :=
  frameFreeCovariantEinsteinHilbertAction period hPeriod data couplings +
    frameFreeCovariantMaxwellAction period hPeriod data couplings

/-- The local curvature contract determines the stored scalar globally. -/
theorem regularEinsteinHilbertMetric_scalarCurvature_eq_global
    (gravity : RegularEinsteinHilbertMetric period hPeriod) :
    gravity.scalarCurvature =
      globalSmoothScalarCurvature period hPeriod gravity.metric.metric := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  rcases canonicalHolonomicChartThroughEveryPoint period hPeriod point with
    ⟨patch, coordinate, hCoordinate⟩
  rw [← hCoordinate]
  exact (gravity.scalarCurvature_eq patch coordinate).trans
    (globalSmoothScalarCurvature_apply_local period hPeriod
      gravity.metric.metric patch coordinate).symm

/-- The stored Maxwell representative is the intrinsic contraction of the
same potential, rather than an independently chosen density. -/
theorem regularIntrinsicMaxwellLine_basePairing_eq_global
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (line : RegularIntrinsicMaxwellLine period hPeriod metric) :
    line.basePairing = globalSmoothMaxwellPairing period hPeriod metric.metric
      line.potential line.potential := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  rcases canonicalHolonomicChartThroughEveryPoint period hPeriod point with
    ⟨patch, coordinate, hCoordinate⟩
  rw [← hCoordinate]
  exact (line.basePairing_eq patch coordinate).trans
    (globalMaxwellPairing_eq_local period hPeriod metric.metric
      line.potential line.potential patch coordinate).symm

/-- Conversion retains the ratio of stored frame volume to intrinsic volume. -/
def frameFreeCovariantBulkSectorDataOfLegacy
    (gravity : RegularEinsteinHilbertMetric period hPeriod)
    (line : RegularIntrinsicMaxwellLine period hPeriod gravity.metric) :
    FrameFreeCovariantBulkSectorData period hPeriod where
  metric := gravity.metric.metric
  potential := line.potential
  volumeWeight :=
    regularFrameEinsteinHilbertActionWeight period hPeriod gravity.metric

theorem frameFreeCovariantSectorEinsteinHilbertAction_ofLegacy
    (gravity : RegularEinsteinHilbertMetric period hPeriod)
    (line : RegularIntrinsicMaxwellLine period hPeriod gravity.metric)
    (couplings : EinsteinHilbertCouplings) :
    frameFreeCovariantSectorEinsteinHilbertAction period hPeriod
        (frameFreeCovariantBulkSectorDataOfLegacy period hPeriod gravity line)
        couplings =
      intrinsicEinsteinHilbertAction period hPeriod couplings gravity
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
  change regularFrameWeightedFrameFreeEinsteinHilbertAction period hPeriod
    gravity.metric couplings = _
  rw [regularFrameWeightedFrameFreeEinsteinHilbertAction_eq_intrinsic]
  unfold intrinsicEinsteinHilbertAction
  apply integral_congr_ae
  filter_upwards [] with point
  change gravity.metric.volume point *
      ((1 / (2 * couplings.gravitationalCoupling)) *
        (globalSmoothScalarCurvature period hPeriod gravity.metric.metric point -
          2 * couplings.cosmologicalConstant)) =
    gravity.metric.volume point *
      ((1 / (2 * couplings.gravitationalCoupling)) *
        (gravity.scalarCurvature point - 2 * couplings.cosmologicalConstant))
  rw [regularEinsteinHilbertMetric_scalarCurvature_eq_global
    period hPeriod gravity]

theorem frameFreeCovariantSectorMaxwellAction_ofLegacy
    (gravity : RegularEinsteinHilbertMetric period hPeriod)
    (line : RegularIntrinsicMaxwellLine period hPeriod gravity.metric) :
    frameFreeCovariantSectorMaxwellAction period hPeriod
        (frameFreeCovariantBulkSectorDataOfLegacy period hPeriod gravity line) =
      intrinsicMaxwellAction period hPeriod gravity.metric line.basePairing
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
  change regularFrameWeightedFrameFreeMaxwellAction period hPeriod
    gravity.metric line.potential = _
  rw [regularFrameWeightedFrameFreeMaxwellAction_eq_intrinsic,
    regularIntrinsicMaxwellLine_basePairing_eq_global period hPeriod
      gravity.metric line]

theorem frameFreeCovariantBulkSectorDataOfLegacy_weight_eq_one
    (gravity : RegularEinsteinHilbertMetric period hPeriod)
    (line : RegularIntrinsicMaxwellLine period hPeriod gravity.metric)
    (hGauge : RegularGeneralMetricInCanonicalVolumeGauge
      period hPeriod gravity.metric)
    (point : EffectiveQuotient period hPeriod) :
    (frameFreeCovariantBulkSectorDataOfLegacy period hPeriod gravity line
      ).volumeWeight point = 1 :=
  regularFrameEinsteinHilbertActionWeight_eq_one_of_canonicalVolumeGauge
    period hPeriod gravity.metric hGauge point

variable {configuration : GlobalFieldConfiguration period hPeriod}
  {couplings : GlobalCandidateAActionCouplings}
  {NonNullFace NullFace : Type*} [Fintype NonNullFace] [Fintype NullFace]

def frameFreeCovariantBulkActionDataOfLegacy
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace) : FrameFreeCovariantBulkActionData period hPeriod where
  plus := frameFreeCovariantBulkSectorDataOfLegacy period hPeriod
    data.plusGravity data.plusMaxwell
  minus := frameFreeCovariantBulkSectorDataOfLegacy period hPeriod
    data.minusGravity data.minusMaxwell

theorem frameFreeCovariantBulkActionDataOfLegacy_eq_ofGeometry
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace) :
    frameFreeCovariantBulkActionDataOfLegacy period hPeriod data =
      frameFreeCovariantBulkActionDataOfGeometry period hPeriod
        configuration.geometry data.plusMaxwell.potential data.minusMaxwell.potential
        (regularFrameEinsteinHilbertActionWeight period hPeriod data.plusGravity.metric)
        (regularFrameEinsteinHilbertActionWeight period hPeriod data.minusGravity.metric) := by
  unfold frameFreeCovariantBulkActionDataOfLegacy
    frameFreeCovariantBulkActionDataOfGeometry frameFreeCovariantBulkSectorDataOfLegacy
  rw [data.plusMetric_eq, data.minusMetric_eq]

theorem frameFreeCovariantEinsteinHilbertAction_ofLegacy
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace) :
    frameFreeCovariantEinsteinHilbertAction period hPeriod
        (frameFreeCovariantBulkActionDataOfLegacy period hPeriod data) couplings =
      globalCandidateAEinsteinHilbertAction period hPeriod data
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
  unfold frameFreeCovariantEinsteinHilbertAction
    frameFreeCovariantBulkActionDataOfLegacy globalCandidateAEinsteinHilbertAction
  rw [frameFreeCovariantSectorEinsteinHilbertAction_ofLegacy,
    frameFreeCovariantSectorEinsteinHilbertAction_ofLegacy]

theorem frameFreeCovariantMaxwellAction_ofLegacy
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace) :
    frameFreeCovariantMaxwellAction period hPeriod
        (frameFreeCovariantBulkActionDataOfLegacy period hPeriod data) couplings =
      globalCandidateAMaxwellAction period hPeriod data
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
  unfold frameFreeCovariantMaxwellAction frameFreeCovariantBulkActionDataOfLegacy
    globalCandidateAMaxwellAction
  rw [frameFreeCovariantSectorMaxwellAction_ofLegacy,
    frameFreeCovariantSectorMaxwellAction_ofLegacy]

/-- Exact EH--Maxwell migration, including both stored volume weights. -/
theorem frameFreeCovariantBulkAction_ofLegacy
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace) :
    frameFreeCovariantBulkAction period hPeriod
        (frameFreeCovariantBulkActionDataOfLegacy period hPeriod data) couplings =
      globalCandidateAEinsteinHilbertAction period hPeriod data
          (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) +
        globalCandidateAMaxwellAction period hPeriod data
          (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
  unfold frameFreeCovariantBulkAction
  rw [frameFreeCovariantEinsteinHilbertAction_ofLegacy,
    frameFreeCovariantMaxwellAction_ofLegacy]

/-- The same complete legacy action after replacing only its EH--Maxwell
bulk by the constructed frame-free datum. All other physical fields persist. -/
theorem globalCandidateACovariantAction_eq_frameFreeBulk_and_same_sectors
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace) :
    globalCandidateACovariantAction period hPeriod data
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) =
      frameFreeCovariantBulkAction period hPeriod
          (frameFreeCovariantBulkActionDataOfLegacy period hPeriod data) couplings +
        globalCandidateAInteractionAction period hPeriod data
          (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) +
        globalCandidateAMatterAction period hPeriod configuration couplings +
        globalCandidateALLAction period hPeriod data +
        globalCandidateAGHYAction period hPeriod data +
        globalCandidateANullBoundaryAction period hPeriod data := by
  rw [frameFreeCovariantBulkAction_ofLegacy]
  unfold globalCandidateACovariantAction
  ring

end

end P0EFTJanusFrameFreeCovariantActionData4D
end JanusFormal
