import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusH1GraphTrace4D
import Mathlib.MeasureTheory.Constructions.HaarToSphere

/-!
# Canonical-volume graph H1 and the exact physical trace frontier

The canonical Lorentz volume is inserted into the existing first-jet graph
completion, using the already constructed finite smooth tangent generators.
The throat is equipped with the analogous round `S^2` surface measure times
one time period.  Both measures are finite and nonzero.

Thus the physical graph-H1 space is unconditional.  A continuous trace to
the canonical throat `L2` exists exactly when the single smooth codimension-one
trace inequality holds.  This is the analytic theorem absent from Mathlib;
no throat-supported spacetime measure is substituted for the physical volume.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff ENNReal
open MeasureTheory Set
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev throatData := fixedEquatorData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)
private abbrev EffectiveThroat := MappingTorus (throatData period hPeriod)
private abbrev StandardThroatSphere := Metric.sphere (0 : EuclideanR3) 1

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance effectiveThroatCompactSpace :
    CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod

local instance effectiveThroatMeasurableSpace :
    MeasurableSpace (EffectiveThroat period hPeriod) := borel _

local instance effectiveThroatBorelSpace :
    BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

private def fundamentalTimeInterval : Set Real :=
  Set.Ioc (min 0 period) (max 0 period)

private def canonicalThroatProductMeasure :
    Measure (StandardThroatSphere × Real) :=
  ((volume : Measure EuclideanR3).toSphere).prod
    (volume.restrict (fundamentalTimeInterval period))

private def canonicalThroatFundamentalDomainMap
    (point : StandardThroatSphere × Real) :
    EffectiveThroat period hPeriod :=
  mappingTorusMk (throatData period hPeriod)
    ((coverHomeomorphProd (throatData period hPeriod)).symm
      (equatorialTwoSphereHomeomorph.symm point.1, point.2))

private theorem canonicalThroatFundamentalDomainMap_continuous :
    Continuous (canonicalThroatFundamentalDomainMap period hPeriod) := by
  have hProduct : Continuous
      (fun point : StandardThroatSphere × Real =>
        (equatorialTwoSphereHomeomorph.symm point.1, point.2)) :=
    (equatorialTwoSphereHomeomorph.symm.continuous.comp continuous_fst).prodMk
      continuous_snd
  exact (mappingTorusMk_isCoveringMap
      (throatData period hPeriod)).isLocalHomeomorph.continuous.comp
    ((coverHomeomorphProd
      (throatData period hPeriod)).symm.continuous.comp hProduct)

private theorem canonicalThroatProductMeasure_isFinite :
    IsFiniteMeasure (canonicalThroatProductMeasure period) := by
  unfold canonicalThroatProductMeasure fundamentalTimeInterval
  infer_instance

private theorem canonicalThroatProductMeasure_ne_zero
    (hPeriod : period ≠ 0) :
    canonicalThroatProductMeasure period ≠ 0 := by
  have hSphere : (volume : Measure EuclideanR3).toSphere ≠ 0 :=
    Measure.toSphere_ne_zero (volume : Measure EuclideanR3)
  have hTime : volume.restrict (fundamentalTimeInterval period) ≠ 0 := by
    intro hZero
    have hVolumeZero := Measure.restrict_eq_zero.mp hZero
    rw [fundamentalTimeInterval, Real.volume_Ioc,
      max_sub_min_eq_abs] at hVolumeZero
    apply (ENNReal.ofReal_pos.mpr (abs_pos.mpr hPeriod)).ne'
    simpa using hVolumeZero
  rw [← Measure.measure_univ_ne_zero]
  rw [show (Set.univ : Set (StandardThroatSphere × Real)) =
      (Set.univ : Set StandardThroatSphere) ×ˢ (Set.univ : Set Real) by simp]
  unfold canonicalThroatProductMeasure
  rw [Measure.prod_prod]
  exact mul_ne_zero
    ((Measure.measure_univ_ne_zero).2 hSphere)
    ((Measure.measure_univ_ne_zero).2 hTime)

/-- Canonical round-sphere-times-time volume on the actual effective throat. -/
def intrinsicCanonicalThroatVolumeMeasure :
    Measure (EffectiveThroat period hPeriod) :=
  (canonicalThroatProductMeasure period).map
    (canonicalThroatFundamentalDomainMap period hPeriod)

theorem intrinsicCanonicalThroatVolumeMeasure_isFinite :
    IsFiniteMeasure (intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
  letI := canonicalThroatProductMeasure_isFinite period
  exact Measure.isFiniteMeasure_map _ _

theorem intrinsicCanonicalThroatVolumeMeasure_ne_zero :
    intrinsicCanonicalThroatVolumeMeasure period hPeriod ≠ 0 := by
  exact (Measure.map_ne_zero_iff
    (canonicalThroatFundamentalDomainMap_continuous
      period hPeriod).measurable.aemeasurable).2
        (canonicalThroatProductMeasure_ne_zero period hPeriod)

/-- Canonical scalar `L2` space on the physical throat volume. -/
abbrev CanonicalPhysicalThroatL2 :=
  let _ : IsFiniteMeasure
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
    intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod
  Lp Real (2 : ENNReal)
    (intrinsicCanonicalThroatVolumeMeasure period hPeriod)

/-- Smooth restriction with its canonical throat measure fixed. -/
def smoothCanonicalPhysicalTraceL2 :
    SmoothQuotientField period hPeriod Real →ₗ[Real]
      CanonicalPhysicalThroatL2 period hPeriod := by
  letI : IsFiniteMeasure
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
    intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod
  exact smoothTraceL2LinearMap period hPeriod Real
    (intrinsicCanonicalThroatVolumeMeasure period hPeriod)

/-- The physical scalar graph-H1 completion, with neither measure nor frame
left as external data. -/
abbrev CanonicalPhysicalScalarH1 :=
  let _ : IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
    intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod
  H1GraphSpace period hPeriod Real
    (finiteSmoothTangentFrame period hPeriod)
    (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)

/-- Smooth scalar fields included into the physical graph completion. -/
def smoothToCanonicalPhysicalScalarH1 :
    SmoothQuotientField period hPeriod Real →ₗ[Real]
      CanonicalPhysicalScalarH1 period hPeriod := by
  letI : IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
    intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod
  exact smoothToH1GraphLinearMap period hPeriod Real
    (finiteSmoothTangentFrame period hPeriod)
    (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)

theorem smoothToCanonicalPhysicalScalarH1_denseRange :
    DenseRange (smoothToCanonicalPhysicalScalarH1 period hPeriod) := by
  letI : IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
    intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod
  exact smoothToH1Graph_denseRange period hPeriod Real
    (finiteSmoothTangentFrame period hPeriod)
    (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)

@[implicit_reducible]
def canonicalPhysicalScalarH1CompleteSpace :
    CompleteSpace (CanonicalPhysicalScalarH1 period hPeriod) := by
  letI : IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
    intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod
  exact h1GraphCompleteSpace period hPeriod Real
    (finiteSmoothTangentFrame period hPeriod)
    (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)

/-- The sole remaining analytic input: the smooth throat restriction is
bounded by the physical first-jet graph norm. -/
abbrev CanonicalPhysicalH1TraceBound :=
  let _ : IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
    intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod
  let _ : IsFiniteMeasure
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
    intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod
  HasH1TraceBound period hPeriod Real
    (finiteSmoothTangentFrame period hPeriod)
    (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
    (intrinsicCanonicalThroatVolumeMeasure period hPeriod)

/-- The physical trace obtained from exactly the preceding smooth bound. -/
def canonicalPhysicalH1Trace
    (traceBound : CanonicalPhysicalH1TraceBound period hPeriod) :
    CanonicalPhysicalScalarH1 period hPeriod →L[Real]
      CanonicalPhysicalThroatL2 period hPeriod := by
  letI : IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
    intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod
  letI : IsFiniteMeasure
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
    intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod
  exact h1Trace period hPeriod Real
    (finiteSmoothTangentFrame period hPeriod)
    (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
    (intrinsicCanonicalThroatVolumeMeasure period hPeriod) traceBound

theorem canonicalPhysicalH1Trace_agrees_on_smooth
    (traceBound : CanonicalPhysicalH1TraceBound period hPeriod)
    (field : SmoothQuotientField period hPeriod Real) :
    canonicalPhysicalH1Trace period hPeriod traceBound
        (smoothToCanonicalPhysicalScalarH1 period hPeriod field) =
      smoothCanonicalPhysicalTraceL2 period hPeriod field := by
  letI : IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
    intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod
  letI : IsFiniteMeasure
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
    intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod
  exact h1Trace_agrees_on_smooth period hPeriod Real
    (finiteSmoothTangentFrame period hPeriod)
    (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
    (intrinsicCanonicalThroatVolumeMeasure period hPeriod) traceBound field

/-- Bound constant exposed without leaking measure-instance parameters into
the theorem statements consuming it. -/
def canonicalPhysicalH1TraceConstant
    (traceBound : CanonicalPhysicalH1TraceBound period hPeriod) : Real := by
  letI : IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
    intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod
  letI : IsFiniteMeasure
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
    intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod
  exact traceBound.constant

theorem canonicalPhysicalH1Trace_norm_le
    (traceBound : CanonicalPhysicalH1TraceBound period hPeriod)
    (field : CanonicalPhysicalScalarH1 period hPeriod) :
    norm (canonicalPhysicalH1Trace period hPeriod traceBound field) ≤
      canonicalPhysicalH1TraceConstant period hPeriod traceBound *
        norm field := by
  letI : IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
    intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod
  letI : IsFiniteMeasure
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
    intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod
  exact h1Trace_norm_le period hPeriod Real
    (finiteSmoothTangentFrame period hPeriod)
    (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
    (intrinsicCanonicalThroatVolumeMeasure period hPeriod) traceBound field

/-- Existence of a continuous physical trace agreeing with smooth
restriction. -/
def CanonicalPhysicalH1TraceExists : Prop :=
  let _ : IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
    intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod
  let _ : IsFiniteMeasure
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
    intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod
  ∃ trace : CanonicalPhysicalScalarH1 period hPeriod →L[Real]
      CanonicalPhysicalThroatL2 period hPeriod,
    ∀ field : SmoothQuotientField period hPeriod Real,
      trace (smoothToCanonicalPhysicalScalarH1 period hPeriod field) =
        smoothCanonicalPhysicalTraceL2 period hPeriod field

/-- Exact frontier theorem: the physical trace exists if and only if the
single smooth trace inequality is proved. -/
theorem canonicalPhysicalH1TraceExists_iff :
    CanonicalPhysicalH1TraceExists period hPeriod ↔
      Nonempty (CanonicalPhysicalH1TraceBound period hPeriod) := by
  letI : IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
    intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod
  letI : IsFiniteMeasure
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
    intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod
  constructor
  · rintro ⟨trace, hTrace⟩
    refine ⟨{ constant := norm trace
              nonnegative := norm_nonneg trace
              bound := ?_ }⟩
    intro field
    have hTraceField := hTrace field
    change trace
        (smoothToH1GraphLinearMap period hPeriod Real
          (finiteSmoothTangentFrame period hPeriod)
          (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) field) =
      smoothTraceL2LinearMap period hPeriod Real
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) field
      at hTraceField
    rw [← hTraceField]
    exact trace.le_opNorm _
  · rintro ⟨traceBound⟩
    exact ⟨canonicalPhysicalH1Trace period hPeriod traceBound,
      canonicalPhysicalH1Trace_agrees_on_smooth
        period hPeriod traceBound⟩

theorem canonical_volume_h1_trace4D_closure :
    IsFiniteMeasure (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) ∧
      intrinsicCanonicalLorentzVolumeMeasure period hPeriod ≠ 0 ∧
      IsFiniteMeasure
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) ∧
      intrinsicCanonicalThroatVolumeMeasure period hPeriod ≠ 0 ∧
      (CanonicalPhysicalH1TraceExists period hPeriod ↔
        Nonempty (CanonicalPhysicalH1TraceBound period hPeriod)) :=
  ⟨intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod,
    intrinsicCanonicalLorentzVolumeMeasure_ne_zero period hPeriod,
    intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod,
    intrinsicCanonicalThroatVolumeMeasure_ne_zero period hPeriod,
    canonicalPhysicalH1TraceExists_iff period hPeriod⟩

end

end P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
end JanusFormal
