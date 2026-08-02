import Mathlib.Geometry.Manifold.Metrizable
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicH1CoerciveVariationalClosure4D

/-!
# Canonical physical strong `C⁰ ∩ H¹` scalar space

The canonical continuous and graph-`H¹` realizations already map continuously
to the same physical bulk `L²`. Their equalizer is a closed subspace of the
product and therefore a Banach space. It controls pointwise admissibility via
its `C⁰` projection while retaining the intrinsic first-jet energy through its
`H¹` projection.

No Sobolev embedding or new analytic axiom is used. The two components are
required to represent the same `L²` field, and every smooth quotient scalar
has its canonical compatible lift.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0Space4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff ENNReal
open MeasureTheory Set Topology Filter TopologicalSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusL2PTFunctionalSpace4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1HilbertRenorming4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarSmoothL2Density4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicH1CoerciveVariationalClosure4D

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

local instance effectiveQuotientMetrizableSpace :
    MetrizableSpace (EffectiveQuotient period hPeriod) :=
  Manifold.metrizableSpace coverModelWithCorners _

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance canonicalLorentzVolumeFinite :
    IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

private abbrev ContinuousScalar :=
  C(EffectiveQuotient period hPeriod, Real)

private abbrev PhysicalHilbertH1 :=
  CanonicalPhysicalScalarHilbertH1 period hPeriod

private abbrev BulkL2 :=
  CanonicalPhysicalBulkL2 period hPeriod

local instance physicalHilbertH1CompleteSpace :
    CompleteSpace (PhysicalHilbertH1 period hPeriod) :=
  canonicalPhysicalScalarHilbertH1CompleteSpace period hPeriod

/-- Difference of the existing continuous and `H¹` realizations in the common
physical bulk `L²`. -/
def canonicalPhysicalStrongH1C0Compatibility :
    (ContinuousScalar period hPeriod × PhysicalHilbertH1 period hPeriod) →L[Real]
      BulkL2 period hPeriod :=
  (continuousToCanonicalPhysicalBulkL2 period hPeriod).comp
      (ContinuousLinearMap.fst Real
        (ContinuousScalar period hPeriod)
        (PhysicalHilbertH1 period hPeriod)) -
    (canonicalPhysicalScalarHilbertH1ToBulkL2 period hPeriod).comp
      (ContinuousLinearMap.snd Real
        (ContinuousScalar period hPeriod)
        (PhysicalHilbertH1 period hPeriod))

/-- Closed compatible product `C⁰ ∩ H¹`: both entries represent the same
physical `L²` scalar. -/
abbrev CanonicalPhysicalScalarStrongH1C0 :=
  (canonicalPhysicalStrongH1C0Compatibility period hPeriod).ker

theorem canonicalPhysicalScalarStrongH1C0_isClosed :
    IsClosed
      (CanonicalPhysicalScalarStrongH1C0 period hPeriod :
        Set (ContinuousScalar period hPeriod ×
          PhysicalHilbertH1 period hPeriod)) :=
  (canonicalPhysicalStrongH1C0Compatibility period hPeriod).isClosed_ker

@[implicit_reducible]
def canonicalPhysicalScalarStrongH1C0CompleteSpace :
    CompleteSpace (CanonicalPhysicalScalarStrongH1C0 period hPeriod) :=
  inferInstance

/-- Continuous pointwise representative of a strong field. -/
def canonicalPhysicalScalarStrongH1C0ToContinuous :
    CanonicalPhysicalScalarStrongH1C0 period hPeriod →L[Real]
      ContinuousScalar period hPeriod :=
  (ContinuousLinearMap.fst Real
    (ContinuousScalar period hPeriod)
    (PhysicalHilbertH1 period hPeriod)).comp
      (canonicalPhysicalStrongH1C0Compatibility period hPeriod).ker.subtypeL

/-- Intrinsic graph-`H¹` representative of a strong field. -/
def canonicalPhysicalScalarStrongH1C0ToHilbertH1 :
    CanonicalPhysicalScalarStrongH1C0 period hPeriod →L[Real]
      PhysicalHilbertH1 period hPeriod :=
  (ContinuousLinearMap.snd Real
    (ContinuousScalar period hPeriod)
    (PhysicalHilbertH1 period hPeriod)).comp
      (canonicalPhysicalStrongH1C0Compatibility period hPeriod).ker.subtypeL

theorem canonicalPhysicalScalarStrongH1C0_l2_compatibility
    (field : CanonicalPhysicalScalarStrongH1C0 period hPeriod) :
    continuousToCanonicalPhysicalBulkL2 period hPeriod
        (canonicalPhysicalScalarStrongH1C0ToContinuous
          period hPeriod field) =
      canonicalPhysicalScalarHilbertH1ToBulkL2 period hPeriod
        (canonicalPhysicalScalarStrongH1C0ToHilbertH1
          period hPeriod field) := by
  have hKernel := field.2
  change continuousToCanonicalPhysicalBulkL2 period hPeriod field.1.1 -
      canonicalPhysicalScalarHilbertH1ToBulkL2 period hPeriod field.1.2 = 0
    at hKernel
  exact sub_eq_zero.mp hKernel

/-- Regard a smooth quotient scalar as a continuous scalar. -/
def smoothToCanonicalPhysicalContinuousScalar :
    SmoothQuotientField period hPeriod Real →ₗ[Real]
      ContinuousScalar period hPeriod where
  toFun field :=
    ⟨field, field.contMDiff_toFun.continuous⟩
  map_add' first second := by
    apply ContinuousMap.ext
    intro point
    rfl
  map_smul' scalar field := by
    apply ContinuousMap.ext
    intro point
    rfl

/-- The continuous and smooth inclusions of one smooth scalar agree in the
common physical `L²`. -/
theorem continuousToCanonicalPhysicalBulkL2_agrees_on_smooth
    (field : SmoothQuotientField period hPeriod Real) :
    continuousToCanonicalPhysicalBulkL2 period hPeriod
        (smoothToCanonicalPhysicalContinuousScalar
          period hPeriod field) =
      smoothToCanonicalPhysicalBulkL2 period hPeriod field := by
  change
    (ContinuousMap.toLp (2 : ENNReal)
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) Real)
        (smoothToCanonicalPhysicalContinuousScalar
          period hPeriod field) =
      smoothFieldToL2 period hPeriod Real
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) field
  rw [Lp.ext_iff]
  filter_upwards
    [ContinuousMap.coeFn_toLp
      (p := (2 : ENNReal))
      (μ := intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
      (𝕜 := Real)
      (smoothToCanonicalPhysicalContinuousScalar period hPeriod field),
     smoothFieldToL2_ae period hPeriod Real
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) field]
    with point hContinuous hSmooth
  calc
    _ = smoothToCanonicalPhysicalContinuousScalar
          period hPeriod field point := hContinuous
    _ = field point := rfl
    _ = _ := hSmooth.symm

/-- Canonical compatible strong lift of every smooth scalar. -/
def smoothToCanonicalPhysicalScalarStrongH1C0 :
    SmoothQuotientField period hPeriod Real →ₗ[Real]
      CanonicalPhysicalScalarStrongH1C0 period hPeriod where
  toFun field :=
    ⟨(smoothToCanonicalPhysicalContinuousScalar period hPeriod field,
      smoothToCanonicalPhysicalScalarHilbertH1 period hPeriod field), by
      change continuousToCanonicalPhysicalBulkL2 period hPeriod
          (smoothToCanonicalPhysicalContinuousScalar
            period hPeriod field) -
        canonicalPhysicalScalarHilbertH1ToBulkL2 period hPeriod
          (smoothToCanonicalPhysicalScalarHilbertH1
            period hPeriod field) = 0
      rw [continuousToCanonicalPhysicalBulkL2_agrees_on_smooth,
        canonicalPhysicalScalarHilbertH1ToBulkL2_agrees_on_smooth]
      exact sub_self _⟩
  map_add' first second := by
    apply Subtype.ext
    apply Prod.ext
    · exact (smoothToCanonicalPhysicalContinuousScalar
        period hPeriod).map_add first second
    · exact (smoothToCanonicalPhysicalScalarHilbertH1
        period hPeriod).map_add first second
  map_smul' scalar field := by
    apply Subtype.ext
    apply Prod.ext
    · exact (smoothToCanonicalPhysicalContinuousScalar
        period hPeriod).map_smul scalar field
    · exact (smoothToCanonicalPhysicalScalarHilbertH1
        period hPeriod).map_smul scalar field

@[simp]
theorem strongH1C0ToContinuous_smooth
    (field : SmoothQuotientField period hPeriod Real) :
    canonicalPhysicalScalarStrongH1C0ToContinuous period hPeriod
        (smoothToCanonicalPhysicalScalarStrongH1C0
          period hPeriod field) =
      smoothToCanonicalPhysicalContinuousScalar period hPeriod field :=
  rfl

@[simp]
theorem strongH1C0ToHilbertH1_smooth
    (field : SmoothQuotientField period hPeriod Real) :
    canonicalPhysicalScalarStrongH1C0ToHilbertH1 period hPeriod
        (smoothToCanonicalPhysicalScalarStrongH1C0
          period hPeriod field) =
      smoothToCanonicalPhysicalScalarHilbertH1 period hPeriod field :=
  rfl

theorem canonicalPhysicalScalarStrongH1C0_ext
    {first second : CanonicalPhysicalScalarStrongH1C0 period hPeriod}
    (hContinuous :
      canonicalPhysicalScalarStrongH1C0ToContinuous period hPeriod first =
        canonicalPhysicalScalarStrongH1C0ToContinuous period hPeriod second)
    (hH1 : canonicalPhysicalScalarStrongH1C0ToHilbertH1
        period hPeriod first =
      canonicalPhysicalScalarStrongH1C0ToHilbertH1
        period hPeriod second) :
    first = second := by
  apply Subtype.ext
  exact Prod.ext hContinuous hH1

/-- Summary gate: the strong space is closed and complete, both projections
are continuous, compatible in `L²`, and contain the exact smooth core. -/
theorem canonical_physical_scalar_strong_h1_c0_gate :
    IsClosed
        (CanonicalPhysicalScalarStrongH1C0 period hPeriod :
          Set (ContinuousScalar period hPeriod ×
            PhysicalHilbertH1 period hPeriod)) ∧
      Nonempty (CanonicalPhysicalScalarStrongH1C0 period hPeriod) ∧
      (∀ field : SmoothQuotientField period hPeriod Real,
        canonicalPhysicalScalarStrongH1C0ToContinuous period hPeriod
            (smoothToCanonicalPhysicalScalarStrongH1C0
              period hPeriod field) =
          smoothToCanonicalPhysicalContinuousScalar period hPeriod field ∧
        canonicalPhysicalScalarStrongH1C0ToHilbertH1 period hPeriod
            (smoothToCanonicalPhysicalScalarStrongH1C0
              period hPeriod field) =
          smoothToCanonicalPhysicalScalarHilbertH1 period hPeriod field) := by
  exact ⟨canonicalPhysicalScalarStrongH1C0_isClosed period hPeriod,
    ⟨0⟩,
    fun field => ⟨strongH1C0ToContinuous_smooth period hPeriod field,
      strongH1C0ToHilbertH1_smooth period hPeriod field⟩⟩

end

end P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0Space4D
end JanusFormal
