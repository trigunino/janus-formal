import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D

/-!
# Canonical physical bulk L2 and the graph-H1 inclusion

The canonical Lorentz volume already defines the physical first-jet graph H1
completion.  This file exposes the corresponding scalar bulk L2 Hilbert space
and the continuous map that forgets the derivative coordinates.

The construction agrees exactly with the smooth-to-L2 inclusion on the dense
smooth core.  Injectivity of the completed map is deliberately not asserted:
it is precisely the closability/single-valuedness issue isolated by the later
closed-graph realization.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D

set_option autoImplicit false
noncomputable section

open scoped ENNReal Manifold ContDiff
open MeasureTheory Set
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusL2PTFunctionalSpace4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

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

local instance canonicalLorentzVolumeFinite :
    IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

/-- Canonical scalar bulk L2 space for the physical Lorentz volume measure. -/
abbrev CanonicalPhysicalBulkL2 :=
  Lp Real (2 : ENNReal)
    (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)

/-- Smooth scalar fields included in physical bulk L2. -/
def smoothToCanonicalPhysicalBulkL2 :
    SmoothQuotientField period hPeriod Real →ₗ[Real]
      CanonicalPhysicalBulkL2 period hPeriod where
  toFun := smoothFieldToL2 period hPeriod Real
    (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
  map_add' first second := by
    apply Lp.ext
    filter_upwards
      [smoothFieldToL2_ae period hPeriod Real
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) (first + second),
       smoothFieldToL2_ae period hPeriod Real
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) first,
       smoothFieldToL2_ae period hPeriod Real
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) second,
       Lp.coeFn_add
        (smoothFieldToL2 period hPeriod Real
          (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) first)
        (smoothFieldToL2 period hPeriod Real
          (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) second)]
      with point hSum hFirst hSecond hAdd
    calc
      _ = (first + second).toFun point := hSum
      _ =
          first.toFun point + second.toFun point := rfl
      _ = _ := by
        simpa only [Pi.add_apply, hFirst, hSecond] using hAdd.symm
  map_smul' scalar field := by
    apply Lp.ext
    filter_upwards
      [smoothFieldToL2_ae period hPeriod Real
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) (scalar • field),
       smoothFieldToL2_ae period hPeriod Real
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) field,
       Lp.coeFn_smul scalar
        (smoothFieldToL2 period hPeriod Real
          (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) field)]
      with point hScaled hField hSmul
    calc
      _ = (scalar • field).toFun point := hScaled
      _ = scalar • field.toFun point := rfl
      _ = _ := by
        simpa only [Pi.smul_apply, hField, RingHom.id_apply] using hSmul.symm

/-- Forgetting the derivative part of the physical graph H1 completion. -/
def canonicalPhysicalScalarH1ToBulkL2 :
    CanonicalPhysicalScalarH1 period hPeriod →L[Real]
      CanonicalPhysicalBulkL2 period hPeriod :=
  h1GraphToL2 period hPeriod Real
    (finiteSmoothTangentFrame period hPeriod)
    (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)

/-- Exact agreement of the completed H1-to-L2 map on smooth fields. -/
theorem canonicalPhysicalScalarH1ToBulkL2_agrees_on_smooth
    (field : SmoothQuotientField period hPeriod Real) :
    canonicalPhysicalScalarH1ToBulkL2 period hPeriod
        (smoothToCanonicalPhysicalScalarH1 period hPeriod field) =
      smoothToCanonicalPhysicalBulkL2 period hPeriod field := by
  exact h1GraphToL2_agrees_on_smooth period hPeriod Real
    (finiteSmoothTangentFrame period hPeriod)
    (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) field

/-- Operator-norm control for the continuous H1-to-L2 forgetting map. -/
theorem canonicalPhysicalScalarH1ToBulkL2_norm_le
    (field : CanonicalPhysicalScalarH1 period hPeriod) :
    ‖canonicalPhysicalScalarH1ToBulkL2 period hPeriod field‖ ≤
      ‖canonicalPhysicalScalarH1ToBulkL2 period hPeriod‖ * ‖field‖ :=
  (canonicalPhysicalScalarH1ToBulkL2 period hPeriod).le_opNorm field

/-- The smooth core is dense in the physical graph H1 space and its L2 image is
exactly the canonical smooth bulk L2 image. -/
theorem canonicalPhysicalBulkL2H1Bridge_certificate :
    DenseRange (smoothToCanonicalPhysicalScalarH1 period hPeriod) ∧
      (∀ field : SmoothQuotientField period hPeriod Real,
        canonicalPhysicalScalarH1ToBulkL2 period hPeriod
            (smoothToCanonicalPhysicalScalarH1 period hPeriod field) =
          smoothToCanonicalPhysicalBulkL2 period hPeriod field) :=
  ⟨smoothToCanonicalPhysicalScalarH1_denseRange period hPeriod,
    canonicalPhysicalScalarH1ToBulkL2_agrees_on_smooth period hPeriod⟩

end
end P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
end JanusFormal
