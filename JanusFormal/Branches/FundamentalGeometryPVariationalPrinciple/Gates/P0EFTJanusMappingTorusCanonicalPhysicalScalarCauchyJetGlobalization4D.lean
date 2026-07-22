import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetProfiles4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetBoundaryExtension4D

/-!
# Globalization criterion for the physical scalar Cauchy jet

The one-dimensional profiles already realize exact value and normal jets.  The
remaining geometric step is to globalize the corresponding collar expression to
a smooth deck-invariant quotient field.

This file packages that globalization step.  Once the global field agrees with
the explicit local collar formula, the first-sheet value and normal `L²` traces
are proved to be the prescribed dense boundary-core embeddings.  Thus a collar
globalization immediately produces the smooth Cauchy-extension data used by the
physical Green core.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetGlobalization4D

set_option autoImplicit false
noncomputable section

open scoped ENNReal Manifold ContDiff
open MeasureTheory Set Topology Filter
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetProfiles4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetBoundaryExtension4D
open P0EFTJanusMappingTorusScalarBoundarySmoothExtensionDensity4D

universe x y

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev BoundaryL2 := CanonicalPhysicalScalarFirstSheetL2 period

/-- Dense boundary representatives together with a smooth global collar
extension reproducing the exact local Cauchy-jet formula. -/
structure CanonicalPhysicalScalarCauchyJetGlobalizationData
    (ValueCore : Type x) (NormalCore : Type y)
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore] where
  valueRepresentative : ValueCore →ₗ[Real]
    (CanonicalLatitudeBase → Real)
  normalRepresentative : NormalCore →ₗ[Real]
    (CanonicalLatitudeBase → Real)
  valueEmbedding : ValueCore →ₗ[Real] BoundaryL2 period
  normalEmbedding : NormalCore →ₗ[Real] BoundaryL2 period
  valueDense : DenseRange valueEmbedding
  normalDense : DenseRange normalEmbedding
  valueEmbedding_ae : ∀ value : ValueCore,
    (valueEmbedding value : CanonicalLatitudeBase → Real) =ᵐ[
      canonicalLatitudeBaseMeasure period]
      valueRepresentative value
  normalEmbedding_ae : ∀ normal : NormalCore,
    (normalEmbedding normal : CanonicalLatitudeBase → Real) =ᵐ[
      canonicalLatitudeBaseMeasure period]
      normalRepresentative normal
  extension : ValueCore × NormalCore →ₗ[Real]
    SmoothQuotientField period hPeriod Real
  extension_slice : ∀ (data : ValueCore × NormalCore)
    (base : CanonicalLatitudeBase) (normal : Real),
    canonicalLatitudeValue period hPeriod (extension data) base normal =
      canonicalLatitudeLocalCauchyExtension
        (valueRepresentative data.1, normalRepresentative data.2)
        (base, normal)

namespace CanonicalPhysicalScalarCauchyJetGlobalizationData

/-- The globalization has the prescribed first-sheet value trace. -/
theorem valueTrace_extension
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (globalization : CanonicalPhysicalScalarCauchyJetGlobalizationData
      period hPeriod ValueCore NormalCore)
    (data : ValueCore × NormalCore) :
    smoothCanonicalPhysicalScalarFirstSheetValueL2 period hPeriod
        (globalization.extension data) =
      globalization.valueEmbedding data.1 := by
  apply Lp.ext
  filter_upwards
    [smoothCanonicalPhysicalScalarFirstSheetValueL2_ae period hPeriod
      (globalization.extension data),
     globalization.valueEmbedding_ae data.1]
    with base hTrace hEmbedding
  rw [hTrace, hEmbedding]
  change canonicalLatitudeValue period hPeriod
      (globalization.extension data) base 0 =
    globalization.valueRepresentative data.1 base
  rw [globalization.extension_slice]
  exact canonicalLatitudeLocalCauchyExtensionSlice_zero
    (globalization.valueRepresentative data.1,
      globalization.normalRepresentative data.2) base

/-- The globalization has the prescribed first-sheet normal trace. -/
theorem normalTrace_extension
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (globalization : CanonicalPhysicalScalarCauchyJetGlobalizationData
      period hPeriod ValueCore NormalCore)
    (data : ValueCore × NormalCore) :
    smoothCanonicalPhysicalScalarFirstSheetNormalL2 period hPeriod
        (globalization.extension data) =
      globalization.normalEmbedding data.2 := by
  apply Lp.ext
  filter_upwards
    [smoothCanonicalPhysicalScalarFirstSheetNormalL2_ae period hPeriod
      (globalization.extension data),
     globalization.normalEmbedding_ae data.2]
    with base hTrace hEmbedding
  rw [hTrace, hEmbedding]
  change canonicalLatitudeDerivative period hPeriod
      (globalization.extension data) base 0 =
    globalization.normalRepresentative data.2 base
  unfold canonicalLatitudeDerivative
  have hSlice :
      canonicalLatitudeValue period hPeriod
          (globalization.extension data) base =
        canonicalLatitudeLocalCauchyExtensionSlice
          (globalization.valueRepresentative data.1,
            globalization.normalRepresentative data.2) base := by
    funext normal
    exact globalization.extension_slice data base normal
  rw [hSlice]
  exact deriv_canonicalLatitudeLocalCauchyExtensionSlice_zero
    (globalization.valueRepresentative data.1,
      globalization.normalRepresentative data.2) base

/-- Exact paired Cauchy trace of the globalized collar extension. -/
theorem cauchyTrace_extension
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (globalization : CanonicalPhysicalScalarCauchyJetGlobalizationData
      period hPeriod ValueCore NormalCore)
    (data : ValueCore × NormalCore) :
    smoothCanonicalPhysicalScalarFirstSheetCauchyTrace period hPeriod
        (globalization.extension data) =
      canonicalScalarBoundaryCorePairEmbedding
        globalization.valueEmbedding globalization.normalEmbedding data := by
  ext
  · exact globalization.valueTrace_extension data
  · exact globalization.normalTrace_extension data

/-- The explicit collar globalization proves density of the smooth physical
Cauchy trace. -/
theorem boundaryTrace_denseRange
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (globalization : CanonicalPhysicalScalarCauchyJetGlobalizationData
      period hPeriod ValueCore NormalCore) :
    DenseRange
      (smoothCanonicalPhysicalScalarFirstSheetCauchyTrace period hPeriod) := by
  let extensionData : CanonicalScalarSmoothCauchyExtensionData
      (ValueCore := ValueCore) (NormalCore := NormalCore)
      (smoothCanonicalPhysicalScalarFirstSheetCauchyTrace period hPeriod) :=
    { valueEmbedding := globalization.valueEmbedding
      normalEmbedding := globalization.normalEmbedding
      valueDense := globalization.valueDense
      normalDense := globalization.normalDense
      extension := globalization.extension
      boundary_extension := globalization.cauchyTrace_extension }
  exact extensionData.boundaryTrace_denseRange

/-- Convert the globalization theorem into the smooth physical Cauchy-extension
package once the Euler operator and bulk Green identity are supplied. -/
def toSmoothCauchyExtensionData
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (globalization : CanonicalPhysicalScalarCauchyJetGlobalizationData
      period hPeriod ValueCore NormalCore)
    (operatorData :
      P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerAtlas4D.CanonicalPhysicalScalarEulerGlobalOperatorData
        period hPeriod massSquared)
    (bulkGreenStokes : ∀ first second :
      SmoothQuotientField period hPeriod Real,
      inner Real (operatorData.toBulkL2LinearMap first)
            (P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D.smoothToCanonicalPhysicalBulkL2
              period hPeriod second) -
          inner Real
            (P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D.smoothToCanonicalPhysicalBulkL2
              period hPeriod first)
            (operatorData.toBulkL2LinearMap second) =
        P0EFTJanusMappingTorusCutBulkGlobalOrientedBoundaryCurrent4D.cutBulkGlobalOrientedScalarCurrentIntegral
          period hPeriod first second) :
    CanonicalPhysicalScalarSmoothCauchyExtensionData
      period hPeriod massSquared ValueCore NormalCore where
  operatorData := operatorData
  valueEmbedding := globalization.valueEmbedding
  normalEmbedding := globalization.normalEmbedding
  valueDense := globalization.valueDense
  normalDense := globalization.normalDense
  extension := globalization.extension
  boundary_extension := globalization.cauchyTrace_extension
  bulk_green_stokes := bulkGreenStokes

/-- Globalization certificate. -/
theorem certificate
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (globalization : CanonicalPhysicalScalarCauchyJetGlobalizationData
      period hPeriod ValueCore NormalCore) :
    DenseRange
        (smoothCanonicalPhysicalScalarFirstSheetCauchyTrace period hPeriod) ∧
      (∀ data,
        smoothCanonicalPhysicalScalarFirstSheetCauchyTrace period hPeriod
            (globalization.extension data) =
          canonicalScalarBoundaryCorePairEmbedding
            globalization.valueEmbedding globalization.normalEmbedding data) :=
  ⟨globalization.boundaryTrace_denseRange,
    globalization.cauchyTrace_extension⟩

end CanonicalPhysicalScalarCauchyJetGlobalizationData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetGlobalization4D
end JanusFormal
