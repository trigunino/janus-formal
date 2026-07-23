import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetGlobalization4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarGeometricGreenCore4D

/-!
# Green core from a globalized Cauchy jet

This layer replaces the abstract smooth Cauchy extension field in the geometric
Green-core input by the explicit collar-globalization criterion.  The local jet
profiles prove the exact first-sheet value and normal traces, while wave
naturality and the global divergence integral provide the bulk operator and
Green identity.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetGreenCore4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerAtlasNaturality4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetGlobalization4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarGeometricGreenCore4D
open P0EFTJanusMappingTorusCutBulkCanonicalDivergenceMeasure4D

universe x y

variable (period : Real) (hPeriod : period ≠ 0)
variable {massSquared : Real}

/-- Constructive smooth Green-core data based on an explicit globalized collar
Cauchy jet. -/
structure CanonicalPhysicalScalarCauchyJetGreenCoreData
    (massSquared : Real)
    (ValueCore : Type x) (NormalCore : Type y)
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore] where
  waveGlobalization : CanonicalPhysicalScalarWaveGlobalizationData
    period hPeriod massSquared
  cauchyGlobalization : CanonicalPhysicalScalarCauchyJetGlobalizationData
    period hPeriod ValueCore NormalCore
  integral_eq_divergence :
    ∀ field test : SmoothQuotientField period hPeriod Real,
      (∫ point,
        P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerGreenL2Reduction4D.canonicalPhysicalScalarEulerSkewDensity
          period hPeriod massSquared field test point
        ∂P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D.intrinsicCanonicalLorentzVolumeMeasure
          period hPeriod) =
      -2 * cutBulkCanonicalDivergenceMeasure
        period hPeriod massSquared field test Set.univ

namespace CanonicalPhysicalScalarCauchyJetGreenCoreData

/-- Conversion to the geometric Green-core input. -/
def toGeometricGreenCoreData
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (constructive : CanonicalPhysicalScalarCauchyJetGreenCoreData
      period hPeriod massSquared ValueCore NormalCore) :
    CanonicalPhysicalScalarGeometricGreenCoreData
      period hPeriod massSquared ValueCore NormalCore where
  globalization := constructive.waveGlobalization
  valueEmbedding := constructive.cauchyGlobalization.valueEmbedding
  normalEmbedding := constructive.cauchyGlobalization.normalEmbedding
  valueDense := constructive.cauchyGlobalization.valueDense
  normalDense := constructive.cauchyGlobalization.normalDense
  extension := constructive.cauchyGlobalization.extension
  boundary_extension :=
    constructive.cauchyGlobalization.cauchyTrace_extension period hPeriod
  integral_eq_divergence := constructive.integral_eq_divergence

/-- Constructed physical first-sheet Green core. -/
def greenCore
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (constructive : CanonicalPhysicalScalarCauchyJetGreenCoreData
      period hPeriod massSquared ValueCore NormalCore) :=
  (constructive.toGeometricGreenCoreData period hPeriod)
    |>.greenCore period hPeriod

/-- The explicit jet globalization gives a dense smooth Cauchy trace. -/
theorem boundaryTrace_denseRange
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (constructive : CanonicalPhysicalScalarCauchyJetGreenCoreData
      period hPeriod massSquared ValueCore NormalCore) :
    DenseRange
      (P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D.smoothCanonicalPhysicalScalarFirstSheetCauchyTrace
        period hPeriod) :=
  constructive.cauchyGlobalization.boundaryTrace_denseRange period hPeriod

/-- Exact globalized Cauchy jet of every core pair. -/
theorem boundary_extension
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (constructive : CanonicalPhysicalScalarCauchyJetGreenCoreData
      period hPeriod massSquared ValueCore NormalCore)
    (data : ValueCore × NormalCore) :
    constructive.greenCore.core.boundaryTrace
        (constructive.cauchyGlobalization.extension data) =
      P0EFTJanusMappingTorusScalarBoundarySmoothExtensionDensity4D.canonicalScalarBoundaryCorePairEmbedding
        constructive.cauchyGlobalization.valueEmbedding
        constructive.cauchyGlobalization.normalEmbedding data :=
  constructive.cauchyGlobalization.cauchyTrace_extension
    period hPeriod data

/-- Constructive Green-core certificate. -/
theorem certificate
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (constructive : CanonicalPhysicalScalarCauchyJetGreenCoreData
      period hPeriod massSquared ValueCore NormalCore) :
    DenseRange
        (P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D.smoothCanonicalPhysicalScalarFirstSheetCauchyTrace
          period hPeriod) ∧
      (∀ field test : SmoothQuotientField period hPeriod Real,
        inner Real (constructive.greenCore.core.operator field)
              (constructive.greenCore.core.inclusion test) -
            inner Real (constructive.greenCore.core.inclusion field)
              (constructive.greenCore.core.operator test) =
          2 * P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D.canonicalScalarHilbertBoundarySymplecticForm
            (constructive.greenCore.core.boundaryTrace field)
            (constructive.greenCore.core.boundaryTrace test)) :=
  ⟨constructive.boundaryTrace_denseRange period hPeriod,
    ((constructive.toGeometricGreenCoreData period hPeriod)
      |>.greenCore period hPeriod).core.green_identity⟩

end CanonicalPhysicalScalarCauchyJetGreenCoreData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetGreenCore4D
end JanusFormal
