import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLorentzInteriorDenseRange4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerFullSupportReduction4D

/-!
# Canonical full support for the physical scalar Euler operator

The open fundamental strip has open-positive source measure, preserves the
canonical Lorentz volume and has dense physical image.  Hence the physical
Lorentz volume itself is positive on every nonempty open set.

This closes the last measure-theoretic input in the compatibility-only Euler
construction.  Overlap compatibility now directly produces the faithful bulk
`L²` operator; no parametrization datum and no fieldwise a.e.-faithfulness datum
remain in the preferred interface.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerCanonicalFullSupport4D

set_option autoImplicit false
noncomputable section

open Set Topology MeasureTheory
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalLorentzInteriorDenseRange4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerAtlas4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerFullSupportReduction4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- The canonical physical Lorentz volume has full topological support. -/
theorem intrinsicCanonicalLorentzVolumeMeasure_isOpenPosMeasure :
    (intrinsicCanonicalLorentzVolumeMeasure period hPeriod).IsOpenPosMeasure :=
  (canonicalLorentzInteriorDenseRange_certificate period hPeriod).2

namespace CanonicalPhysicalScalarEulerCompatibilityOnlyData

/-- Canonical faithful compatibility package, with full support discharged. -/
def toCanonicalCompatibilityData
    (data : CanonicalPhysicalScalarEulerCompatibilityOnlyData
      period hPeriod massSquared) :
    P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerCompatibilityClosure4D.CanonicalPhysicalScalarEulerCompatibilityData
      period hPeriod massSquared :=
  data.toCompatibilityData
    (intrinsicCanonicalLorentzVolumeMeasure_isOpenPosMeasure period hPeriod)

/-- Canonical physical bulk `L²` Euler operator. -/
def toCanonicalBulkL2LinearMap
    (data : CanonicalPhysicalScalarEulerCompatibilityOnlyData
      period hPeriod massSquared) :=
  data.toCanonicalCompatibilityData.toBulkL2LinearMap

/-- Almost-everywhere vanishing of the continuous physical residual is faithful. -/
theorem residual_eq_zero_of_ae_eq_zero_canonical
    (data : CanonicalPhysicalScalarEulerCompatibilityOnlyData
      period hPeriod massSquared)
    (field : SmoothScalarField period hPeriod)
    (hZero :
      canonicalPhysicalScalarEulerGlobalResidual
          period hPeriod massSquared field =ᵐ[
            intrinsicCanonicalLorentzVolumeMeasure period hPeriod] 0) :
    canonicalPhysicalScalarEulerGlobalResidual
      period hPeriod massSquared field = 0 :=
  data.residual_eq_zero_of_ae_eq_zero
    (intrinsicCanonicalLorentzVolumeMeasure_isOpenPosMeasure period hPeriod)
    field hZero

/-- Canonical Euler full-support certificate. -/
theorem canonicalFullSupport_certificate
    (data : CanonicalPhysicalScalarEulerCompatibilityOnlyData
      period hPeriod massSquared) :
    (intrinsicCanonicalLorentzVolumeMeasure
        period hPeriod).IsOpenPosMeasure ∧
      (∀ field : SmoothScalarField period hPeriod,
        canonicalPhysicalScalarEulerGlobalResidual
            period hPeriod massSquared field =ᵐ[
              intrinsicCanonicalLorentzVolumeMeasure period hPeriod] 0 →
          canonicalPhysicalScalarEulerGlobalResidual
            period hPeriod massSquared field = 0) :=
  ⟨intrinsicCanonicalLorentzVolumeMeasure_isOpenPosMeasure period hPeriod,
    data.residual_eq_zero_of_ae_eq_zero_canonical period hPeriod⟩

end CanonicalPhysicalScalarEulerCompatibilityOnlyData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerCanonicalFullSupport4D
end JanusFormal
