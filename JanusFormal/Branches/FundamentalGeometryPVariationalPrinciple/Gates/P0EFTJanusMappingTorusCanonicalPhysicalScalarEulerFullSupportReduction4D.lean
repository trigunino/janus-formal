import Mathlib.MeasureTheory.Measure.OpenPos
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerCompatibilityClosure4D

/-!
# Euler `L²` faithfulness from full support of the physical measure

The compatibility globalization package still carried a field saying that a
continuous Euler residual which is zero almost everywhere is zero everywhere.
This is not a field-specific PDE theorem.  It is a general consequence of full
support of the physical volume measure.

For an `IsOpenPosMeasure`, two continuous functions which agree almost
everywhere agree everywhere.  Therefore Euler overlap compatibility plus open
positivity of the canonical Lorentz volume constructs the complete physical
bulk operator.

This file isolates the sole remaining measure statement:

`(intrinsicCanonicalLorentzVolumeMeasure period hPeriod).IsOpenPosMeasure`.

Once that global theorem is supplied, no per-field `ae_zero_eq_zero` input is
needed anywhere in the scalar Euler construction.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerFullSupportReduction4D

set_option autoImplicit false
noncomputable section

open Set Topology MeasureTheory
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerAtlas4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerLinearity4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerCompatibilityClosure4D

variable (period : Real) (hPeriod : period ≠ 0)
variable {massSquared : Real}

/-- Compatibility-only physical Euler data. -/
structure CanonicalPhysicalScalarEulerCompatibilityOnlyData
    (massSquared : Real) where
  compatible : ∀ field : SmoothScalarField period hPeriod,
    CanonicalPhysicalScalarEulerAtlasCompatible
      period hPeriod massSquared field

namespace CanonicalPhysicalScalarEulerCompatibilityOnlyData

/-- Continuity of every global residual follows from overlap compatibility. -/
theorem residual_continuous
    (data : CanonicalPhysicalScalarEulerCompatibilityOnlyData
      period hPeriod massSquared)
    (field : SmoothScalarField period hPeriod) :
    Continuous
      (canonicalPhysicalScalarEulerGlobalResidual
        period hPeriod massSquared field) :=
  canonicalPhysicalScalarEulerGlobalResidual_continuous_of_compatible
    period hPeriod massSquared field (data.compatible field)

/-- On a full-support physical measure, an almost-everywhere zero residual is
identically zero. -/
theorem residual_eq_zero_of_ae_eq_zero
    (data : CanonicalPhysicalScalarEulerCompatibilityOnlyData
      period hPeriod massSquared)
    (openPositive :
      (intrinsicCanonicalLorentzVolumeMeasure
        period hPeriod).IsOpenPosMeasure)
    (field : SmoothScalarField period hPeriod)
    (hZero :
      canonicalPhysicalScalarEulerGlobalResidual
          period hPeriod massSquared field =ᵐ[
            intrinsicCanonicalLorentzVolumeMeasure period hPeriod] 0) :
    canonicalPhysicalScalarEulerGlobalResidual
      period hPeriod massSquared field = 0 := by
  letI : (intrinsicCanonicalLorentzVolumeMeasure
    period hPeriod).IsOpenPosMeasure := openPositive
  exact Measure.eq_of_ae_eq hZero
    (data.residual_continuous period hPeriod field) continuous_const

/-- Full compatibility data generated from one global full-support theorem. -/
def toCompatibilityData
    (data : CanonicalPhysicalScalarEulerCompatibilityOnlyData
      period hPeriod massSquared)
    (openPositive :
      (intrinsicCanonicalLorentzVolumeMeasure
        period hPeriod).IsOpenPosMeasure) :
    CanonicalPhysicalScalarEulerCompatibilityData
      period hPeriod massSquared where
  compatible := data.compatible
  ae_zero_eq_zero :=
    data.residual_eq_zero_of_ae_eq_zero period hPeriod openPositive

/-- Genuine bulk `L²` Euler operator from compatibility and full support. -/
def toBulkL2LinearMap
    (data : CanonicalPhysicalScalarEulerCompatibilityOnlyData
      period hPeriod massSquared)
    (openPositive :
      (intrinsicCanonicalLorentzVolumeMeasure
        period hPeriod).IsOpenPosMeasure) :=
  (data.toCompatibilityData period hPeriod openPositive).toBulkL2LinearMap

/-- Compatibility/full-support reduction certificate. -/
theorem certificate
    (data : CanonicalPhysicalScalarEulerCompatibilityOnlyData
      period hPeriod massSquared)
    (openPositive :
      (intrinsicCanonicalLorentzVolumeMeasure
        period hPeriod).IsOpenPosMeasure) :
    (∀ field : SmoothScalarField period hPeriod,
      Continuous
        (canonicalPhysicalScalarEulerGlobalResidual
          period hPeriod massSquared field)) ∧
      (∀ field : SmoothScalarField period hPeriod,
        canonicalPhysicalScalarEulerGlobalResidual
            period hPeriod massSquared field =ᵐ[
              intrinsicCanonicalLorentzVolumeMeasure period hPeriod] 0 →
          canonicalPhysicalScalarEulerGlobalResidual
            period hPeriod massSquared field = 0) :=
  ⟨data.residual_continuous period hPeriod,
    data.residual_eq_zero_of_ae_eq_zero period hPeriod openPositive⟩

end CanonicalPhysicalScalarEulerCompatibilityOnlyData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerFullSupportReduction4D
end JanusFormal
