import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusMeasureOpenPositiveDenseMap4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerFullSupportReduction4D

/-!
# Physical Euler faithfulness from a dense measure parametrization

The only measure input needed by the compatibility-only Euler construction is
full support of the physical Lorentz volume.  This file supplies a constructive
route to that fact.

Any continuous dense-range measure-preserving parametrization by an
open-positive source measure makes the physical target measure open-positive.
Combining this general transport theorem with Euler overlap compatibility
constructs the faithful bulk `L²` operator without a separate
`ae_zero_eq_zero` hypothesis.

The latitude coarea parametrization is the intended future instance: one may
restrict it to an open fundamental time strip and the nonpolar latitude band.
Its range is dense even though the two polar orbits are omitted.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerDenseParametrizationClosure4D

set_option autoImplicit false
noncomputable section

open Set Topology MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusMeasureOpenPositiveDenseMap4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerFullSupportReduction4D

universe u

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

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

/-- A dense open-positive parametrization of the physical Lorentz volume. -/
structure CanonicalPhysicalScalarEulerDenseParametrizationData
    (Source : Type u)
    [TopologicalSpace Source] [MeasurableSpace Source]
    (sourceMeasure : Measure Source) where
  sourceOpenPositive : sourceMeasure.IsOpenPosMeasure
  parameterization : Source → EffectiveQuotient period hPeriod
  continuous : Continuous parameterization
  denseRange : DenseRange parameterization
  measurePreserving : MeasurePreserving parameterization sourceMeasure
    (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)

namespace CanonicalPhysicalScalarEulerDenseParametrizationData

/-- The physical Lorentz volume has full support. -/
def physicalMeasureOpenPositive
    {Source : Type u}
    [TopologicalSpace Source] [MeasurableSpace Source]
    {sourceMeasure : Measure Source}
    (parameterization : CanonicalPhysicalScalarEulerDenseParametrizationData
      period hPeriod Source sourceMeasure) :
    (intrinsicCanonicalLorentzVolumeMeasure
      period hPeriod).IsOpenPosMeasure := by
  let openParameterization : OpenPositiveDenseParametrization
      (sourceMeasure := sourceMeasure)
      (targetMeasure := intrinsicCanonicalLorentzVolumeMeasure period hPeriod) where
    map := parameterization.parameterization
    continuous := parameterization.continuous
    denseRange := parameterization.denseRange
    measurePreserving := parameterization.measurePreserving
    sourceOpenPositive := parameterization.sourceOpenPositive
  exact openParameterization.targetOpenPositive

/-- Compatibility-only Euler data become the complete faithful Euler package. -/
def toEulerCompatibilityData
    {Source : Type u}
    [TopologicalSpace Source] [MeasurableSpace Source]
    {sourceMeasure : Measure Source}
    (parameterization : CanonicalPhysicalScalarEulerDenseParametrizationData
      period hPeriod Source sourceMeasure)
    (euler : CanonicalPhysicalScalarEulerCompatibilityOnlyData
      period hPeriod massSquared) :=
  euler.toCompatibilityData parameterization.physicalMeasureOpenPositive

/-- Genuine physical bulk operator. -/
def toBulkL2LinearMap
    {Source : Type u}
    [TopologicalSpace Source] [MeasurableSpace Source]
    {sourceMeasure : Measure Source}
    (parameterization : CanonicalPhysicalScalarEulerDenseParametrizationData
      period hPeriod Source sourceMeasure)
    (euler : CanonicalPhysicalScalarEulerCompatibilityOnlyData
      period hPeriod massSquared) :=
  (parameterization.toEulerCompatibilityData euler).toBulkL2LinearMap

/-- Dense-parametrization Euler certificate. -/
theorem certificate
    {Source : Type u}
    [TopologicalSpace Source] [MeasurableSpace Source]
    {sourceMeasure : Measure Source}
    (parameterization : CanonicalPhysicalScalarEulerDenseParametrizationData
      period hPeriod Source sourceMeasure)
    (euler : CanonicalPhysicalScalarEulerCompatibilityOnlyData
      period hPeriod massSquared) :
    (intrinsicCanonicalLorentzVolumeMeasure
        period hPeriod).IsOpenPosMeasure ∧
      (∀ field,
        P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerAtlas4D.canonicalPhysicalScalarEulerGlobalResidual
            period hPeriod massSquared field =ᵐ[
              intrinsicCanonicalLorentzVolumeMeasure period hPeriod] 0 →
          P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerAtlas4D.canonicalPhysicalScalarEulerGlobalResidual
            period hPeriod massSquared field = 0) :=
  ⟨parameterization.physicalMeasureOpenPositive,
    euler.residual_eq_zero_of_ae_eq_zero
      parameterization.physicalMeasureOpenPositive⟩

end CanonicalPhysicalScalarEulerDenseParametrizationData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerDenseParametrizationClosure4D
end JanusFormal
