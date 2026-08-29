import Mathlib.MeasureTheory.Function.L2Space
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarGreenDivergence4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerAtlas4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarBulkEulerGreenBridge4D

/-!
# Reducing the physical bulk Green identity to one divergence integral

The local jet identity already says that the divergence of the scalar Green
current is the antisymmetrized wave expression.  The mass terms cancel, so it is
also the antisymmetrized physical Euler residual.

At the Hilbert level, the defect

`<A field,test> - <field,A test>`

is exactly the integral of the opposite pointwise Euler skew density.  In every
holonomic chart this density is minus the local Green-current divergence.
Consequently the entire bulk Green bridge is reduced to one global integration
theorem identifying that scalar integral with the canonical pushed divergence
measure.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerGreenL2Reduction4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff ENNReal
open MeasureTheory Set Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusL2PTFunctionalSpace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarJet4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarGreenDivergence4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerAtlas4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarBulkEulerGreenBridge4D
open P0EFTJanusMappingTorusCutBulkCanonicalDivergenceMeasure4D

variable (period : Real) (hPeriod : period ≠ 0)
variable {massSquared : Real}

private abbrev Vector4 :=
  P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerAtlas4D.Vector4

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

/-- Local Green divergence in terms of the physical Euler residual. -/
theorem localSmoothScalarGreenDivergence_eq_eulerDifference
    (massSquared : Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (field test : SmoothScalarField period hPeriod)
    (coordinate : Vector4) :
    localSmoothScalarGreenDivergence period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod)
        patch field test coordinate =
      localScalarRepresentative period hPeriod field patch coordinate *
          canonicalPhysicalScalarEulerAtlasResidual
            period hPeriod massSquared test patch coordinate -
        localScalarRepresentative period hPeriod test patch coordinate *
          canonicalPhysicalScalarEulerAtlasResidual
            period hPeriod massSquared field patch coordinate := by
  rw [localSmoothScalarGreenDivergence_eq_waveDifference,
    canonicalPhysicalScalarEulerAtlasResidual_eq_wave_sub_mass,
    canonicalPhysicalScalarEulerAtlasResidual_eq_wave_sub_mass]
  ring

/-- Pointwise global Euler skew density with the Hilbert-pairing sign. -/
def canonicalPhysicalScalarEulerSkewDensity
    (massSquared : Real)
    (field test : SmoothScalarField period hPeriod)
    (point : EffectiveQuotient period hPeriod) : Real :=
  canonicalPhysicalScalarEulerGlobalResidual
      period hPeriod massSquared field point * test point -
    field point * canonicalPhysicalScalarEulerGlobalResidual
      period hPeriod massSquared test point

/-- In every chart, the Hilbert-sign skew density is minus the local Green
current divergence. -/
theorem canonicalPhysicalScalarEulerSkewDensity_eq_neg_localDivergence
    (operatorData : CanonicalPhysicalScalarEulerGlobalOperatorData
      period hPeriod massSquared)
    (field test : SmoothScalarField period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    canonicalPhysicalScalarEulerSkewDensity period hPeriod massSquared
        field test (patch.coordinateMap coordinate) =
      -localSmoothScalarGreenDivergence period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod)
        patch field test coordinate := by
  unfold canonicalPhysicalScalarEulerSkewDensity
  rw [canonicalPhysicalScalarEulerGlobalResidual_eq_chart
      period hPeriod massSquared field (operatorData.compatible field),
    canonicalPhysicalScalarEulerGlobalResidual_eq_chart
      period hPeriod massSquared test (operatorData.compatible test),
    localSmoothScalarGreenDivergence_eq_eulerDifference
      period hPeriod massSquared patch field test coordinate]
  unfold localScalarRepresentative
  ring

/-- The global skew density is continuous. -/
theorem canonicalPhysicalScalarEulerSkewDensity_continuous
    (operatorData : CanonicalPhysicalScalarEulerGlobalOperatorData
      period hPeriod massSquared)
    (field test : SmoothScalarField period hPeriod) :
    Continuous
      (canonicalPhysicalScalarEulerSkewDensity
        period hPeriod massSquared field test) :=
  ((operatorData.continuous field).mul test.contMDiff_toFun.continuous).sub
    (field.contMDiff_toFun.continuous.mul (operatorData.continuous test))

/-- The global skew density is integrable. -/
theorem canonicalPhysicalScalarEulerSkewDensity_integrable
    (operatorData : CanonicalPhysicalScalarEulerGlobalOperatorData
      period hPeriod massSquared)
    (field test : SmoothScalarField period hPeriod) :
    Integrable
      (canonicalPhysicalScalarEulerSkewDensity
        period hPeriod massSquared field test)
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  (canonicalPhysicalScalarEulerSkewDensity_continuous
    period hPeriod operatorData field test).memLp_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
    |>.integrable one_le_two

/-- One mixed physical `L²` pairing is the integral of the corresponding smooth
representatives. -/
theorem inner_euler_bulk_eq_integral
    (operatorData : CanonicalPhysicalScalarEulerGlobalOperatorData
      period hPeriod massSquared)
    (field test : SmoothScalarField period hPeriod) :
    inner Real (operatorData.toBulkL2LinearMap field)
        (smoothToCanonicalPhysicalBulkL2 period hPeriod test) =
      ∫ point,
        canonicalPhysicalScalarEulerGlobalResidual
            period hPeriod massSquared field point * test point
        ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards
    [operatorData.toBulkL2LinearMap_ae field,
     smoothFieldToL2_ae period hPeriod Real
       (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) test]
    with point hEuler hTest
  change inner Real
      ((operatorData.toBulkL2LinearMap field :
        EffectiveQuotient period hPeriod → Real) point)
      ((smoothFieldToL2 period hPeriod Real
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) test :
          EffectiveQuotient period hPeriod → Real) point) = _
  rw [hEuler, hTest]
  exact Real.inner_apply _ _

/-- The physical `L²` adjunction defect is the integral of the global skew
density. -/
theorem bulkPairingDefect_eq_integral_skewDensity
    (operatorData : CanonicalPhysicalScalarEulerGlobalOperatorData
      period hPeriod massSquared)
    (field test : SmoothScalarField period hPeriod) :
    inner Real (operatorData.toBulkL2LinearMap field)
          (smoothToCanonicalPhysicalBulkL2 period hPeriod test) -
        inner Real (smoothToCanonicalPhysicalBulkL2 period hPeriod field)
          (operatorData.toBulkL2LinearMap test) =
      ∫ point,
        canonicalPhysicalScalarEulerSkewDensity
          period hPeriod massSquared field test point
        ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod := by
  rw [inner_euler_bulk_eq_integral period hPeriod operatorData field test]
  rw [real_inner_comm,
    inner_euler_bulk_eq_integral period hPeriod operatorData test field]
  rw [← integral_sub]
  · apply integral_congr_ae
    exact Filter.Eventually.of_forall fun point => by
      unfold canonicalPhysicalScalarEulerSkewDensity
      ring
  · exact (operatorData.residual_memLp field).integrable_mul
      (smoothQuotientField_memLp period hPeriod Real
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) test)
  · exact (operatorData.residual_memLp test).integrable_mul
      (smoothQuotientField_memLp period hPeriod Real
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) field)

/-- The single remaining global divergence-integration theorem. -/
structure CanonicalPhysicalScalarEulerDivergenceIntegralData
    (massSquared : Real) where
  operatorData : CanonicalPhysicalScalarEulerGlobalOperatorData
    period hPeriod massSquared
  integral_eq_divergence :
    ∀ field test : SmoothScalarField period hPeriod,
      (∫ point,
        canonicalPhysicalScalarEulerSkewDensity
          period hPeriod massSquared field test point
        ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod) =
      -2 * cutBulkCanonicalDivergenceMeasure
        period hPeriod massSquared field test Set.univ

namespace CanonicalPhysicalScalarEulerDivergenceIntegralData

/-- The integral theorem produces the exact bulk Euler/divergence bridge. -/
def toBulkEulerDivergenceBridge
    (integralData : CanonicalPhysicalScalarEulerDivergenceIntegralData
      period hPeriod massSquared) :
    CanonicalPhysicalScalarBulkEulerDivergenceBridge
      period hPeriod massSquared where
  operatorData := integralData.operatorData
  pairing_eq_neg_two_divergence := by
    intro field test
    rw [bulkPairingDefect_eq_integral_skewDensity
      period hPeriod integralData.operatorData]
    exact integralData.integral_eq_divergence field test

/-- The integral theorem closes the full oriented Green identity. -/
theorem pairing_eq_orientedBoundaryCurrent
    (integralData : CanonicalPhysicalScalarEulerDivergenceIntegralData
      period hPeriod massSquared)
    (field test : SmoothScalarField period hPeriod) :
    inner Real (integralData.operatorData.toBulkL2LinearMap field)
          (smoothToCanonicalPhysicalBulkL2 period hPeriod test) -
        inner Real (smoothToCanonicalPhysicalBulkL2 period hPeriod field)
          (integralData.operatorData.toBulkL2LinearMap test) =
      P0EFTJanusMappingTorusCutBulkGlobalOrientedBoundaryCurrent4D.cutBulkGlobalOrientedScalarCurrentIntegral
        period hPeriod field test :=
  CanonicalPhysicalScalarBulkEulerDivergenceBridge.pairing_eq_orientedBoundaryCurrent
    period hPeriod
    (toBulkEulerDivergenceBridge period hPeriod integralData) field test

/-- Euler/Green `L²` reduction certificate. -/
theorem certificate
    (integralData : CanonicalPhysicalScalarEulerDivergenceIntegralData
      period hPeriod massSquared) :
    (∀ field test : SmoothScalarField period hPeriod,
      inner Real (integralData.operatorData.toBulkL2LinearMap field)
            (smoothToCanonicalPhysicalBulkL2 period hPeriod test) -
          inner Real (smoothToCanonicalPhysicalBulkL2 period hPeriod field)
            (integralData.operatorData.toBulkL2LinearMap test) =
        ∫ point,
          canonicalPhysicalScalarEulerSkewDensity
            period hPeriod massSquared field test point
          ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod) ∧
      (∀ field test : SmoothScalarField period hPeriod,
        inner Real (integralData.operatorData.toBulkL2LinearMap field)
              (smoothToCanonicalPhysicalBulkL2 period hPeriod test) -
            inner Real (smoothToCanonicalPhysicalBulkL2 period hPeriod field)
              (integralData.operatorData.toBulkL2LinearMap test) =
          P0EFTJanusMappingTorusCutBulkGlobalOrientedBoundaryCurrent4D.cutBulkGlobalOrientedScalarCurrentIntegral
            period hPeriod field test) :=
  ⟨bulkPairingDefect_eq_integral_skewDensity
      period hPeriod integralData.operatorData,
    pairing_eq_orientedBoundaryCurrent period hPeriod integralData⟩

end CanonicalPhysicalScalarEulerDivergenceIntegralData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerGreenL2Reduction4D
end JanusFormal
