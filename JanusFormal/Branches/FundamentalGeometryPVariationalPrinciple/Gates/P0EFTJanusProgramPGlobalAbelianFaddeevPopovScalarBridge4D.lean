import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalAbelianLorenzGraphRiesz4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWave4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerCanonicalFullSupport4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerGreenL2Reduction4D

/-!
# Intrinsic Abelian Faddeev--Popov/scalar-wave bridge

For the intrinsic metric, each real component of the Abelian FP operator
`δ_g d` is the already constructed canonical mass-zero scalar Euler operator.
The equality is proved pointwise and in the physical `L²` realization.

Consequently the smooth FP adjunction defect is exactly the established scalar
Euler skew-density integral.  This gate does not assert that the integral
vanishes and therefore adds no Green, symmetry, or closability hypothesis.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalAbelianFaddeevPopovScalarBridge4D

set_option autoImplicit false
noncomputable section

open scoped ENNReal Manifold ContDiff
open MeasureTheory Set Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusL2PTFunctionalSpace4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusGlobalGeneralMetricAbelianLorenzCodifferential4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerAtlas4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerFullSupportReduction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerCanonicalFullSupport4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWave4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerGreenL2Reduction4D
open P0EFTJanusProgramPGlobalAbelianLorenzGraphRiesz4D

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

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance canonicalLorentzVolumeFinite :
    IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

/-- Canonical mass-zero scalar Euler data, with every field supplied by the
proved intrinsic Levi-Civita wave naturality. -/
def canonicalMassZeroEulerCompatibilityOnlyData :
    CanonicalPhysicalScalarEulerCompatibilityOnlyData period hPeriod 0 where
  compatible := fun field =>
    (CanonicalPhysicalScalarIntrinsicWaveData.canonical period hPeriod
      ).eulerAtlasCompatible period hPeriod 0 field

/-- Faithful physical `L²` realization of the canonical mass-zero scalar wave. -/
def canonicalMassZeroEulerOperatorData :
    CanonicalPhysicalScalarEulerGlobalOperatorData period hPeriod 0 :=
  (canonicalMassZeroEulerCompatibilityOnlyData period hPeriod
    ).toCanonicalCompatibilityData period hPeriod |>.toOperatorData

/-- For the intrinsic metric, one Abelian FP component is exactly the
canonical mass-zero scalar Euler residual. -/
theorem intrinsicAbelianFaddeevPopov_component_eq_scalarResidual
    (ghost : SmoothQuotientField period hPeriod GaugeLieAlgebra)
    (component : Fin 2)
    (point : EffectiveQuotient period hPeriod) :
    globalGeneralMetricAbelianFaddeevPopov period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod) ghost point component =
      canonicalPhysicalScalarEulerGlobalResidual period hPeriod 0
        (ghostComponent period hPeriod ghost component) point := by
  let witness := canonicalPhysicalScalarEulerChartWitness period hPeriod point
  rw [← witness.coordinate_eq]
  rw [globalGeneralMetricAbelianFaddeevPopov_apply_local]
  rw [canonicalPhysicalScalarEulerGlobalResidual_eq_chart period hPeriod 0
    (ghostComponent period hPeriod ghost component)
    ((canonicalMassZeroEulerOperatorData period hPeriod).compatible
      (ghostComponent period hPeriod ghost component))]
  rw [canonicalPhysicalScalarEulerAtlasResidual_eq_wave_sub_mass]
  ring

/-- The physical `L²` coordinate of the intrinsic FP operator is the faithful
mass-zero scalar Euler operator. -/
theorem intrinsicAbelianFaddeevPopov_component_l2_eq_scalarOperator
    (ghost : SmoothQuotientField period hPeriod GaugeLieAlgebra)
    (component : Fin 2) :
    globalGaugeLieFieldL2Coordinates period hPeriod
        (globalGeneralMetricAbelianFaddeevPopov period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod) ghost) component =
      (canonicalMassZeroEulerOperatorData period hPeriod).toBulkL2LinearMap
        (ghostComponent period hPeriod ghost component) := by
  apply Lp.ext
  filter_upwards
    [smoothFieldToL2_ae period hPeriod Real
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
      (ghostComponent period hPeriod
        (globalGeneralMetricAbelianFaddeevPopov period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod) ghost) component),
     (canonicalMassZeroEulerOperatorData period hPeriod).toBulkL2LinearMap_ae
      (ghostComponent period hPeriod ghost component)]
    with point hFP hScalar
  change
    ((smoothFieldToL2 period hPeriod Real
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
      (ghostComponent period hPeriod
        (globalGeneralMetricAbelianFaddeevPopov period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod) ghost) component) :
        EffectiveQuotient period hPeriod → Real) point) = _
  rw [hFP, hScalar]
  exact intrinsicAbelianFaddeevPopov_component_eq_scalarResidual
    period hPeriod ghost component point

/-- The intrinsic FP adjunction defect is exactly the already constructed
scalar Euler skew-density integral.  No Stokes or symmetry claim is used. -/
theorem intrinsicAbelianFaddeevPopov_component_pairingDefect_eq_integral
    (first second : SmoothQuotientField period hPeriod GaugeLieAlgebra)
    (component : Fin 2) :
    inner Real
          (globalGaugeLieFieldL2Coordinates period hPeriod
            (globalGeneralMetricAbelianFaddeevPopov period hPeriod
              (intrinsicSmoothGeneralLorentzMetric period hPeriod) first)
            component)
          (globalGaugeLieFieldL2Coordinates period hPeriod second component) -
        inner Real
          (globalGaugeLieFieldL2Coordinates period hPeriod first component)
          (globalGaugeLieFieldL2Coordinates period hPeriod
            (globalGeneralMetricAbelianFaddeevPopov period hPeriod
              (intrinsicSmoothGeneralLorentzMetric period hPeriod) second)
            component) =
      ∫ point,
        canonicalPhysicalScalarEulerSkewDensity period hPeriod 0
          (ghostComponent period hPeriod first component)
          (ghostComponent period hPeriod second component) point
        ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod := by
  rw [intrinsicAbelianFaddeevPopov_component_l2_eq_scalarOperator,
    intrinsicAbelianFaddeevPopov_component_l2_eq_scalarOperator]
  exact bulkPairingDefect_eq_integral_skewDensity period hPeriod
    (canonicalMassZeroEulerOperatorData period hPeriod)
    (ghostComponent period hPeriod first component)
    (ghostComponent period hPeriod second component)

/-- Exact obstruction to smooth-core symmetry of one intrinsic FP component. -/
theorem intrinsicAbelianFaddeevPopov_component_symmetric_iff_skewIntegral_zero
    (first second : SmoothQuotientField period hPeriod GaugeLieAlgebra)
    (component : Fin 2) :
    inner Real
          (globalGaugeLieFieldL2Coordinates period hPeriod
            (globalGeneralMetricAbelianFaddeevPopov period hPeriod
              (intrinsicSmoothGeneralLorentzMetric period hPeriod) first)
            component)
          (globalGaugeLieFieldL2Coordinates period hPeriod second component) =
        inner Real
          (globalGaugeLieFieldL2Coordinates period hPeriod first component)
          (globalGaugeLieFieldL2Coordinates period hPeriod
            (globalGeneralMetricAbelianFaddeevPopov period hPeriod
              (intrinsicSmoothGeneralLorentzMetric period hPeriod) second)
            component) ↔
      (∫ point,
        canonicalPhysicalScalarEulerSkewDensity period hPeriod 0
          (ghostComponent period hPeriod first component)
          (ghostComponent period hPeriod second component) point
        ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod) = 0 := by
  constructor
  · intro hSymmetric
    have hZero :
        inner Real
              (globalGaugeLieFieldL2Coordinates period hPeriod
                (globalGeneralMetricAbelianFaddeevPopov period hPeriod
                  (intrinsicSmoothGeneralLorentzMetric period hPeriod) first)
                component)
              (globalGaugeLieFieldL2Coordinates period hPeriod second component) -
            inner Real
              (globalGaugeLieFieldL2Coordinates period hPeriod first component)
              (globalGaugeLieFieldL2Coordinates period hPeriod
                (globalGeneralMetricAbelianFaddeevPopov period hPeriod
                  (intrinsicSmoothGeneralLorentzMetric period hPeriod) second)
                component) = 0 :=
      sub_eq_zero.mpr hSymmetric
    rwa [intrinsicAbelianFaddeevPopov_component_pairingDefect_eq_integral] at hZero
  · intro hIntegral
    apply sub_eq_zero.mp
    rw [intrinsicAbelianFaddeevPopov_component_pairingDefect_eq_integral]
    exact hIntegral

end
end P0EFTJanusProgramPGlobalAbelianFaddeevPopovScalarBridge4D
end JanusFormal
