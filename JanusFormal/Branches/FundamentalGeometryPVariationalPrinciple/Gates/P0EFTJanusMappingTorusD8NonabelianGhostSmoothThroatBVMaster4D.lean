import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusD8NonabelianGhostFinitePositiveMetricBVMaster4D

/-!
# Pointwise BV master model on the smooth physical throat

The finite 32-dimensional BV phase is promoted fibrewise to smooth fields on
the actual compact throat.  Its BRST operator remains smooth and square-zero,
and the finite classical master equation holds at every throat point.  The
master density is integrated against the existing canonical finite nonzero
throat measure, with an explicit nonzero constant-field witness.

This is a pointwise finite-dimensional odd bracket; no functional BV bracket
on the infinite-dimensional smooth field space is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusD8NonabelianGhostSmoothThroatBVMaster4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff ENNReal BigOperators
open MeasureTheory Set
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusD8NonabelianGhostPositiveMetricThroatBV4D
open P0EFTJanusMappingTorusD8NonabelianGhostFinitePositiveMetricBVMaster4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev throatData := fixedEquatorData period hPeriod
private abbrev EffectiveThroat := MappingTorus (throatData period hPeriod)

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

/-- Smooth sections of the constant finite BV phase bundle over the physical
throat. -/
abbrev SmoothFiniteMetricBVField :=
  SmoothThroatField period hPeriod FiniteMetricBVPhase

private def finiteMetricBVBRSTContinuous :
    FiniteMetricBVPhase →L[Real] FiniteMetricBVPhase :=
  LinearMap.toContinuousLinearMap finiteMetricBVBRST

private def finiteMetricCEDifferentialContinuous :
    FiniteMetricCEField →L[Real] FiniteMetricCEField :=
  LinearMap.toContinuousLinearMap finiteMetricCEDifferential

/-- Fibrewise finite BRST differential on smooth throat BV fields. -/
def smoothThroatBVBRST
    (field : SmoothFiniteMetricBVField period hPeriod) :
    SmoothFiniteMetricBVField period hPeriod where
  toFun point := finiteMetricBVBRST (field point)
  contMDiff_toFun :=
    (finiteMetricBVBRSTContinuous.contDiff.contMDiff).comp
      field.contMDiff_toFun

@[simp]
theorem smoothThroatBVBRST_apply
    (field : SmoothFiniteMetricBVField period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    smoothThroatBVBRST period hPeriod field point =
      finiteMetricBVBRST (field point) :=
  rfl

/-- The smooth fibrewise BRST differential remains square-zero. -/
theorem smoothThroatBVBRST_square_zero
    (field : SmoothFiniteMetricBVField period hPeriod) :
    smoothThroatBVBRST period hPeriod
        (smoothThroatBVBRST period hPeriod field) = 0 := by
  apply SmoothThroatField.ext period hPeriod FiniteMetricBVPhase
  intro point
  exact finiteMetricBVBRST_square_zero (field point)

private theorem finiteMetricBVMasterAction_contDiff :
    ContDiff Real ω finiteMetricBVMasterAction := by
  unfold finiteMetricBVMasterAction finiteMetricDot
  apply ContDiff.sum
  intro coordinate _
  apply ContDiff.sum
  intro slot _
  exact ((contDiff_apply Real Real (coordinate, slot)).comp contDiff_snd).mul
    ((contDiff_apply Real Real (coordinate, slot)).comp
      (finiteMetricCEDifferentialContinuous.contDiff.comp contDiff_fst))

/-- Smooth scalar master density obtained from the finite master Hamiltonian
at each throat point. -/
def smoothThroatBVMasterDensity
    (field : SmoothFiniteMetricBVField period hPeriod) :
    SmoothThroatField period hPeriod Real where
  toFun point := finiteMetricBVMasterAction (field point)
  contMDiff_toFun :=
    (finiteMetricBVMasterAction_contDiff.contMDiff.of_le (by simp)).comp
      field.contMDiff_toFun

@[simp]
theorem smoothThroatBVMasterDensity_apply
    (field : SmoothFiniteMetricBVField period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    smoothThroatBVMasterDensity period hPeriod field point =
      finiteMetricBVMasterAction (field point) :=
  rfl

/-- The finite classical master equation holds at every point of the actual
smooth throat. -/
theorem smoothThroatBV_classical_master_equation_pointwise
    (field : SmoothFiniteMetricBVField period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    finiteBVOddAntibracket finiteMetricBVMasterObservable
        finiteMetricBVMasterObservable (field point) = 0 :=
  finiteMetricBV_classical_master_equation (field point)

theorem smoothThroatBVMaster_generates_field_pointwise
    (field : SmoothFiniteMetricBVField period hPeriod)
    (point : EffectiveThroat period hPeriod)
    (index : FiniteMetricCEIndex) :
    finiteBVOddAntibracket finiteMetricBVMasterObservable
        (finiteBVFieldCoordinateObservable index) (field point) =
      (smoothThroatBVBRST period hPeriod field point).1 index :=
  finiteMetricBVMaster_generates_field (field point) index

theorem smoothThroatBVMaster_generates_antifield_pointwise
    (field : SmoothFiniteMetricBVField period hPeriod)
    (point : EffectiveThroat period hPeriod)
    (index : FiniteMetricCEIndex) :
    finiteBVOddAntibracket finiteMetricBVMasterObservable
        (finiteBVAntifieldCoordinateObservable index) (field point) =
      (smoothThroatBVBRST period hPeriod field point).2 index :=
  finiteMetricBVMaster_generates_antifield (field point) index

/-- Actual integrated master action on the canonical physical throat volume. -/
def canonicalSmoothThroatBVMasterAction
    (field : SmoothFiniteMetricBVField period hPeriod) : Real :=
  ∫ point, smoothThroatBVMasterDensity period hPeriod field point
    ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)

theorem smoothThroatBVMasterDensity_integrable
    (field : SmoothFiniteMetricBVField period hPeriod) :
    Integrable (smoothThroatBVMasterDensity period hPeriod field)
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
  letI : IsFiniteMeasure
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
    intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod
  exact (smoothThroatBVMasterDensity period hPeriod field).contMDiff_toFun.continuous
    |>.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace
        (smoothThroatBVMasterDensity period hPeriod field))

/-- Explicit phase on which the finite master Hamiltonian is one. -/
def smoothThroatBVWitnessPhase : FiniteMetricBVPhase :=
  (finiteMetricBasis ((((0 : Fin 2), (0 : Fin 4)), 0)),
    finiteMetricBasis ((((0 : Fin 2), (0 : Fin 4)), 1)))

/-- Constant smooth throat section carrying the nonzero finite master phase. -/
def smoothThroatBVWitnessField :
    SmoothFiniteMetricBVField period hPeriod where
  toFun _ := smoothThroatBVWitnessPhase
  contMDiff_toFun := contMDiff_const

@[simp]
theorem smoothThroatBVWitnessField_apply
    (point : EffectiveThroat period hPeriod) :
    smoothThroatBVWitnessField period hPeriod point =
      smoothThroatBVWitnessPhase :=
  rfl

@[simp]
theorem smoothThroatBVWitnessDensity
    (point : EffectiveThroat period hPeriod) :
    smoothThroatBVMasterDensity period hPeriod
        (smoothThroatBVWitnessField period hPeriod) point = 1 := by
  change finiteMetricBVMasterAction smoothThroatBVWitnessPhase = 1
  exact finiteMetricBVMasterAction_witness

theorem canonicalSmoothThroatBVMasterAction_witness :
    canonicalSmoothThroatBVMasterAction period hPeriod
        (smoothThroatBVWitnessField period hPeriod) =
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod Set.univ).toReal := by
  letI : IsFiniteMeasure
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
    intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod
  rw [canonicalSmoothThroatBVMasterAction]
  calc
    ∫ point, smoothThroatBVMasterDensity period hPeriod
        (smoothThroatBVWitnessField period hPeriod) point
        ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod) =
        ∫ _point, (1 : Real)
          ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
            apply integral_congr_ae
            filter_upwards [] with point
            exact smoothThroatBVWitnessDensity period hPeriod point
    _ = _ := by simp [measureReal_def]

/-- The canonical integrated smooth-throat master action is genuinely
nonzero. -/
theorem canonicalSmoothThroatBVMasterAction_nonzero :
    canonicalSmoothThroatBVMasterAction period hPeriod ≠ 0 := by
  letI : IsFiniteMeasure
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
    intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod
  intro hZero
  have hWitness :
      canonicalSmoothThroatBVMasterAction period hPeriod
          (smoothThroatBVWitnessField period hPeriod) = 0 := by
    rw [hZero]
    rfl
  rw [canonicalSmoothThroatBVMasterAction_witness] at hWitness
  exact (ENNReal.toReal_ne_zero.2
    ⟨(Measure.measure_univ_ne_zero).2
      (intrinsicCanonicalThroatVolumeMeasure_ne_zero period hPeriod),
      measure_ne_top _ _⟩) hWitness

end
end P0EFTJanusMappingTorusD8NonabelianGhostSmoothThroatBVMaster4D
end JanusFormal
