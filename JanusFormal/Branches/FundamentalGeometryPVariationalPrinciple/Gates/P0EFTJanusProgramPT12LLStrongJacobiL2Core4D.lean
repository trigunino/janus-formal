import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalBoundaryCompletion4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusPTSymmetricLLWeakEulerJacobiOperator4D

/-!
# Smooth LL Jacobi residual in L²

The canonical strong LL equation, with its coefficients frozen and its field
replaced by a smooth variation, realizes the actual weak Jacobi form in L².
This is a smooth-core realization, before completing the second-order graph.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT12LLStrongJacobiL2Core4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff ENNReal
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusGlobalLLCovariance4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLHessian4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLStrongEquation4D
open P0EFTJanusMappingTorusPTSymmetricLLWeakEulerJacobiOperator4D
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusProgramPGlobalBoundaryCompletion4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance :
    IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance : CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod

local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _

local instance : BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

local instance :
    IsFiniteMeasure (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod

/-- Freeze every LL coefficient and insert the variation as the field. -/
def llJacobiFrozenFields
    (fields : IndependentFields period hPeriod)
    (direction : LLWeakTestSpace period hPeriod) :
    IndependentFields period hPeriod :=
  { fields with llField := direction }

/-- The strong Jacobi residual of the unchanged PT-averaged LL action. -/
def llStrongJacobiResidual
    (fields : IndependentFields period hPeriod)
    (direction : LLWeakTestSpace period hPeriod) :
    SmoothThroatField period hPeriod LLFieldFiber :=
  ptSymmetricStrongDifferentialLLEulerField period hPeriod
    (canonicalDivergenceFreeLLFrame period hPeriod)
    (smoothLLStrongRegularity period hPeriod
      (canonicalDivergenceFreeLLFrame period hPeriod))
    (llJacobiFrozenFields period hPeriod fields direction)

theorem llStrongJacobiResidual_memLp
    (fields : IndependentFields period hPeriod)
    (direction : LLWeakTestSpace period hPeriod) :
    MemLp (llStrongJacobiResidual period hPeriod fields direction)
      (2 : ENNReal) (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  (llStrongJacobiResidual period hPeriod fields direction).contMDiff_toFun.continuous
    |>.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Genuine L² value of the smooth strong Jacobi residual. -/
def llStrongJacobiToL2
    (fields : IndependentFields period hPeriod)
    (direction : LLWeakTestSpace period hPeriod) :
    Lp LLFieldFiber (2 : ENNReal)
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  (llStrongJacobiResidual_memLp period hPeriod fields direction).toLp
    (llStrongJacobiResidual period hPeriod fields direction)

theorem llStrongJacobiToL2_ae
    (fields : IndependentFields period hPeriod)
    (direction : LLWeakTestSpace period hPeriod) :
    (llStrongJacobiToL2 period hPeriod fields direction :
      EffectiveThroat period hPeriod → LLFieldFiber) =ᵐ[
        intrinsicCanonicalThroatVolumeMeasure period hPeriod]
      llStrongJacobiResidual period hPeriod fields direction :=
  (llStrongJacobiResidual_memLp period hPeriod fields direction).coeFn_toLp

/-- Freezing the two coefficient slots identifies the weak Euler pairing with
the same-action Hessian in the LL-field slot. -/
theorem llJacobiFrozenFields_firstVariation_eq_hessian
    (fields : IndependentFields period hPeriod)
    (first second : LLWeakTestSpace period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) :
    globalPTSymmetricDifferentialLLFluxFirstVariation period hPeriod
        (canonicalDivergenceFreeLLFrame period hPeriod)
        (llJacobiFrozenFields period hPeriod fields first) second mu =
      globalPTSymmetricDifferentialLLFluxHessian period hPeriod
        (canonicalDivergenceFreeLLFrame period hPeriod)
        fields first second mu := by
  rfl

/-- The L² strong residual pairs to the actual weak Hessian on smooth tests.
This is the pure `llField` block with `llAuxMetric` and `llMeasure` fixed. -/
theorem llStrongJacobiResidual_pairing_eq_hessian
    (fields : IndependentFields period hPeriod)
    (first second : LLWeakTestSpace period hPeriod) :
    (∫ point,
      inner Real (llStrongJacobiResidual period hPeriod fields first point)
        (second point)
        ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) =
      globalPTSymmetricDifferentialLLFluxHessian period hPeriod
        (canonicalDivergenceFreeLLFrame period hPeriod) fields first second
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
  rw [← llJacobiFrozenFields_firstVariation_eq_hessian period hPeriod
    fields first second]
  exact (canonicalDivergenceFreeLLFrame_globalIPP period hPeriod
    (llJacobiFrozenFields period hPeriod fields first)
    (smoothLLStrongRegularity period hPeriod
      (canonicalDivergenceFreeLLFrame period hPeriod)) second).symm

/-- The pairing is unchanged when the strong residual is taken as an L²
equivalence class. -/
theorem llStrongJacobiToL2_pairing_eq_hessian
    (fields : IndependentFields period hPeriod)
    (first second : LLWeakTestSpace period hPeriod) :
    (∫ point,
      inner Real (llStrongJacobiToL2 period hPeriod fields first point)
        (second point)
        ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) =
      globalPTSymmetricDifferentialLLFluxHessian period hPeriod
        (canonicalDivergenceFreeLLFrame period hPeriod) fields first second
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
  rw [← llStrongJacobiResidual_pairing_eq_hessian period hPeriod fields
    first second]
  apply integral_congr_ae
  filter_upwards [llStrongJacobiToL2_ae period hPeriod fields first] with point hPoint
  rw [hPoint]

/-- The L² residual represents the previously defined weak LL Jacobi
operator, without replacing the LL-field action or its coefficients. -/
theorem weakLLJacobiOperator_eq_llStrongJacobiToL2_pairing
    (fields : IndependentFields period hPeriod)
    (first second : LLWeakTestSpace period hPeriod) :
    weakLLJacobiOperator period hPeriod
        (canonicalDivergenceFreeLLFrame period hPeriod) fields
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) first second =
      ∫ point,
        inner Real (llStrongJacobiToL2 period hPeriod fields first point)
          (second point)
          ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
  rw [weakLLJacobiOperator_apply]
  exact (llStrongJacobiToL2_pairing_eq_hessian period hPeriod fields
    first second).symm

end
end P0EFTJanusProgramPT12LLStrongJacobiL2Core4D
end JanusFormal
