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

private theorem smoothResidual_pairing_injective
    (first second : SmoothThroatField period hPeriod LLFieldFiber)
    (hPairing : ∀ test : LLWeakTestSpace period hPeriod,
      (∫ point, inner Real (first point) (test point)
        ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) =
      ∫ point, inner Real (second point) (test point)
        ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) :
    first = second := by
  letI : (intrinsicCanonicalThroatVolumeMeasure period hPeriod).IsOpenPosMeasure :=
    intrinsicCanonicalThroatVolumeMeasure_isOpenPosMeasure period hPeriod
  have hZero := (smoothLLField_pairing_detects_pointwise_zero period hPeriod
    (first - second) (intrinsicCanonicalThroatVolumeMeasure period hPeriod)).mp
  have hIntegrable (field test : SmoothThroatField period hPeriod LLFieldFiber) :
      Integrable (fun point => inner Real (field point) (test point))
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
    (field.contMDiff_toFun.continuous.inner test.contMDiff_toFun.continuous)
      |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  apply SmoothThroatField.ext
  intro point
  have hPoint := hZero (by
    intro test
    have hApply (point) : (first - second) point = first point - second point := rfl
    simp only [hApply, inner_sub_left]
    rw [integral_sub (hIntegrable first test) (hIntegrable second test),
      hPairing test, sub_self]) point
  exact sub_eq_zero.mp hPoint

/-- The same-action smooth Jacobi residual is additive in its LL direction. -/
theorem llStrongJacobiResidual_add
    (fields : IndependentFields period hPeriod)
    (first second : LLWeakTestSpace period hPeriod) :
    llStrongJacobiResidual period hPeriod fields (first + second) =
      llStrongJacobiResidual period hPeriod fields first +
        llStrongJacobiResidual period hPeriod fields second := by
  apply smoothResidual_pairing_injective period hPeriod
  intro test
  have hApply (point) :
      (llStrongJacobiResidual period hPeriod fields first +
        llStrongJacobiResidual period hPeriod fields second) point =
      llStrongJacobiResidual period hPeriod fields first point +
        llStrongJacobiResidual period hPeriod fields second point := rfl
  simp only [hApply, inner_add_left]
  rw [integral_add]
  · rw [llStrongJacobiResidual_pairing_eq_hessian,
      llStrongJacobiResidual_pairing_eq_hessian,
      llStrongJacobiResidual_pairing_eq_hessian]
    exact globalPTSymmetricDifferentialLLFluxHessian_add_left period hPeriod
      (canonicalDivergenceFreeLLFrame period hPeriod) fields first second test
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod)
  · exact ((llStrongJacobiResidual period hPeriod fields first).contMDiff_toFun.continuous.inner
      test.contMDiff_toFun.continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  · exact ((llStrongJacobiResidual period hPeriod fields second).contMDiff_toFun.continuous.inner
      test.contMDiff_toFun.continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)

/-- The same-action smooth Jacobi residual is homogeneous in its LL direction. -/
theorem llStrongJacobiResidual_smul
    (fields : IndependentFields period hPeriod)
    (scalar : Real) (direction : LLWeakTestSpace period hPeriod) :
    llStrongJacobiResidual period hPeriod fields (scalar • direction) =
      scalar • llStrongJacobiResidual period hPeriod fields direction := by
  apply smoothResidual_pairing_injective period hPeriod
  intro test
  have hApply (point) :
      (scalar • llStrongJacobiResidual period hPeriod fields direction) point =
      scalar • llStrongJacobiResidual period hPeriod fields direction point := rfl
  simp only [hApply, real_inner_smul_left, integral_const_mul]
  rw [llStrongJacobiResidual_pairing_eq_hessian,
    llStrongJacobiResidual_pairing_eq_hessian]
  exact globalPTSymmetricDifferentialLLFluxHessian_smul_left period hPeriod
    (canonicalDivergenceFreeLLFrame period hPeriod) fields direction test scalar
    (intrinsicCanonicalThroatVolumeMeasure period hPeriod)

/-- Additivity persists after taking the genuine L² equivalence class. -/
theorem llStrongJacobiToL2_add
    (fields : IndependentFields period hPeriod)
    (first second : LLWeakTestSpace period hPeriod) :
    llStrongJacobiToL2 period hPeriod fields (first + second) =
      llStrongJacobiToL2 period hPeriod fields first +
        llStrongJacobiToL2 period hPeriod fields second := by
  apply Lp.ext
  filter_upwards
    [llStrongJacobiToL2_ae period hPeriod fields (first + second),
      llStrongJacobiToL2_ae period hPeriod fields first,
      llStrongJacobiToL2_ae period hPeriod fields second,
      Lp.coeFn_add (llStrongJacobiToL2 period hPeriod fields first)
        (llStrongJacobiToL2 period hPeriod fields second)]
    with point hSum hFirst hSecond hAdd
  simp only [Pi.add_apply] at hAdd
  rw [hSum, hAdd, hFirst, hSecond]
  exact congrArg (fun field : SmoothThroatField period hPeriod LLFieldFiber =>
    field.toFun point)
    (llStrongJacobiResidual_add period hPeriod fields first second)

/-- Homogeneity persists after taking the genuine L² equivalence class. -/
theorem llStrongJacobiToL2_smul
    (fields : IndependentFields period hPeriod)
    (scalar : Real) (direction : LLWeakTestSpace period hPeriod) :
    llStrongJacobiToL2 period hPeriod fields (scalar • direction) =
      scalar • llStrongJacobiToL2 period hPeriod fields direction := by
  apply Lp.ext
  filter_upwards
    [llStrongJacobiToL2_ae period hPeriod fields (scalar • direction),
      llStrongJacobiToL2_ae period hPeriod fields direction,
      Lp.coeFn_smul scalar (llStrongJacobiToL2 period hPeriod fields direction)]
    with point hScaled hDirection hSmul
  simp only [Pi.smul_apply] at hSmul
  rw [hScaled, hSmul, hDirection]
  exact congrArg (fun field : SmoothThroatField period hPeriod LLFieldFiber =>
    field.toFun point)
    (llStrongJacobiResidual_smul period hPeriod fields scalar direction)

/-- Linear smooth-core realization of the unchanged LL Jacobi Hessian in L². -/
def llStrongJacobiLinearMap
    (fields : IndependentFields period hPeriod) :
    LLWeakTestSpace period hPeriod →ₗ[Real]
      Lp LLFieldFiber (2 : ENNReal)
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) where
  toFun := llStrongJacobiToL2 period hPeriod fields
  map_add' := llStrongJacobiToL2_add period hPeriod fields
  map_smul' := llStrongJacobiToL2_smul period hPeriod fields

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
