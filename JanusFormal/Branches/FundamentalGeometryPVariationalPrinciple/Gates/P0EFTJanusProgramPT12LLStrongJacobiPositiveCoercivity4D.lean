import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LLStrongJacobiClosedLowerBound4D

/-! A positive LL measure gives a uniform L² bound for the closed field Jacobi operator. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12LLStrongJacobiPositiveCoercivity4D

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

open scoped Manifold ContDiff ENNReal LinearPMap
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusPTInvolution
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusGlobalLLCovariance4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLHessian4D
open P0EFTJanusMappingTorusPTSymmetricLLWeakEulerJacobiOperator4D
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
open P0EFTJanusMappingTorusCanonicalThroatPTMeasureInvariance4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusProgramPT12LLStrongJacobiL2Core4D
open P0EFTJanusProgramPT12LLSmoothL2Density4D
open P0EFTJanusProgramPT12LLStrongJacobiClosure4D
open P0EFTJanusProgramPT12LLStrongJacobiClosedLowerBound4D

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

private theorem uniform_measure_lower
    (fields : IndependentFields period hPeriod)
    (hMeasure : ∀ point, 0 < fields.llMeasure point) :
    ∃ lower : Real, 0 < lower ∧ ∀ point, lower ≤ fields.llMeasure point := by
  rcases isCompact_univ.exists_forall_le'
      fields.llMeasure.contMDiff_toFun.continuous.continuousOn
      (fun point _ => hMeasure point) with ⟨lower, hLower, hBound⟩
  exact ⟨lower, hLower, fun point => hBound point (Set.mem_univ point)⟩

private theorem raw_hessian_positive_lower
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (direction : LLWeakTestSpace period hPeriod)
    (lower : Real) (hLower : ∀ point, lower ≤ fields.llMeasure point) :
    2 * lower *
        (∫ point, ‖direction point‖ ^ 2
          ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) ≤
      globalDifferentialLLFluxHessian period hPeriod frame fields
        direction direction
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
  let mu := intrinsicCanonicalThroatVolumeMeasure period hPeriod
  have hNormContinuous : Continuous (fun point => ‖direction point‖ ^ 2) :=
    direction.contMDiff_toFun.continuous.norm.pow 2
  have hNormIntegrable : Integrable (fun point => ‖direction point‖ ^ 2) mu :=
    hNormContinuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hDensityIntegrable : Integrable
      (differentialLLFluxHessianDensity period hPeriod frame fields
        direction direction) mu :=
    (differentialLLFluxHessianDensity_continuous period hPeriod frame fields
      direction direction).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hPoint (point : EffectiveThroat period hPeriod) :
      2 * lower * ‖direction point‖ ^ 2 ≤
        differentialLLFluxHessianDensity period hPeriod frame fields
          direction direction point := by
    have hKinetic : 0 ≤
        llAuxiliaryKineticWeight period hPeriod fields point *
          throatDerivativeEnergy period hPeriod frame direction point := by
      apply mul_nonneg
      · exact (llAuxiliaryKineticWeight_pos period hPeriod fields point).le
      · unfold throatDerivativeEnergy
        exact Finset.sum_nonneg fun index _ => sq_nonneg _
    have hMass := mul_le_mul_of_nonneg_right (hLower point)
      (show 0 ≤ 2 * ‖direction point‖ ^ 2 by positivity)
    unfold differentialLLFluxHessianDensity
    rw [throatDerivativePairing_self_eq_energy period hPeriod
      frame direction point, real_inner_self_eq_norm_sq]
    nlinarith
  have hIntegral := integral_mono
    (hNormIntegrable.const_mul (2 * lower)) hDensityIntegrable hPoint
  change (∫ point, (2 * lower) * ‖direction point‖ ^ 2 ∂mu) ≤
    globalDifferentialLLFluxHessian period hPeriod frame fields
      direction direction mu at hIntegral
  rw [integral_const_mul] at hIntegral
  simpa [mu, mul_assoc] using hIntegral

private theorem pt_hessian_positive_lower
    (fields : IndependentFields period hPeriod)
    (direction : LLWeakTestSpace period hPeriod)
    (lower : Real) (hLower : ∀ point, lower ≤ fields.llMeasure point) :
    2 * lower *
        (∫ point, ‖direction point‖ ^ 2
          ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) ≤
      globalPTSymmetricDifferentialLLFluxHessian period hPeriod
        (canonicalDivergenceFreeLLFrame period hPeriod) fields
        direction direction
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
  let frame := canonicalDivergenceFreeLLFrame period hPeriod
  have hRaw := raw_hessian_positive_lower period hPeriod frame fields
    direction lower hLower
  have hPulledLower : ∀ point,
      lower ≤ (llPTPullback period hPeriod fields).llMeasure point := by
    intro point
    change lower ≤ fields.llMeasure (fixedThroatPT period hPeriod point)
    exact hLower _
  have hPulled := raw_hessian_positive_lower period hPeriod frame
    (llPTPullback period hPeriod fields)
    (differentialLLFluxDirectionPT period hPeriod direction)
    lower hPulledLower
  have hPTIntegral :
      (∫ point,
          ‖differentialLLFluxDirectionPT period hPeriod direction point‖ ^ 2
            ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) =
        ∫ point, ‖direction point‖ ^ 2
          ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
    have hMap :=
      (intrinsicCanonicalThroatVolumeMeasure_pt_measurePreserving
        period hPeriod).integral_comp'
        (fun point => ‖direction point‖ ^ 2)
    change (∫ point,
        ‖direction (fixedThroatPT period hPeriod point)‖ ^ 2
          ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) = _
    exact hMap
  rw [hPTIntegral] at hPulled
  unfold globalPTSymmetricDifferentialLLFluxHessian
  linarith

private theorem smooth_l2_norm_sq_eq_integral
    (direction : LLWeakTestSpace period hPeriod) :
    ‖llSmoothToL2 period hPeriod direction‖ ^ 2 =
      ∫ point, ‖direction point‖ ^ 2
        ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
  have hAE :
      (llSmoothToL2 period hPeriod direction :
        EffectiveThroat period hPeriod → LLFieldFiber) =ᵐ[
          intrinsicCanonicalThroatVolumeMeasure period hPeriod]
        direction.toFun :=
    (smoothThroatField_memLp period hPeriod LLFieldFiber
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod)
      direction).coeFn_toLp
  have hNorm :
      ‖llSmoothToL2 period hPeriod direction‖ ^ 2 =
        inner Real (llSmoothToL2 period hPeriod direction)
          (llSmoothToL2 period hPeriod direction) := by
    rw [real_inner_self_eq_norm_sq]
  rw [hNorm, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hAE] with point hPoint
  rw [hPoint, real_inner_self_eq_norm_sq]

private theorem strong_l2_inner_eq_hessian
    (fields : IndependentFields period hPeriod)
    (direction : LLWeakTestSpace period hPeriod) :
    inner Real (llStrongJacobiToL2 period hPeriod fields direction)
        (llSmoothToL2 period hPeriod direction) =
      globalPTSymmetricDifferentialLLFluxHessian period hPeriod
        (canonicalDivergenceFreeLLFrame period hPeriod) fields
        direction direction
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
  have hAE :
      (llSmoothToL2 period hPeriod direction :
        EffectiveThroat period hPeriod → LLFieldFiber) =ᵐ[
          intrinsicCanonicalThroatVolumeMeasure period hPeriod]
        direction.toFun :=
    (smoothThroatField_memLp period hPeriod LLFieldFiber
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod)
      direction).coeFn_toLp
  rw [L2.inner_def]
  calc
    (∫ point,
      inner Real (llStrongJacobiToL2 period hPeriod fields direction point)
        (llSmoothToL2 period hPeriod direction point)
      ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) =
      ∫ point,
        inner Real (llStrongJacobiToL2 period hPeriod fields direction point)
          (direction point)
        ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
          apply integral_congr_ae
          filter_upwards [hAE] with point hPoint
          rw [hPoint]
    _ = _ := llStrongJacobiToL2_pairing_eq_hessian period hPeriod fields
      direction direction

theorem llStrongJacobi_smooth_positive_l2_lower_bound
    (fields : IndependentFields period hPeriod)
    (hMeasure : ∀ point, 0 < fields.llMeasure point) :
    ∃ constant : Real, 0 < constant ∧
      ∀ direction : LLWeakTestSpace period hPeriod,
        constant * ‖llSmoothToL2 period hPeriod direction‖ ^ 2 ≤
          inner Real (llStrongJacobiToL2 period hPeriod fields direction)
            (llSmoothToL2 period hPeriod direction) := by
  obtain ⟨lower, hLower, hBound⟩ :=
    uniform_measure_lower period hPeriod fields hMeasure
  refine ⟨2 * lower, mul_pos (by norm_num) hLower, ?_⟩
  intro direction
  have hHessian := pt_hessian_positive_lower period hPeriod fields direction
    lower hBound
  rw [← smooth_l2_norm_sq_eq_integral period hPeriod direction,
    ← strong_l2_inner_eq_hessian period hPeriod fields direction] at hHessian
  exact hHessian

/-- Positive LL measure makes the genuine closed field Jacobi operator
uniformly coercive in the canonical L² norm. -/
theorem llJacobiClosedPMap_positive_l2_lower_bound
    (fields : IndependentFields period hPeriod)
    (hMeasure : ∀ point, 0 < fields.llMeasure point) :
    ∃ constant : Real, 0 < constant ∧
      ∀ x : (llJacobiClosedPMap period hPeriod fields).domain,
        constant * ‖(x : Lp LLFieldFiber (2 : ENNReal)
          (intrinsicCanonicalThroatVolumeMeasure period hPeriod))‖ ^ 2 ≤
          inner Real (llJacobiClosedPMap period hPeriod fields x)
            (x : Lp LLFieldFiber (2 : ENNReal)
              (intrinsicCanonicalThroatVolumeMeasure period hPeriod)) := by
  obtain ⟨constant, hPositive, hSmooth⟩ :=
    llStrongJacobi_smooth_positive_l2_lower_bound period hPeriod fields hMeasure
  let T := llJacobiSmoothPMap period hPeriod fields
  have hCore (x : T.domain) :
      -((-constant) * ‖(x : Lp LLFieldFiber (2 : ENNReal)
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod))‖ ^ 2) ≤
        inner Real (T x)
          (x : Lp LLFieldFiber (2 : ENNReal)
            (intrinsicCanonicalThroatVolumeMeasure period hPeriod)) := by
    obtain ⟨direction, hDirection⟩ := x.property
    let e : LLWeakTestSpace period hPeriod ≃ₗ[Real]
        llJacobiSmoothDomain period hPeriod :=
      LinearEquiv.ofInjective (llSmoothToL2LinearMap period hPeriod)
        (llSmoothToL2LinearMap_injective period hPeriod)
    have hInput : (x : Lp LLFieldFiber (2 : ENNReal)
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod)) =
        llSmoothToL2 period hPeriod direction := hDirection.symm
    have hApply : T x = llStrongJacobiToL2 period hPeriod fields direction := by
      have hEq : x =
          ⟨llSmoothToL2 period hPeriod direction,
            LinearMap.mem_range_self (llSmoothToL2LinearMap period hPeriod)
              direction⟩ := Subtype.ext hDirection.symm
      rw [hEq]
      change llStrongJacobiLinearMap period hPeriod fields
        (e.symm (e direction)) = _
      rw [e.symm_apply_apply]
      rfl
    rw [hInput, hApply]
    simpa only [neg_mul, neg_neg] using hSmooth direction
  refine ⟨constant, hPositive, ?_⟩
  intro x
  have hClosed := linearPMap_closure_quadratic_lower_bound T
    (llJacobiSmoothPMap_isClosable period hPeriod fields) (-constant) hCore x
  simpa [T, llJacobiClosedPMap, neg_mul] using hClosed

/-- Uniform positivity excludes an L² kernel for the closed field operator. -/
theorem llJacobiClosedPMap_injective_of_positive_measure
    (fields : IndependentFields period hPeriod)
    (hMeasure : ∀ point, 0 < fields.llMeasure point) :
    Function.Injective
      (llJacobiClosedPMap period hPeriod fields).toFun := by
  let C := llJacobiClosedPMap period hPeriod fields
  obtain ⟨constant, hPositive, hLower⟩ :=
    llJacobiClosedPMap_positive_l2_lower_bound period hPeriod fields hMeasure
  intro x y hEqual
  have hDiff : C.toFun (x - y) = 0 := by
    rw [map_sub, hEqual, sub_self]
  have hBound := hLower (x - y)
  change constant * ‖((x - y : C.domain) : Lp LLFieldFiber (2 : ENNReal)
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod))‖ ^ 2 ≤
    inner Real (C.toFun (x - y)) ((x - y : C.domain) : Lp LLFieldFiber
      (2 : ENNReal) (intrinsicCanonicalThroatVolumeMeasure period hPeriod))
      at hBound
  rw [hDiff, inner_zero_left] at hBound
  have hProduct :
      constant * ‖((x - y : C.domain) : Lp LLFieldFiber (2 : ENNReal)
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod))‖ ^ 2 = 0 :=
    le_antisymm hBound
      (mul_nonneg hPositive.le (sq_nonneg _))
  have hSquare :
      ‖((x - y : C.domain) : Lp LLFieldFiber (2 : ENNReal)
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod))‖ ^ 2 = 0 :=
    (mul_eq_zero.mp hProduct).resolve_left hPositive.ne'
  have hNorm : ‖((x - y : C.domain) : Lp LLFieldFiber (2 : ENNReal)
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod))‖ = 0 := by
    nlinarith [norm_nonneg ((x - y : C.domain) : Lp LLFieldFiber (2 : ENNReal)
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod))]
  have hZero : x - y = 0 :=
    Subtype.ext (norm_eq_zero.mp hNorm)
  exact sub_eq_zero.mp hZero

end
end P0EFTJanusProgramPT12LLStrongJacobiPositiveCoercivity4D
end JanusFormal
