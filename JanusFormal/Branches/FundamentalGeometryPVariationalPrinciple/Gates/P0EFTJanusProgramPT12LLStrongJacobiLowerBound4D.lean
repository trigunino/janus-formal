import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LLStrongJacobiL2Core4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LLSmoothL2Density4D

/-!
# Lower bound for the same-action LL Jacobi operator on its smooth core

The kinetic coefficient is positive.  The independent smooth zeroth-order
coefficient `llMeasure` may have either sign, but is uniformly bounded on the
compact throat.  PT invariance of the canonical volume gives one common L²
bound for both terms of the unchanged PT-averaged Hessian.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT12LLStrongJacobiLowerBound4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff ENNReal
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusPTInvolution
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusGlobalLLCovariance4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLHessian4D
open P0EFTJanusMappingTorusPTSymmetricLLWeakEulerJacobiOperator4D
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
open P0EFTJanusMappingTorusCanonicalThroatPTMeasureInvariance4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusProgramPT12LLStrongJacobiL2Core4D
open P0EFTJanusProgramPT12LLSmoothL2Density4D

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

private theorem raw_hessian_lower_bound
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (direction : LLWeakTestSpace period hPeriod)
    (bound : Real)
    (hLower : ∀ point, -bound ≤ fields.llMeasure point) :
    -2 * bound *
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
      -2 * bound * ‖direction point‖ ^ 2 ≤
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
    (hNormIntegrable.const_mul (-2 * bound)) hDensityIntegrable hPoint
  change (∫ point, (-2 * bound) * ‖direction point‖ ^ 2 ∂mu) ≤
    globalDifferentialLLFluxHessian period hPeriod frame fields
      direction direction mu at hIntegral
  rw [integral_const_mul] at hIntegral
  simpa [mu, mul_assoc] using hIntegral

private theorem pt_hessian_lower_bound
    (fields : IndependentFields period hPeriod)
    (direction : LLWeakTestSpace period hPeriod)
    (bound : Real)
    (hLower : ∀ point, -bound ≤ fields.llMeasure point) :
    -2 * bound *
        (∫ point, ‖direction point‖ ^ 2
          ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) ≤
      globalPTSymmetricDifferentialLLFluxHessian period hPeriod
        (canonicalDivergenceFreeLLFrame period hPeriod) fields
        direction direction
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
  let frame := canonicalDivergenceFreeLLFrame period hPeriod
  have hRaw := raw_hessian_lower_bound period hPeriod frame fields
    direction bound hLower
  have hPulledLower : ∀ point,
      -bound ≤ (llPTPullback period hPeriod fields).llMeasure point := by
    intro point
    change -bound ≤ fields.llMeasure (fixedThroatPT period hPeriod point)
    exact hLower _
  have hPulled := raw_hessian_lower_bound period hPeriod frame
    (llPTPullback period hPeriod fields)
    (differentialLLFluxDirectionPT period hPeriod direction)
    bound hPulledLower
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

/-- The actual smooth-core L² Jacobi pairing is uniformly bounded below,
without a positivity assumption on the independent `llMeasure` coefficient. -/
theorem llStrongJacobi_smooth_l2_lower_bound
    (fields : IndependentFields period hPeriod) :
    ∃ constant : Real, 0 ≤ constant ∧
      ∀ direction : LLWeakTestSpace period hPeriod,
        -(constant * ‖llSmoothToL2 period hPeriod direction‖ ^ 2) ≤
          inner Real (llStrongJacobiToL2 period hPeriod fields direction)
            (llSmoothToL2 period hPeriod direction) := by
  obtain ⟨bound, hBound⟩ :=
    isCompact_univ.exists_bound_of_continuousOn
      fields.llMeasure.contMDiff_toFun.continuous.continuousOn
  let nonnegativeBound := max bound 0
  have hLower : ∀ point, -nonnegativeBound ≤ fields.llMeasure point := by
    intro point
    have hNorm := hBound point (Set.mem_univ point)
    have hAbs : |fields.llMeasure point| ≤ bound := by
      simpa [Real.norm_eq_abs] using hNorm
    exact (neg_le_neg (le_max_left bound 0)).trans (abs_le.mp hAbs).1
  refine ⟨2 * nonnegativeBound,
    mul_nonneg (by norm_num) (le_max_right bound 0), ?_⟩
  intro direction
  have hHessian := pt_hessian_lower_bound period hPeriod fields direction
    nonnegativeBound hLower
  rw [← smooth_l2_norm_sq_eq_integral period hPeriod direction,
    ← strong_l2_inner_eq_hessian period hPeriod fields direction] at hHessian
  convert hHessian using 1; ring

end
end P0EFTJanusProgramPT12LLStrongJacobiLowerBound4D
end JanusFormal
