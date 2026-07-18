import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProductThroatHolonomyGraphInverseC1_4D
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Exact derivative of the inverse common-graph family

The derivative of inversion is obtained from its realization through ring
inversion, then restricted from `ℂ` to `ℝ` and composed with the holonomy
derivative.  This yields `d(A⁻¹) = -A⁻¹ (dA) A⁻¹`.
-/

namespace JanusFormal
namespace P0EFTJanusProductThroatHolonomyGraphInverseDerivative4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

noncomputable section

open Filter
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProductThroatHeatOperator4D
open P0EFTJanusProductThroatHeatOperatorNuclearExpansion4D
open P0EFTJanusProductThroatUnboundedDiracFredholm4D
open P0EFTJanusProductThroatHolonomyDerivative4D
open P0EFTJanusProductThroatHolonomyGraphFamily4D
open P0EFTJanusProductThroatHolonomyGraphRealFredholmFamily4D
open P0EFTJanusProductThroatHolonomyGraphInverseRegularity4D
open P0EFTJanusProductThroatHolonomyGraphInverseC1_4D

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedSpace Complex E] [NormedSpace Complex F] [CompleteSpace E]
  [Nontrivial E]

/-- Complex derivative of inversion at an equivalence. -/
def continuousLinearMapInverseFDeriv
    (equiv : E ≃L[Complex] F) :
    (E →L[Complex] F) →L[Complex] (F →L[Complex] E) :=
  ((ContinuousLinearMap.compL Complex F E E).flip
      (equiv.symm : F →L[Complex] E)).comp
    ((-ContinuousLinearMap.mulLeftRight Complex (E →L[Complex] E) 1 1).comp
      (ContinuousLinearMap.compL Complex E F E
        (equiv.symm : F →L[Complex] E)))

omit [CompleteSpace E] [Nontrivial E] in
@[simp] theorem continuousLinearMapInverseFDeriv_apply
    (equiv : E ≃L[Complex] F) (variation : E →L[Complex] F) :
    continuousLinearMapInverseFDeriv equiv variation =
      -((equiv.symm : F →L[Complex] E).comp
        (variation.comp (equiv.symm : F →L[Complex] E))) := by
  ext state
  simp [continuousLinearMapInverseFDeriv]

theorem continuousLinearMap_inverse_hasFDerivAt
    (equiv : E ≃L[Complex] F) :
    HasFDerivAt ContinuousLinearMap.inverse
      (continuousLinearMapInverseFDeriv equiv)
      (equiv : E →L[Complex] F) := by
  nontriviality E
  let left : (E →L[Complex] E) →L[Complex] (F →L[Complex] E) :=
    (ContinuousLinearMap.compL Complex F E E).flip
      (equiv.symm : F →L[Complex] E)
  let right : (E →L[Complex] F) →L[Complex] (E →L[Complex] E) :=
    ContinuousLinearMap.compL Complex E F E
      (equiv.symm : F →L[Complex] E)
  have hRight : right (equiv : E →L[Complex] F) = 1 := by
    ext state
    simp [right]
  have hRing : HasFDerivAt Ring.inverse
      (-ContinuousLinearMap.mulLeftRight Complex (E →L[Complex] E) 1 1)
      (1 : E →L[Complex] E) := by
    simpa using hasFDerivAt_ringInverse
      (𝕜 := Complex) (1 : (E →L[Complex] E)ˣ)
  have hRingAt : HasFDerivAt Ring.inverse
      (-ContinuousLinearMap.mulLeftRight Complex (E →L[Complex] E) 1 1)
      (right (equiv : E →L[Complex] F)) := by
    rw [hRight]
    exact hRing
  have hComposite := left.hasFDerivAt.comp
    (equiv : E →L[Complex] F)
      (hRingAt.comp (equiv : E →L[Complex] F) right.hasFDerivAt)
  have hFunction : ContinuousLinearMap.inverse =
      (left : (E →L[Complex] E) → F →L[Complex] E) ∘
        Ring.inverse ∘
          (right : (E →L[Complex] F) → E →L[Complex] E) :=
    funext (ContinuousLinearMap.inverse_eq_ringInverse equiv)
  rw [hFunction]
  exact hComposite

/-- Exact derivative of inversion at a product-throat holonomy fiber. -/
def productThroatCommonGraphInverseOperationFDeriv
    (data : ProductThroatSpectralData) (fold : Fold) (reference : CircleTwist)
    (holonomy : ℝ) :
    (ProductThroatCommonGraphDomain data fold reference →L[Complex]
      ProductThroatHeatHilbert data) →L[Complex]
        (ProductThroatHeatHilbert data →L[Complex]
          ProductThroatCommonGraphDomain data fold reference) :=
  continuousLinearMapInverseFDeriv
    (productThroatCommonGraphDiracContinuousLinearEquiv_real
      data fold reference holonomy)

@[simp] theorem productThroatCommonGraphInverseOperationFDeriv_apply
    (data : ProductThroatSpectralData) (fold : Fold) (reference : CircleTwist)
    (holonomy : ℝ)
    (variation : ProductThroatCommonGraphDomain data fold reference →L[Complex]
      ProductThroatHeatHilbert data) :
    productThroatCommonGraphInverseOperationFDeriv
        data fold reference holonomy variation =
      -(productThroatCommonGraphDiracInverseCLM
          data fold reference holonomy).comp
        (variation.comp
          (productThroatCommonGraphDiracInverseCLM
            data fold reference holonomy)) := by
  rw [productThroatCommonGraphDiracInverse_eq_equiv_symm]
  exact continuousLinearMapInverseFDeriv_apply _ _

/-- The exact inversion derivative transported to the canonical real structures. -/
def productThroatCommonGraphInverseOperationRealFDeriv
    (data : ProductThroatSpectralData) (fold : Fold) (reference : CircleTwist)
    (holonomy : ℝ) :
    ProductThroatCommonGraphOperatorReal data fold reference →L[ℝ]
      ProductThroatCommonGraphInverseOperatorReal data fold reference where
  toFun := productThroatCommonGraphInverseOperationFDeriv
    data fold reference holonomy
  map_add' := by
    intro first second
    unfold ProductThroatCommonGraphOperatorReal
      ProductThroatCommonGraphInverseOperatorReal
    exact (productThroatCommonGraphInverseOperationFDeriv
      data fold reference holonomy).map_add first second
  map_smul' := by
    intro scalar variation
    unfold ProductThroatCommonGraphOperatorReal
      ProductThroatCommonGraphInverseOperatorReal
    change
      productThroatCommonGraphInverseOperationFDeriv data fold reference holonomy
          ((scalar : Complex) •
            (show ProductThroatCommonGraphDomain data fold reference →L[Complex]
              ProductThroatHeatHilbert data from variation)) =
        (scalar : Complex) •
          productThroatCommonGraphInverseOperationFDeriv data fold reference holonomy
            (show ProductThroatCommonGraphDomain data fold reference →L[Complex]
              ProductThroatHeatHilbert data from variation)
    exact (productThroatCommonGraphInverseOperationFDeriv
      data fold reference holonomy).map_smul _ _
  cont := (productThroatCommonGraphInverseOperationFDeriv
    data fold reference holonomy).continuous

theorem productThroatCommonGraph_inverseOperation_hasFDerivAt
    (data : ProductThroatSpectralData) (fold : Fold) (reference : CircleTwist)
    (holonomy : ℝ) :
    HasFDerivAt ContinuousLinearMap.inverse
      (productThroatCommonGraphInverseOperationFDeriv
        data fold reference holonomy)
      (productThroatCommonGraphDiracCLM
        data fold reference holonomy) := by
  let equiv := productThroatCommonGraphDiracContinuousLinearEquiv_real
    data fold reference holonomy
  let mode : ProductThroatHeatMode data :=
    (⟨0, ⟨0, sphere_multiplicity_positive data 0⟩⟩, 0)
  have hBasis : productThroatHeatBasis data mode ≠ 0 := by
    intro hZero
    have hNorm := productThroatHeatBasis_norm data mode
    rw [hZero, norm_zero] at hNorm
    norm_num at hNorm
  letI : Nontrivial (ProductThroatHeatHilbert data) :=
    ⟨⟨productThroatHeatBasis data mode, 0, hBasis⟩⟩
  letI : Nontrivial (ProductThroatCommonGraphDomain data fold reference) :=
    equiv.toEquiv.nontrivial
  exact continuousLinearMap_inverse_hasFDerivAt equiv

/-- Inversion between the two explicit real operator structures. -/
def productThroatCommonGraphInverseOperationReal
    (data : ProductThroatSpectralData) (fold : Fold) (reference : CircleTwist)
    (operator : ProductThroatCommonGraphOperatorReal data fold reference) :
    ProductThroatCommonGraphInverseOperatorReal data fold reference :=
  ContinuousLinearMap.inverse
    (show ProductThroatCommonGraphDomain data fold reference →L[Complex]
      ProductThroatHeatHilbert data from operator)

/-- Real Fréchet derivative of inversion at every common-graph fiber. -/
theorem productThroatCommonGraph_inverseOperation_hasFDerivAt_real
    (data : ProductThroatSpectralData) (fold : Fold) (reference : CircleTwist)
    (holonomy : ℝ) :
    HasFDerivAt
      (productThroatCommonGraphInverseOperationReal data fold reference)
      (productThroatCommonGraphInverseOperationRealFDeriv
        data fold reference holonomy)
      (productThroatCommonGraphDiracReal
        data fold reference holonomy) := by
  let equiv := productThroatCommonGraphDiracContinuousLinearEquiv_real
    data fold reference holonomy
  have hComplex : ContDiffAt Complex 1 ContinuousLinearMap.inverse
      (equiv : ProductThroatCommonGraphDomain data fold reference →L[Complex]
        ProductThroatHeatHilbert data) :=
    contDiffAt_map_inverse equiv
  rcases contDiffAt_one_iff.mp hComplex with
    ⟨derivative, neighborhood, hNeighborhood, _, hHasDerivative⟩
  have hAt := hHasDerivative
    (equiv : ProductThroatCommonGraphDomain data fold reference →L[Complex]
      ProductThroatHeatHilbert data) (mem_of_mem_nhds hNeighborhood)
  have hExact := productThroatCommonGraph_inverseOperation_hasFDerivAt
    data fold reference holonomy
  have hDerivative : derivative
      (equiv : ProductThroatCommonGraphDomain data fold reference →L[Complex]
        ProductThroatHeatHilbert data) =
      productThroatCommonGraphInverseOperationFDeriv
        data fold reference holonomy :=
    hAt.unique hExact
  have hReal := hAt.restrictScalars ℝ
  rw [hDerivative] at hReal
  convert hReal using 1 <;>
    rfl

/-- Exact real derivative of the inverse common-graph holonomy family. -/
theorem productThroatCommonGraphDiracInverse_hasDerivAt
    (data : ProductThroatSpectralData) (fold : Fold) (reference : CircleTwist)
    (holonomy : ℝ) :
    HasDerivAt
      (productThroatCommonGraphDiracInverseCLM data fold reference)
      (productThroatCommonGraphInverseOperationRealFDeriv
        data fold reference holonomy
        (productThroatCommonGraphDiracDerivativeReal
          data fold reference holonomy))
      holonomy := by
  have hChain :=
    (productThroatCommonGraph_inverseOperation_hasFDerivAt_real
      data fold reference holonomy).comp holonomy
      (productThroatCommonGraphDirac_hasDerivAt
        data fold reference holonomy)
  have hDeriv := hChain.hasDerivAt
  have hValue :
      ((productThroatCommonGraphInverseOperationRealFDeriv
          data fold reference holonomy).comp
        (ContinuousLinearMap.toSpanSingleton ℝ
          (productThroatCommonGraphDiracDerivativeReal
            data fold reference holonomy))) 1 =
        productThroatCommonGraphInverseOperationRealFDeriv
          data fold reference holonomy
          (productThroatCommonGraphDiracDerivativeReal
            data fold reference holonomy) := by
    rw [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply_one]
  convert hDeriv using 1
  · rfl
  · funext parameter
    rfl
  · exact hValue.symm

/-- The chain rule in the explicit form `d(A⁻¹) = -A⁻¹ A' A⁻¹`. -/
theorem productThroatCommonGraphDiracInverse_hasDerivAt_explicit
    (data : ProductThroatSpectralData) (fold : Fold) (reference : CircleTwist)
    (holonomy : ℝ) :
    HasDerivAt
      (productThroatCommonGraphDiracInverseCLM data fold reference)
      (-(productThroatCommonGraphDiracInverseCLM
          data fold reference holonomy).comp
        ((productThroatCommonGraphDiracDerivativeCLM
          data fold reference holonomy).comp
          (productThroatCommonGraphDiracInverseCLM
            data fold reference holonomy)))
      holonomy := by
  simpa [productThroatCommonGraphInverseOperationRealFDeriv,
    productThroatCommonGraphDiracDerivativeReal] using
      (productThroatCommonGraphDiracInverse_hasDerivAt
        data fold reference holonomy)

/-- Explicit derivative family of the inverse common-graph operators. -/
def productThroatCommonGraphDiracInverseDerivative
    (data : ProductThroatSpectralData) (fold : Fold) (reference : CircleTwist)
    (holonomy : ℝ) :
    ProductThroatCommonGraphInverseOperatorReal data fold reference :=
  -(productThroatCommonGraphDiracInverseCLM
      data fold reference holonomy).comp
    ((productThroatCommonGraphDiracDerivativeCLM
      data fold reference holonomy).comp
      (productThroatCommonGraphDiracInverseCLM
        data fold reference holonomy))

theorem productThroatCommonGraphDiracInverseDerivative_continuous
    (data : ProductThroatSpectralData) (fold : Fold) (reference : CircleTwist) :
    Continuous
      (productThroatCommonGraphDiracInverseDerivative data fold reference) := by
  have hInverse : Continuous
      (fun holonomy =>
        (productThroatCommonGraphDiracInverseCLM data fold reference holonomy :
          ProductThroatHeatHilbert data →L[Complex]
            ProductThroatCommonGraphDomain data fold reference)) :=
    productThroatCommonGraphDiracInverse_continuous data fold reference
  have hForwardDerivative : Continuous
      (fun holonomy =>
        (productThroatCommonGraphDiracDerivativeCLM data fold reference holonomy :
          ProductThroatCommonGraphDomain data fold reference →L[Complex]
            ProductThroatHeatHilbert data)) := by
    apply (show LipschitzWith
      ⟨(productThroatDiracGap data)⁻¹,
        inv_nonneg.mpr (productThroatDiracGap_positive data).le⟩
      (fun holonomy => productThroatCommonGraphDiracDerivativeCLM
        data fold reference holonomy) from ?_).continuous
    apply LipschitzWith.of_dist_le_mul
    intro first second
    simp only [dist_eq_norm, Real.norm_eq_abs]
    change ‖productThroatCommonGraphDiracDerivativeCLM
        data fold reference first -
        productThroatCommonGraphDiracDerivativeCLM
          data fold reference second‖ ≤
      (productThroatDiracGap data)⁻¹ * |first - second|
    simpa [abs_sub_comm] using
      (productThroatCommonGraphDiracDerivative_sub_norm_le
        data fold reference second first)
  have hInnerOperator : Continuous
      (fun holonomy =>
        (ContinuousLinearMap.compL Complex
          (ProductThroatHeatHilbert data)
          (ProductThroatCommonGraphDomain data fold reference)
          (ProductThroatHeatHilbert data))
          (productThroatCommonGraphDiracDerivativeCLM
            data fold reference holonomy)) :=
    (ContinuousLinearMap.compL Complex
      (ProductThroatHeatHilbert data)
      (ProductThroatCommonGraphDomain data fold reference)
      (ProductThroatHeatHilbert data)).continuous.comp hForwardDerivative
  have hInner : Continuous
      (fun holonomy =>
        (productThroatCommonGraphDiracDerivativeCLM
          data fold reference holonomy).comp
          (productThroatCommonGraphDiracInverseCLM
            data fold reference holonomy)) := by
    simpa only [ContinuousLinearMap.compL_apply] using
      hInnerOperator.clm_apply hInverse
  have hOuterOperator : Continuous
      (fun holonomy =>
        (ContinuousLinearMap.compL Complex
          (ProductThroatHeatHilbert data)
          (ProductThroatHeatHilbert data)
          (ProductThroatCommonGraphDomain data fold reference))
          (productThroatCommonGraphDiracInverseCLM
            data fold reference holonomy)) :=
    (ContinuousLinearMap.compL Complex
      (ProductThroatHeatHilbert data)
      (ProductThroatHeatHilbert data)
      (ProductThroatCommonGraphDomain data fold reference)).continuous.comp hInverse
  unfold productThroatCommonGraphDiracInverseDerivative
  exact (hOuterOperator.clm_apply hInner).neg

theorem productThroatCommonGraphDiracDerivativeCLM_norm_le_one
    (data : ProductThroatSpectralData) (fold : Fold) (reference : CircleTwist)
    (holonomy : ℝ) :
    ‖productThroatCommonGraphDiracDerivativeCLM
      data fold reference holonomy‖ ≤ 1 := by
  calc
    _ ≤ ‖productThroatDiracHolonomyDerivativeOperator data fold holonomy‖ *
        ‖productThroatCommonGraphFstCLM data fold reference‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * 1 := mul_le_mul
      (productThroatDiracHolonomyDerivativeOperator_norm_le
        data fold holonomy)
      (productThroatCommonGraphFstCLM_norm_le data fold reference)
      (norm_nonneg (productThroatCommonGraphFstCLM data fold reference))
      zero_le_one
    _ = 1 := one_mul 1

theorem productThroatCommonGraphDiracInverseDerivative_norm_isBoundedUnder
    (data : ProductThroatSpectralData) (fold : Fold) (reference : CircleTwist)
    (holonomy : ℝ) :
    (nhds holonomy).IsBoundedUnder (· ≤ ·)
      (fun parameter =>
        ‖productThroatCommonGraphDiracInverseDerivative
          data fold reference parameter‖) :=
  (productThroatCommonGraphDiracInverseDerivative_continuous
    data fold reference).continuousAt.norm.isBoundedUnder_le

@[simp] theorem productThroatCommonGraphDiracInverse_deriv
    (data : ProductThroatSpectralData) (fold : Fold) (reference : CircleTwist)
    (holonomy : ℝ) :
    deriv (productThroatCommonGraphDiracInverseCLM data fold reference) holonomy =
      productThroatCommonGraphDiracInverseDerivative
        data fold reference holonomy :=
  (productThroatCommonGraphDiracInverse_hasDerivAt_explicit
    data fold reference holonomy).deriv

/-- `C¹` regularity certified by the explicit continuous derivative family. -/
theorem productThroatCommonGraphDiracInverse_contDiff_one_explicit
    (data : ProductThroatSpectralData) (fold : Fold) (reference : CircleTwist) :
    ContDiff ℝ 1
      (productThroatCommonGraphDiracInverseCLM data fold reference) := by
  rw [contDiff_one_iff_deriv]
  constructor
  · intro holonomy
    exact (productThroatCommonGraphDiracInverse_hasDerivAt_explicit
      data fold reference holonomy).differentiableAt
  · have hDeriv :
        deriv (productThroatCommonGraphDiracInverseCLM data fold reference) =
          productThroatCommonGraphDiracInverseDerivative
            data fold reference := by
      funext holonomy
      exact productThroatCommonGraphDiracInverse_deriv
        data fold reference holonomy
    exact hDeriv.symm ▸
      productThroatCommonGraphDiracInverseDerivative_continuous
        data fold reference

end


end P0EFTJanusProductThroatHolonomyGraphInverseDerivative4D
end JanusFormal
