import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProductThroatHolonomyOperatorDifferentiable4D
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.RestrictScalars

/-!
# Common graph-domain holonomy family on the product throat

At fixed product geometry and fold, the closed graph at one reference twist is
used as a common Banach domain.  The real-holonomy family is the reference
graph operator plus the bounded diagonal perturbation.  It is differentiable
in operator norm, with Lipschitz derivative, hence `C¹`.
-/

namespace JanusFormal
namespace P0EFTJanusProductThroatHolonomyGraphFamily4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProductThroatHeatOperator4D
open P0EFTJanusProductThroatUnboundedDirac4D
open P0EFTJanusProductThroatUnboundedDiracFredholm4D
open P0EFTJanusProductThroatHolonomyDerivative4D
open P0EFTJanusProductThroatHolonomyDerivativeLipschitz4D
open P0EFTJanusProductThroatHolonomyOperatorDifferentiable4D
open Asymptotics Filter
open scoped Topology

/-- The closed graph at a reference twist, carrying its inherited graph norm. -/
abbrev ProductThroatCommonGraphDomain
    (data : ProductThroatSpectralData) (fold : Fold) (reference : CircleTwist) :=
  (productThroatUnboundedDirac data fold reference).graph

noncomputable instance productThroatCommonGraphDomainCompleteSpace
    (data : ProductThroatSpectralData) (fold : Fold) (reference : CircleTwist) :
    CompleteSpace (ProductThroatCommonGraphDomain data fold reference) := by
  letI : IsClosed
      ((productThroatUnboundedDirac data fold reference).graph :
        Set (ProductThroatHeatHilbert data × ProductThroatHeatHilbert data)) :=
    (productThroatUnboundedDirac_isSelfAdjoint data fold reference).isClosed
  infer_instance

/-- Continuous inclusion of the common graph domain into the ambient Hilbert space. -/
def productThroatCommonGraphFstCLM
    (data : ProductThroatSpectralData) (fold : Fold) (reference : CircleTwist) :
    ProductThroatCommonGraphDomain data fold reference →L[Complex]
      ProductThroatHeatHilbert data :=
  (ContinuousLinearMap.fst Complex
    (ProductThroatHeatHilbert data) (ProductThroatHeatHilbert data)).comp
      ((productThroatUnboundedDirac data fold reference).graph.subtypeL)

/-- Reference Dirac operator, bounded on its graph-norm domain. -/
def productThroatCommonGraphReferenceDiracCLM
    (data : ProductThroatSpectralData) (fold : Fold) (reference : CircleTwist) :
    ProductThroatCommonGraphDomain data fold reference →L[Complex]
      ProductThroatHeatHilbert data :=
  (ContinuousLinearMap.snd Complex
    (ProductThroatHeatHilbert data) (ProductThroatHeatHilbert data)).comp
      ((productThroatUnboundedDirac data fold reference).graph.subtypeL)

@[simp] theorem productThroatCommonGraphFstCLM_apply
    (data : ProductThroatSpectralData) (fold : Fold) (reference : CircleTwist)
    (state : ProductThroatCommonGraphDomain data fold reference) :
    productThroatCommonGraphFstCLM data fold reference state = state.1.1 :=
  rfl

@[simp] theorem productThroatCommonGraphReferenceDiracCLM_apply
    (data : ProductThroatSpectralData) (fold : Fold) (reference : CircleTwist)
    (state : ProductThroatCommonGraphDomain data fold reference) :
    productThroatCommonGraphReferenceDiracCLM data fold reference state = state.1.2 :=
  rfl

theorem productThroatCommonGraphFstCLM_norm_le
    (data : ProductThroatSpectralData) (fold : Fold) (reference : CircleTwist) :
    ‖productThroatCommonGraphFstCLM data fold reference‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound
    (productThroatCommonGraphFstCLM data fold reference) zero_le_one
  intro state
  simpa using norm_fst_le state.1

/-- The real-holonomy Dirac family on one fixed common graph domain. -/
def productThroatCommonGraphDiracCLM
    (data : ProductThroatSpectralData) (fold : Fold) (reference : CircleTwist)
    (holonomy : ℝ) :
    ProductThroatCommonGraphDomain data fold reference →L[Complex]
      ProductThroatHeatHilbert data :=
  productThroatCommonGraphReferenceDiracCLM data fold reference +
    (productThroatDiracHolonomyPerturbationOperator
      data fold reference.value holonomy).comp
        (productThroatCommonGraphFstCLM data fold reference)

/-- Exact derivative on the common graph domain. -/
def productThroatCommonGraphDiracDerivativeCLM
    (data : ProductThroatSpectralData) (fold : Fold) (reference : CircleTwist)
    (holonomy : ℝ) :
    ProductThroatCommonGraphDomain data fold reference →L[Complex]
      ProductThroatHeatHilbert data :=
  (productThroatDiracHolonomyDerivativeOperator data fold holonomy).comp
    (productThroatCommonGraphFstCLM data fold reference)

@[simp] theorem productThroatCommonGraphDiracCLM_apply
    (data : ProductThroatSpectralData) (fold : Fold) (reference : CircleTwist)
    (holonomy : ℝ) (state : ProductThroatCommonGraphDomain data fold reference) :
    productThroatCommonGraphDiracCLM data fold reference holonomy state =
      state.1.2 + productThroatDiracHolonomyPerturbationOperator
        data fold reference.value holonomy state.1.1 :=
  rfl

@[simp] theorem productThroatCommonGraphDiracDerivativeCLM_apply
    (data : ProductThroatSpectralData) (fold : Fold) (reference : CircleTwist)
    (holonomy : ℝ) (state : ProductThroatCommonGraphDomain data fold reference) :
    productThroatCommonGraphDiracDerivativeCLM data fold reference holonomy state =
      productThroatDiracHolonomyDerivativeOperator data fold holonomy state.1.1 :=
  rfl

/-- Complex graph operators viewed as a real normed space of parameter variations. -/
def ProductThroatCommonGraphOperatorReal
    (data : ProductThroatSpectralData) (fold : Fold) (reference : CircleTwist) :=
  RestrictScalars ℝ Complex
    (ProductThroatCommonGraphDomain data fold reference →L[Complex]
      ProductThroatHeatHilbert data)

instance productThroatCommonGraphOperatorRealNormedAddCommGroup
    (data : ProductThroatSpectralData) (fold : Fold) (reference : CircleTwist) :
    NormedAddCommGroup (ProductThroatCommonGraphOperatorReal data fold reference) := by
  unfold ProductThroatCommonGraphOperatorReal
  infer_instance

instance productThroatCommonGraphOperatorRealModule
    (data : ProductThroatSpectralData) (fold : Fold) (reference : CircleTwist) :
    Module ℝ (ProductThroatCommonGraphOperatorReal data fold reference) :=
  RestrictScalars.module ℝ Complex
    (ProductThroatCommonGraphDomain data fold reference →L[Complex]
      ProductThroatHeatHilbert data)

instance productThroatCommonGraphOperatorRealNormedSpace
    (data : ProductThroatSpectralData) (fold : Fold) (reference : CircleTwist) :
    NormedSpace ℝ (ProductThroatCommonGraphOperatorReal data fold reference) :=
  RestrictScalars.normedSpace ℝ Complex
    (ProductThroatCommonGraphDomain data fold reference →L[Complex]
      ProductThroatHeatHilbert data)

def productThroatCommonGraphDiracReal
    (data : ProductThroatSpectralData) (fold : Fold) (reference : CircleTwist)
    (holonomy : ℝ) : ProductThroatCommonGraphOperatorReal data fold reference :=
  productThroatCommonGraphDiracCLM data fold reference holonomy

def productThroatCommonGraphDiracDerivativeReal
    (data : ProductThroatSpectralData) (fold : Fold) (reference : CircleTwist)
    (holonomy : ℝ) : ProductThroatCommonGraphOperatorReal data fold reference :=
  productThroatCommonGraphDiracDerivativeCLM data fold reference holonomy

theorem productThroatCommonGraphDirac_taylor_remainder_le
    (data : ProductThroatSpectralData) (fold : Fold) (reference : CircleTwist)
    (first second : ℝ) :
    ‖productThroatCommonGraphDiracReal data fold reference second -
        productThroatCommonGraphDiracReal data fold reference first -
        (second - first) •
          productThroatCommonGraphDiracDerivativeReal data fold reference first‖ ≤
      (productThroatDiracGap data)⁻¹ * |second - first| ^ 2 := by
  unfold productThroatCommonGraphDiracReal
    productThroatCommonGraphDiracDerivativeReal
    ProductThroatCommonGraphOperatorReal
  change ‖productThroatCommonGraphDiracCLM data fold reference second -
      productThroatCommonGraphDiracCLM data fold reference first -
      (second - first) •
        productThroatCommonGraphDiracDerivativeCLM data fold reference first‖ ≤ _
  calc
    _ = ‖(productThroatDiracHolonomyPerturbationOperator data fold reference.value second -
          productThroatDiracHolonomyPerturbationOperator data fold reference.value first -
          (second - first) •
            productThroatDiracHolonomyDerivativeOperator data fold first).comp
        (productThroatCommonGraphFstCLM data fold reference)‖ := by
      congr 1
      ext state
      simp [productThroatCommonGraphDiracCLM,
        productThroatCommonGraphDiracDerivativeCLM]
    _ ≤ ‖productThroatDiracHolonomyPerturbationOperator data fold reference.value second -
          productThroatDiracHolonomyPerturbationOperator data fold reference.value first -
          (second - first) •
            productThroatDiracHolonomyDerivativeOperator data fold first‖ *
        ‖productThroatCommonGraphFstCLM data fold reference‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ((productThroatDiracGap data)⁻¹ * |second - first| ^ 2) * 1 :=
      mul_le_mul
        (productThroatDiracHolonomyPerturbationOperator_taylor_remainder_le
          data fold reference.value first second)
        (productThroatCommonGraphFstCLM_norm_le data fold reference)
        (norm_nonneg (productThroatCommonGraphFstCLM data fold reference)) (mul_nonneg
          (inv_nonneg.mpr (productThroatDiracGap_positive data).le) (sq_nonneg _))
    _ = _ := mul_one _

theorem productThroatCommonGraphDirac_hasDerivAt
    (data : ProductThroatSpectralData) (fold : Fold) (reference : CircleTwist)
    (holonomy : ℝ) :
    HasDerivAt
      (fun parameter => productThroatCommonGraphDiracReal
        data fold reference parameter)
      (productThroatCommonGraphDiracDerivativeReal
        data fold reference holonomy)
      holonomy := by
  apply HasDerivAt.of_isLittleO
  have hBigO :
      (fun parameter =>
        productThroatCommonGraphDiracReal data fold reference parameter -
          productThroatCommonGraphDiracReal data fold reference holonomy -
          (parameter - holonomy) •
            productThroatCommonGraphDiracDerivativeReal data fold reference holonomy) =O[𝓝 holonomy]
        (fun parameter : ℝ => ‖parameter - holonomy‖ ^ 2) := by
    have hBound : IsBigOWith (productThroatDiracGap data)⁻¹ (𝓝 holonomy)
        (fun parameter =>
          productThroatCommonGraphDiracReal data fold reference parameter -
            productThroatCommonGraphDiracReal data fold reference holonomy -
            (parameter - holonomy) •
              productThroatCommonGraphDiracDerivativeReal data fold reference holonomy)
        (fun parameter : ℝ => ‖parameter - holonomy‖ ^ 2) := by
      apply IsBigOWith.of_bound
      filter_upwards with parameter
      simpa only [norm_pow, norm_norm, Real.norm_eq_abs, abs_abs] using
        (productThroatCommonGraphDirac_taylor_remainder_le
          data fold reference holonomy parameter)
    exact hBound.isBigO
  exact hBigO.trans_isLittleO
    (isLittleO_pow_sub_sub holonomy (by norm_num : 1 < 2))

theorem productThroatCommonGraphDiracDerivative_sub_norm_le
    (data : ProductThroatSpectralData) (fold : Fold) (reference : CircleTwist)
    (first second : ℝ) :
    ‖productThroatCommonGraphDiracDerivativeCLM data fold reference second -
        productThroatCommonGraphDiracDerivativeCLM data fold reference first‖ ≤
      (productThroatDiracGap data)⁻¹ * |second - first| := by
  calc
    _ = ‖(productThroatDiracHolonomyDerivativeOperator data fold second -
          productThroatDiracHolonomyDerivativeOperator data fold first).comp
        (productThroatCommonGraphFstCLM data fold reference)‖ := by
      rfl
    _ ≤ ‖productThroatDiracHolonomyDerivativeOperator data fold second -
          productThroatDiracHolonomyDerivativeOperator data fold first‖ *
        ‖productThroatCommonGraphFstCLM data fold reference‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ((productThroatDiracGap data)⁻¹ * |second - first|) * 1 :=
      mul_le_mul
        (productThroatDiracHolonomyDerivativeOperator_sub_norm_le
          data fold first second)
        (productThroatCommonGraphFstCLM_norm_le data fold reference)
        (norm_nonneg (productThroatCommonGraphFstCLM data fold reference)) (mul_nonneg
          (inv_nonneg.mpr (productThroatDiracGap_positive data).le) (abs_nonneg _))
    _ = _ := mul_one _

theorem productThroatCommonGraphDiracDerivative_lipschitz
    (data : ProductThroatSpectralData) (fold : Fold) (reference : CircleTwist) :
    LipschitzWith
      ⟨(productThroatDiracGap data)⁻¹,
        inv_nonneg.mpr (productThroatDiracGap_positive data).le⟩
      (productThroatCommonGraphDiracDerivativeReal data fold reference) := by
  apply LipschitzWith.of_dist_le_mul
  intro first second
  simp only [dist_eq_norm]
  unfold productThroatCommonGraphDiracDerivativeReal
    ProductThroatCommonGraphOperatorReal
  change ‖productThroatCommonGraphDiracDerivativeCLM data fold reference first -
      productThroatCommonGraphDiracDerivativeCLM data fold reference second‖ ≤
    (productThroatDiracGap data)⁻¹ * |first - second|
  simpa [abs_sub_comm] using
    productThroatCommonGraphDiracDerivative_sub_norm_le
      data fold reference second first

theorem productThroatCommonGraphDirac_contDiff_one
    (data : ProductThroatSpectralData) (fold : Fold) (reference : CircleTwist) :
    ContDiff ℝ 1 (productThroatCommonGraphDiracReal data fold reference) := by
  rw [contDiff_one_iff_deriv]
  constructor
  · intro holonomy
    exact (productThroatCommonGraphDirac_hasDerivAt
      data fold reference holonomy).differentiableAt
  · have hDeriv : deriv (productThroatCommonGraphDiracReal data fold reference) =
        productThroatCommonGraphDiracDerivativeReal data fold reference := by
      funext holonomy
      exact (productThroatCommonGraphDirac_hasDerivAt
        data fold reference holonomy).deriv
    convert (productThroatCommonGraphDiracDerivative_lipschitz
      data fold reference).continuous using 1
    exact hDeriv

end

end P0EFTJanusProductThroatHolonomyGraphFamily4D
end JanusFormal
