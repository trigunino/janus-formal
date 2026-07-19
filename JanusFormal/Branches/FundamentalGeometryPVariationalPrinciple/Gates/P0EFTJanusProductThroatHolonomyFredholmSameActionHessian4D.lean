import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProductThroatHolonomyGraphFredholmFamily4D
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-!
# Same-action Hessian for one product-throat holonomy fiber

At fixed product geometry, fold and admissible holonomy, the common graph-domain
Fredholm fiber defines its usual real quadratic Dirac action.  Formal
self-adjointness of the maximal diagonal Dirac operator identifies the genuine
second Frechet derivative of that same action with the unsymmetrized operator
pairing.  The fiber is already bijective and has index zero.

This is a fixed separated product-throat spectral result.  It does not identify
the spectral Hilbert space with the global Program-P field space, vary the
geometry or boundary data, or construct the global Janus Dirac operator.
-/

namespace JanusFormal
namespace P0EFTJanusProductThroatHolonomyFredholmSameActionHessian4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProductThroatHeatOperator4D
open P0EFTJanusProductThroatUnboundedDirac4D
open P0EFTJanusProductThroatHolonomyCommonDomain4D
open P0EFTJanusProductThroatHolonomyGraphFamily4D
open P0EFTJanusProductThroatHolonomyGraphFredholmFamily4D

local instance productThroatHeatHilbertRealInnerProductSpace
    (data : ProductThroatSpectralData) :
    InnerProductSpace Real (ProductThroatHeatHilbert data) :=
  InnerProductSpace.complexToReal

/-- The common graph-domain inclusion, viewed over the real scalars used by
the quadratic action. -/
def productThroatCommonGraphFstRealCLM
    (data : ProductThroatSpectralData) (fold : Fold) (reference : CircleTwist) :
    ProductThroatCommonGraphDomain data fold reference →L[Real]
      ProductThroatHeatHilbert data :=
  (productThroatCommonGraphFstCLM data fold reference).restrictScalars Real

/-- One admissible common-domain Dirac fiber, viewed as a real continuous
linear map without changing its complex-linear operator. -/
def productThroatCommonGraphDiracRealCLM
    (data : ProductThroatSpectralData) (fold : Fold)
    (reference target : CircleTwist) :
    ProductThroatCommonGraphDomain data fold reference →L[Real]
      ProductThroatHeatHilbert data :=
  (productThroatCommonGraphDiracCLM
    data fold reference target.value).restrictScalars Real

/-- Real Dirac pairing on the fixed common graph domain. -/
def productThroatCommonGraphDiracForm
    (data : ProductThroatSpectralData) (fold : Fold)
    (reference target : CircleTwist) :
    ProductThroatCommonGraphDomain data fold reference →L[Real]
      ProductThroatCommonGraphDomain data fold reference →L[Real] Real :=
  (innerSL Real).bilinearComp
    (productThroatCommonGraphFstRealCLM data fold reference)
    (productThroatCommonGraphDiracRealCLM data fold reference target)

@[simp]
theorem productThroatCommonGraphDiracForm_apply
    (data : ProductThroatSpectralData) (fold : Fold)
    (reference target : CircleTwist)
    (first second : ProductThroatCommonGraphDomain data fold reference) :
    productThroatCommonGraphDiracForm data fold reference target first second =
      inner Real
        (productThroatCommonGraphFstCLM data fold reference first)
        (productThroatCommonGraphDiracCLM
          data fold reference target.value second) :=
  rfl

/-- The admissible Dirac pairing is symmetric on the common graph domain.
This is derived from the already proved formal self-adjointness of the actual
maximal target operator, after canonical domain rebasing. -/
theorem productThroatCommonGraphDiracForm_comm
    (data : ProductThroatSpectralData) (fold : Fold)
    (reference target : CircleTwist)
    (first second : ProductThroatCommonGraphDomain data fold reference) :
    productThroatCommonGraphDiracForm data fold reference target first second =
      productThroatCommonGraphDiracForm data fold reference target second first := by
  let firstTarget := productThroatDiracRebaseDomain data fold reference target
    (productThroatCommonGraphDomainState data fold reference first)
  let secondTarget := productThroatDiracRebaseDomain data fold reference target
    (productThroatCommonGraphDomainState data fold reference second)
  have hFirstState :
      productThroatCommonGraphFstCLM data fold reference first =
        (firstTarget : ProductThroatHeatHilbert data) := by
    rfl
  have hSecondState :
      productThroatCommonGraphFstCLM data fold reference second =
        (secondTarget : ProductThroatHeatHilbert data) := by
    rfl
  have hFirstOperator :
      productThroatCommonGraphDiracCLM data fold reference target.value first =
        productThroatUnboundedDirac data fold target firstTarget := by
    exact productThroatCommonGraphDirac_at_twist
      data fold reference target first
  have hSecondOperator :
      productThroatCommonGraphDiracCLM data fold reference target.value second =
        productThroatUnboundedDirac data fold target secondTarget := by
    exact productThroatCommonGraphDirac_at_twist
      data fold reference target second
  have hAdjoint := productThroatUnboundedDirac_isFormalAdjoint_self
    data fold target firstTarget secondTarget
  rw [productThroatCommonGraphDiracForm_apply,
    productThroatCommonGraphDiracForm_apply, hFirstState, hSecondState,
    hFirstOperator, hSecondOperator]
  calc
    inner Real (firstTarget : ProductThroatHeatHilbert data)
        (productThroatUnboundedDirac data fold target secondTarget) =
      inner Real (productThroatUnboundedDirac data fold target firstTarget)
        (secondTarget : ProductThroatHeatHilbert data) := by
          simpa only [real_inner_eq_re_inner] using
            congrArg RCLike.re hAdjoint.symm
    _ = inner Real (secondTarget : ProductThroatHeatHilbert data)
        (productThroatUnboundedDirac data fold target firstTarget) :=
      real_inner_comm _ _

/-- Symmetric continuous Hessian associated with the fixed Dirac fiber. -/
def productThroatCommonGraphDiracHessian
    (data : ProductThroatSpectralData) (fold : Fold)
    (reference target : CircleTwist) :
    ProductThroatCommonGraphDomain data fold reference →L[Real]
      ProductThroatCommonGraphDomain data fold reference →L[Real] Real :=
  productThroatCommonGraphDiracForm data fold reference target

@[simp]
theorem productThroatCommonGraphDiracHessian_apply
    (data : ProductThroatSpectralData) (fold : Fold)
    (reference target : CircleTwist)
    (first second : ProductThroatCommonGraphDomain data fold reference) :
    productThroatCommonGraphDiracHessian data fold reference target first second =
      productThroatCommonGraphDiracForm
        data fold reference target first second :=
  rfl

theorem productThroatCommonGraphDiracHessian_comm
    (data : ProductThroatSpectralData) (fold : Fold)
    (reference target : CircleTwist)
    (first second : ProductThroatCommonGraphDomain data fold reference) :
    productThroatCommonGraphDiracHessian
        data fold reference target first second =
      productThroatCommonGraphDiracHessian
        data fold reference target second first := by
  exact productThroatCommonGraphDiracForm_comm
    data fold reference target first second

/-- At an admissible holonomy the symmetric Hessian is exactly the original
operator pairing, not a different averaged operator. -/
theorem productThroatCommonGraphDiracHessian_eq_form
    (data : ProductThroatSpectralData) (fold : Fold)
    (reference target : CircleTwist)
    (first second : ProductThroatCommonGraphDomain data fold reference) :
    productThroatCommonGraphDiracHessian
        data fold reference target first second =
      productThroatCommonGraphDiracForm
        data fold reference target first second := by
  rfl

/-- The real quadratic Dirac action of this very same Fredholm fiber. -/
def productThroatCommonGraphDiracQuadraticAction
    (data : ProductThroatSpectralData) (fold : Fold)
    (reference target : CircleTwist)
    (state : ProductThroatCommonGraphDomain data fold reference) : Real :=
  (1 / 2 : Real) *
    productThroatCommonGraphDiracHessian
      data fold reference target state state

@[simp]
theorem productThroatCommonGraphDiracQuadraticAction_eq_pairing
    (data : ProductThroatSpectralData) (fold : Fold)
    (reference target : CircleTwist)
    (state : ProductThroatCommonGraphDomain data fold reference) :
    productThroatCommonGraphDiracQuadraticAction
        data fold reference target state =
      (1 / 2 : Real) *
        inner Real
          (productThroatCommonGraphFstCLM data fold reference state)
          (productThroatCommonGraphDiracCLM
            data fold reference target.value state) := by
  rw [productThroatCommonGraphDiracQuadraticAction,
    productThroatCommonGraphDiracHessian_eq_form]
  rfl

private theorem symmetricQuadratic_hasFDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (bilinear : E →L[Real] E →L[Real] Real)
    (hSymmetric : ∀ first second, bilinear first second = bilinear second first)
    (point : E) :
    HasFDerivAt (fun state => (1 / 2 : Real) * bilinear state state)
      (bilinear point) point := by
  have hDiagonal :=
    (bilinear.hasFDerivAt (x := point)).clm_apply
      (hasFDerivAt_id (𝕜 := Real) point)
  have hHalf := hDiagonal.const_mul (1 / 2 : Real)
  apply hHalf.congr_fderiv
  ext direction
  change (1 / 2 : Real) *
      (bilinear point direction + bilinear direction point) =
    bilinear point direction
  rw [hSymmetric direction point]
  ring

/-- The displayed first Frechet derivative is proved from the actual action. -/
theorem productThroatCommonGraphDiracQuadraticAction_hasFDerivAt
    (data : ProductThroatSpectralData) (fold : Fold)
    (reference target : CircleTwist)
    (state : ProductThroatCommonGraphDomain data fold reference) :
    HasFDerivAt
      (productThroatCommonGraphDiracQuadraticAction
        data fold reference target)
      (productThroatCommonGraphDiracHessian
        data fold reference target state) state := by
  exact symmetricQuadratic_hasFDerivAt
    (productThroatCommonGraphDiracHessian data fold reference target)
    (productThroatCommonGraphDiracHessian_comm data fold reference target)
    state

theorem productThroatCommonGraphDiracQuadraticAction_fderiv
    (data : ProductThroatSpectralData) (fold : Fold)
    (reference target : CircleTwist)
    (state : ProductThroatCommonGraphDomain data fold reference) :
    fderiv Real
        (productThroatCommonGraphDiracQuadraticAction
          data fold reference target) state =
      productThroatCommonGraphDiracHessian
        data fold reference target state :=
  (productThroatCommonGraphDiracQuadraticAction_hasFDerivAt
    data fold reference target state).fderiv

/-- The genuine second Frechet derivative of the quadratic action is the
constant continuous Hessian on the same graph domain. -/
theorem productThroatCommonGraphDiracQuadraticAction_second_fderiv
    (data : ProductThroatSpectralData) (fold : Fold)
    (reference target : CircleTwist)
    (base : ProductThroatCommonGraphDomain data fold reference) :
    fderiv Real
        (fun state => fderiv Real
          (productThroatCommonGraphDiracQuadraticAction
            data fold reference target) state) base =
      productThroatCommonGraphDiracHessian
        data fold reference target := by
  rw [show (fun state => fderiv Real
      (productThroatCommonGraphDiracQuadraticAction
        data fold reference target) state) =
      (fun state => productThroatCommonGraphDiracHessian
        data fold reference target state) from by
    funext state
    exact productThroatCommonGraphDiracQuadraticAction_fderiv
      data fold reference target state]
  let hessian :
      ProductThroatCommonGraphDomain data fold reference →L[Real]
        ProductThroatCommonGraphDomain data fold reference →L[Real] Real :=
    productThroatCommonGraphDiracHessian data fold reference target
  change fderiv Real
      (hessian : ProductThroatCommonGraphDomain data fold reference →
        ProductThroatCommonGraphDomain data fold reference →L[Real] Real)
      base = hessian
  exact ContinuousLinearMap.fderiv
    (𝕜 := Real)
    (E := ProductThroatCommonGraphDomain data fold reference)
    (F := ProductThroatCommonGraphDomain data fold reference →L[Real] Real)
    hessian

/-- Exact same-action bridge: the pairing of the Fredholm fiber is the actual
mixed second Frechet derivative of its quadratic Dirac action. -/
theorem productThroatCommonGraphDirac_pairing_eq_sameActionHessian
    (data : ProductThroatSpectralData) (fold : Fold)
    (reference target : CircleTwist)
    (base first second :
      ProductThroatCommonGraphDomain data fold reference) :
    inner Real
        (productThroatCommonGraphFstCLM data fold reference first)
        (productThroatCommonGraphDiracCLM
          data fold reference target.value second) =
      fderiv Real
          (fun state => fderiv Real
            (productThroatCommonGraphDiracQuadraticAction
              data fold reference target) state) base first second := by
  rw [productThroatCommonGraphDiracQuadraticAction_second_fderiv,
    productThroatCommonGraphDiracHessian_eq_form]
  rfl

/-- The same fiber is simultaneously bijective, index-zero and the genuine
Hessian operator of the displayed action. -/
theorem productThroatCommonGraphDirac_fredholm_sameActionHessian
    (data : ProductThroatSpectralData) (fold : Fold)
    (reference target : CircleTwist) :
    Function.Bijective
        (productThroatCommonGraphDiracCLM
          data fold reference target.value) ∧
      productThroatCommonGraphDiracIndex data fold reference target = 0 ∧
      ∀ base first second :
          ProductThroatCommonGraphDomain data fold reference,
        inner Real
            (productThroatCommonGraphFstCLM data fold reference first)
            (productThroatCommonGraphDiracCLM
              data fold reference target.value second) =
          fderiv Real
              (fun state => fderiv Real
                (productThroatCommonGraphDiracQuadraticAction
                  data fold reference target) state) base first second := by
  refine ⟨⟨productThroatCommonGraphDirac_injective
      data fold reference target,
    productThroatCommonGraphDirac_surjective data fold reference target⟩,
    productThroatCommonGraphDiracIndex_zero data fold reference target, ?_⟩
  intro base first second
  exact productThroatCommonGraphDirac_pairing_eq_sameActionHessian
    data fold reference target base first second

end

end P0EFTJanusProductThroatHolonomyFredholmSameActionHessian4D
end JanusFormal
