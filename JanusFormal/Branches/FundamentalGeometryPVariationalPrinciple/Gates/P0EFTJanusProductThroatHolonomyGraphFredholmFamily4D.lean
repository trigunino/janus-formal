import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProductThroatHolonomyGraphFamily4D

/-!
# Fredholm fibers of the common graph-domain holonomy family

At every admissible circle twist, the common graph-domain family is exactly
the corresponding maximal unbounded product Dirac operator after canonical
domain rebasing.  The strict sphere gap then gives bijectivity, closed full
range, zero kernel and Fredholm index zero for every fiber.
-/

namespace JanusFormal
namespace P0EFTJanusProductThroatHolonomyGraphFredholmFamily4D

set_option autoImplicit false

noncomputable section

open Set
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProductThroatHeatOperator4D
open P0EFTJanusProductThroatUnboundedDirac4D
open P0EFTJanusProductThroatUnboundedDiracFredholm4D
open P0EFTJanusProductThroatHolonomyCommonDomain4D
open P0EFTJanusProductThroatHolonomyDerivative4D
open P0EFTJanusProductThroatHolonomyOperatorDifferentiable4D
open P0EFTJanusProductThroatHolonomyGraphFamily4D

/-- Recover the reference maximal-domain vector from a graph vector. -/
def productThroatCommonGraphDomainState
    (data : ProductThroatSpectralData) (fold : Fold) (reference : CircleTwist)
    (state : ProductThroatCommonGraphDomain data fold reference) :
    (productThroatUnboundedDirac data fold reference).domain :=
  ⟨state.1.1, LinearPMap.mem_domain_of_mem_graph state.property⟩

/-- Canonical graph vector associated with a maximal-domain vector. -/
def productThroatCommonGraphStateOfDomain
    (data : ProductThroatSpectralData) (fold : Fold) (reference : CircleTwist)
    (state : (productThroatUnboundedDirac data fold reference).domain) :
    ProductThroatCommonGraphDomain data fold reference :=
  ⟨(state.1, productThroatUnboundedDirac data fold reference state),
    (productThroatUnboundedDirac data fold reference).mem_graph state⟩

@[simp] theorem productThroatCommonGraphDomainState_stateOfDomain
    (data : ProductThroatSpectralData) (fold : Fold) (reference : CircleTwist)
    (state : (productThroatUnboundedDirac data fold reference).domain) :
    productThroatCommonGraphDomainState data fold reference
      (productThroatCommonGraphStateOfDomain data fold reference state) = state := by
  apply Subtype.ext
  rfl

@[simp] theorem productThroatCommonGraphStateOfDomain_domainState
    (data : ProductThroatSpectralData) (fold : Fold) (reference : CircleTwist)
    (state : ProductThroatCommonGraphDomain data fold reference) :
    productThroatCommonGraphStateOfDomain data fold reference
      (productThroatCommonGraphDomainState data fold reference state) = state := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact (productThroatUnboundedDirac data fold reference).mem_graph_snd_inj'
      ((productThroatUnboundedDirac data fold reference).mem_graph
        (productThroatCommonGraphDomainState data fold reference state))
      state.property rfl

theorem productThroatCommonGraphDirac_on_domain_at_twist
    (data : ProductThroatSpectralData) (fold : Fold)
    (reference target : CircleTwist)
    (state : (productThroatUnboundedDirac data fold reference).domain) :
    productThroatCommonGraphDiracCLM data fold reference target.value
        (productThroatCommonGraphStateOfDomain data fold reference state) =
      productThroatUnboundedDirac data fold target
        (productThroatDiracRebaseDomain data fold reference target state) := by
  ext mode
  change (productThroatUnboundedDirac data fold reference state) mode +
      ((productThroatDiracEigenvalueAt data fold target.value mode -
        productThroatDiracEigenvalueAt data fold reference.value mode : ℝ) : Complex) *
          state.1 mode =
    (productThroatUnboundedDirac data fold target
      (productThroatDiracRebaseDomain data fold reference target state)) mode
  rw [productThroatUnboundedDirac_apply, productThroatUnboundedDirac_apply,
    productThroatDiracEigenvalueAt_twist, productThroatDiracEigenvalueAt_twist]
  rw [show (productThroatDiracRebaseDomain data fold reference target state :
      ProductThroatHeatHilbert data) mode = state.1 mode by rfl]
  push_cast
  ring

/-- Exact identification of every admissible fiber with the maximal Dirac operator. -/
theorem productThroatCommonGraphDirac_at_twist
    (data : ProductThroatSpectralData) (fold : Fold)
    (reference target : CircleTwist)
    (state : ProductThroatCommonGraphDomain data fold reference) :
    productThroatCommonGraphDiracCLM data fold reference target.value state =
      productThroatUnboundedDirac data fold target
        (productThroatDiracRebaseDomain data fold reference target
          (productThroatCommonGraphDomainState data fold reference state)) := by
  rw [← productThroatCommonGraphStateOfDomain_domainState
    data fold reference state]
  simpa using productThroatCommonGraphDirac_on_domain_at_twist
    data fold reference target
      (productThroatCommonGraphDomainState data fold reference state)

theorem productThroatCommonGraphDirac_injective
    (data : ProductThroatSpectralData) (fold : Fold)
    (reference target : CircleTwist) :
    Function.Injective
      (productThroatCommonGraphDiracCLM data fold reference target.value) := by
  intro first second hEqual
  rw [productThroatCommonGraphDirac_at_twist,
    productThroatCommonGraphDirac_at_twist] at hEqual
  have hRebased := productThroatUnboundedDirac_injective data fold target hEqual
  have hDomain : productThroatCommonGraphDomainState data fold reference first =
      productThroatCommonGraphDomainState data fold reference second := by
    apply Subtype.ext
    exact congrArg
      (fun state : (productThroatUnboundedDirac data fold target).domain =>
        (state : ProductThroatHeatHilbert data)) hRebased
  rw [← productThroatCommonGraphStateOfDomain_domainState
      data fold reference first,
    ← productThroatCommonGraphStateOfDomain_domainState
      data fold reference second, hDomain]

theorem productThroatCommonGraphDirac_surjective
    (data : ProductThroatSpectralData) (fold : Fold)
    (reference target : CircleTwist) :
    Function.Surjective
      (productThroatCommonGraphDiracCLM data fold reference target.value) := by
  intro output
  let targetState := productThroatDiracInverse data fold target output
  let referenceState := productThroatDiracRebaseDomain
    data fold target reference targetState
  let graphState := productThroatCommonGraphStateOfDomain
    data fold reference referenceState
  refine ⟨graphState, ?_⟩
  rw [show graphState = productThroatCommonGraphStateOfDomain
      data fold reference referenceState by rfl,
    productThroatCommonGraphDirac_on_domain_at_twist]
  have hRebase : productThroatDiracRebaseDomain data fold reference target
      referenceState = targetState := by
    apply Subtype.ext
    rfl
  rw [hRebase]
  exact productThroatUnboundedDirac_rightInverse data fold target output

theorem productThroatCommonGraphDirac_ker_eq_bot
    (data : ProductThroatSpectralData) (fold : Fold)
    (reference target : CircleTwist) :
    LinearMap.ker
      (productThroatCommonGraphDiracCLM data fold reference target.value).toLinearMap = ⊥ :=
  LinearMap.ker_eq_bot.mpr
    (productThroatCommonGraphDirac_injective data fold reference target)

theorem productThroatCommonGraphDirac_range_eq_top
    (data : ProductThroatSpectralData) (fold : Fold)
    (reference target : CircleTwist) :
    LinearMap.range
      (productThroatCommonGraphDiracCLM data fold reference target.value).toLinearMap = ⊤ :=
  LinearMap.range_eq_top.mpr
    (productThroatCommonGraphDirac_surjective data fold reference target)

theorem productThroatCommonGraphDirac_range_isClosed
    (data : ProductThroatSpectralData) (fold : Fold)
    (reference target : CircleTwist) :
    IsClosed
      (LinearMap.range
        (productThroatCommonGraphDiracCLM data fold reference target.value).toLinearMap :
          Set (ProductThroatHeatHilbert data)) := by
  rw [productThroatCommonGraphDirac_range_eq_top data fold reference target]
  exact isClosed_univ

abbrev ProductThroatCommonGraphCokernel
    (data : ProductThroatSpectralData) (fold : Fold)
    (reference target : CircleTwist) :=
  ProductThroatHeatHilbert data ⧸ LinearMap.range
    (productThroatCommonGraphDiracCLM data fold reference target.value).toLinearMap

theorem productThroatCommonGraphDirac_fredholm_criterion
    (data : ProductThroatSpectralData) (fold : Fold)
    (reference target : CircleTwist) :
    IsClosed
        (LinearMap.range
          (productThroatCommonGraphDiracCLM data fold reference target.value).toLinearMap :
            Set (ProductThroatHeatHilbert data)) ∧
      FiniteDimensional Complex
        (LinearMap.ker
          (productThroatCommonGraphDiracCLM data fold reference target.value).toLinearMap) ∧
      FiniteDimensional Complex
        (ProductThroatCommonGraphCokernel data fold reference target) := by
  refine ⟨productThroatCommonGraphDirac_range_isClosed
    data fold reference target, ?_, ?_⟩
  · rw [productThroatCommonGraphDirac_ker_eq_bot data fold reference target]
    infer_instance
  · unfold ProductThroatCommonGraphCokernel
    rw [productThroatCommonGraphDirac_range_eq_top data fold reference target]
    infer_instance

def productThroatCommonGraphDiracIndex
    (data : ProductThroatSpectralData) (fold : Fold)
    (reference target : CircleTwist) : Int :=
  (productThroatCommonGraphDiracCLM
    data fold reference target.value).toLinearMap.index

theorem productThroatCommonGraphDiracIndex_zero
    (data : ProductThroatSpectralData) (fold : Fold)
    (reference target : CircleTwist) :
    productThroatCommonGraphDiracIndex data fold reference target = 0 := by
  unfold productThroatCommonGraphDiracIndex
  rw [LinearMap.index_of_surjective
      (productThroatCommonGraphDirac_surjective data fold reference target),
    productThroatCommonGraphDirac_ker_eq_bot data fold reference target]
  simp

end

end P0EFTJanusProductThroatHolonomyGraphFredholmFamily4D
end JanusFormal
