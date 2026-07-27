import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Topology.Constructions

/-!
# Product of an unbounded operator with an identity block

This file supplies the analytic product construction needed to append an
exact completed energy Hessian to an already closed Fredholm operator.
-/

namespace JanusFormal
namespace P0EFTJanusLinearPMapProdIdentityFredholm4D

set_option autoImplicit false
noncomputable section

open Set
open scoped LinearPMap

variable
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace Real F] [CompleteSpace F]

private abbrev ProductHilbert := WithLp 2 (E × F)

private def prodIdentityDomain (operator : E →ₗ.[Real] E) :
    Submodule Real (ProductHilbert (E := E) (F := F)) :=
  (operator.domain.prod ⊤).comap
    (WithLp.linearEquiv 2 Real (E × F)).toLinearMap

private def prodDomainFst (operator : E →ₗ.[Real] E) :
    prodIdentityDomain (F := F) operator →ₗ[Real] operator.domain where
  toFun := fun state => ⟨(WithLp.ofLp state.1).1, state.2.1⟩
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

private def prodDomainSnd (operator : E →ₗ.[Real] E) :
    prodIdentityDomain (F := F) operator →ₗ[Real] F where
  toFun := fun state => (WithLp.ofLp state.1).2
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

/-- Direct product of a partially defined operator with the identity on a
second Hilbert factor. -/
def linearPMapProdIdentity (operator : E →ₗ.[Real] E) :
    ProductHilbert (E := E) (F := F) →ₗ.[Real]
      ProductHilbert (E := E) (F := F) where
  domain := prodIdentityDomain (F := F) operator
  toFun :=
    (WithLp.linearEquiv 2 Real (E × F)).symm.toLinearMap.comp
      ((operator.toFun.comp (prodDomainFst (F := F) operator)).prod
        (prodDomainSnd operator))

@[simp]
theorem linearPMapProdIdentity_domain
    (operator : E →ₗ.[Real] E) :
    (linearPMapProdIdentity (F := F) operator).domain =
      prodIdentityDomain (F := F) operator :=
  rfl

@[simp]
theorem linearPMapProdIdentity_apply
    (operator : E →ₗ.[Real] E)
    (state : (linearPMapProdIdentity (F := F) operator).domain) :
    linearPMapProdIdentity (F := F) operator state =
      WithLp.toLp 2
        (operator ⟨(WithLp.ofLp state.1).1, state.2.1⟩,
          (WithLp.ofLp state.1).2) :=
  rfl

theorem linearPMapProdIdentity_domain_dense
    (operator : E →ₗ.[Real] E)
    (hDense : Dense (operator.domain : Set E)) :
    Dense
      ((linearPMapProdIdentity (F := F) operator).domain :
        Set (ProductHilbert (E := E) (F := F))) := by
  let coreEmbedding : operator.domain × F →
      ProductHilbert (E := E) (F := F) :=
    fun state => WithLp.toLp 2 ((state.1 : E), state.2)
  have hProduct :
      DenseRange (fun state : operator.domain × F =>
        ((state.1 : E), state.2)) :=
    hDense.denseRange_val.prodMap denseRange_id
  have hEmbedding : DenseRange coreEmbedding := by
    exact
      (WithLp.homeomorphProd 2 E F).symm.surjective.denseRange.comp
        hProduct (WithLp.homeomorphProd 2 E F).symm.continuous
  rw [DenseRange] at hEmbedding
  apply hEmbedding.mono
  rintro state ⟨source, rfl⟩
  change (source.1 : E) ∈ operator.domain ∧ source.2 ∈ (⊤ : Submodule Real F)
  exact ⟨source.1.2, Submodule.mem_top⟩

theorem linearPMapProdIdentity_isFormalAdjoint
    (operator : E →ₗ.[Real] E)
    (hFormal : operator.IsFormalAdjoint operator) :
    (linearPMapProdIdentity (F := F) operator).IsFormalAdjoint
      (linearPMapProdIdentity (F := F) operator) := by
  intro first second
  rw [linearPMapProdIdentity_apply, linearPMapProdIdentity_apply,
    WithLp.prod_inner_apply, WithLp.prod_inner_apply]
  exact congrArg
    (fun value => value +
      inner Real (WithLp.ofLp first.1).2 (WithLp.ofLp second.1).2)
    (hFormal
      ⟨(WithLp.ofLp first.1).1, first.2.1⟩
      ⟨(WithLp.ofLp second.1).1, second.2.1⟩)

theorem linearPMapProdIdentity_selfAdjoint
    (operator : E →ₗ.[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator) :
    IsSelfAdjoint (linearPMapProdIdentity (F := F) operator) := by
  rw [LinearPMap.isSelfAdjoint_def]
  have hDense :=
    linearPMapProdIdentity_domain_dense (F := F) operator
      hSelfAdjoint.dense_domain
  have hOperatorAdjoint :
      operator.adjoint = operator :=
    LinearPMap.isSelfAdjoint_def.mp hSelfAdjoint
  have hOperatorFormal : operator.IsFormalAdjoint operator := by
    have hFormal :=
      LinearPMap.adjoint_isFormalAdjoint hSelfAdjoint.dense_domain
    rwa [hOperatorAdjoint] at hFormal
  have hFormal :=
    linearPMapProdIdentity_isFormalAdjoint (F := F) operator hOperatorFormal
  have hLe :
      linearPMapProdIdentity (F := F) operator ≤
        (linearPMapProdIdentity (F := F) operator).adjoint :=
    hFormal.le_adjoint hDense
  have hReverseDomain :
      (linearPMapProdIdentity (F := F) operator).adjoint.domain ≤
        (linearPMapProdIdentity (F := F) operator).domain := by
    intro state hState
    have hFirstAdjoint :
        (WithLp.ofLp state).1 ∈ operator.adjoint.domain := by
      apply LinearPMap.mem_adjoint_domain_of_exists
      refine
        ⟨(WithLp.ofLp
          ((linearPMapProdIdentity (F := F) operator).adjoint
            ⟨state, hState⟩)).1, ?_⟩
      intro first
      let lifted :
          (linearPMapProdIdentity (F := F) operator).domain :=
        ⟨WithLp.toLp 2 ((first : E), 0), by
          exact ⟨first.2, Submodule.mem_top⟩⟩
      have hAdjoint :=
        LinearPMap.adjoint_isFormalAdjoint hDense
          (T := linearPMapProdIdentity (F := F) operator)
          ⟨state, hState⟩ lifted
      simpa [lifted, linearPMapProdIdentity_apply,
        WithLp.prod_inner_apply] using hAdjoint
    have hFirst : (WithLp.ofLp state).1 ∈ operator.domain := by
      rw [← hOperatorAdjoint]
      exact hFirstAdjoint
    exact ⟨hFirst, Submodule.mem_top⟩
  have hDomain :
      (linearPMapProdIdentity (F := F) operator).domain =
        (linearPMapProdIdentity (F := F) operator).adjoint.domain :=
    le_antisymm hLe.1 hReverseDomain
  exact
    (LinearPMap.eq_of_le_of_domain_eq hLe hDomain).symm

theorem linearPMapProdIdentity_range
    (operator : E →ₗ.[Real] E) :
    LinearMap.range
        (linearPMapProdIdentity (F := F) operator).toFun =
      ((LinearMap.range operator.toFun).prod
        (⊤ : Submodule Real F)).map
          (WithLp.linearEquiv 2 Real (E × F)).symm.toLinearMap := by
  ext state
  constructor
  · rintro ⟨source, rfl⟩
    refine
      ⟨(operator ⟨(WithLp.ofLp source.1).1, source.2.1⟩,
          (WithLp.ofLp source.1).2), ?_, rfl⟩
    exact
      ⟨⟨⟨(WithLp.ofLp source.1).1, source.2.1⟩, rfl⟩,
        Submodule.mem_top⟩
  · rintro ⟨state, ⟨⟨source, hSource⟩, -, rfl⟩, rfl⟩
    refine
      ⟨⟨WithLp.toLp 2 ((source : E), state.2),
          ⟨source.2, Submodule.mem_top⟩⟩, ?_⟩
    change WithLp.toLp 2 (operator source, state.2) =
      WithLp.toLp 2 state
    apply congrArg (WithLp.toLp 2)
    apply Prod.ext
    · exact hSource
    · rfl

theorem linearPMapProdIdentity_range_isClosed
    (operator : E →ₗ.[Real] E)
    (hClosed :
      IsClosed (LinearMap.range operator.toFun : Set E)) :
    IsClosed
      (LinearMap.range
        (linearPMapProdIdentity (F := F) operator).toFun :
        Set (ProductHilbert (E := E) (F := F))) := by
  rw [linearPMapProdIdentity_range]
  change IsClosed
    ((WithLp.homeomorphProd 2 E F).symm ''
      ((LinearMap.range operator.toFun : Set E) ×ˢ Set.univ))
  exact
    (WithLp.homeomorphProd 2 E F).symm.isClosedMap _
      (hClosed.prod isClosed_univ)

/-- Projection identifies the product kernel with a subspace of the original
kernel; the identity factor contributes no zero mode. -/
def linearPMapProdIdentityKernelFst
    (operator : E →ₗ.[Real] E) :
    LinearMap.ker
        (linearPMapProdIdentity (F := F) operator).toFun →ₗ[Real]
      LinearMap.ker operator.toFun where
  toFun := fun state =>
    ⟨⟨(WithLp.ofLp state.1.1).1, state.1.2.1⟩, by
      have hImage := congrArg
        (fun value : ProductHilbert (E := E) (F := F) =>
          (WithLp.ofLp value).1) state.2
      change operator ⟨(WithLp.ofLp state.1.1).1, state.1.2.1⟩ = 0
        at hImage
      exact hImage⟩
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

theorem linearPMapProdIdentityKernelFst_injective
    (operator : E →ₗ.[Real] E) :
    Function.Injective
      (linearPMapProdIdentityKernelFst (F := F) operator) := by
  intro first second hFirst
  apply Subtype.ext
  apply Subtype.ext
  apply (WithLp.linearEquiv 2 Real (E × F)).injective
  apply Prod.ext
  · exact congrArg
      (fun state : LinearMap.ker operator.toFun => (state.1 : E))
      hFirst
  · have hFirstSecond := congrArg
      (fun value : ProductHilbert (E := E) (F := F) =>
        (WithLp.ofLp value).2) first.2
    have hSecondSecond := congrArg
      (fun value : ProductHilbert (E := E) (F := F) =>
        (WithLp.ofLp value).2) second.2
    change (WithLp.ofLp first.1.1).2 = 0 at hFirstSecond
    change (WithLp.ofLp second.1.1).2 = 0 at hSecondSecond
    exact hFirstSecond.trans hSecondSecond.symm

theorem linearPMapProdIdentity_kernel_finite
    (operator : E →ₗ.[Real] E)
    (hFinite :
      FiniteDimensional Real (LinearMap.ker operator.toFun)) :
    FiniteDimensional Real
      (LinearMap.ker
        (linearPMapProdIdentity (F := F) operator).toFun) := by
  letI := hFinite
  exact FiniteDimensional.of_injective
    (linearPMapProdIdentityKernelFst (F := F) operator)
    (linearPMapProdIdentityKernelFst_injective (F := F) operator)

private def productQuotientFst
    (subspace : Submodule Real E) :
    ((E × F) ⧸ subspace.prod (⊤ : Submodule Real F)) →ₗ[Real]
      E ⧸ subspace :=
  (subspace.prod (⊤ : Submodule Real F)).mapQ subspace
    (LinearMap.fst Real E F) (by
      intro state hState
      exact hState.1)

private theorem productQuotientFst_injective
    (subspace : Submodule Real E) :
    Function.Injective (productQuotientFst (F := F) subspace) := by
  rw [← LinearMap.ker_eq_bot]
  apply le_antisymm
  · intro state hState
    induction state using Submodule.Quotient.induction_on with
    | _ representative =>
        rw [Submodule.mem_bot]
        apply
          (Submodule.Quotient.mk_eq_zero
            (subspace.prod (⊤ : Submodule Real F))).2
        have hFirst : representative.1 ∈ subspace := by
          apply (Submodule.Quotient.mk_eq_zero subspace).1
          simpa [productQuotientFst] using hState
        exact ⟨hFirst, Submodule.mem_top⟩
  · exact bot_le

theorem linearPMapProdIdentity_cokernel_finite
    (operator : E →ₗ.[Real] E)
    (hFinite :
      FiniteDimensional Real
        (E ⧸ LinearMap.range operator.toFun)) :
    FiniteDimensional Real
      (ProductHilbert (E := E) (F := F) ⧸
        LinearMap.range
          (linearPMapProdIdentity (F := F) operator).toFun) := by
  letI := hFinite
  let originalRange := LinearMap.range operator.toFun
  let productRange :=
    originalRange.prod (⊤ : Submodule Real F)
  let totalRange :=
    LinearMap.range
      (linearPMapProdIdentity (F := F) operator).toFun
  have hRange :
      productRange.map
          (WithLp.linearEquiv 2 Real (E × F)).symm.toLinearMap =
        totalRange :=
    (linearPMapProdIdentity_range (F := F) operator).symm
  let quotientEquivalence :
      ((E × F) ⧸ productRange) ≃ₗ[Real]
        (ProductHilbert (E := E) (F := F) ⧸ totalRange) :=
    Submodule.Quotient.equiv productRange totalRange
      (WithLp.linearEquiv 2 Real (E × F)).symm hRange
  let cokernelEmbedding :
      (ProductHilbert (E := E) (F := F) ⧸ totalRange) →ₗ[Real]
        E ⧸ originalRange :=
    (productQuotientFst (F := F) originalRange).comp
      quotientEquivalence.symm.toLinearMap
  exact FiniteDimensional.of_injective cokernelEmbedding
    ((productQuotientFst_injective (F := F) originalRange).comp
      quotientEquivalence.symm.injective)

/-- Fredholm stability under adjoining an exact identity Hessian block. -/
theorem linearPMapProdIdentity_fredholm
    (operator : E →ₗ.[Real] E)
    (hFredholm :
      IsClosed (LinearMap.range operator.toFun : Set E) ∧
        FiniteDimensional Real (LinearMap.ker operator.toFun) ∧
        FiniteDimensional Real
          (E ⧸ LinearMap.range operator.toFun)) :
    IsClosed
        (LinearMap.range
          (linearPMapProdIdentity (F := F) operator).toFun :
          Set (ProductHilbert (E := E) (F := F))) ∧
      FiniteDimensional Real
        (LinearMap.ker
          (linearPMapProdIdentity (F := F) operator).toFun) ∧
      FiniteDimensional Real
        (ProductHilbert (E := E) (F := F) ⧸
          LinearMap.range
            (linearPMapProdIdentity (F := F) operator).toFun) :=
  ⟨linearPMapProdIdentity_range_isClosed (F := F) operator hFredholm.1,
    linearPMapProdIdentity_kernel_finite (F := F) operator hFredholm.2.1,
    linearPMapProdIdentity_cokernel_finite (F := F) operator hFredholm.2.2⟩

end
end P0EFTJanusLinearPMapProdIdentityFredholm4D
end JanusFormal
