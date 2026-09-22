import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-! Concrete isometric transport of an unbounded operator, including its
domain. Surjective symmetric realizations retain self-adjointness. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12IsometricPMapTransport4D
set_option autoImplicit false
noncomputable section
open Set
open scoped LinearPMap InnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [NormedAddCommGroup F] [InnerProductSpace Real F]
variable (equiv : E ≃ₗᵢ[Real] F) (operator : F →ₗ.[Real] F)

def transportedPMap : E →ₗ.[Real] E where
  domain := operator.domain.comap equiv.toLinearEquiv.toLinearMap
  toFun := equiv.symm.toLinearEquiv.toLinearMap.comp
    (operator.toFun.comp (equiv.toLinearEquiv.toLinearMap.submoduleComap operator.domain))

def transportedDomainEquiv : (transportedPMap equiv operator).domain ≃ₗ[Real] operator.domain where
  toFun vector := ⟨equiv vector, vector.property⟩
  invFun vector := ⟨equiv.symm vector, by
    change equiv (equiv.symm (vector : F)) ∈ operator.domain
    rw [equiv.apply_symm_apply]
    exact vector.property⟩
  left_inv vector := Subtype.ext (equiv.symm_apply_apply _)
  right_inv vector := Subtype.ext (equiv.apply_symm_apply _)
  map_add' _ _ := Subtype.ext (equiv.map_add _ _)
  map_smul' scalar vector := Subtype.ext (equiv.map_smul scalar (vector : E))

theorem transportedPMap_action (vector : (transportedPMap equiv operator).domain) :
    equiv (transportedPMap equiv operator vector) = operator (transportedDomainEquiv equiv operator vector) :=
  equiv.apply_symm_apply _

theorem transportedPMap_graph_iff (first second : E) :
    (first, second) ∈ (transportedPMap equiv operator).graph ↔
      (equiv first, equiv second) ∈ operator.graph := by
  constructor
  · intro hGraph
    obtain ⟨vector, hFirst, hSecond⟩ := (transportedPMap equiv operator).mem_graph_iff.mp hGraph
    refine operator.mem_graph_iff.mpr ⟨transportedDomainEquiv equiv operator vector, ?_, ?_⟩
    · exact congrArg equiv hFirst
    · exact (transportedPMap_action equiv operator vector).symm.trans (congrArg equiv hSecond)
  · intro hGraph
    obtain ⟨vector, hFirst, hSecond⟩ := operator.mem_graph_iff.mp hGraph
    refine (transportedPMap equiv operator).mem_graph_iff.mpr
      ⟨(transportedDomainEquiv equiv operator).symm vector, ?_, ?_⟩
    · exact (congrArg equiv.symm hFirst).trans (equiv.symm_apply_apply first)
    · apply equiv.injective
      rw [transportedPMap_action, LinearEquiv.apply_symm_apply]
      exact hSecond

theorem transportedPMap_isClosed (hClosed : operator.IsClosed) :
    (transportedPMap equiv operator).IsClosed := by
  have hGraph : ((transportedPMap equiv operator).graph : Set (E × E)) =
      (fun pair : E × E => (equiv pair.1, equiv pair.2)) ⁻¹' (operator.graph : Set (F × F)) := by
    ext pair
    exact transportedPMap_graph_iff equiv operator pair.1 pair.2
  change IsClosed ((transportedPMap equiv operator).graph : Set (E × E))
  rw [hGraph]
  exact hClosed.preimage ((equiv.continuous.comp continuous_fst).prodMk
    (equiv.continuous.comp continuous_snd))

theorem transportedPMap_denseDomain (hDense : Dense (operator.domain : Set F)) :
    Dense ((transportedPMap equiv operator).domain : Set E) :=
  hDense.preimage equiv.toHomeomorph.isOpenMap

theorem transportedPMap_symmetric (hSym : operator.IsFormalAdjoint operator) :
    (transportedPMap equiv operator).IsFormalAdjoint (transportedPMap equiv operator) := by
  intro first second
  rw [← equiv.inner_map_map, ← equiv.inner_map_map, transportedPMap_action, transportedPMap_action]
  exact hSym (transportedDomainEquiv equiv operator first) (transportedDomainEquiv equiv operator second)

theorem transportedPMap_surjective (hSurj : Function.Surjective operator) :
    Function.Surjective (transportedPMap equiv operator) := by
  intro target
  obtain ⟨vector, hVector⟩ := hSurj (equiv target)
  refine ⟨(transportedDomainEquiv equiv operator).symm vector, equiv.injective ?_⟩
  rw [transportedPMap_action, LinearEquiv.apply_symm_apply]
  exact hVector

theorem transportedPMap_injective (hInj : Function.Injective operator) :
    Function.Injective (transportedPMap equiv operator) := by
  intro first second hEqual
  apply (transportedDomainEquiv equiv operator).injective
  apply hInj
  exact (transportedPMap_action equiv operator first).symm.trans
    ((congrArg equiv hEqual).trans (transportedPMap_action equiv operator second))

variable [CompleteSpace E]

/-- A dense symmetric surjective operator equals its adjoint. -/
theorem symmetric_surjective_isSelfAdjoint (source : E →ₗ.[Real] E)
    (hDense : Dense (source.domain : Set E)) (hSym : source.IsFormalAdjoint source)
    (hSurj : Function.Surjective source) : IsSelfAdjoint source := by
  have hLe : source ≤ source.adjoint := hSym.le_adjoint hDense
  have hDomain : source.adjoint.domain ≤ source.domain := by
    intro vector hVector
    let adjointVector : source.adjoint.domain := ⟨vector, hVector⟩
    obtain ⟨preimage, hPreimage⟩ := hSurj (source.adjoint adjointVector)
    have hEqual : (preimage : E) = vector := by
      apply ext_inner_left Real
      intro test
      obtain ⟨argument, rfl⟩ := hSurj test
      calc
        inner Real (source argument) (preimage : E) = inner Real (argument : E) (source preimage) := hSym argument preimage
        _ = inner Real (argument : E) (source.adjoint adjointVector) := by rw [hPreimage]
        _ = inner Real (source argument) vector :=
          ((LinearPMap.adjoint_isFormalAdjoint hDense).symm argument adjointVector).symm
    rw [← hEqual]
    exact preimage.property
  rw [LinearPMap.isSelfAdjoint_def]
  apply LinearPMap.dExt (le_antisymm hDomain hLe.1)
  intro first second hEqual
  exact (hLe.2 hEqual.symm).symm

theorem transportedPMap_isSelfAdjoint
    (hDense : Dense (operator.domain : Set F)) (hSym : operator.IsFormalAdjoint operator)
    (hSurj : Function.Surjective operator) : IsSelfAdjoint (transportedPMap equiv operator) :=
  symmetric_surjective_isSelfAdjoint _ (transportedPMap_denseDomain equiv operator hDense)
    (transportedPMap_symmetric equiv operator hSym) (transportedPMap_surjective equiv operator hSurj)

end
end P0EFTJanusProgramPT12IsometricPMapTransport4D
end JanusFormal
