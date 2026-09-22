import Mathlib.Analysis.InnerProductSpace.LinearPMap
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12ClosedNullQuotient4D

/-! Descent of a closed symmetric, possibly unbounded operator through a
closed null subspace. The domain and graph are transported explicitly. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12ClosedNullPMapQuotient4D

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace LinearPMap
open P0EFTJanusProgramPT12ClosedNullQuotient4D

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]
variable (operator : E →ₗ.[Real] E)
variable (nullSpace : Submodule Real E) [IsClosed (nullSpace : Set E)]

def quotientLift : (E ⧸ nullSpace) →L[Real] E :=
  nullSpaceᗮ.subtypeL.comp nullSpace.quotientEquivOrthogonal.toContinuousLinearEquiv.toContinuousLinearMap

theorem mk_quotientLift (vector : E ⧸ nullSpace) :
    nullSpace.mkQ (quotientLift nullSpace vector) = vector := by
  exact (nullSpace.quotientEquivOrthogonal_symm_eq_mk _
    (nullSpace.quotientEquivOrthogonal vector).property).symm.trans
      (nullSpace.quotientEquivOrthogonal.symm_apply_apply vector)

theorem quotientLift_mk (vector : E) (hOrth : vector ∈ nullSpaceᗮ) :
    quotientLift nullSpace (nullSpace.mkQ vector) = vector := by
  exact congrArg Subtype.val (nullSpace.quotientEquivOrthogonal_mk vector hOrth)

private theorem difference_mem (vector : E) :
    vector - quotientLift nullSpace (nullSpace.mkQ vector) ∈ nullSpace :=
  (Submodule.Quotient.eq nullSpace).mp (mk_quotientLift nullSpace _).symm

def quotientGraph : Submodule Real ((E ⧸ nullSpace) × (E ⧸ nullSpace)) :=
  operator.graph.comap ((quotientLift nullSpace).toLinearMap.prodMap
    (quotientLift nullSpace).toLinearMap)

private theorem quotientGraph_functional
    (pair : (E ⧸ nullSpace) × (E ⧸ nullSpace))
    (hPair : pair ∈ quotientGraph operator nullSpace) (hZero : pair.1 = 0) :
    pair.2 = 0 := by
  have hGraph : (quotientLift nullSpace pair.1, quotientLift nullSpace pair.2) ∈ operator.graph := hPair
  rw [hZero, map_zero] at hGraph
  have hOutput := operator.graph_fst_eq_zero_snd hGraph rfl
  calc
    pair.2 = nullSpace.mkQ (quotientLift nullSpace pair.2) := (mk_quotientLift nullSpace _).symm
    _ = 0 := by rw [hOutput, map_zero]

def quotientPMap : (E ⧸ nullSpace) →ₗ.[Real] (E ⧸ nullSpace) :=
  (quotientGraph operator nullSpace).toLinearPMap

theorem quotientPMap_graph :
    (quotientPMap operator nullSpace).graph = quotientGraph operator nullSpace :=
  Submodule.toLinearPMap_graph_eq _ (quotientGraph_functional operator nullSpace)

theorem quotientPMap_isClosed (hClosed : operator.IsClosed) :
    (quotientPMap operator nullSpace).IsClosed := by
  change IsClosed ((quotientPMap operator nullSpace).graph :
    Set ((E ⧸ nullSpace) × (E ⧸ nullSpace)))
  rw [quotientPMap_graph]
  exact hClosed.preimage
    (((quotientLift nullSpace).continuous.comp continuous_fst).prodMk
      ((quotientLift nullSpace).continuous.comp continuous_snd))

variable (hSym : operator.IsFormalAdjoint operator)
variable (hNull : ∀ vector ∈ nullSpace, (vector, (0 : E)) ∈ operator.graph)

include hSym hNull in
omit [CompleteSpace E] [IsClosed (nullSpace : Set E)] in
theorem output_mem_orthogonal (vector : operator.domain) :
    operator vector ∈ nullSpaceᗮ := by
  rw [Submodule.mem_orthogonal']
  intro zeroMode hZeroMode
  obtain ⟨source, hSource, hOutput⟩ := operator.mem_graph_iff.mp (hNull zeroMode hZeroMode)
  change (source : E) = zeroMode at hSource
  change operator source = 0 at hOutput
  rw [← hSource]
  calc
    inner Real (operator vector) (source : E) = inner Real (vector : E) (operator source) := hSym vector source
    _ = 0 := by rw [hOutput, inner_zero_right]

include hSym hNull in
theorem quotientPMap_graph_project (vector : operator.domain) :
    (nullSpace.mkQ (vector : E), nullSpace.mkQ (operator vector)) ∈
      (quotientPMap operator nullSpace).graph := by
  rw [quotientPMap_graph]
  change (quotientLift nullSpace (nullSpace.mkQ (vector : E)),
    quotientLift nullSpace (nullSpace.mkQ (operator vector))) ∈ operator.graph
  rw [quotientLift_mk nullSpace _ (output_mem_orthogonal operator nullSpace hSym hNull vector)]
  have hSub := operator.graph.sub_mem (operator.mem_graph vector)
    (hNull _ (difference_mem nullSpace (vector : E)))
  simpa only [Prod.mk_sub_mk, sub_sub_cancel, sub_zero] using hSub

include hSym hNull in
theorem quotientPMap_domain :
    (quotientPMap operator nullSpace).domain = operator.domain.map nullSpace.mkQ := by
  ext vector
  constructor
  · intro hVector
    have hGraph := (quotientPMap operator nullSpace).mem_graph ⟨vector, hVector⟩
    rw [quotientPMap_graph] at hGraph
    have hLift : quotientLift nullSpace vector ∈ operator.domain :=
      LinearPMap.mem_domain_of_mem_graph hGraph
    exact ⟨_, hLift, mk_quotientLift nullSpace vector⟩
  · rintro ⟨source, hSource, rfl⟩
    exact LinearPMap.mem_domain_of_mem_graph
      (quotientPMap_graph_project operator nullSpace hSym hNull ⟨source, hSource⟩)

include hSym hNull in
theorem quotientPMap_denseDomain (hDense : Dense (operator.domain : Set E)) :
    Dense ((quotientPMap operator nullSpace).domain : Set (E ⧸ nullSpace)) := by
  have hRange : DenseRange (fun vector : operator.domain => (vector : E)) := by
    simpa [DenseRange] using hDense
  have hProjected := nullSpace.mkQ_surjective.denseRange.comp hRange nullSpace.mkQL.continuous
  apply hProjected.mono
  rintro _ ⟨source, rfl⟩
  exact LinearPMap.mem_domain_of_mem_graph
    (quotientPMap_graph_project operator nullSpace hSym hNull source)

include hSym hNull in
theorem quotientPMap_pairing (vector : operator.domain) (test : E)
    (hDomain : nullSpace.mkQ (vector : E) ∈ (quotientPMap operator nullSpace).domain) :
    inner Real ((quotientPMap operator nullSpace) ⟨nullSpace.mkQ (vector : E), hDomain⟩)
      (nullSpace.mkQ test) = inner Real (operator vector) test := by
  have hValue := (quotientPMap operator nullSpace).mem_graph_snd_inj
    ((quotientPMap operator nullSpace).mem_graph ⟨nullSpace.mkQ (vector : E), hDomain⟩)
    (quotientPMap_graph_project operator nullSpace hSym hNull vector) rfl
  rw [hValue]
  exact inner_mk_of_left_orthogonal nullSpace _ _
    (output_mem_orthogonal operator nullSpace hSym hNull vector)

include hSym hNull in
/-- A null quotient cannot erase any nonzero Jacobi output. -/
theorem quotientPMap_zero_iff (vector : operator.domain)
    (hDomain : nullSpace.mkQ (vector : E) ∈ (quotientPMap operator nullSpace).domain) :
    (quotientPMap operator nullSpace) ⟨nullSpace.mkQ (vector : E), hDomain⟩ = 0 ↔
      operator vector = 0 := by
  have hValue := (quotientPMap operator nullSpace).mem_graph_snd_inj
    ((quotientPMap operator nullSpace).mem_graph ⟨nullSpace.mkQ (vector : E), hDomain⟩)
    (quotientPMap_graph_project operator nullSpace hSym hNull vector) rfl
  rw [hValue]
  constructor
  · intro hZero
    have hMem := (Submodule.Quotient.mk_eq_zero nullSpace).mp hZero
    have hOrth := output_mem_orthogonal operator nullSpace hSym hNull vector
    exact inner_self_eq_zero.mp ((nullSpace.mem_orthogonal' _).mp hOrth _ hMem)
  · intro hZero
    rw [hZero, map_zero]

include hSym in
theorem quotientPMap_symmetric :
    (quotientPMap operator nullSpace).IsFormalAdjoint (quotientPMap operator nullSpace) := by
  intro first second
  have hFirst := (quotientPMap operator nullSpace).mem_graph first
  have hSecond := (quotientPMap operator nullSpace).mem_graph second
  rw [quotientPMap_graph] at hFirst hSecond
  obtain ⟨x, hx, hAx⟩ := operator.mem_graph_iff.mp hFirst
  obtain ⟨y, hy, hAy⟩ := operator.mem_graph_iff.mp hSecond
  change (x : E) = quotientLift nullSpace (first : E ⧸ nullSpace) at hx
  change (y : E) = quotientLift nullSpace (second : E ⧸ nullSpace) at hy
  change operator x = quotientLift nullSpace ((quotientPMap operator nullSpace) first) at hAx
  change operator y = quotientLift nullSpace ((quotientPMap operator nullSpace) second) at hAy
  change inner Real (quotientLift nullSpace ((quotientPMap operator nullSpace) first))
      (quotientLift nullSpace (second : E ⧸ nullSpace)) =
    inner Real (quotientLift nullSpace (first : E ⧸ nullSpace))
      (quotientLift nullSpace ((quotientPMap operator nullSpace) second))
  rw [← hx, ← hy, ← hAx, ← hAy]
  exact hSym x y

end
end P0EFTJanusProgramPT12ClosedNullPMapQuotient4D
end JanusFormal
