import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

/-! A bounded self-adjoint operator descends through a closed null subspace.
The quotient preserves its pairing exactly and retains any residual kernel. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12ClosedNullQuotient4D
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]
variable (operator : E →L[Real] E) (hSelf : IsSelfAdjoint operator)
variable (nullSpace : Submodule Real E) [IsClosed (nullSpace : Set E)]
variable (hNull : nullSpace ≤ operator.ker)

def closedNullQuotientOperator : (E ⧸ nullSpace) →L[Real] (E ⧸ nullSpace) :=
  nullSpace.mkQL.comp (nullSpace.liftQL operator hNull)

omit [CompleteSpace E] [IsClosed (nullSpace : Set E)] in
@[simp] theorem closedNullQuotientOperator_mk (vector : E) :
    closedNullQuotientOperator operator nullSpace hNull (nullSpace.mkQ vector) =
      nullSpace.mkQ (operator vector) := rfl

include hSelf hNull in
omit [IsClosed (nullSpace : Set E)] in
theorem operator_mem_null_orthogonal (vector : E) :
    operator vector ∈ nullSpaceᗮ := by
  rw [Submodule.mem_orthogonal']
  intro zeroMode hZeroMode
  have hZero : operator zeroMode = 0 := hNull hZeroMode
  calc
    inner Real (operator vector) zeroMode = inner Real vector (operator zeroMode) :=
      hSelf.isSymmetric vector zeroMode
    _ = 0 := by rw [hZero, inner_zero_right]

/-- Pairing with a quotient class equals the original pairing whenever
the left vector is orthogonal to the null space. -/
theorem inner_mk_of_left_orthogonal (first second : E)
    (hFirst : first ∈ nullSpaceᗮ) :
    inner Real (nullSpace.mkQ first) (nullSpace.mkQ second) = inner Real first second := by
  let representative := nullSpace.quotientEquivOrthogonal (nullSpace.mkQ second)
  have hSame : nullSpace.mkQ (representative : E) = nullSpace.mkQ second := by
    exact (nullSpace.quotientEquivOrthogonal_symm_eq_mk representative.1 representative.2).symm.trans
      (nullSpace.quotientEquivOrthogonal.symm_apply_apply (nullSpace.mkQ second))
  have hDifference : second - (representative : E) ∈ nullSpace :=
    (Submodule.Quotient.eq nullSpace).mp hSame.symm
  have hInner : inner Real first (second - (representative : E)) = 0 :=
    (nullSpace.mem_orthogonal' first).mp hFirst _ hDifference
  rw [inner_sub_right] at hInner
  change inner Real
    (nullSpace.quotientEquivOrthogonal (Submodule.Quotient.mk first)) representative = _
  rw [nullSpace.quotientEquivOrthogonal_mk first hFirst]
  change inner Real first (representative : E) = inner Real first second
  linarith

include hSelf in
theorem closedNullQuotientOperator_pairing (first second : E) :
    inner Real
      (closedNullQuotientOperator operator nullSpace hNull (nullSpace.mkQ first))
      (nullSpace.mkQ second) = inner Real (operator first) second := by
  rw [closedNullQuotientOperator_mk]
  exact inner_mk_of_left_orthogonal nullSpace _ _
    (operator_mem_null_orthogonal operator hSelf nullSpace hNull first)

include hSelf in
theorem closedNullQuotientOperator_isSelfAdjoint :
    IsSelfAdjoint (closedNullQuotientOperator operator nullSpace hNull) := by
  apply LinearMap.IsSymmetric.isSelfAdjoint
  intro first second
  obtain ⟨first, rfl⟩ := nullSpace.mkQ_surjective first
  obtain ⟨second, rfl⟩ := nullSpace.mkQ_surjective second
  calc
    _ = inner Real (operator first) second :=
      closedNullQuotientOperator_pairing operator hSelf nullSpace hNull first second
    _ = inner Real first (operator second) := hSelf.isSymmetric first second
    _ = inner Real (operator second) first := real_inner_comm _ _
    _ = inner Real
        (closedNullQuotientOperator operator nullSpace hNull (nullSpace.mkQ second))
        (nullSpace.mkQ first) :=
      (closedNullQuotientOperator_pairing operator hSelf nullSpace hNull second first).symm
    _ = _ := real_inner_comm _ _

include hSelf in
omit [IsClosed (nullSpace : Set E)] in
/-- Quotienting a subspace of the kernel does not silently erase other
zero modes: the reduced kernel is exactly the image of the original one. -/
theorem closedNullQuotientOperator_mk_eq_zero_iff (vector : E) :
    closedNullQuotientOperator operator nullSpace hNull (nullSpace.mkQ vector) = 0 ↔
      operator vector = 0 := by
  rw [closedNullQuotientOperator_mk]
  constructor
  · intro hZero
    have hMem : operator vector ∈ nullSpace := (Submodule.Quotient.mk_eq_zero nullSpace).mp hZero
    have hOrth := operator_mem_null_orthogonal operator hSelf nullSpace hNull vector
    exact inner_self_eq_zero.mp ((nullSpace.mem_orthogonal' _).mp hOrth _ hMem)
  · intro hZero
    rw [hZero, map_zero]

include hSelf in
omit [IsClosed (nullSpace : Set E)] in
theorem closedNullQuotientOperator_kernel :
    (closedNullQuotientOperator operator nullSpace hNull).ker =
      operator.ker.map nullSpace.mkQ := by
  ext vector
  obtain ⟨vector, rfl⟩ := nullSpace.mkQ_surjective vector
  constructor
  · intro hZero
    exact ⟨vector,
      (closedNullQuotientOperator_mk_eq_zero_iff operator hSelf nullSpace hNull vector).mp hZero,
      rfl⟩
  · rintro ⟨source, hSource, hEqual⟩
    rw [← hEqual]
    exact (closedNullQuotientOperator_mk_eq_zero_iff operator hSelf nullSpace hNull source).mpr hSource

end
end P0EFTJanusProgramPT12ClosedNullQuotient4D
end JanusFormal
