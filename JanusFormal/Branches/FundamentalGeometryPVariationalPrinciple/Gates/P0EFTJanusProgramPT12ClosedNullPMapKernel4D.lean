import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12ClosedNullPMapRange4D
import Mathlib.RingTheory.Finiteness.Prod

/-! A finite null quotient preserves finiteness of the entire operator kernel. -/
namespace JanusFormal.P0EFTJanusProgramPT12ClosedNullPMapKernel4D
set_option autoImplicit false
noncomputable section
open Set
open P0EFTJanusProgramPT12ClosedNullPMapQuotient4D
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

private def kernelAmbient (operator : E →ₗ.[Real] E) : LinearMap.ker operator.toFun →ₗ[Real] E :=
  operator.domain.subtype.comp (LinearMap.ker operator.toFun).subtype

omit [CompleteSpace E] in
private theorem kernelAmbient_graph (operator : E →ₗ.[Real] E) (vector : LinearMap.ker operator.toFun) :
    (kernelAmbient operator vector, 0) ∈ operator.graph := by
  have h := operator.mem_graph vector.val
  have hZero : operator vector.val = 0 := vector.property
  rw [hZero] at h
  exact h

private def kernelOfGraph {D : Type*} [AddCommGroup D] [Module Real D]
    (operator : E →ₗ.[Real] E) (inclusion : D →ₗ[Real] E)
    (hGraph : ∀ vector, (inclusion vector, 0) ∈ operator.graph) :
    D →ₗ[Real] LinearMap.ker operator.toFun where
  toFun vector := ⟨⟨inclusion vector, LinearPMap.mem_domain_of_mem_graph (hGraph vector)⟩, by
    exact operator.mem_graph_snd_inj (operator.mem_graph _) (hGraph vector) rfl⟩
  map_add' _ _ := by apply Subtype.ext; apply Subtype.ext; exact map_add _ _ _
  map_smul' _ _ := by apply Subtype.ext; apply Subtype.ext; exact map_smul _ _ _

variable (operator : E →ₗ.[Real] E) (nullSpace : Submodule Real E) [IsClosed (nullSpace : Set E)]
variable (hSym : operator.IsFormalAdjoint operator)
variable (hNull : ∀ vector ∈ nullSpace, (vector, (0 : E)) ∈ operator.graph)

def quotientKernelProjection : LinearMap.ker operator.toFun →ₗ[Real]
    LinearMap.ker (quotientPMap operator nullSpace).toFun :=
  kernelOfGraph (quotientPMap operator nullSpace) (nullSpace.mkQ.comp (kernelAmbient operator)) (by
    intro vector
    have h := quotientPMap_graph_project operator nullSpace hSym hNull vector.val
    have hZero : operator vector.val = 0 := vector.property
    rw [hZero, map_zero] at h
    exact h)

def quotientKernelLift : LinearMap.ker (quotientPMap operator nullSpace).toFun →ₗ[Real]
    LinearMap.ker operator.toFun :=
  kernelOfGraph operator ((quotientLift nullSpace).toLinearMap.comp (kernelAmbient (quotientPMap operator nullSpace))) (by
    intro vector
    have h := kernelAmbient_graph (quotientPMap operator nullSpace) vector
    rw [quotientPMap_graph] at h
    change (quotientLift nullSpace (kernelAmbient (quotientPMap operator nullSpace) vector), quotientLift nullSpace 0) ∈ operator.graph at h
    change (quotientLift nullSpace (kernelAmbient (quotientPMap operator nullSpace) vector), 0) ∈ operator.graph
    simpa only [map_zero] using h)

theorem quotientKernelProjection_lift (vector : LinearMap.ker (quotientPMap operator nullSpace).toFun) :
    quotientKernelProjection operator nullSpace hSym hNull (quotientKernelLift operator nullSpace vector) = vector := by
  apply Subtype.ext
  apply Subtype.ext
  exact mk_quotientLift nullSpace vector.val.val

theorem quotientKernelProjection_surjective : Function.Surjective (quotientKernelProjection operator nullSpace hSym hNull) :=
  fun vector => ⟨quotientKernelLift operator nullSpace vector, quotientKernelProjection_lift operator nullSpace hSym hNull vector⟩

/-- The original zero mode is recorded by its discarded null part and its residual kernel class. -/
def quotientKernelCoordinates : LinearMap.ker operator.toFun →ₗ[Real]
    nullSpace × LinearMap.ker (quotientPMap operator nullSpace).toFun where
  toFun vector :=
    (⟨kernelAmbient operator vector - quotientLift nullSpace (nullSpace.mkQ (kernelAmbient operator vector)),
      (Submodule.Quotient.eq nullSpace).mp (mk_quotientLift nullSpace _).symm⟩,
      quotientKernelProjection operator nullSpace hSym hNull vector)
  map_add' first second := by
    apply Prod.ext
    · apply Subtype.ext
      change kernelAmbient operator (first + second) - quotientLift nullSpace (nullSpace.mkQ (kernelAmbient operator (first + second))) =
        (kernelAmbient operator first - quotientLift nullSpace (nullSpace.mkQ (kernelAmbient operator first))) +
        (kernelAmbient operator second - quotientLift nullSpace (nullSpace.mkQ (kernelAmbient operator second)))
      simp only [map_add]
      abel
    · exact map_add _ _ _
  map_smul' scalar vector := by
    apply Prod.ext
    · apply Subtype.ext
      change kernelAmbient operator (scalar • vector) - quotientLift nullSpace (nullSpace.mkQ (kernelAmbient operator (scalar • vector))) =
        scalar • (kernelAmbient operator vector - quotientLift nullSpace (nullSpace.mkQ (kernelAmbient operator vector)))
      simp only [map_smul, smul_sub]
    · exact map_smul _ _ _

theorem quotientKernelCoordinates_injective : Function.Injective (quotientKernelCoordinates operator nullSpace hSym hNull) := by
  intro first second h
  have hClass : nullSpace.mkQ (kernelAmbient operator first) = nullSpace.mkQ (kernelAmbient operator second) :=
    congrArg (fun pair => pair.2.val.val) h
  have hNullPart : kernelAmbient operator first - quotientLift nullSpace (nullSpace.mkQ (kernelAmbient operator first)) =
      kernelAmbient operator second - quotientLift nullSpace (nullSpace.mkQ (kernelAmbient operator second)) :=
    congrArg (fun pair => pair.1.val) h
  rw [hClass] at hNullPart
  apply Subtype.ext
  apply Subtype.ext
  exact sub_left_inj.mp hNullPart

include hSym hNull in
theorem quotientKernel_finite_iff [FiniteDimensional Real nullSpace] :
    FiniteDimensional Real (LinearMap.ker (quotientPMap operator nullSpace).toFun) ↔
      FiniteDimensional Real (LinearMap.ker operator.toFun) := by
  constructor
  · intro hFinite
    letI := hFinite
    exact FiniteDimensional.of_injective (V₂ := nullSpace × LinearMap.ker (quotientPMap operator nullSpace).toFun)
      (quotientKernelCoordinates operator nullSpace hSym hNull)
      (quotientKernelCoordinates_injective operator nullSpace hSym hNull)
  · intro hFinite
    letI := hFinite
    exact FiniteDimensional.of_surjective (quotientKernelProjection operator nullSpace hSym hNull)
      (quotientKernelProjection_surjective operator nullSpace hSym hNull)

end
end JanusFormal.P0EFTJanusProgramPT12ClosedNullPMapKernel4D
