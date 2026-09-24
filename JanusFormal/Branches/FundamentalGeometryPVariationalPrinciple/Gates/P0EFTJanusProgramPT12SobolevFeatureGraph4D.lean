import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Tactic

/-! Minimal feature graphs with a Banach source, allowing the actual H¹ graph norm.
No Hilbert structure on the source, closed-range claim, or maximal-domain identification is used. -/
namespace JanusFormal.P0EFTJanusProgramPT12SobolevFeatureGraph4D
set_option autoImplicit false
noncomputable section
open Set Topology

variable {D X Y : Type*} [AddCommGroup D] [Module Real D]
  [NormedAddCommGroup X] [NormedSpace Real X]
  [NormedAddCommGroup Y] [NormedSpace Real Y]

def sobolevFeatureGraphClosure (inclusion : D →ₗ[Real] X) (operator : D →ₗ[Real] Y) :
    Submodule Real (X × Y) :=
  (inclusion.prod operator).range.topologicalClosure

def sobolevFeatureOperator (inclusion : D →ₗ[Real] X) (operator : D →ₗ[Real] Y) :
    X →ₗ.[Real] Y :=
  (sobolevFeatureGraphClosure inclusion operator).toLinearPMap

variable (inclusion : D →ₗ[Real] X) (operator : D →ₗ[Real] Y)

theorem sobolevFeatureOperator_graph
    (hSingle : Function.Injective
      (fun graph : sobolevFeatureGraphClosure inclusion operator => graph.val.1)) :
    (sobolevFeatureOperator inclusion operator).graph =
      sobolevFeatureGraphClosure inclusion operator := by
  apply Submodule.toLinearPMap_graph_eq
  intro pair hPair hZero
  exact congrArg (fun graph => graph.val.2)
    (hSingle (a₁ := ⟨pair, hPair⟩) (a₂ := 0) hZero)

theorem sobolevFeatureOperator_isClosed
    (hSingle : Function.Injective
      (fun graph : sobolevFeatureGraphClosure inclusion operator => graph.val.1)) :
    (sobolevFeatureOperator inclusion operator).IsClosed := by
  rw [LinearPMap.IsClosed, sobolevFeatureOperator_graph inclusion operator hSingle]
  exact (inclusion.prod operator).range.isClosed_topologicalClosure

theorem sobolevFeatureOperator_smooth_mem (field : D) :
    inclusion field ∈ (sobolevFeatureOperator inclusion operator).domain :=
  ⟨(inclusion field, operator field),
    (inclusion.prod operator).range.le_topologicalClosure ⟨field, rfl⟩, rfl⟩

theorem sobolevFeatureOperator_smooth_apply
    (hSingle : Function.Injective
      (fun graph : sobolevFeatureGraphClosure inclusion operator => graph.val.1)) (field : D) :
    sobolevFeatureOperator inclusion operator
      ⟨inclusion field, sobolevFeatureOperator_smooth_mem inclusion operator field⟩ = operator field := by
  have hGraph := (sobolevFeatureOperator inclusion operator).mem_graph
    ⟨inclusion field, sobolevFeatureOperator_smooth_mem inclusion operator field⟩
  rw [sobolevFeatureOperator_graph inclusion operator hSingle] at hGraph
  exact congrArg (fun graph => graph.val.2)
    (hSingle (a₁ := ⟨_, hGraph⟩) (a₂ := ⟨(inclusion field, operator field),
      (inclusion.prod operator).range.le_topologicalClosure ⟨field, rfl⟩⟩) rfl)

theorem sobolevFeatureOperator_dense_domain (hDense : DenseRange inclusion) :
    Dense ((sobolevFeatureOperator inclusion operator).domain : Set X) :=
  hDense.mono (by rintro _ ⟨field, rfl⟩; exact sobolevFeatureOperator_smooth_mem inclusion operator field)

theorem sobolevFeatureOperator_minimal
    (hSingle : Function.Injective
      (fun graph : sobolevFeatureGraphClosure inclusion operator => graph.val.1))
    (extension : X →ₗ.[Real] Y) (hClosed : extension.IsClosed)
    (hExtends : ∀ field, (inclusion field, operator field) ∈ extension.graph) :
    sobolevFeatureOperator inclusion operator ≤ extension := by
  apply LinearPMap.le_of_le_graph
  rw [sobolevFeatureOperator_graph inclusion operator hSingle]
  exact closure_minimal (by rintro pair ⟨field, rfl⟩; exact hExtends field) hClosed

/-- The correction is bounded in the source norm, which need not be the target L² norm. -/
def sobolevBoundedGraphShear (correction : X →L[Real] Y) : (X × Y) ≃L[Real] (X × Y) where
  toFun pair := (pair.1, pair.2 + correction pair.1)
  invFun pair := (pair.1, pair.2 - correction pair.1)
  left_inv pair := by simp
  right_inv pair := by simp
  map_add' first second := by simp; abel
  map_smul' scalar pair := by simp [smul_add]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem sobolevFeatureGraphClosure_bounded_shear (correction : X →L[Real] Y) :
    sobolevFeatureGraphClosure inclusion (operator + correction.toLinearMap.comp inclusion) =
      (sobolevFeatureGraphClosure inclusion operator).map
        (sobolevBoundedGraphShear correction).toLinearMap := by
  apply SetLike.coe_injective
  change closure ((inclusion.prod (operator + correction.toLinearMap.comp inclusion)).range : Set (X × Y)) =
    (sobolevBoundedGraphShear correction) '' closure ((inclusion.prod operator).range : Set (X × Y))
  rw [(sobolevBoundedGraphShear correction).image_closure]
  congr 1
  ext pair
  constructor
  · rintro ⟨field, rfl⟩
    exact ⟨(inclusion field, operator field), ⟨field, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨field, rfl⟩, rfl⟩
    exact ⟨field, rfl⟩

theorem sobolevFeatureOperator_bounded_shear_domain (correction : X →L[Real] Y) :
    (sobolevFeatureOperator inclusion (operator + correction.toLinearMap.comp inclusion)).domain =
      (sobolevFeatureOperator inclusion operator).domain := by
  change (sobolevFeatureGraphClosure inclusion (operator + correction.toLinearMap.comp inclusion)).map
      (LinearMap.fst Real X Y) =
    (sobolevFeatureGraphClosure inclusion operator).map (LinearMap.fst Real X Y)
  rw [sobolevFeatureGraphClosure_bounded_shear, ← Submodule.map_comp]
  rfl

theorem sobolevFeatureGraphClosure_bounded_shear_fst_injective
    (hSingle : Function.Injective
      (fun graph : sobolevFeatureGraphClosure inclusion operator => graph.val.1))
    (correction : X →L[Real] Y) :
    Function.Injective (fun graph : sobolevFeatureGraphClosure inclusion
      (operator + correction.toLinearMap.comp inclusion) => graph.val.1) := by
  intro first second hInput
  have hFirst := first.property
  have hSecond := second.property
  simp only [sobolevFeatureGraphClosure_bounded_shear] at hFirst hSecond
  obtain ⟨p, hp, hFirst⟩ := hFirst
  obtain ⟨q, hq, hSecond⟩ := hSecond
  have hInputs : p.1 = q.1 := by
    exact (congrArg Prod.fst hFirst).trans (hInput.trans (congrArg Prod.fst hSecond).symm)
  have hEqual : p = q := congrArg Subtype.val (hSingle (a₁ := ⟨p, hp⟩) (a₂ := ⟨q, hq⟩) hInputs)
  subst q
  exact Subtype.ext (hFirst.symm.trans hSecond)

/-- A continuous forgetting map sends the stronger-source closure into an existing closed graph. -/
theorem sobolevFeatureGraphClosure_forget_mem
    (forget : X →L[Real] Y) (extension : Y →ₗ.[Real] Y) (hClosed : extension.IsClosed)
    (hExtends : ∀ field, (forget (inclusion field), operator field) ∈ extension.graph)
    (pair : X × Y) (hPair : pair ∈ sobolevFeatureGraphClosure inclusion operator) :
    (forget pair.1, pair.2) ∈ extension.graph := by
  have hPreimage : IsClosed {pair : X × Y | (forget pair.1, pair.2) ∈ extension.graph} :=
    hClosed.preimage (forget.prodMap (ContinuousLinearMap.id Real Y)).continuous
  exact closure_minimal (by rintro pair ⟨field, rfl⟩; exact hExtends field) hPreimage hPair

theorem sobolevFeatureGraphClosure_fst_injective_of_forget
    (forget : X →L[Real] Y) (extension : Y →ₗ.[Real] Y) (hClosed : extension.IsClosed)
    (hExtends : ∀ field, (forget (inclusion field), operator field) ∈ extension.graph) :
    Function.Injective (fun graph : sobolevFeatureGraphClosure inclusion operator => graph.val.1) := by
  intro first second hInput
  change first.val.1 = second.val.1 at hInput
  have hDifference := extension.graph.sub_mem
    (sobolevFeatureGraphClosure_forget_mem inclusion operator forget extension hClosed hExtends _ first.property)
    (sobolevFeatureGraphClosure_forget_mem inclusion operator forget extension hClosed hExtends _ second.property)
  have hZero := extension.graph_fst_eq_zero_snd hDifference
    (show forget first.val.1 - forget second.val.1 = 0 by rw [hInput, sub_self])
  exact Subtype.ext (Prod.ext hInput (sub_eq_zero.mp hZero))

end
end JanusFormal.P0EFTJanusProgramPT12SobolevFeatureGraph4D
