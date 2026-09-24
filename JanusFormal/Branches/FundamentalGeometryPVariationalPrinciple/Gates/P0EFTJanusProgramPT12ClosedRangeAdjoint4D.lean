import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12ClosedDoubleAdjoint4D
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.LinearAlgebra.Isomorphisms

/-! Closed range duality for densely defined closed real Hilbert operators. -/
namespace JanusFormal.P0EFTJanusProgramPT12ClosedRangeAdjoint4D
set_option autoImplicit false
noncomputable section
open Set
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace Real H] [CompleteSpace H]

private theorem continuous_descent {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace Real V] [CompleteSpace V]
    [NormedAddCommGroup W] [NormedSpace Real W] [CompleteSpace W]
    (f : V →L[Real] W) (g : V →L[Real] Real) (hf : Function.Surjective f)
    (hker : LinearMap.ker f.toLinearMap ≤ LinearMap.ker g.toLinearMap) :
    ∃ φ : W →L[Real] Real, ∀ v, φ (f v) = g v := by
  let lin : W →ₗ[Real] Real :=
    ((LinearMap.ker f.toLinearMap).liftQ g.toLinearMap hker).comp
      (f.toLinearMap.quotKerEquivOfSurjective hf).symm.toLinearMap
  have hlin (v : V) : lin (f v) = g v := by
    change (LinearMap.ker f.toLinearMap).liftQ g.toLinearMap hker
      ((f.toLinearMap.quotKerEquivOfSurjective hf).symm (f.toLinearMap v)) = g v
    rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
    rfl
  have hcont : Continuous lin := (f.isQuotientMap hf).continuous_iff.mpr (by
    have heq : (fun v => lin (f v)) = g := funext hlin
    simpa only [Function.comp_def, heq] using g.continuous)
  exact ⟨⟨lin, hcont⟩, hlin⟩

def operatorNullSpace (A : H →ₗ.[Real] H) : Submodule Real H :=
  A.graph.comap ((LinearMap.id : H →ₗ[Real] H).prod 0)

theorem adjoint_range_eq_null_orthogonal (A : H →ₗ.[Real] H)
    (hClosed : A.IsClosed) (hDense : Dense (A.domain : Set H))
    (hRange : IsClosed (LinearMap.range A.toFun : Set H)) :
    LinearMap.range A.adjoint.toFun = (operatorNullSpace A)ᗮ := by
  apply le_antisymm
  · rintro x ⟨v, rfl⟩
    rw [Submodule.mem_orthogonal']
    intro k hk
    have hkGraph : (k, 0) ∈ A.graph := hk
    let u : A.domain := ⟨k, LinearPMap.mem_domain_of_mem_graph hkGraph⟩
    have hu : A u = 0 := A.mem_graph_snd_inj (A.mem_graph u) hkGraph rfl
    have h := LinearPMap.adjoint_isFormalAdjoint hDense v u
    simpa [hu] using h
  · intro x hx
    letI : CompleteSpace A.graph := hClosed.completeSpace_coe
    letI : CompleteSpace (LinearMap.range A.toFun) := hRange.completeSpace_coe
    let out : A.graph →L[Real] H :=
      (ContinuousLinearMap.snd Real H H).comp A.graph.subtypeL
    have hout (v : A.graph) : out v ∈ LinearMap.range A.toFun := by
      obtain ⟨u, _, hu⟩ := A.mem_graph_iff.mp v.property
      exact ⟨u, hu⟩
    let f := out.codRestrict (LinearMap.range A.toFun) hout
    have hf : Function.Surjective f := by
      rintro ⟨y, u, rfl⟩
      exact ⟨⟨(u.val, A u), A.mem_graph u⟩, rfl⟩
    let g : A.graph →L[Real] Real :=
      (innerSL Real x).comp ((ContinuousLinearMap.fst Real H H).comp A.graph.subtypeL)
    have hker : LinearMap.ker f.toLinearMap ≤ LinearMap.ker g.toLinearMap := by
      intro v hv
      have hvZero : v.val.2 = 0 := congrArg Subtype.val hv
      have hvNull : v.val.1 ∈ operatorNullSpace A := by
        change (v.val.1, 0) ∈ A.graph
        simpa only [← hvZero] using v.property
      exact ((operatorNullSpace A).mem_orthogonal' x).mp hx v.val.1 hvNull
    obtain ⟨φ, hφ⟩ := continuous_descent f g hf hker
    let z : LinearMap.range A.toFun := (InnerProductSpace.toDual Real _).symm φ
    have hz (u : A.domain) : inner Real x u.val = inner Real (z : H) (A u) := by
      have h := hφ ⟨(u.val, A u), A.mem_graph u⟩
      have hr := InnerProductSpace.toDual_symm_apply (𝕜 := Real)
        (x := f ⟨(u.val, A u), A.mem_graph u⟩) (y := φ)
      exact h.symm.trans hr.symm
    have hzDomain : (z : H) ∈ A.adjoint.domain :=
      A.mem_adjoint_domain_of_exists z ⟨x, hz⟩
    exact ⟨⟨z, hzDomain⟩, LinearPMap.adjoint_apply_eq hDense _ hz⟩

theorem adjoint_range_isClosed (A : H →ₗ.[Real] H)
    (hClosed : A.IsClosed) (hDense : Dense (A.domain : Set H))
    (hRange : IsClosed (LinearMap.range A.toFun : Set H)) :
    IsClosed (LinearMap.range A.adjoint.toFun : Set H) := by
  rw [adjoint_range_eq_null_orthogonal A hClosed hDense hRange]
  exact (operatorNullSpace A).isClosed_orthogonal

theorem adjoint_range_isClosed_iff (A : H →ₗ.[Real] H)
    (hClosed : A.IsClosed) (hDense : Dense (A.domain : Set H))
    (hAdjointDense : Dense (A.adjoint.domain : Set H)) :
    IsClosed (LinearMap.range A.adjoint.toFun : Set H) ↔
      IsClosed (LinearMap.range A.toFun : Set H) := by
  constructor
  · intro h
    have hDouble := adjoint_range_isClosed A.adjoint
      (LinearPMap.adjoint_isClosed hDense) hAdjointDense h
    rwa [P0EFTJanusProgramPT12ClosedDoubleAdjoint4D.closedOperator_adjoint_adjoint
      A hClosed hDense hAdjointDense] at hDouble
  · exact adjoint_range_isClosed A hClosed hDense

end
end JanusFormal.P0EFTJanusProgramPT12ClosedRangeAdjoint4D
