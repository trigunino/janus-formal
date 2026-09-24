import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12MinimalNormInverse4D

/-! Boundedness of the actual range inverse is exactly the closed-range obligation. -/
namespace JanusFormal.P0EFTJanusProgramPT12MinimalNormInverseBound4D
set_option autoImplicit false
noncomputable section
open Set
open P0EFTJanusProgramPT12MinimalNormInverse4D
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace Real H] [CompleteSpace H]
variable (A : H →ₗ.[Real] H) (hClosed : A.IsClosed)
include hClosed

theorem closedRange_of_minimalNormInverse_bound (C : NNReal)
    (hBound : ∀ y : (minimalNormInverse A).domain, ‖minimalNormInverse A y‖ ≤ C * ‖y.val‖) :
    IsClosed (LinearMap.range A.toFun : Set H) := by
  let I := minimalNormInverse A
  letI : CompleteSpace I.graph := (minimalNormInverse_isClosed A hClosed).completeSpace_coe
  let input : I.graph →L[Real] H := (ContinuousLinearMap.fst Real H H).comp I.graph.subtypeL
  have hEstimate (v : I.graph) : ‖v‖ ≤ (C + 1 : NNReal) * ‖input v‖ := by
    obtain ⟨y, hy, hIy⟩ := I.mem_graph_iff.mp v.property
    have h := hBound y
    rw [hy, hIy] at h
    change max ‖v.val.1‖ ‖v.val.2‖ ≤ ((C + 1 : NNReal) : Real) * ‖v.val.1‖
    simp only [NNReal.coe_add, NNReal.coe_one]
    have hC := C.coe_nonneg
    have hv := norm_nonneg v.val.1
    apply max_le <;> nlinarith
  have hRange := (input.antilipschitz_of_bound hEstimate).isClosed_range input.uniformContinuous
  have hEq : LinearMap.range input.toLinearMap = I.domain := by
    ext x
    constructor
    · rintro ⟨v, rfl⟩
      exact LinearPMap.mem_domain_of_mem_graph v.property
    · intro hx
      exact ⟨⟨(x, I ⟨x, hx⟩), I.mem_graph ⟨x, hx⟩⟩, rfl⟩
  change IsClosed (LinearMap.range input.toLinearMap : Set H) at hRange
  rw [hEq, minimalNormInverse_domain A hClosed] at hRange
  exact hRange

theorem minimalNormInverse_bounded_iff_closedRange :
    (∃ C : NNReal, ∀ y : (minimalNormInverse A).domain, ‖minimalNormInverse A y‖ ≤ C * ‖y.val‖) ↔
      IsClosed (LinearMap.range A.toFun : Set H) := by
  constructor
  · rintro ⟨C, hC⟩
    exact closedRange_of_minimalNormInverse_bound A hClosed C hC
  · intro hRange
    let I := minimalNormInverse A
    have hDomain : IsClosed (I.domain : Set H) := by
      rw [minimalNormInverse_domain A hClosed]
      exact hRange
    letI : CompleteSpace I.domain := hDomain.completeSpace_coe
    have hGraph : IsClosed (I.toFun.graph : Set (I.domain × H)) := by
      have hPre := (minimalNormInverse_isClosed A hClosed).preimage
        (show Continuous (fun p : I.domain × H => (p.1.val, p.2)) by fun_prop)
      convert hPre using 1
      ext p
      change p ∈ I.toFun.graph ↔ (p.1.val, p.2) ∈ I.graph
      rw [LinearMap.mem_graph_iff]
      change p.2 = I p.1 ↔ (p.1.val, p.2) ∈ I.graph
      constructor
      · intro h; exact I.mem_graph_iff.mpr ⟨p.1, rfl, h.symm⟩
      · intro h; exact (I.mem_graph_snd_inj (I.mem_graph p.1) h rfl).symm
    let f : I.domain →L[Real] H := ⟨I.toFun, I.toFun.continuous_of_isClosed_graph hGraph⟩
    exact ⟨‖f‖₊, fun y => f.le_opNorm y⟩

end
end JanusFormal.P0EFTJanusProgramPT12MinimalNormInverseBound4D
