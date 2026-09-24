import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12NormalResolventDefect4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12ClosedRangeAdjoint4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12NullQuotientFredholm4D

/-! Closed range is preserved by the bounded normal defect, without a spectral assumption. -/
namespace JanusFormal.P0EFTJanusProgramPT12NormalDefectClosedRange4D
set_option autoImplicit false
noncomputable section
open Set
open P0EFTJanusProgramPT12NormalResolventDefect4D
open P0EFTJanusProgramPT12ClosedRangeAdjoint4D
open P0EFTJanusProgramPT12NullQuotientFredholm4D
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace Real H] [CompleteSpace H]
variable (A : H →ₗ.[Real] H) (hClosed : A.IsClosed) (hDense : Dense (A.domain : Set H))

include hDense in
theorem normalDefect_range_le_adjoint :
    LinearMap.range (normalDefect A hClosed).toLinearMap ≤ LinearMap.range A.adjoint.toFun := by
  intro y hy
  obtain ⟨u, hImage, hValue⟩ := (normalDefect_range_iff A hClosed hDense y).mp hy
  exact ⟨⟨A u, hImage⟩, hValue⟩

include hDense in
theorem normalDefect_range_eq_adjoint_of_closedRange
    (hRange : IsClosed (LinearMap.range A.toFun : Set H)) :
    LinearMap.range (normalDefect A hClosed).toLinearMap = LinearMap.range A.adjoint.toFun := by
  apply le_antisymm (normalDefect_range_le_adjoint A hClosed hDense)
  rintro y ⟨w, rfl⟩
  let R := LinearMap.range A.toFun
  letI : CompleteSpace R := hRange.completeSpace_coe
  let p : R := R.orthogonalProjectionOnto w.val
  obtain ⟨u, hu⟩ := p.property
  have hNull : (w.val - p.val, 0) ∈ A.adjoint.graph :=
    (rangeOrthogonal_iff_adjoint_graph A hDense _).mp (R.sub_starProjection_mem_orthogonal w.val)
  have hGraph : (p.val, A.adjoint w) ∈ A.adjoint.graph := by
    have h := A.adjoint.graph.sub_mem (A.adjoint.mem_graph w) hNull
    simpa only [Prod.mk_sub_mk, sub_sub_cancel, sub_zero] using h
  rw [← hu] at hGraph
  have hDomain := LinearPMap.mem_domain_of_mem_graph hGraph
  apply (normalDefect_range_iff A hClosed hDense _).mpr
  exact ⟨u, hDomain, A.adjoint.mem_graph_snd_inj (A.adjoint.mem_graph _) hGraph rfl⟩

include hDense in
theorem normalDefect_adjoint_range_eq_of_closedRange
    (hRange : IsClosed (LinearMap.range (normalDefect A hClosed).toLinearMap : Set H)) :
    LinearMap.range A.adjoint.toFun = LinearMap.range (normalDefect A hClosed).toLinearMap := by
  let B := normalDefect A hClosed
  have hOrth : (LinearMap.range B.toLinearMap)ᗮ = LinearMap.ker B.toLinearMap := by
    rw [ContinuousLinearMap.orthogonal_range, (normalDefect_selfAdjoint A hClosed).adjoint_eq]
  have hBRange : LinearMap.range B.toLinearMap = (LinearMap.ker B.toLinearMap)ᗮ := by
    rw [← hOrth, Submodule.orthogonal_orthogonal_eq_closure]
    exact hRange.submodule_topologicalClosure_eq.symm
  apply le_antisymm
  · rw [hBRange]
    rintro y ⟨w, rfl⟩
    rw [Submodule.mem_orthogonal']
    intro z hz
    have hNull := (normalDefect_zero_iff A hClosed z).mp hz
    obtain ⟨u, hu, hAu⟩ := A.mem_graph_iff.mp hNull
    change (u : H) = z at hu
    have h := LinearPMap.adjoint_isFormalAdjoint hDense w u
    rw [hAu, inner_zero_right] at h
    change inner Real (A.adjoint w) z = 0
    rw [← hu]
    exact h
  · exact normalDefect_range_le_adjoint A hClosed hDense

include hDense in
theorem normalDefect_range_isClosed_iff (hAdjointDense : Dense (A.adjoint.domain : Set H)) :
    IsClosed (LinearMap.range (normalDefect A hClosed).toLinearMap : Set H) ↔
      IsClosed (LinearMap.range A.toFun : Set H) := by
  constructor
  · intro hRange
    apply (adjoint_range_isClosed_iff A hClosed hDense hAdjointDense).mp
    rw [normalDefect_adjoint_range_eq_of_closedRange A hClosed hDense hRange]
    exact hRange
  · intro hRange
    rw [normalDefect_range_eq_adjoint_of_closedRange A hClosed hDense hRange]
    exact adjoint_range_isClosed A hClosed hDense hRange

theorem normalDefect_kernel_finite_iff :
    FiniteDimensional Real (LinearMap.ker (normalDefect A hClosed).toLinearMap) ↔
      FiniteDimensional Real (LinearMap.ker A.toFun) := by
  constructor
  · intro h; letI := h; exact (normalDefectKernelEquiv A hClosed).symm.finiteDimensional
  · intro h; letI := h; exact (normalDefectKernelEquiv A hClosed).finiteDimensional

end
end JanusFormal.P0EFTJanusProgramPT12NormalDefectClosedRange4D
