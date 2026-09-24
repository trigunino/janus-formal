import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12ResolventInverseApproximation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12MinimalNormInverse4D

/-! Strong graph convergence to the actual range inverse, without a spectral gap. -/
namespace JanusFormal.P0EFTJanusProgramPT12ResolventInverseConvergence4D
set_option autoImplicit false
noncomputable section
open Filter Set
open scoped Topology InnerProductSpace
open P0EFTJanusProgramPT12NormalGraphResolvent4D
open P0EFTJanusProgramPT12ClosedRangeAdjoint4D
open P0EFTJanusProgramPT12MinimalNormInverse4D
open P0EFTJanusProgramPT12ResolventInverseApproximation4D
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace Real H] [CompleteSpace H]
variable (A : H →ₗ.[Real] H) (hClosed : A.IsClosed)

theorem normalResolvent_fixedSpace :
    (normalResolvent A hClosed).eqLocus (1 : H →L[Real] H) = operatorNullSpace A := by
  ext u
  exact normalResolvent_fixed_iff_null A hClosed u

theorem resolventMean_tendsto (u : H) :
    Tendsto (fun n => resolventMean A hClosed n u) atTop
      (𝓝 (u - (operatorNullSpace A)ᗮ.starProjection u)) := by
  letI : CompleteSpace (operatorNullSpace A) :=
    (operatorNullSpace_isClosed A hClosed).completeSpace_coe
  have h := (normalResolvent A hClosed).tendsto_birkhoffAverage_orthogonalProjection
    (normalResolvent_opNorm_le A hClosed) u
  change Tendsto (fun n => birkhoffAverage Real (normalResolvent A hClosed) id n u) atTop
    (𝓝 (((normalResolvent A hClosed).eqLocus (1 : H →L[Real] H)).starProjection u)) at h
  simp only [normalResolvent_fixedSpace] at h
  simpa only [resolventMean, Submodule.starProjection_orthogonal_val, sub_sub_cancel, Function.comp_def]
    using h.comp (tendsto_add_atTop_nat 1)

theorem normalResolventImage_of_null (u : H) (hu : (u, 0) ∈ A.graph) :
    normalResolventImage A hClosed u = 0 := by
  have h := normalResolvent_graph A hClosed u
  rw [normalResolvent_fixed_of_null A hClosed u hu] at h
  exact A.mem_graph_snd_inj h hu rfl

theorem resolventInverseAverage_graph_tendsto (u : A.domain) :
    Tendsto (fun n => (resolventInverseAverage A hClosed n (A u),
      A u - normalResolventImage A hClosed (resolventMean A hClosed n u.val))) atTop
      (𝓝 ((operatorNullSpace A)ᗮ.starProjection u.val, A u)) := by
  letI : CompleteSpace (operatorNullSpace A) :=
    (operatorNullSpace_isClosed A hClosed).completeSpace_coe
  let k := (operatorNullSpace A).starProjection u.val
  have hk : (k, 0) ∈ A.graph := ((operatorNullSpace A).orthogonalProjectionOnto u.val).property
  have hMean : Tendsto (fun n => resolventMean A hClosed n u.val) atTop (𝓝 k) := by
    simpa only [Submodule.starProjection_orthogonal_val, sub_sub_cancel] using
      resolventMean_tendsto A hClosed u.val
  have hR := (normalResolvent A hClosed).continuous.continuousAt.tendsto.comp hMean
  have hW := (normalResolventImage A hClosed).continuous.continuousAt.tendsto.comp hMean
  rw [normalResolvent_fixed_of_null A hClosed k hk] at hR
  rw [normalResolventImage_of_null A hClosed k hk] at hW
  simpa only [resolventInverseAverage_on_domain, Submodule.starProjection_orthogonal_val,
    sub_zero, k, Function.comp_def] using
    (tendsto_const_nhds.sub hR).prodMk_nhds (tendsto_const_nhds.sub hW)

theorem resolventInverseAverage_mem_domain (n : Nat) (rhs : (minimalNormInverse A).domain) :
    resolventInverseAverage A hClosed n rhs.val ∈ A.domain := by
  have hRange : rhs.val ∈ LinearMap.range A.toFun :=
    (minimalNormInverse_domain A hClosed) ▸ rhs.property
  obtain ⟨u, hu⟩ := hRange
  change A u = rhs.val at hu
  rw [← hu]
  exact LinearPMap.mem_domain_of_mem_graph (resolventInverseAverage_graph A hClosed n u)

theorem resolventInverseAverage_tendsto_inverse_graph (rhs : (minimalNormInverse A).domain) :
    Tendsto (fun n =>
      (resolventInverseAverage A hClosed n rhs.val,
        A ⟨_, resolventInverseAverage_mem_domain A hClosed n rhs⟩)) atTop
      (𝓝 (minimalNormInverse A rhs, rhs.val)) := by
  have hRange : rhs.val ∈ LinearMap.range A.toFun :=
    (minimalNormInverse_domain A hClosed) ▸ rhs.property
  obtain ⟨u, hu⟩ := hRange
  change A u = rhs.val at hu
  have hValue (n : Nat) :
      A ⟨_, resolventInverseAverage_mem_domain A hClosed n rhs⟩ =
        A u - normalResolventImage A hClosed (resolventMean A hClosed n u.val) := by
    have h := resolventInverseAverage_graph A hClosed n u
    rw [hu] at h ⊢
    exact A.mem_graph_snd_inj (A.mem_graph _) h rfl
  simpa only [hValue, hu, minimalNormInverse_apply_of_solution A hClosed rhs u hu] using
    resolventInverseAverage_graph_tendsto A hClosed u

end
end JanusFormal.P0EFTJanusProgramPT12ResolventInverseConvergence4D
