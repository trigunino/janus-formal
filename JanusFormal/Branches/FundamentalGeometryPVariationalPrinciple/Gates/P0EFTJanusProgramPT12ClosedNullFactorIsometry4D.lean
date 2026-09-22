import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12ClosedNullQuotient4D

/-! Isometric inclusion of a Hilbert factor after compatible closed null quotients. -/
namespace JanusFormal
namespace P0EFTJanusProgramPT12ClosedNullFactorIsometry4D

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped InnerProductSpace

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace Real F] [CompleteSpace F]
variable (inclusion : E →ₗᵢ[Real] F)
variable (sourceNull : Submodule Real E) (targetNull : Submodule Real F)
variable [IsClosed (sourceNull : Set E)] [IsClosed (targetNull : Set F)]
variable (hNull : sourceNull ≤ (targetNull.mkQL.comp inclusion.toContinuousLinearMap).ker)
variable (hOrthogonal : ∀ vector ∈ sourceNullᗮ, inclusion vector ∈ targetNullᗮ)
open P0EFTJanusProgramPT12ClosedNullQuotient4D

def quotientFactorInclusion : (E ⧸ sourceNull) →ₗᵢ[Real] (F ⧸ targetNull) where
  toLinearMap := (sourceNull.liftQL (targetNull.mkQL.comp inclusion.toContinuousLinearMap) hNull).toLinearMap
  norm_map' vector := by
    let representative := sourceNull.quotientEquivOrthogonal vector
    have hSame : sourceNull.mkQ (representative : E) = vector :=
      (sourceNull.quotientEquivOrthogonal_symm_eq_mk representative.1 representative.2).symm.trans
        (sourceNull.quotientEquivOrthogonal.symm_apply_apply vector)
    rw [← hSame]
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
    exact (inner_mk_of_left_orthogonal _ _ _ (hOrthogonal _ representative.2)).trans
      ((inclusion.inner_map_map _ _).trans
        (inner_mk_of_left_orthogonal sourceNull _ _ representative.2).symm)

@[simp] theorem quotientFactorInclusion_mk (vector : E) :
    quotientFactorInclusion inclusion sourceNull targetNull hNull hOrthogonal (sourceNull.mkQ vector) =
      targetNull.mkQ (inclusion vector) := rfl

variable (readout : F →L[Real] E)
variable (hReadout : targetNull ≤ (sourceNull.mkQL.comp readout).ker)
variable (hPairing : ∀ vector test, inner Real (inclusion vector) test = inner Real vector (readout test))

include hPairing in
theorem quotientFactorInclusion_inner (vector : E ⧸ sourceNull) (test : F ⧸ targetNull) :
    inner Real (quotientFactorInclusion inclusion sourceNull targetNull hNull hOrthogonal vector) test =
      inner Real vector (targetNull.liftQL (sourceNull.mkQL.comp readout) hReadout test) := by
  let representative := sourceNull.quotientEquivOrthogonal vector
  have hSame : sourceNull.mkQ (representative : E) = vector :=
    (sourceNull.quotientEquivOrthogonal_symm_eq_mk representative.1 representative.2).symm.trans
      (sourceNull.quotientEquivOrthogonal.symm_apply_apply vector)
  rw [← hSame]
  obtain ⟨test, rfl⟩ := targetNull.mkQ_surjective test
  exact (inner_mk_of_left_orthogonal _ _ _ (hOrthogonal _ representative.2)).trans
    ((hPairing _ test).trans (inner_mk_of_left_orthogonal sourceNull _ _ representative.2).symm)

end
end P0EFTJanusProgramPT12ClosedNullFactorIsometry4D
end JanusFormal
