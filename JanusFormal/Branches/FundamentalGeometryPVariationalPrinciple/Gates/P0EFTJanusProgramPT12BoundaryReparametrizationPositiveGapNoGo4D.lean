import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalBoundaryReparametrizationHilbertHessian4D

/-! The exact boundary-reparametrization Riesz operator has no positive diagonal gap. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12BoundaryReparametrizationPositiveGapNoGo4D

set_option autoImplicit false
noncomputable section

open scoped InnerProductSpace
open P0EFTJanusProgramPGlobalBoundaryReparametrizationHilbertHessian4D

/-- A nonempty null-face set supplies a nonzero finite boundary direction. -/
theorem boundaryReparametrization_single_ne_zero
    (NullFace : Type*) [Fintype NullFace] [Nonempty NullFace] :
    ∃ b : GlobalCandidateABoundaryReparametrizationHilbert NullFace, b ≠ 0 := by
  classical
  let i : NullFace := Classical.choice inferInstance
  refine ⟨EuclideanSpace.single i (1 : Real), ?_⟩
  intro h
  simp at h

/-- No strictly positive lower diagonal bound holds for the concrete
same-action boundary Riesz operator when a null face exists. -/
theorem no_positive_boundaryReparametrizationRiesz_diagonal_bound
    (NullFace : Type*) [Fintype NullFace] [Nonempty NullFace]
    (c : Real) (hc : 0 < c) :
    ¬ ∀ b : GlobalCandidateABoundaryReparametrizationHilbert NullFace,
      c * ‖b‖ ^ 2 ≤
        inner Real
          (globalCandidateABoundaryReparametrizationRieszOperator NullFace b) b := by
  intro hbound
  obtain ⟨b, hb⟩ := boundaryReparametrization_single_ne_zero NullFace
  have hpos : 0 < c * ‖b‖ ^ 2 :=
    mul_pos hc (sq_pos_of_pos (norm_pos_iff.mpr hb))
  have hzero :
      inner Real
        (globalCandidateABoundaryReparametrizationRieszOperator NullFace b) b = 0 := by
    simp [globalCandidateABoundaryReparametrizationRieszOperator]
  have hle := hbound b
  rw [hzero] at hle
  exact (not_le_of_gt hpos) hle

end
end P0EFTJanusProgramPT12BoundaryReparametrizationPositiveGapNoGo4D
end JanusFormal
