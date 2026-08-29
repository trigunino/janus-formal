import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateASevenPhysicalContinuousExtension4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteBlockBilinearBoundSum4D

/-!
# Candidate-A H11 estimate: H10 Robin plus six physical blocks

This specialization fixes the finite index to the six non-Robin Candidate-A
blocks exported by the H11 common-domain layer.  Matter and LL do not occur in
this family, and the Robin term is necessarily the pullback of the unique H10
Hessian.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAH10RobinSixBlockBound4D

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalContinuousExtension4D
open P0EFTJanusProgramPFiniteBlockBilinearBoundSum4D

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [NormedAddCommGroup F] [NormedSpace Real F]

/-- The common-domain physical form with the exact seven allowed summands. -/
def candidateAH10RobinPlusSixPhysicalForm
    (h10Robin : F →L[Real] F →L[Real] Real)
    (boundaryProjection : E →L[Real] F)
    (physical : GlobalCandidateANonRobinPhysicalBlock →
      E →L[Real] E →L[Real] Real) :
    E →L[Real] E →L[Real] Real :=
  robinPlusFinitePhysicalForm h10Robin boundaryProjection physical

/-- The H11 estimate contains one automatic H10 constant and exactly six
non-Robin constants. -/
theorem norm_candidateAH10RobinPlusSixPhysicalForm_le
    (h10Robin : F →L[Real] F →L[Real] Real)
    (boundaryProjection : E →L[Real] F)
    (physical : GlobalCandidateANonRobinPhysicalBlock →
      E →L[Real] E →L[Real] Real)
    (constant : GlobalCandidateANonRobinPhysicalBlock → Real)
    (constant_nonneg : ∀ block, 0 ≤ constant block)
    (estimate : ∀ block first second,
      ‖physical block first second‖ ≤
        constant block * ‖first‖ * ‖second‖)
    (first second : E) :
    ‖candidateAH10RobinPlusSixPhysicalForm h10Robin boundaryProjection physical
        first second‖ ≤
      ((‖h10Robin‖ * ‖boundaryProjection‖ * ‖boundaryProjection‖) +
          ∑ block : GlobalCandidateANonRobinPhysicalBlock, constant block) *
        ‖first‖ * ‖second‖ :=
  norm_robinPlusFinitePhysicalForm_le h10Robin boundaryProjection physical
    constant constant_nonneg estimate first second

/-- Symmetry of H10 and of the six physical blocks gives symmetry of the exact
seven-block Candidate-A form. -/
theorem candidateAH10RobinPlusSixPhysicalForm_symmetric
    (h10Robin : F →L[Real] F →L[Real] Real)
    (boundaryProjection : E →L[Real] F)
    (physical : GlobalCandidateANonRobinPhysicalBlock →
      E →L[Real] E →L[Real] Real)
    (hRobin : ∀ first second,
      h10Robin first second = h10Robin second first)
    (hPhysical : ∀ block first second,
      physical block first second = physical block second first) :
    ∀ first second,
      candidateAH10RobinPlusSixPhysicalForm h10Robin boundaryProjection physical
          first second =
        candidateAH10RobinPlusSixPhysicalForm h10Robin boundaryProjection physical
          second first :=
  robinPlusFinitePhysicalForm_symmetric h10Robin boundaryProjection physical
    hRobin hPhysical

/-- Public H11 checkpoint specialized to the actual Candidate-A block list. -/
theorem candidateA_h10_robin_six_block_bound_gate
    (h10Robin : F →L[Real] F →L[Real] Real)
    (boundaryProjection : E →L[Real] F)
    (physical : GlobalCandidateANonRobinPhysicalBlock →
      E →L[Real] E →L[Real] Real)
    (constant : GlobalCandidateANonRobinPhysicalBlock → Real)
    (constant_nonneg : ∀ block, 0 ≤ constant block)
    (estimate : ∀ block first second,
      ‖physical block first second‖ ≤
        constant block * ‖first‖ * ‖second‖)
    (hRobin : ∀ first second,
      h10Robin first second = h10Robin second first)
    (hPhysical : ∀ block first second,
      physical block first second = physical block second first) :
    (∀ first second,
      ‖candidateAH10RobinPlusSixPhysicalForm h10Robin boundaryProjection physical
          first second‖ ≤
        ((‖h10Robin‖ * ‖boundaryProjection‖ * ‖boundaryProjection‖) +
            ∑ block : GlobalCandidateANonRobinPhysicalBlock, constant block) *
          ‖first‖ * ‖second‖) ∧
    (∀ first second,
      candidateAH10RobinPlusSixPhysicalForm h10Robin boundaryProjection physical
          first second =
        candidateAH10RobinPlusSixPhysicalForm h10Robin boundaryProjection physical
          second first) :=
  ⟨norm_candidateAH10RobinPlusSixPhysicalForm_le h10Robin boundaryProjection
      physical constant constant_nonneg estimate,
    candidateAH10RobinPlusSixPhysicalForm_symmetric h10Robin boundaryProjection
      physical hRobin hPhysical⟩

end
end P0EFTJanusProgramPGlobalCandidateAH10RobinSixBlockBound4D
end JanusFormal
