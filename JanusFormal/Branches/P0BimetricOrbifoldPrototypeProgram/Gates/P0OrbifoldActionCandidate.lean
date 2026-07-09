import JanusFormal.Branches.P0BimetricOrbifoldPrototypeProgram.Gates.P0OrbifoldActionProgram

namespace JanusFormal
namespace P0OrbifoldActionCandidate

open P0OrbifoldActionProgram

set_option autoImplicit false

structure OrbifoldActionCandidate where
  single4DOrbifoldIntegral : Prop
  bulkPalatiniCartan : Prop
  equivariantDiffeomorphismInvariant : Prop
  z2PTCompatible : Prop
  boundaryGHYTermWellPosed : Prop
  matterZ2Symmetric : Prop
  matterVariationWellPosed : Prop
  solderFieldPresent : Prop
  solderVariationWellPosed : Prop

def candidateActionProblem : OrbifoldActionProblem OrbifoldActionCandidate :=
  { lagrangian4D := fun s =>
      s.single4DOrbifoldIntegral /\ s.bulkPalatiniCartan
    diffInvariant := fun s =>
      s.equivariantDiffeomorphismInvariant
    ptCompatible := fun s =>
      s.z2PTCompatible
    boundaryVariationWellPosed := fun s =>
      s.boundaryGHYTermWellPosed
    matterVariationWellPosed := fun s =>
      s.matterZ2Symmetric /\ s.matterVariationWellPosed
    solderVariationWellPosed := fun s =>
      s.solderFieldPresent /\ s.solderVariationWellPosed }

def candidateObligationsHold (s : OrbifoldActionCandidate) : Prop :=
  s.single4DOrbifoldIntegral /\
  s.bulkPalatiniCartan /\
  s.equivariantDiffeomorphismInvariant /\
  s.z2PTCompatible /\
  s.boundaryGHYTermWellPosed /\
  s.matterZ2Symmetric /\
  s.matterVariationWellPosed /\
  s.solderFieldPresent /\
  s.solderVariationWellPosed

theorem candidate_obligations_imply_accepted_action
    (s : OrbifoldActionCandidate)
    (h : candidateObligationsHold s) :
    acceptedOrbifoldAction candidateActionProblem s := by
  rcases h with
    âŸ¨hIntegral, hPalatini, hDiff, hPT, hBoundary,
      hMatterSym, hMatterVar, hSolderField, hSolderVarâŸ©
  exact
    âŸ¨âŸ¨hIntegral, hPalatiniâŸ©,
      hDiff,
      hPT,
      hBoundary,
      âŸ¨hMatterSym, hMatterVarâŸ©,
      âŸ¨hSolderField, hSolderVarâŸ©âŸ©

theorem accepted_action_implies_candidate_obligations
    (s : OrbifoldActionCandidate)
    (h : acceptedOrbifoldAction candidateActionProblem s) :
    candidateObligationsHold s := by
  rcases h with
    âŸ¨hLag, hDiff, hPT, hBoundary, hMatter, hSolderâŸ©
  exact
    âŸ¨hLag.left,
      hLag.right,
      hDiff,
      hPT,
      hBoundary,
      hMatter.left,
      hMatter.right,
      hSolder.left,
      hSolder.rightâŸ©

theorem accepted_action_iff_candidate_obligations
    (s : OrbifoldActionCandidate) :
    acceptedOrbifoldAction candidateActionProblem s <->
      candidateObligationsHold s := by
  constructor
  Â· exact accepted_action_implies_candidate_obligations s
  Â· exact candidate_obligations_imply_accepted_action s

structure TwoAcceptedCandidates where
  left : OrbifoldActionCandidate
  right : OrbifoldActionCandidate
  leftAccepted : acceptedOrbifoldAction candidateActionProblem left
  rightAccepted : acceptedOrbifoldAction candidateActionProblem right
  distinct : left â‰  right

theorem two_accepted_candidates_block_unique_action
    (c : TwoAcceptedCandidates) :
    Not (uniqueOrbifoldAction candidateActionProblem) := by
  intro hUnique
  rcases hUnique with âŸ¨s0, _hs0, huniqâŸ©
  have hLeft : c.left = s0 := huniq c.left c.leftAccepted
  have hRight : c.right = s0 := huniq c.right c.rightAccepted
  exact c.distinct (hLeft.trans hRight.symm)

structure CandidateUniquenessCertificate where
  candidate : OrbifoldActionCandidate
  obligations : candidateObligationsHold candidate
  allAcceptedEqualCandidate :
    forall s, acceptedOrbifoldAction candidateActionProblem s -> s = candidate

def uniqueActionCertificateFromCandidate
    (c : CandidateUniquenessCertificate) :
    UniqueOrbifoldActionCertificate candidateActionProblem :=
  { candidate := c.candidate
    candidateAccepted :=
      candidate_obligations_imply_accepted_action c.candidate c.obligations
    allAcceptedEqualCandidate := c.allAcceptedEqualCandidate }

theorem candidate_uniqueness_certificate_closes_source_action
    (c : CandidateUniquenessCertificate) :
    uniqueOrbifoldAction candidateActionProblem := by
  exact certificate_implies_unique_orbifold_action
    candidateActionProblem
    (uniqueActionCertificateFromCandidate c)

theorem palatini_bulk_alone_does_not_give_accepted_action
    (s : OrbifoldActionCandidate)
    (hMissingBoundary : Not s.boundaryGHYTermWellPosed) :
    Not (acceptedOrbifoldAction candidateActionProblem s) := by
  intro hAccepted
  exact hMissingBoundary hAccepted.right.right.right.left

end P0OrbifoldActionCandidate
end JanusFormal
