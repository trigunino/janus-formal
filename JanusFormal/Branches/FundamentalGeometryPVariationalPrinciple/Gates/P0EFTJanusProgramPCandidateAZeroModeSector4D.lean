import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype

namespace JanusFormal
namespace P0EFTJanusProgramPCandidateAZeroModeSector4D

/-- Physical sectors of the corrected Candidate-A tangent. -/
inductive CandidateAZeroModeSector
  | metricDiffeomorphism
  | abelianGauge
  | primitiveSpinCMatter
  | longitudinalLL
  | boundaryFiniteBV
  deriving DecidableEq, Fintype

end P0EFTJanusProgramPCandidateAZeroModeSector4D
end JanusFormal
