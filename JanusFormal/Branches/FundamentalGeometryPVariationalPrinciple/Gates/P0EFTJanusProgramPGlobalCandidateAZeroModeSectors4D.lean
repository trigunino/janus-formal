import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteKernelSectorClassification4D

/-!
# Physical sectors for Candidate-A zero modes

The terminal Candidate-A tangent is D10-free.  Its actual zero modes can still
be classified by the physical origin of their leading component without
assuming that the full interacting Hessian is block diagonal.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAZeroModeSectors4D

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open P0EFTJanusProgramPFiniteKernelNamedModes4D
open P0EFTJanusProgramPFiniteKernelSectorClassification4D

/-- Physical labels available in the corrected Candidate-A Hessian.  There is
intentionally no D10 case. -/
inductive GlobalCandidateAZeroModeSector
  | metricDiffeomorphism
  | abelianGauge
  | primitiveSpinCMatter
  | longitudinalLL
  | boundaryFiniteBV
  deriving DecidableEq, Fintype

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]
variable {operator : E →L[Real] E}
variable {ZeroMode : Type*} [Fintype ZeroMode] [DecidableEq ZeroMode]

/-- Candidate-A spelling of a sector-classified named kernel. -/
abbrev GlobalCandidateAZeroModeSectorClassification
    (operator : E →L[Real] E) (ZeroMode : Type*)
    [Fintype ZeroMode] [DecidableEq ZeroMode] :=
  FiniteKernelSectorClassification operator ZeroMode
    GlobalCandidateAZeroModeSector

/-- Exact number of zero modes in one Candidate-A physical sector. -/
def globalCandidateAZeroModeMultiplicity
    (classification :
      GlobalCandidateAZeroModeSectorClassification operator ZeroMode)
    (physicalSector : GlobalCandidateAZeroModeSector) : Nat :=
  classification.multiplicity physicalSector

/-- The actual kernel dimension is the sum of the five D10-free sector
multiplicities. -/
theorem globalCandidateAZeroMode_finrank_decomposition
    (classification :
      GlobalCandidateAZeroModeSectorClassification operator ZeroMode) :
    Module.finrank Real operator.ker =
      ∑ physicalSector : GlobalCandidateAZeroModeSector,
        globalCandidateAZeroModeMultiplicity classification physicalSector :=
  classification.kernel_finrank_eq_sum_multiplicity

/-- Expanded five-sector form of the same identity. -/
theorem globalCandidateAZeroMode_finrank_five_sectors
    (classification :
      GlobalCandidateAZeroModeSectorClassification operator ZeroMode) :
    Module.finrank Real operator.ker =
      globalCandidateAZeroModeMultiplicity classification
          .metricDiffeomorphism +
        globalCandidateAZeroModeMultiplicity classification .abelianGauge +
        globalCandidateAZeroModeMultiplicity classification
          .primitiveSpinCMatter +
        globalCandidateAZeroModeMultiplicity classification .longitudinalLL +
        globalCandidateAZeroModeMultiplicity classification .boundaryFiniteBV := by
  rw [globalCandidateAZeroMode_finrank_decomposition]
  decide

/-- Public Candidate-A zero-mode sector checkpoint. -/
theorem global_candidateA_zeroMode_sector_gate
    (classification :
      GlobalCandidateAZeroModeSectorClassification operator ZeroMode) :
    Module.finrank Real operator.ker =
      ∑ physicalSector : GlobalCandidateAZeroModeSector,
        globalCandidateAZeroModeMultiplicity classification physicalSector :=
  globalCandidateAZeroMode_finrank_decomposition classification

end
end P0EFTJanusProgramPGlobalCandidateAZeroModeSectors4D
end JanusFormal
