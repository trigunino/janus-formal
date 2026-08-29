import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPCandidateAFiveSectorSymmetricGarding4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteSectorPhysicalSmallnessGarding4D

/-!
# Candidate-A total Hessian Gårding from sector and physical margins

The principal Candidate-A form is controlled by five diagonal estimates and ten
symmetric cross-sector bounds.  The retained H11 physical form is then one
bounded perturbation.  This file combines both finite calculations and returns
a positive coercive constant for the total augmented Hessian.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPCandidateAFiveSectorPhysicalSmallnessGarding4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPFiniteSectorPhysicalSmallnessGarding4D
open P0EFTJanusProgramPCandidateAFiveSectorSymmetricGarding4D
open P0EFTJanusProgramPCandidateAZeroModeSector4D
open P0EFTJanusProgramPGlobalCandidateANamedZeroModeSectors4D

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]

/-- Complete finite analytic packet for the Candidate-A total quadratic form. -/
structure CandidateAFiveSectorPhysicalSmallnessGardingData where
  principal : CandidateAFiveSectorSymmetricGardingData (E := E)
  physicalEnergy : E → Real
  physicalConstant : Real
  physicalConstant_nonneg : 0 ≤ physicalConstant
  physical_bound : ∀ vector,
    |physicalEnergy vector| ≤ physicalConstant * ‖vector‖ ^ 2
  physical_small : physicalConstant < principal.margin
  totalEnergy : E → Real
  total_eq : ∀ vector,
    totalEnergy vector = principal.principalEnergy vector + physicalEnergy vector

namespace CandidateAFiveSectorPhysicalSmallnessGardingData

/-- Generic full-smallness packet generated from the Candidate-A sector table. -/
def toFiniteSectorPhysicalSmallnessData
    (data : CandidateAFiveSectorPhysicalSmallnessGardingData (E := E)) :
    FiniteSectorPhysicalSmallnessGardingData
      (Sector := CandidateAZeroModeSector) (E := E) where
  principal := data.principal.toQuadraticGardingData
  physicalEnergy := data.physicalEnergy
  physicalConstant := data.physicalConstant
  physicalConstant_nonneg := data.physicalConstant_nonneg
  physical_bound := data.physical_bound
  physical_small := by
    simpa [CandidateAFiveSectorSymmetricGardingData.margin,
      CandidateAFiveSectorSymmetricGardingData.couplingConstant,
      CandidateAFiveSectorSymmetricGardingData.toQuadraticGardingData,
      P0EFTJanusProgramPFiniteSectorQuadraticGarding4D.FiniteSectorQuadraticGardingData.margin]
      using data.physical_small
  totalEnergy := data.totalEnergy
  total_eq := data.total_eq

/-- Explicit total Candidate-A coercive margin. -/
def margin
    (data : CandidateAFiveSectorPhysicalSmallnessGardingData (E := E)) : Real :=
  data.principal.margin - data.physicalConstant

/-- Candidate-A full-Hessian Gårding theorem. -/
theorem candidateA_five_sector_physical_smallness_garding_gate
    (data : CandidateAFiveSectorPhysicalSmallnessGardingData (E := E)) :
    0 < data.margin ∧
      ∀ vector : E,
        data.margin * ‖vector‖ ^ 2 ≤ data.totalEnergy vector := by
  simpa [margin,
    toFiniteSectorPhysicalSmallnessData,
    FiniteSectorPhysicalSmallnessGardingData.margin,
    CandidateAFiveSectorSymmetricGardingData.margin,
    CandidateAFiveSectorSymmetricGardingData.couplingConstant,
    CandidateAFiveSectorSymmetricGardingData.toQuadraticGardingData,
    P0EFTJanusProgramPFiniteSectorQuadraticGarding4D.FiniteSectorQuadraticGardingData.margin]
    using data.toFiniteSectorPhysicalSmallnessData
      |>.finite_sector_physical_smallness_garding_gate

end CandidateAFiveSectorPhysicalSmallnessGardingData

end
end P0EFTJanusProgramPCandidateAFiveSectorPhysicalSmallnessGarding4D
end JanusFormal
