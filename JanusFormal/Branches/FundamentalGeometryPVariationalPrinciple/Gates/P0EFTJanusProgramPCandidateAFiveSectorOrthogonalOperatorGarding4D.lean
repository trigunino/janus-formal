import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPCandidateAFiveSectorOrthogonalPhysicalSmallness4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPCandidateAFiveSectorSelfAdjointOperatorGarding4D

/-!
# Operator Gårding from one orthogonal sector decomposition

The finite total margin generated in orthogonal sector coordinates is now
identified with one displayed Hessian operator energy.  This gives the linear
operator lower bound and injectivity without exposing the generated projectors
as input fields.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPCandidateAFiveSectorOrthogonalOperatorGarding4D

set_option autoImplicit false
set_option maxHeartbeats 4600000
set_option synthInstance.maxHeartbeats 2300000

noncomputable section

open scoped InnerProductSpace
open P0EFTJanusProgramPCandidateAFiveSectorOrthogonalPhysicalSmallness4D
open P0EFTJanusProgramPCandidateAFiveSectorSelfAdjointOperatorGarding4D

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E]

variable (Component : CandidateAZeroModeSector → Type*)
  [∀ sector, NormedAddCommGroup (Component sector)]
  [∀ sector, NormedSpace Real (Component sector)]
  [∀ sector, InnerProductSpace Real (Component sector)]

/-- Orthogonal-coordinate finite margin identified with one operator. -/
structure CandidateAFiveSectorOrthogonalOperatorGardingData
    (operator : E →L[Real] E) where
  finiteMargin : CandidateAFiveSectorOrthogonalPhysicalSmallnessData
    (E := E) Component
  energy_upper : ∀ vector,
    finiteMargin.totalEnergy vector ≤ ‖vector‖ * ‖operator vector‖

namespace CandidateAFiveSectorOrthogonalOperatorGardingData

/-- Generate the previous natural-projection operator packet. -/
def toSelfAdjointOperatorGarding
    {operator : E →L[Real] E}
    (data : CandidateAFiveSectorOrthogonalOperatorGardingData
      (Component := Component) operator) :
    CandidateAFiveSectorSelfAdjointOperatorGardingData operator where
  finiteMargin := data.finiteMargin.toSelfAdjointPhysicalSmallness Component
  energy_upper := data.energy_upper

/-- Explicit operator lower bound. -/
theorem lowerBound
    {operator : E →L[Real] E}
    (data : CandidateAFiveSectorOrthogonalOperatorGardingData
      (Component := Component) operator)
    (vector : E) :
    data.finiteMargin.margin Component * ‖vector‖ ≤ ‖operator vector‖ := by
  simpa [CandidateAFiveSectorOrthogonalPhysicalSmallnessData.margin,
    CandidateAFiveSectorSelfAdjointPhysicalSmallnessData.margin] using
      data.toSelfAdjointOperatorGarding Component |>.lowerBound vector

/-- Injectivity follows from the positive generated margin. -/
theorem injective
    {operator : E →L[Real] E}
    (data : CandidateAFiveSectorOrthogonalOperatorGardingData
      (Component := Component) operator) :
    Function.Injective operator :=
  data.toSelfAdjointOperatorGarding Component |>.injective

/-- Public orthogonal-coordinate operator checkpoint. -/
theorem candidateA_five_sector_orthogonal_operator_garding_gate
    (operator : E →L[Real] E)
    (data : CandidateAFiveSectorOrthogonalOperatorGardingData
      (Component := Component) operator) :
    (∀ vector,
      data.finiteMargin.margin Component * ‖vector‖ ≤ ‖operator vector‖) ∧
      Function.Injective operator :=
  ⟨data.lowerBound Component, data.injective Component⟩

end CandidateAFiveSectorOrthogonalOperatorGardingData

end
end P0EFTJanusProgramPCandidateAFiveSectorOrthogonalOperatorGarding4D
end JanusFormal
