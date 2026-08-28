import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPCandidateAFiveSectorProjectionPhysicalSmallness4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPCandidateAFiveSectorPrincipalOperatorGarding4D

/-!
# Operator lower bound from a positive five-sector projection resolution

This adapter turns the projection-resolution quadratic packet into the
projected-principal operator packet used by the actual-kernel H12 bridge.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPCandidateAFiveSectorProjectionOperatorGarding4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPCandidateAFiveSectorProjectionPhysicalSmallness4D
open P0EFTJanusProgramPCandidateAFiveSectorPrincipalOperatorGarding4D
open P0EFTJanusProgramPCandidateAFiveSectorPrincipalPhysicalSmallness4D
open P0EFTJanusProgramPCandidateAFiveSectorPrincipalProjectionResolution4D

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace Real E]

/-- Positive projection resolution identified with one displayed operator
energy. -/
structure CandidateAFiveSectorProjectionOperatorGardingData
    (operator : E →L[Real] E) where
  finiteMargin : CandidateAFiveSectorProjectionPhysicalSmallnessData (E := E)
  energy_upper : ∀ vector,
    finiteMargin.totalEnergy vector ≤ ‖vector‖ * ‖operator vector‖

namespace CandidateAFiveSectorProjectionOperatorGardingData

/-- Established projected-principal operator packet. -/
def toPrincipalOperatorGardingData
    {operator : E →L[Real] E}
    (data : CandidateAFiveSectorProjectionOperatorGardingData operator) :
    CandidateAFiveSectorPrincipalOperatorGardingData operator where
  finiteMargin := data.finiteMargin.toPrincipalPhysicalSmallnessData
  energy_upper := data.energy_upper

/-- Explicit operator lower bound. -/
theorem lowerBound
    {operator : E →L[Real] E}
    (data : CandidateAFiveSectorProjectionOperatorGardingData operator)
    (vector : E) :
    data.finiteMargin.margin * ‖vector‖ ≤ ‖operator vector‖ := by
  simpa [CandidateAFiveSectorProjectionPhysicalSmallnessData.margin,
    toPrincipalOperatorGardingData,
    CandidateAFiveSectorProjectionPhysicalSmallnessData.toPrincipalPhysicalSmallnessData,
    CandidateAFiveSectorPrincipalProjectionResolutionData.margin,
    CandidateAFiveSectorPrincipalPhysicalSmallnessData.margin] using
      data.toPrincipalOperatorGardingData.lowerBound vector

/-- Injectivity on the zero-mode complement. -/
theorem injective
    {operator : E →L[Real] E}
    (data : CandidateAFiveSectorProjectionOperatorGardingData operator) :
    Function.Injective operator :=
  data.toPrincipalOperatorGardingData.injective

/-- Public projection-resolution operator checkpoint. -/
theorem candidateA_five_sector_projection_operator_garding_gate
    (operator : E →L[Real] E)
    (data : CandidateAFiveSectorProjectionOperatorGardingData operator) :
    (∀ vector,
      data.finiteMargin.margin * ‖vector‖ ≤ ‖operator vector‖) ∧
      Function.Injective operator :=
  ⟨data.lowerBound, data.injective⟩

end CandidateAFiveSectorProjectionOperatorGardingData

end
end P0EFTJanusProgramPCandidateAFiveSectorProjectionOperatorGarding4D
end JanusFormal
