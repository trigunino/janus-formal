import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusIndependentCompleteVariationEmbedding4D

/-!
# Boundary domain of the complete Program-P variation

The current boundary condition is imposed on the genuine independent-field
curve.  This gate proves that its pullback to `ProgramPCompleteVariation4D`
depends exactly on the stored independent direction and is unchanged by the
three additional geometric D9/D10 slots.  No Fredholm-domain identification
is claimed.
-/

namespace JanusFormal
namespace P0EFTJanusCompleteVariationBoundaryDomainBridge4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusMappingTorusInducedFieldVariation4D
open P0EFTJanusMappingTorusIndependentPTBoundaryAction4D
open P0EFTJanusProgramPCommonGeometricDomain4D
open P0EFTJanusIndependentCompleteVariationEmbedding4D
open P0EFTJanusD8NormalBundleD9DisplacementBridge4D
open P0EFTJanusMappingTorusD8NonabelianGhostThroatBRST4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Boundary-admissible directions before adding the normal, tangent-ghost and
full symmetric-metric completion slots. -/
def independentBoundaryTangentDomain4D
    (domain : ProgramPCommonGeometricDomain4D period hPeriod) :
    Set (IndependentFieldVariation period hPeriod) :=
  { variation | ∀ parameter : Real,
      SatisfiesIndependentBoundary period hPeriod domain.boundary
        (independentFieldCurve period hPeriod domain.configuration
          variation parameter) }

theorem completeVariation_mem_boundaryDomain_iff
    (domain : ProgramPCommonGeometricDomain4D period hPeriod)
    (variation : ProgramPCompleteVariation4D period hPeriod) :
    variation ∈ programPBoundaryTangentDomain4D period hPeriod domain ↔
      variation.independent ∈
        independentBoundaryTangentDomain4D period hPeriod domain :=
  Iff.rfl

/-- Two completed directions with the same genuine independent-field tangent
have exactly the same boundary admissibility. -/
theorem boundaryDomain_congr_independent
    (domain : ProgramPCommonGeometricDomain4D period hPeriod)
    {first second : ProgramPCompleteVariation4D period hPeriod}
    (hIndependent : first.independent = second.independent) :
    first ∈ programPBoundaryTangentDomain4D period hPeriod domain ↔
      second ∈ programPBoundaryTangentDomain4D period hPeriod domain := by
  rw [completeVariation_mem_boundaryDomain_iff,
    completeVariation_mem_boundaryDomain_iff, hIndependent]

/-- Replace all geometric completion slots while retaining the exact
independent direction used by the boundary curve. -/
def withGeometricCompletionSlots
    (variation : ProgramPCompleteVariation4D period hPeriod)
    (normalDisplacement :
      P0EFTJanusD9D10ExactFieldContentBridge4D.Sector →
        SmoothNormalDisplacement period hPeriod)
    (diffeomorphismGhost :
      P0EFTJanusD9D10ExactFieldContentBridge4D.Sector →
        CInfinityThroatGhost period hPeriod)
    (fullMetricPerturbation :
      P0EFTJanusD9D10ExactFieldContentBridge4D.Sector →
        SmoothSymmetricCovariantTwoTensor period hPeriod) :
    ProgramPCompleteVariation4D period hPeriod where
  independent := variation.independent
  normalDisplacement := normalDisplacement
  diffeomorphismGhost := diffeomorphismGhost
  fullMetricPerturbation := fullMetricPerturbation

@[simp]
theorem withGeometricCompletionSlots_independent
    (variation : ProgramPCompleteVariation4D period hPeriod)
    (normalDisplacement :
      P0EFTJanusD9D10ExactFieldContentBridge4D.Sector →
        SmoothNormalDisplacement period hPeriod)
    (diffeomorphismGhost :
      P0EFTJanusD9D10ExactFieldContentBridge4D.Sector →
        CInfinityThroatGhost period hPeriod)
    (fullMetricPerturbation :
      P0EFTJanusD9D10ExactFieldContentBridge4D.Sector →
        SmoothSymmetricCovariantTwoTensor period hPeriod) :
    (withGeometricCompletionSlots period hPeriod variation normalDisplacement
      diffeomorphismGhost fullMetricPerturbation).independent =
        variation.independent :=
  rfl

theorem withGeometricCompletionSlots_mem_boundaryDomain_iff
    (domain : ProgramPCommonGeometricDomain4D period hPeriod)
    (variation : ProgramPCompleteVariation4D period hPeriod)
    (normalDisplacement :
      P0EFTJanusD9D10ExactFieldContentBridge4D.Sector →
        SmoothNormalDisplacement period hPeriod)
    (diffeomorphismGhost :
      P0EFTJanusD9D10ExactFieldContentBridge4D.Sector →
        CInfinityThroatGhost period hPeriod)
    (fullMetricPerturbation :
      P0EFTJanusD9D10ExactFieldContentBridge4D.Sector →
        SmoothSymmetricCovariantTwoTensor period hPeriod) :
    withGeometricCompletionSlots period hPeriod variation normalDisplacement
        diffeomorphismGhost fullMetricPerturbation ∈
        programPBoundaryTangentDomain4D period hPeriod domain ↔
      variation ∈ programPBoundaryTangentDomain4D period hPeriod domain :=
  boundaryDomain_congr_independent period hPeriod domain rfl

/-- Exact preimage statement for the canonical inclusion of the already-used
independent tangent into the complete variation type. -/
theorem independentCompleteVariation_mem_boundaryDomain_iff
    (domain : ProgramPCommonGeometricDomain4D period hPeriod)
    (variation : IndependentFieldVariation period hPeriod) :
    independentCompleteVariation period hPeriod variation ∈
        programPBoundaryTangentDomain4D period hPeriod domain ↔
      variation ∈ independentBoundaryTangentDomain4D period hPeriod domain :=
  Iff.rfl

end
end P0EFTJanusCompleteVariationBoundaryDomainBridge4D
end JanusFormal
