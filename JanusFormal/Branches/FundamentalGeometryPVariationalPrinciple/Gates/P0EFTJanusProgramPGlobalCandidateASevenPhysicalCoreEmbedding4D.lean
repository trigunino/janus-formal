import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D

/-!
# Lightweight seven-physical core embedding

This module exports the dense-core embedding without importing the later
blockwise H11 estimates.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateASevenPhysicalBlockBounds4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 2400000

noncomputable section

open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev PhysicalCore
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :=
  GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod analysis

private def rawPhysicalCoreEmbedding
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :=
  diagonalExtendedBulkL2SmoothEmbedding period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
    couplings.matterMassSquared data analysis

/-- The dense algebraic embedding used by the H11 physical estimates. -/
def globalCandidateASevenPhysicalCoreEmbedding
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    PhysicalCore period hPeriod analysis →ₗ[Real]
      CommonAugmentedHilbert period hPeriod configuration data analysis where
  toFun := fun current =>
    rawPhysicalCoreEmbedding period hPeriod configuration data analysis current
  map_add' first second := by
    change
      rawPhysicalCoreEmbedding period hPeriod configuration data analysis
          (first + second) =
        rawPhysicalCoreEmbedding period hPeriod configuration data analysis first +
          rawPhysicalCoreEmbedding period hPeriod configuration data analysis second
    exact map_add
      (rawPhysicalCoreEmbedding period hPeriod configuration data analysis)
      first second
  map_smul' scalar current := by
    change
      rawPhysicalCoreEmbedding period hPeriod configuration data analysis
          (scalar • current) =
        scalar •
          rawPhysicalCoreEmbedding period hPeriod configuration data analysis current
    exact map_smul
      (rawPhysicalCoreEmbedding period hPeriod configuration data analysis)
      scalar current

end
end P0EFTJanusProgramPGlobalCandidateASevenPhysicalBlockBounds4D
end JanusFormal
