import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FourSectorFactorwiseCoreAgreement4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAExtendedBulkCoreCoordinates4D

/-! The actual Candidate-A L² core embedding is factorwise. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12FourSectorPhysicalFactorwiseEmbedding4D

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
noncomputable section

open scoped InnerProductSpace
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Bilinear4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Graph4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPGlobalCandidateAAbelianExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalFullLLGraphRiesz4D
open P0EFTJanusProgramPT12FourSectorFactorwiseCoreAgreement4D

attribute [local instance]
  coreDiffeomorphismNormedAddCommGroup
  coreDiffeomorphismNormedSpace
  coreDiffeomorphismModule
  coreDiffeomorphismInnerProductSpace
  coreAbelianNormedSpace
  coreAbelianModule
  coreAbelianInnerProductSpace
  coreMatterInnerProductSpace
  coreLLInnerProductSpace
  coreLLNormedSpace
  coreLLModule

variable (period : Real) (hPeriod : period ≠ 0)

theorem diagonalExtendedBulkL2SmoothEmbedding_factorwise
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (core : P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Graph4D.GlobalCandidateADiagonalExtendedBulkSmoothCore
      period hPeriod data analysis) :
    factorwiseEmbedding
        (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding
          period hPeriod metric)
        (globalPairedAbelianOffShellSmoothEmbedding period hPeriod metric)
        ((programPPrimitiveSpinCMatterL2GraphEquiv period hPeriod massSquared
          ).symm.toLinearMap.comp
          (programPPrimitiveSpinCMatterGraphFiniteRealLinearMap
            period hPeriod massSquared))
        (globalCandidateAFullLLSmoothEmbedding period hPeriod data analysis)
        core =
      P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Graph4D.diagonalExtendedBulkL2SmoothEmbedding
        period hPeriod metric massSquared data analysis core := by
  rfl

end
end P0EFTJanusProgramPT12FourSectorPhysicalFactorwiseEmbedding4D
end JanusFormal
