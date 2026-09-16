import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FourSectorPhysicalFactorwiseEmbedding4D

/-! The four completed coordinate projectors on the actual Candidate-A smooth core. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12FourSectorPhysicalSmoothCoreAgreement4D

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
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Graph4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Bilinear4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPGlobalCandidateAAbelianExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalFullLLGraphRiesz4D
open P0EFTJanusProgramPT12DiagonalExtendedBulkHilbertProjectors4D
open P0EFTJanusProgramPT12DiagonalExtendedBulkMetricAbelianHilbertProjectors4D
open P0EFTJanusProgramPT12FourSectorFactorwiseCoreAgreement4D
open P0EFTJanusProgramPT12FourSectorPhysicalFactorwiseEmbedding4D

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

theorem diffeomorphismProjector_smoothCore
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (core : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod data analysis) :
    diffeomorphismProjector
        (diagonalExtendedBulkL2SmoothEmbedding period hPeriod metric massSquared
          data analysis core) =
      diagonalExtendedBulkL2SmoothEmbedding period hPeriod metric massSquared
        data analysis ((core.1.1, 0), (0, 0)) := by
  exact diffeomorphismProjector_factorwiseEmbedding
    (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding
      period hPeriod metric)
    (globalPairedAbelianOffShellSmoothEmbedding period hPeriod metric)
    ((programPPrimitiveSpinCMatterL2GraphEquiv period hPeriod massSquared
      ).symm.toLinearMap.comp
      (programPPrimitiveSpinCMatterGraphFiniteRealLinearMap
        period hPeriod massSquared))
    (globalCandidateAFullLLSmoothEmbedding period hPeriod data analysis)
    core

theorem abelianProjector_smoothCore
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (core : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod data analysis) :
    abelianProjector
        (diagonalExtendedBulkL2SmoothEmbedding period hPeriod metric massSquared
          data analysis core) =
      diagonalExtendedBulkL2SmoothEmbedding period hPeriod metric massSquared
        data analysis ((0, core.1.2), (0, 0)) := by
  exact abelianProjector_factorwiseEmbedding
    (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding
      period hPeriod metric)
    (globalPairedAbelianOffShellSmoothEmbedding period hPeriod metric)
    ((programPPrimitiveSpinCMatterL2GraphEquiv period hPeriod massSquared
      ).symm.toLinearMap.comp
      (programPPrimitiveSpinCMatterGraphFiniteRealLinearMap
        period hPeriod massSquared))
    (globalCandidateAFullLLSmoothEmbedding period hPeriod data analysis)
    core

theorem matterProjector_smoothCore
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (core : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod data analysis) :
    matterProjector
        (diagonalExtendedBulkL2SmoothEmbedding period hPeriod metric massSquared
          data analysis core) =
      diagonalExtendedBulkL2SmoothEmbedding period hPeriod metric massSquared
        data analysis ((0, 0), (core.2.1, 0)) := by
  exact matterProjector_factorwiseEmbedding
    (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding
      period hPeriod metric)
    (globalPairedAbelianOffShellSmoothEmbedding period hPeriod metric)
    ((programPPrimitiveSpinCMatterL2GraphEquiv period hPeriod massSquared
      ).symm.toLinearMap.comp
      (programPPrimitiveSpinCMatterGraphFiniteRealLinearMap
        period hPeriod massSquared))
    (globalCandidateAFullLLSmoothEmbedding period hPeriod data analysis)
    core

theorem llProjector_smoothCore
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (core : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod data analysis) :
    llProjector
        (diagonalExtendedBulkL2SmoothEmbedding period hPeriod metric massSquared
          data analysis core) =
      diagonalExtendedBulkL2SmoothEmbedding period hPeriod metric massSquared
        data analysis ((0, 0), (0, core.2.2)) := by
  exact llProjector_factorwiseEmbedding
    (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding
      period hPeriod metric)
    (globalPairedAbelianOffShellSmoothEmbedding period hPeriod metric)
    ((programPPrimitiveSpinCMatterL2GraphEquiv period hPeriod massSquared
      ).symm.toLinearMap.comp
      (programPPrimitiveSpinCMatterGraphFiniteRealLinearMap
        period hPeriod massSquared))
    (globalCandidateAFullLLSmoothEmbedding period hPeriod data analysis)
    core

end
end P0EFTJanusProgramPT12FourSectorPhysicalSmoothCoreAgreement4D
end JanusFormal
