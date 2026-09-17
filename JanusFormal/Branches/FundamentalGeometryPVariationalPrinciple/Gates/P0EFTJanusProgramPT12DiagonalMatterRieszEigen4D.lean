import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FourSectorMatterEigen4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12MatterGraphRieszEigen4D

/-! A signed SpinC singleton is an eigenvector of the complete diagonal four-sector Riesz map. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12DiagonalMatterRieszEigen4D

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
noncomputable section

open scoped InnerProductSpace
open P0EFTJanusProgramPT12FourSectorMatterEigen4D
open P0EFTJanusProgramPT12MatterGraphRieszEigen4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateAAbelianExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalPairedAbelianBRSTGaugeFermion4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPPrimitiveSpinCGeometricSignedFredholm4D
open P0EFTJanusProgramPGlobalFullLLGraphRiesz4D

attribute [local instance]
  diagonalL2DiffeomorphismNormedAddCommGroup
  diagonalL2DiffeomorphismInnerProductSpace
  diagonalL2AbelianInnerProductSpace
  diagonalL2MatterInnerProductSpace
  diagonalL2LLInnerProductSpace
  diagonalL2ExtendedBulkNormedAddCommGroup
  diagonalL2ExtendedBulkInnerProductSpace
  diagonalL2ExtendedBulkCompleteSpace

variable (period : Real) (hPeriod : period ≠ 0)

/-- The isolated SpinC modal ratio remains an eigenvalue of the genuine
diagonal BRST--Abelian--matter--LL Riesz operator. -/
theorem diagonalExtendedBulkL2RieszOperator_matter_mode_eigen
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (sector : Sector) (mode : PrimitiveSpinCGeometricSignedMode) :
    let w := programPPrimitiveSpinCMatterHessianWeight
      period hPeriod massSquared (sector, mode)
    let m := (programPPrimitiveSpinCMatterL2GraphEquiv
      period hPeriod massSquared).symm
        (programPPrimitiveSpinCMatterGraphSingle
          period hPeriod massSquared sector mode 1)
    diagonalExtendedBulkL2RieszOperator period hPeriod metric massSquared data
        analysis (pureMatter m) =
      (w / (1 + w ^ 2)) • pureMatter m := by
  dsimp only
  have hSplit (first second : GlobalCandidateADiagonalExtendedBulkL2Hilbert
      period hPeriod metric massSquared data analysis) :
      diagonalExtendedBulkL2Hessian period hPeriod metric massSquared data
          analysis first second =
        globalCandidateADiagonalDiffeomorphismOffShellHessian
            period hPeriod couplings metric first.fst second.fst +
          globalPairedAbelianOffShellHessian period hPeriod metric
            first.snd.fst second.snd.fst +
          matterL2GraphForm period hPeriod massSquared
            first.snd.snd.fst second.snd.snd.fst +
          globalCandidateAFullLLGraphForm period hPeriod data analysis
            first.snd.snd.snd second.snd.snd.snd := by
    rw [diagonalExtendedBulkL2Hessian_apply,
      diagonalExtendedBulkHessian_apply]
    rfl
  exact pureMatter_eigen_of_block_form
    (diagonalExtendedBulkL2Hessian period hPeriod metric massSquared data analysis)
    (diagonalExtendedBulkL2RieszOperator period hPeriod metric massSquared data analysis)
    (globalCandidateADiagonalDiffeomorphismOffShellHessian period hPeriod couplings metric)
    (globalPairedAbelianOffShellHessian period hPeriod metric)
    (matterL2GraphForm period hPeriod massSquared)
    (globalCandidateAFullLLGraphForm period hPeriod data analysis)
    (matterL2GraphRiesz period hPeriod massSquared)
    hSplit
    (diagonalExtendedBulkL2RieszOperator_pairing period hPeriod metric
      massSquared data analysis)
    (matterL2GraphRiesz_pairing period hPeriod massSquared)
    _ _
    (matterL2GraphRiesz_single_eigen period hPeriod massSquared sector mode)

end
end P0EFTJanusProgramPT12DiagonalMatterRieszEigen4D
end JanusFormal
