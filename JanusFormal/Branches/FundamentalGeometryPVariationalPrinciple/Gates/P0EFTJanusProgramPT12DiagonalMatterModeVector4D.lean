import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12MatterGraphRieszNoGap4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiagonalFourSectorRieszCommutation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateACanonicalStablePerturbation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D

/-! A nonzero pure SpinC mode in the diagonal four-sector Hilbert product. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12DiagonalMatterModeVector4D

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
noncomputable section

open scoped Manifold ContDiff InnerProductSpace
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateAAbelianExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalFullLLGraphRiesz4D
open P0EFTJanusProgramPGlobalCandidateACanonicalStablePerturbation4D
open P0EFTJanusProgramPGlobalCandidateAFaithfulFredholmSum4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPPrimitiveSpinCGeometricSignedFredholm4D
open P0EFTJanusProgramPT12MatterGraphRieszEigen4D
open P0EFTJanusProgramPT12MatterGraphRieszNoGap4D

attribute [local instance]
  actualKernelNormedAddCommGroup
  actualKernelInnerProductSpace
  actualKernelNormedSpace
  actualKernelModule
  actualKernelCompleteSpace

variable (period : Real) (hPeriod : period ≠ 0)

variable {couplings : GlobalCandidateAActionCouplings}
  {NonNullFace NullFace : Type*}
  [Fintype NonNullFace] [Fintype NullFace]
  (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
  (data : GlobalCandidateAActionData period hPeriod configuration.physical
    couplings NonNullFace NullFace)
  (analysis : GlobalAnalysisData period hPeriod configuration.physical)

private abbrev Hilbert :=
  GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration data analysis

/-- The genuine matter singleton inside the completed four-factor product. -/
def diagonalMatterModeVector
    (sector : Sector) (mode : PrimitiveSpinCGeometricSignedMode) :
    Hilbert period hPeriod configuration data analysis :=
  WithLp.toLp 2 (0, WithLp.toLp 2 (0, WithLp.toLp 2
    ((programPPrimitiveSpinCMatterL2GraphEquiv period hPeriod
      couplings.matterMassSquared).symm
      (programPPrimitiveSpinCMatterGraphSingle period hPeriod
        couplings.matterMassSquared sector mode 1), 0)))

theorem diagonalMatterModeVector_ne_zero
    (sector : Sector) (mode : PrimitiveSpinCGeometricSignedMode) :
    diagonalMatterModeVector period hPeriod configuration data analysis
      sector mode ≠ 0 := by
  intro hZero
  let m := (programPPrimitiveSpinCMatterL2GraphEquiv period hPeriod
    couplings.matterMassSquared).symm
    (programPPrimitiveSpinCMatterGraphSingle period hPeriod
      couplings.matterMassSquared sector mode 1)
  have hCoord :
      (diagonalMatterModeVector period hPeriod configuration data analysis
        sector mode).snd.snd.fst = m := rfl
  have hZeroCoord :
      (0 : Hilbert period hPeriod configuration data analysis).snd.snd.fst = 0 := rfl
  have hMatter := congrArg
    (fun x : Hilbert period hPeriod configuration data analysis => x.snd.snd.fst)
    hZero
  rw [hCoord, hZeroCoord] at hMatter
  exact matterL2GraphSingle_one_ne_zero period hPeriod
    couplings.matterMassSquared sector mode hMatter


end
end P0EFTJanusProgramPT12DiagonalMatterModeVector4D
end JanusFormal
