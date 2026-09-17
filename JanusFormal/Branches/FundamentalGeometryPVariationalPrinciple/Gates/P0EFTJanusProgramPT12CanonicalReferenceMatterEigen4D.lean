import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiagonalMatterRieszEigen4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiagonalMatterModeVector4D

/-! The diagonal SpinC eigenrelation on the canonical H12 reference operator. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12CanonicalReferenceMatterEigen4D

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
noncomputable section

open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateACanonicalStablePerturbation4D
open P0EFTJanusProgramPGlobalCandidateAFaithfulFredholmSum4D
open P0EFTJanusProgramPPrimitiveSpinCGeometricSignedFredholm4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPT12DiagonalMatterModeVector4D
open P0EFTJanusProgramPT12DiagonalMatterRieszEigen4D
open P0EFTJanusProgramPT12FourSectorMatterEigen4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D

variable (period : Real) (hPeriod : period ≠ 0)

variable {couplings : GlobalCandidateAActionCouplings}
  {NonNullFace NullFace : Type*}
  [Fintype NonNullFace] [Fintype NullFace]
  (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
  (data : GlobalCandidateAActionData period hPeriod configuration.physical
    couplings NonNullFace NullFace)
  (analysis : GlobalAnalysisData period hPeriod configuration.physical)

/-- A pure SpinC mode is an eigenvector of the canonical H12 reference operator. -/
theorem globalCandidateACanonicalStableReferenceOperator_matter_mode_eigen
    (sector : Sector) (mode : PrimitiveSpinCGeometricSignedMode) :
    let w := programPPrimitiveSpinCMatterHessianWeight period hPeriod
      couplings.matterMassSquared (sector, mode)
    globalCandidateACanonicalStableReferenceOperator period hPeriod
        configuration data analysis
        (diagonalMatterModeVector period hPeriod configuration data analysis
          sector mode) =
      (w / (1 + w ^ 2)) •
        diagonalMatterModeVector period hPeriod configuration data analysis
          sector mode := by
  simpa only [ActualKernelHilbert, GlobalCandidateAFaithfulSameActionHilbert,
    globalCandidateACanonicalStableReferenceOperator,
    diagonalMatterModeVector, pureMatter] using
    (diagonalExtendedBulkL2RieszOperator_matter_mode_eigen period hPeriod
      (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis sector mode)

end
end P0EFTJanusProgramPT12CanonicalReferenceMatterEigen4D
end JanusFormal
