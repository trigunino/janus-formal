import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiagonalMatterModeVector4D

/-! The completed SpinC singleton is the image of a genuine smooth finite core vector. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12MatterModeSmoothCoreEmbedding4D

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 1200000
noncomputable section

open scoped Manifold ContDiff InnerProductSpace
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateAFaithfulFredholmSum4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPPrimitiveSpinCGeometricSignedFredholm4D
open P0EFTJanusProgramPT12DiagonalMatterModeVector4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- The finite coefficient singleton has exactly the pre-existing graph singleton. -/
theorem matterGraphFinite_single_eq_graphSingle
    (massSquared : Real) (sector : Sector)
    (mode : PrimitiveSpinCGeometricSignedMode) :
    programPPrimitiveSpinCMatterGraphFinite period hPeriod massSquared
        (Finsupp.single (sector, mode) (1 : Complex)) =
      programPPrimitiveSpinCMatterGraphSingle period hPeriod massSquared
        sector mode 1 := by
  apply Subtype.ext
  apply Prod.ext
  · ext key
    rw [programPPrimitiveSpinCMatterGraphFinite_fst]
    have hSingle :
        (programPPrimitiveSpinCMatterGraphSingle period hPeriod massSquared
          sector mode 1).1.1 =
          (lp.single 2 (sector, mode) (1 : Complex) :
            ProgramPPrimitiveSpinCMatterHilbert) := by
      simp [programPPrimitiveSpinCMatterGraphSingle]
      ext other
      by_cases hOther : other = (sector, mode)
      · subst other
        simp [lp.single_apply]
      · simp [lp.single_apply, hOther]
    rw [hSingle]
    rw [programPPrimitiveSpinCMatterFiniteHilbertEmbedding_apply]
    by_cases hKey : key = (sector, mode)
    · subst key
      simp [lp.single_apply]
    · simp [lp.single_apply, hKey]
  · ext key
    rw [programPPrimitiveSpinCMatterGraphFinite_snd]
    have hSingle :
        (programPPrimitiveSpinCMatterGraphSingle period hPeriod massSquared
          sector mode 1).1.2 =
          (lp.single 2 (sector, mode)
            ((programPPrimitiveSpinCMatterHessianWeight period hPeriod massSquared
              (sector, mode) : Real) * (1 : Complex)) :
            ProgramPPrimitiveSpinCMatterHilbert) := by
      simp [programPPrimitiveSpinCMatterGraphSingle]
      ext other
      by_cases hOther : other = (sector, mode)
      · subst other
        simp [lp.single_apply]
      · simp [lp.single_apply, hOther]
    rw [hSingle]
    rw [programPPrimitiveSpinCMatterFiniteHilbertEmbedding_apply,
      programPPrimitiveSpinCMatterFiniteHessian_apply]
    by_cases hKey : key = (sector, mode)
    · subst key
      simp [lp.single_apply]
    · simp [lp.single_apply, hKey]

variable {couplings : GlobalCandidateAActionCouplings}
  {NonNullFace NullFace : Type*}
  [Fintype NonNullFace] [Fintype NullFace]
  (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
  (data : GlobalCandidateAActionData period hPeriod configuration.physical
    couplings NonNullFace NullFace)
  (analysis : GlobalAnalysisData period hPeriod configuration.physical)

/-- The pure SpinC singleton in the original four-factor smooth core. -/
def diagonalMatterModeSmoothCore
    (sector : Sector) (mode : PrimitiveSpinCGeometricSignedMode) :
    GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod analysis :=
  (0, (0, (Finsupp.single (sector, mode) (1 : Complex), 0)))

/-- Its faithful L² embedding is the mode used by the diagonal eigen theorem. -/
theorem diagonalMatterModeVector_eq_smoothCoreEmbedding
    (sector : Sector) (mode : PrimitiveSpinCGeometricSignedMode) :
    diagonalMatterModeVector period hPeriod configuration data analysis
        sector mode =
      diagonalExtendedBulkL2SmoothEmbedding period hPeriod
        (globalCandidateAMetricBySector period hPeriod data)
        couplings.matterMassSquared data analysis
        (diagonalMatterModeSmoothCore period hPeriod configuration analysis
          sector mode) := by
  let metric := globalCandidateAMetricBySector period hPeriod data
  let massSquared := couplings.matterMassSquared
  let equiv := diagonalExtendedBulkL2Equiv period hPeriod metric massSquared
    data analysis
  calc
    diagonalMatterModeVector period hPeriod configuration data analysis
        sector mode =
      equiv.symm
        (0, (0, (programPPrimitiveSpinCMatterGraphSingle period hPeriod
          massSquared sector mode 1, 0))) := rfl
    _ = equiv.symm
        (diagonalExtendedBulkSmoothEmbedding period hPeriod metric massSquared
          data analysis
          (diagonalMatterModeSmoothCore period hPeriod configuration analysis
            sector mode)) := by
      congr 1
      simp [diagonalExtendedBulkSmoothEmbedding,
        diagonalMatterModeSmoothCore]
      change programPPrimitiveSpinCMatterGraphSingle period hPeriod massSquared
          sector mode 1 =
        programPPrimitiveSpinCMatterGraphFinite period hPeriod massSquared
          (Finsupp.single (sector, mode) (1 : Complex))
      exact (matterGraphFinite_single_eq_graphSingle period hPeriod
        massSquared sector mode).symm
    _ = diagonalExtendedBulkL2SmoothEmbedding period hPeriod metric massSquared
          data analysis
          (diagonalMatterModeSmoothCore period hPeriod configuration analysis
            sector mode) := rfl

end
end P0EFTJanusProgramPT12MatterModeSmoothCoreEmbedding4D
end JanusFormal
