import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12PureAntighostBRSTIsotropic4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12PureNonminimalSevenPhysicalNull4D

/-! # Pure-antighost isotropy of the full smooth-core Hessian -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12PureAntighostFullCoreIsotropic4D

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 1200000

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff InnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPGlobalFullLLGraphRiesz4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalCovariantHessianResidualBridge4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalBoundedExtension4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalHilbertAugmentationObstruction4D
open P0EFTJanusProgramPT12PureAntighostBRSTIsotropic4D
open P0EFTJanusProgramPT12PureNonminimalSevenPhysicalNull4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace

/-- Only the antighost coordinate is populated in this four-factor core. -/
def pureAntighostCore
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (antighost : GlobalDiffeomorphismAntighostField period hPeriod) :
    GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod analysis :=
  globalCandidateAPureDiffeomorphismNonminimalCore period hPeriod
    configuration analysis
    (pureAntighostNonminimal period hPeriod antighost)

private theorem pureAntighost_graphHessian_self
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (antighost : GlobalDiffeomorphismAntighostField period hPeriod) :
    diagonalExtendedBulkGraphHessianOnCore period hPeriod configuration data
        analysis (pureAntighostCore period hPeriod configuration analysis antighost)
        (pureAntighostCore period hPeriod configuration analysis antighost) = 0 := by
  let metric := globalCandidateAMetricBySector period hPeriod data
  let x := diagonalExtendedBulkSmoothEmbedding period hPeriod metric
    couplings.matterMassSquared data analysis
    (pureAntighostCore period hPeriod configuration analysis antighost)
  change diagonalExtendedBulkHessian period hPeriod metric
    couplings.matterMassSquared data analysis x x = 0
  rw [diagonalExtendedBulkHessian_apply]
  have hDiffeomorphism : x.1 =
      globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding
        period hPeriod metric
        { metricPerturbation := 0
          nonminimal := pureAntighostNonminimal period hPeriod antighost } := rfl
  have hAbelian : x.2.1 = 0 := by
    change globalPairedAbelianOffShellSmoothEmbedding period hPeriod metric 0 = 0
    exact (globalPairedAbelianOffShellSmoothEmbedding period hPeriod metric).map_zero
  have hMatter : x.2.2.1 = 0 := by
    change programPPrimitiveSpinCMatterGraphFiniteRealLinearMap period hPeriod
      couplings.matterMassSquared 0 = 0
    exact (programPPrimitiveSpinCMatterGraphFiniteRealLinearMap period hPeriod
      couplings.matterMassSquared).map_zero
  have hLL : x.2.2.2 = 0 := by
    change globalCandidateAFullLLSmoothEmbedding period hPeriod data analysis 0 = 0
    exact (globalCandidateAFullLLSmoothEmbedding period hPeriod data analysis).map_zero
  simp only [hDiffeomorphism, hAbelian, hMatter, hLL,
    pureAntighost_diagonalBRSTHessian_self, map_zero, add_zero]

/-- The diagonal Candidate-A graph Hessian plus the seven physical blocks
has zero self-pairing on a pure-antighost smooth-core direction. -/
theorem pureAntighost_fullCoreHessian_self
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (sameAction : ProgramPGlobalMinimalPhysicalLocalMatterLLSameActionBridge4D
      period hPeriod configuration data analysis chart)
    (antighost : GlobalDiffeomorphismAntighostField period hPeriod) :
    diagonalExtendedBulkGraphHessianOnCore period hPeriod configuration data
        analysis (pureAntighostCore period hPeriod configuration analysis antighost)
        (pureAntighostCore period hPeriod configuration analysis antighost) +
      globalCandidateASevenPhysicalCoreLinearForm period hPeriod configuration
        data analysis chart sameAction
        (pureAntighostCore period hPeriod configuration analysis antighost)
        (pureAntighostCore period hPeriod configuration analysis antighost) = 0 := by
  rw [pureAntighost_graphHessian_self]
  change 0 + globalCandidateASevenPhysicalCoreLinearForm period hPeriod
      configuration data analysis chart sameAction
      (globalCandidateAPureDiffeomorphismNonminimalCore period hPeriod
        configuration analysis (pureAntighostNonminimal period hPeriod antighost))
      (pureAntighostCore period hPeriod configuration analysis antighost) = 0
  rw [pureDiffeomorphismNonminimal_sevenPhysicalCore_left_zero]
  norm_num

end
end P0EFTJanusProgramPT12PureAntighostFullCoreIsotropic4D
end JanusFormal
