import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12AbelianBRSTNegativeDirection4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12PureNonminimalSevenPhysicalNull4D

/-! H11 leaves the negative Abelian BRST square unchanged. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12AbelianBRSTNegativePhysicalColumn4D

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 1600000

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
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalBoundedExtension4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalLocalHessianBridge4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalHilbertAugmentationObstruction4D

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

open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalGaugeTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPGlobalMetricTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPGlobalCandidateAAbelianExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalCovariantHessianResidualBridge4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPT12AbelianBRSTNegativeDirection4D

attribute [local instance]
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2DiffeomorphismNormedAddCommGroup
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2DiffeomorphismInnerProductSpace
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2AbelianInnerProductSpace
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2MatterInnerProductSpace
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2LLInnerProductSpace
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkNormedAddCommGroup
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkInnerProductSpace
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkCompleteSpace

variable {couplings : GlobalCandidateAActionCouplings}
variable {NonNullFace NullFace : Type*}
variable [Fintype NonNullFace] [Fintype NullFace]
variable {measure : Measure (EffectiveQuotient period hPeriod)}
variable (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
variable (data : GlobalCandidateAActionData period hPeriod configuration.physical
  couplings NonNullFace NullFace)
variable (analysis : GlobalAnalysisData period hPeriod configuration.physical)

/-- The negative Abelian BRST direction inside the complete actual core. -/
def pureAbelianNakanishiLautrupCore
    (field : GlobalPairedGaugeLieSmooth period hPeriod) :
    GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod analysis :=
  (0, (pureAbelianNakanishiLautrup period hPeriod field, 0))

/-- Nonminimal B does not enter the physical tangent. -/
theorem pureAbelianNakanishiLautrupCore_physicalTangent_zero
    (field : GlobalPairedGaugeLieSmooth period hPeriod) :
    diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
      configuration data analysis
      (pureAbelianNakanishiLautrupCore period hPeriod configuration analysis field) = 0 := by
  change (diagonalExtendedBulkGaugeFixedTangentLinearMap period hPeriod
    configuration data analysis
    (pureAbelianNakanishiLautrupCore period hPeriod configuration analysis field)).1 = 0
  change (diagonalDiffeomorphismGaugeFixedTangentLinearMap period hPeriod
      configuration 0 +
    globalPairedAbelianBRSTStateGaugeFixedTangentLinearMap period hPeriod
      configuration data (pureAbelianNakanishiLautrup period hPeriod field) +
    extendedMatterGaugeFixedTangentLinearMap period hPeriod configuration 0 +
    extendedLLGaugeFixedTangentLinearMap period hPeriod configuration analysis 0).1 = 0
  rw [map_zero, map_zero, map_zero, zero_add, add_zero, add_zero]
  change globalCandidateAPairedGaugePotentialMinimalTangentLinearMap
    period hPeriod data 0 = 0
  exact map_zero _

variable (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
  NonNullFace NullFace measure)
variable (sameAction : ProgramPGlobalMinimalPhysicalLocalMatterLLSameActionBridge4D
  period hPeriod configuration data analysis chart)

/-- H11's seven physical columns vanish on this negative BRST direction. -/
theorem pureAbelianNakanishiLautrupCore_physicalHessian_left_zero
    (field : GlobalPairedGaugeLieSmooth period hPeriod)
    (test : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod analysis) :
    diagonalExtendedBulkMinimalPhysicalLocalActionHessianOnCore period hPeriod
      configuration data analysis chart sameAction.chartBridge
      (pureAbelianNakanishiLautrupCore period hPeriod configuration analysis field)
      test = 0 := by
  unfold diagonalExtendedBulkMinimalPhysicalLocalActionHessianOnCore
  rw [pureAbelianNakanishiLautrupCore_physicalTangent_zero]
  simp

/-- Adding the exact physical Hessian does not remove the negative B square. -/
theorem pureAbelianNakanishiLautrupCore_augmented_pairing_self
    (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis chart sameAction)
    (field : GlobalPairedGaugeLieSmooth period hPeriod) :
    let state := diagonalExtendedBulkL2SmoothEmbedding period hPeriod
      (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis
      (pureAbelianNakanishiLautrupCore period hPeriod configuration analysis field)
    inner Real (globalCandidateACommonAugmentedRieszOperator period hPeriod
      configuration data analysis chart sameAction physical state) state =
      -‖globalPairedGaugeLieL2LinearMap period hPeriod field‖ ^ 2 := by
  dsimp only
  rw [globalCandidateACommonAugmentedRieszOperator_pairing,
    globalCandidateACommonAugmentedHessian_smooth_eq_gaugeFixed,
    diagonalExtendedBulkH13GaugeFixed_eq_graph_add_sevenPhysical,
    pureAbelianNakanishiLautrupCore_physicalHessian_left_zero, add_zero]
  simpa [diagonalExtendedBulkGraphHessianOnCore,
    diagonalExtendedBulkHessian_apply, pureAbelianNakanishiLautrupCore] using
    pureAbelianNakanishiLautrup_hessian_self period hPeriod
      (globalCandidateAMetricBySector period hPeriod data) field

end
end P0EFTJanusProgramPT12AbelianBRSTNegativePhysicalColumn4D
end JanusFormal
