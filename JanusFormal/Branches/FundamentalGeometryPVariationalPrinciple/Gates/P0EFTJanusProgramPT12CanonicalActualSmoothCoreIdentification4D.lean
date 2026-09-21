import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedAugmentedBRSTAction4D

/-!
Canonical smooth-core identification for the actual augmented BRST action.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT12CanonicalActualSmoothCoreIdentification4D

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff InnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusImmersionFiberAlgebra
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalLocalHessianBridge4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedHilbert4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCoreToChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedAugmentedBRSTAction4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance : IsManifold coverModelWithCorners ω
    (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance : BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

section

variable {couplings : GlobalCandidateAActionCouplings}
variable {NonNullFace NullFace : Type*}
variable [Fintype NonNullFace] [Fintype NullFace]
variable {measure : Measure (EffectiveQuotient period hPeriod)}
variable (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
variable (data : GlobalCandidateAActionData period hPeriod
  configuration.physical couplings NonNullFace NullFace)
variable (analysis : GlobalAnalysisData period hPeriod configuration.physical)
variable (chartData : ProgramPGlobalMinimalPhysicalActionChartData4D period
  hPeriod (measure := measure) configuration data analysis)
variable (reducedChart : ProgramPGlobalMinimalPhysicalReducedHilbertChart4D
  period hPeriod configuration data analysis chartData)

private abbrev CanonicalChart :=
  globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
    configuration data analysis chartData

private abbrev CanonicalSameAction :=
  globalCandidateAMinimalPhysicalMatterLLSameActionBridge period hPeriod
    configuration data analysis chartData

private abbrev SmoothCore :=
  GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod analysis

private abbrev ActualHilbert :=
  CommonAugmentedHilbert period hPeriod configuration data analysis

private def smoothEmbedding :
    SmoothCore period hPeriod configuration analysis →ₗ[Real]
      ActualHilbert period hPeriod configuration data analysis :=
  diagonalExtendedBulkL2SmoothEmbedding period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
    couplings.matterMassSquared data analysis

/-- The canonical augmented Riesz operator pairs on the complete smooth core
as the genuine gauge-fixed local Candidate-A Hessian. -/
theorem globalCandidateAGaugeFixedAugmentedBRSTRieszOperator_smooth_pairing
    (first second : SmoothCore period hPeriod configuration analysis) :
    inner Real
        (globalCandidateAGaugeFixedAugmentedBRSTRieszOperator period hPeriod
          configuration data analysis chartData reducedChart
          (smoothEmbedding period hPeriod configuration data analysis first))
        (smoothEmbedding period hPeriod configuration data analysis second) =
      diagonalExtendedBulkMinimalPhysicalLocalGaugeFixedHessianOnCore period
        hPeriod configuration data analysis
        (CanonicalChart period hPeriod configuration data analysis chartData)
        (CanonicalSameAction period hPeriod configuration data analysis
          chartData).chartBridge first second := by
  rw [globalCandidateAGaugeFixedAugmentedBRSTRieszOperator_pairing,
    globalCandidateAGaugeFixedAugmentedBRSTAction_fderiv]
  exact globalCandidateACommonAugmentedHessian_smooth_eq_gaugeFixed period
    hPeriod configuration data analysis
      (CanonicalChart period hPeriod configuration data analysis chartData)
      (CanonicalSameAction period hPeriod configuration data analysis chartData)
      (globalCandidateAGaugeFixedAugmentedPhysicalExtension period hPeriod
        configuration data analysis chartData reducedChart) first second

/-- The genuine second derivative of the same canonical action has the same
complete smooth-core pairing, independently of the base point. -/
theorem globalCandidateAGaugeFixedAugmentedBRSTAction_second_fderiv_smooth
    (base : ActualHilbert period hPeriod configuration data analysis)
    (first second : SmoothCore period hPeriod configuration analysis) :
    (fderiv Real
        (fun state => fderiv Real
          (globalCandidateAGaugeFixedAugmentedBRSTAction period hPeriod
            configuration data analysis chartData reducedChart) state)
        base)
        (smoothEmbedding period hPeriod configuration data analysis first)
        (smoothEmbedding period hPeriod configuration data analysis second) =
      diagonalExtendedBulkMinimalPhysicalLocalGaugeFixedHessianOnCore period
        hPeriod configuration data analysis
        (CanonicalChart period hPeriod configuration data analysis chartData)
        (CanonicalSameAction period hPeriod configuration data analysis
          chartData).chartBridge first second := by
  exact globalCandidateACommonAugmentedAction_second_fderiv_smooth period
    hPeriod configuration data analysis
      (CanonicalChart period hPeriod configuration data analysis chartData)
      (CanonicalSameAction period hPeriod configuration data analysis chartData)
      (globalCandidateAGaugeFixedAugmentedPhysicalExtension period hPeriod
        configuration data analysis chartData reducedChart) base first second

/-- One typed packet records both canonical operator/action identifications on
the complete actual smooth core. -/
theorem globalCandidateAGaugeFixedAugmentedBRST_smooth_identification_gate
    (base : ActualHilbert period hPeriod configuration data analysis)
    (first second : SmoothCore period hPeriod configuration analysis) :
    inner Real
          (globalCandidateAGaugeFixedAugmentedBRSTRieszOperator period hPeriod
            configuration data analysis chartData reducedChart
            (smoothEmbedding period hPeriod configuration data analysis first))
          (smoothEmbedding period hPeriod configuration data analysis second) =
        diagonalExtendedBulkMinimalPhysicalLocalGaugeFixedHessianOnCore period
          hPeriod configuration data analysis
          (CanonicalChart period hPeriod configuration data analysis chartData)
          (CanonicalSameAction period hPeriod configuration data analysis
            chartData).chartBridge first second ∧
      (fderiv Real
          (fun state => fderiv Real
            (globalCandidateAGaugeFixedAugmentedBRSTAction period hPeriod
              configuration data analysis chartData reducedChart) state)
          base)
          (smoothEmbedding period hPeriod configuration data analysis first)
          (smoothEmbedding period hPeriod configuration data analysis second) =
        diagonalExtendedBulkMinimalPhysicalLocalGaugeFixedHessianOnCore period
          hPeriod configuration data analysis
          (CanonicalChart period hPeriod configuration data analysis chartData)
          (CanonicalSameAction period hPeriod configuration data analysis
            chartData).chartBridge first second :=
  ⟨globalCandidateAGaugeFixedAugmentedBRSTRieszOperator_smooth_pairing period
      hPeriod configuration data analysis chartData reducedChart first second,
    globalCandidateAGaugeFixedAugmentedBRSTAction_second_fderiv_smooth period
      hPeriod configuration data analysis chartData reducedChart base first second⟩

end
end
end P0EFTJanusProgramPT12CanonicalActualSmoothCoreIdentification4D
end JanusFormal
