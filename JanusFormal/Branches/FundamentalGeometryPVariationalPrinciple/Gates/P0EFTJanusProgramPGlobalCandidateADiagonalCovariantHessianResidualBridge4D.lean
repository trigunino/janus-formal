import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianFrontier4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D

/-!
# Candidate-A diagonal graph/covariant Hessian residual bridge

The completed diagonal BRST graph, matter graph and LL graph are compared
with the actual second Frechet derivative of Candidate A on one regular
variational chart.  The comparison is exact on the common smooth core.

No chart bridge is postulated here.  Given the already named dense chart
bridge, the sole remaining equality is reduced to the vanishing of one
physical residual.  Thus the closed BRST, matter and LL blocks cannot be
reintroduced as independent obligations.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateADiagonalCovariantHessianResidualBridge4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 2400000

noncomputable section

open scoped Manifold ContDiff
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalEulerLagrange4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalAnalyticSpine4D
open P0EFTJanusProgramPGlobalHessianFrontier4D
open P0EFTJanusFrechetPullbackQuotientHessian
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPGlobalFullLLGraphRiesz4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

attribute [local instance]
  GlobalCandidateAVariationalChart.normedAddCommGroup
  GlobalCandidateAVariationalChart.normedSpace

/-- Forget the typed nonminimal directions while staying in the corrected
D10-free, nonduplicated physical tangent. -/
def diagonalExtendedBulkMinimalPhysicalTangentLinearMap
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod analysis
      →ₗ[Real] GlobalMinimalPhysicalFieldTangent
        period hPeriod configuration.physical :=
  (globalGaugeFixedPhysicalTangentPhysicalProjectionLinearMap
      period hPeriod configuration).comp
    (diagonalExtendedBulkGaugeFixedTangentLinearMap
      period hPeriod configuration data analysis)

/-- Forget the typed nonminimal directions and include the corrected
D10-free physical direction in the legacy tangent with zero D10 entry. -/
def diagonalExtendedBulkLegacyTangentLinearMap
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod analysis
      →ₗ[Real] GlobalFieldTangent period hPeriod configuration.physical :=
  (globalPhysicalFieldTangentZeroD10InclusionLinearMap
      period hPeriod).comp
    ((globalMinimalPhysicalTangentInclusionLinearMap
        period hPeriod configuration.physical).comp
      (diagonalExtendedBulkMinimalPhysicalTangentLinearMap
        period hPeriod configuration data analysis))

theorem diagonalExtendedBulkLegacyTangentLinearMap_eq_zeroD10_minimal
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    diagonalExtendedBulkLegacyTangentLinearMap period hPeriod
        configuration data analysis =
      (globalPhysicalFieldTangentZeroD10InclusionLinearMap period hPeriod).comp
        ((globalMinimalPhysicalTangentInclusionLinearMap
            period hPeriod configuration.physical).comp
          (diagonalExtendedBulkMinimalPhysicalTangentLinearMap
            period hPeriod configuration data analysis)) :=
  rfl

@[simp]
theorem diagonalExtendedBulkLegacyTangentLinearMap_d10_eq_zero
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (core : GlobalCandidateADiagonalExtendedBulkSmoothCore
      period hPeriod analysis) :
    (diagonalExtendedBulkLegacyTangentLinearMap period hPeriod
      configuration data analysis core).2.2 = 0 :=
  rfl

@[simp]
theorem diagonalExtendedBulkSmoothEmbedding_apply_core
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (core : GlobalCandidateADiagonalExtendedBulkSmoothCore
      period hPeriod analysis) :
    diagonalExtendedBulkSmoothEmbedding period hPeriod
        (globalCandidateAMetricBySector period hPeriod data)
        couplings.matterMassSquared data analysis core =
      (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding
          period hPeriod (globalCandidateAMetricBySector period hPeriod data)
          core.1,
        (globalPairedAbelianOffShellSmoothEmbedding
            period hPeriod (globalCandidateAMetricBySector period hPeriod data)
            core.2.1,
          (programPPrimitiveSpinCMatterGraphFiniteRealLinearMap
              period hPeriod couplings.matterMassSquared core.2.2.1,
            globalCandidateAFullLLSmoothEmbedding
              period hPeriod data analysis core.2.2.2))) :=
  rfl

/-- Actual covariant Candidate-A Hessian, pulled back to the completed
diagonal graph's smooth core through an existing regular chart bridge. -/
def diagonalExtendedBulkCovariantHessianOnCore
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (bridge : ProgramPGlobalVariationalChartCoreBridge4D
      period hPeriod configuration.physical chart)
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore
      period hPeriod analysis) : Real :=
  globalCandidateAHessianOnSmoothGlobalCore period hPeriod
    configuration.physical chart bridge
    (diagonalExtendedBulkLegacyTangentLinearMap period hPeriod
      configuration data analysis first)
    (diagonalExtendedBulkLegacyTangentLinearMap period hPeriod
      configuration data analysis second)

theorem diagonalExtendedBulkCovariantHessianOnCore_comm
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (bridge : ProgramPGlobalVariationalChartCoreBridge4D
      period hPeriod configuration.physical chart)
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore
      period hPeriod analysis) :
    diagonalExtendedBulkCovariantHessianOnCore period hPeriod configuration
        data analysis chart bridge first second =
      diagonalExtendedBulkCovariantHessianOnCore period hPeriod configuration
        data analysis chart bridge second first :=
  globalCandidateAHessianOnSmoothGlobalCore_symmetric period hPeriod
    configuration.physical chart bridge
    (diagonalExtendedBulkLegacyTangentLinearMap period hPeriod
      configuration data analysis first)
    (diagonalExtendedBulkLegacyTangentLinearMap period hPeriod
      configuration data analysis second)

/-- The two already closed BRST gauge-fixing Hessians on the common core. -/
def diagonalExtendedBulkGaugeFixingHessianOnCore
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore
      period hPeriod analysis) : Real :=
  globalCandidateADiagonalDiffeomorphismOffShellHessian period hPeriod
      couplings (globalCandidateAMetricBySector period hPeriod data)
      (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding
        period hPeriod (globalCandidateAMetricBySector period hPeriod data)
        first.1)
      (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding
        period hPeriod (globalCandidateAMetricBySector period hPeriod data)
        second.1) +
    globalPairedAbelianOffShellHessian period hPeriod
      (globalCandidateAMetricBySector period hPeriod data)
      (globalPairedAbelianOffShellSmoothEmbedding period hPeriod
        (globalCandidateAMetricBySector period hPeriod data) first.2.1)
      (globalPairedAbelianOffShellSmoothEmbedding period hPeriod
        (globalCandidateAMetricBySector period hPeriod data) second.2.1)

theorem diagonalExtendedBulkGaugeFixingHessianOnCore_comm
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore
      period hPeriod analysis) :
    diagonalExtendedBulkGaugeFixingHessianOnCore period hPeriod configuration
        data analysis first second =
      diagonalExtendedBulkGaugeFixingHessianOnCore period hPeriod configuration
        data analysis second first := by
  unfold diagonalExtendedBulkGaugeFixingHessianOnCore
  rw [globalCandidateADiagonalDiffeomorphismOffShellHessian_comm,
    globalPairedAbelianOffShellHessian_comm]

/-- The actual covariant Hessian plus only the two BRST gauge-fixing
Hessians.  Matter and LL are not added again. -/
def diagonalExtendedBulkGaugeFixedCovariantHessianOnCore
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (bridge : ProgramPGlobalVariationalChartCoreBridge4D
      period hPeriod configuration.physical chart)
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore
      period hPeriod analysis) : Real :=
  diagonalExtendedBulkCovariantHessianOnCore period hPeriod configuration
      data analysis chart bridge first second +
    diagonalExtendedBulkGaugeFixingHessianOnCore period hPeriod configuration
      data analysis first second

theorem diagonalExtendedBulkGaugeFixedCovariantHessianOnCore_comm
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (bridge : ProgramPGlobalVariationalChartCoreBridge4D
      period hPeriod configuration.physical chart)
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore
      period hPeriod analysis) :
    diagonalExtendedBulkGaugeFixedCovariantHessianOnCore period hPeriod
        configuration data analysis chart bridge first second =
      diagonalExtendedBulkGaugeFixedCovariantHessianOnCore period hPeriod
        configuration data analysis chart bridge second first := by
  unfold diagonalExtendedBulkGaugeFixedCovariantHessianOnCore
  rw [diagonalExtendedBulkCovariantHessianOnCore_comm,
    diagonalExtendedBulkGaugeFixingHessianOnCore_comm]

/-- The completed four-block graph Hessian evaluated on its smooth core. -/
def diagonalExtendedBulkGraphHessianOnCore
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore
      period hPeriod analysis) : Real :=
  diagonalExtendedBulkHessian period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
    couplings.matterMassSquared data analysis
    (diagonalExtendedBulkSmoothEmbedding period hPeriod
      (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis first)
    (diagonalExtendedBulkSmoothEmbedding period hPeriod
      (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis second)

theorem diagonalExtendedBulkGraphHessianOnCore_comm
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore
      period hPeriod analysis) :
    diagonalExtendedBulkGraphHessianOnCore period hPeriod configuration
        data analysis first second =
      diagonalExtendedBulkGraphHessianOnCore period hPeriod configuration
        data analysis second first :=
  diagonalExtendedBulkHessian_comm period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
    couplings.matterMassSquared data analysis
    (diagonalExtendedBulkSmoothEmbedding period hPeriod
      (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis first)
    (diagonalExtendedBulkSmoothEmbedding period hPeriod
      (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis second)

/-- The already closed matter and LL graph contributions on the smooth
core. -/
def diagonalExtendedBulkMatterLLHessianOnCore
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore
      period hPeriod analysis) : Real :=
  programPPrimitiveSpinCMatterGraphForm period hPeriod
      couplings.matterMassSquared
      (programPPrimitiveSpinCMatterGraphFiniteRealLinearMap period hPeriod
        couplings.matterMassSquared first.2.2.1)
      (programPPrimitiveSpinCMatterGraphFiniteRealLinearMap period hPeriod
        couplings.matterMassSquared second.2.2.1) +
    globalCandidateAFullLLGraphForm period hPeriod data analysis
      (globalCandidateAFullLLSmoothEmbedding period hPeriod data analysis
        first.2.2.2)
      (globalCandidateAFullLLSmoothEmbedding period hPeriod data analysis
        second.2.2.2)

theorem diagonalExtendedBulkMatterLLHessianOnCore_comm
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore
      period hPeriod analysis) :
    diagonalExtendedBulkMatterLLHessianOnCore period hPeriod configuration
        data analysis first second =
      diagonalExtendedBulkMatterLLHessianOnCore period hPeriod configuration
        data analysis second first := by
  unfold diagonalExtendedBulkMatterLLHessianOnCore
  rw [programPPrimitiveSpinCMatterGraphForm_comm,
    globalCandidateAFullLLGraphForm_comm]

/-- The unique physical comparison residual left after removing the already
closed matter and LL graph blocks from the actual covariant Hessian. -/
def diagonalExtendedBulkPhysicalHessianResidualOnCore
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (bridge : ProgramPGlobalVariationalChartCoreBridge4D
      period hPeriod configuration.physical chart)
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore
      period hPeriod analysis) : Real :=
  diagonalExtendedBulkCovariantHessianOnCore period hPeriod configuration
      data analysis chart bridge first second -
    diagonalExtendedBulkMatterLLHessianOnCore period hPeriod configuration
      data analysis first second

theorem diagonalExtendedBulkPhysicalHessianResidualOnCore_comm
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (bridge : ProgramPGlobalVariationalChartCoreBridge4D
      period hPeriod configuration.physical chart)
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore
      period hPeriod analysis) :
    diagonalExtendedBulkPhysicalHessianResidualOnCore period hPeriod
        configuration data analysis chart bridge first second =
      diagonalExtendedBulkPhysicalHessianResidualOnCore period hPeriod
        configuration data analysis chart bridge second first := by
  unfold diagonalExtendedBulkPhysicalHessianResidualOnCore
  rw [diagonalExtendedBulkCovariantHessianOnCore_comm,
    diagonalExtendedBulkMatterLLHessianOnCore_comm]

/-- Exact comparison: the gauge-fixed covariant Hessian is the completed
graph Hessian plus one physical residual. -/
theorem diagonalExtendedBulkGaugeFixedCovariantHessian_decomposition
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (bridge : ProgramPGlobalVariationalChartCoreBridge4D
      period hPeriod configuration.physical chart)
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore
      period hPeriod analysis) :
    diagonalExtendedBulkGaugeFixedCovariantHessianOnCore period hPeriod
        configuration data analysis chart bridge first second =
      diagonalExtendedBulkGraphHessianOnCore period hPeriod configuration
          data analysis first second +
        diagonalExtendedBulkPhysicalHessianResidualOnCore period hPeriod
          configuration data analysis chart bridge first second := by
  unfold diagonalExtendedBulkGaugeFixedCovariantHessianOnCore
    diagonalExtendedBulkGraphHessianOnCore
    diagonalExtendedBulkPhysicalHessianResidualOnCore
    diagonalExtendedBulkMatterLLHessianOnCore
    diagonalExtendedBulkGaugeFixingHessianOnCore
  rw [diagonalExtendedBulkHessian_apply]
  simp only [diagonalExtendedBulkSmoothEmbedding_apply_core]
  ring

/-- Consequently the desired graph/covariant equality is equivalent to the
vanishing of the single named physical residual. -/
theorem diagonalExtendedBulkGaugeFixedCovariantHessian_eq_graph_iff
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (bridge : ProgramPGlobalVariationalChartCoreBridge4D
      period hPeriod configuration.physical chart)
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore
      period hPeriod analysis) :
    diagonalExtendedBulkGaugeFixedCovariantHessianOnCore period hPeriod
        configuration data analysis chart bridge first second =
        diagonalExtendedBulkGraphHessianOnCore period hPeriod configuration
          data analysis first second ↔
      diagonalExtendedBulkPhysicalHessianResidualOnCore period hPeriod
        configuration data analysis chart bridge first second = 0 := by
  rw [diagonalExtendedBulkGaugeFixedCovariantHessian_decomposition]
  constructor <;> intro h <;> linarith

end

end P0EFTJanusProgramPGlobalCandidateADiagonalCovariantHessianResidualBridge4D
end JanusFormal
