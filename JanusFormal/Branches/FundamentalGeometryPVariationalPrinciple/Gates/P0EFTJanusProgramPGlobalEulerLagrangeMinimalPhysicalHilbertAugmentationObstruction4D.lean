import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalDenseCoreHilbertClosure4D

/-!
# Obstruction to an augmented-Hilbert/minimal-chart equivalence

The common augmented core contains the typed diffeomorphism nonminimal
directions, while the minimal physical chart deliberately projects them out.
Consequently its core-to-chart map has this explicit kernel.  An isometric
dense-core closure can therefore exist only if those directions are trivial.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalHilbertAugmentationObstruction4D

set_option autoImplicit false
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
open P0EFTJanusProgramPGlobalMetricTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateAAbelianExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateADiagonalCovariantHessianResidualBridge4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateACanonicalSixDenseCore4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeDenseCoreHilbertChartEquivalence4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalDenseCoreHilbertClosure4D

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
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace

section

variable
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chartData : ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
      (measure := measure) configuration data analysis)

local instance obstructionCommonNormedAddCommGroup : NormedAddCommGroup
    (CommonAugmentedHilbert period hPeriod configuration data analysis) :=
  diagonalL2ExtendedBulkNormedAddCommGroup period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance obstructionCommonNormedSpace : NormedSpace Real
    (CommonAugmentedHilbert period hPeriod configuration data analysis) :=
  diagonalL2ExtendedBulkNormedSpace period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance obstructionCommonModule : Module Real
    (CommonAugmentedHilbert period hPeriod configuration data analysis) :=
  diagonalL2ExtendedBulkModule period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance obstructionCommonCompleteSpace : CompleteSpace
    (CommonAugmentedHilbert period hPeriod configuration data analysis) :=
  diagonalL2ExtendedBulkCompleteSpace period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

/-- A smooth-core vector supported only in the typed diffeomorphism
nonminimal slots. -/
def globalCandidateAPureDiffeomorphismNonminimalCore
    (nonminimal : GlobalDiffeomorphismNonminimalFields period hPeriod) :
    GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod analysis :=
  ({ metricPerturbation := 0
     nonminimal := nonminimal }, 0)

theorem globalCandidateAPureDiffeomorphismNonminimalCore_eq_zero_iff
    (nonminimal : GlobalDiffeomorphismNonminimalFields period hPeriod) :
    globalCandidateAPureDiffeomorphismNonminimalCore period hPeriod
        configuration analysis nonminimal = 0 ↔
      nonminimal = 0 := by
  constructor
  · intro hZero
    have hNonminimal := congrArg
      (fun core : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod
        analysis => core.1.nonminimal) hZero
    change nonminimal = 0 at hNonminimal
    exact hNonminimal
  · intro hZero
    subst nonminimal
    rfl

/-- The projection to the corrected minimal physical tangent forgets every
pure typed diffeomorphism nonminimal direction. -/
theorem diagonalExtendedBulkMinimalPhysicalTangent_pureDiffeomorphismNonminimal_eq_zero
    (nonminimal : GlobalDiffeomorphismNonminimalFields period hPeriod) :
    diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
        configuration data analysis
          (globalCandidateAPureDiffeomorphismNonminimalCore period hPeriod
            configuration analysis nonminimal) = 0 := by
  have hDiffeomorphism :
      (diagonalDiffeomorphismGaugeFixedTangentLinearMap period hPeriod
        configuration
          { metricPerturbation := 0
            nonminimal := nonminimal }).1 = 0 := by
    change
      globalMetricPerturbationMinimalPhysicalTangentLinearMap period hPeriod
        configuration.physical 0 = 0
    exact LinearMap.map_zero _
  change
    (diagonalExtendedBulkGaugeFixedTangentLinearMap period hPeriod
      configuration data analysis
        (globalCandidateAPureDiffeomorphismNonminimalCore period hPeriod
          configuration analysis nonminimal)).1 = 0
  change
    (diagonalDiffeomorphismGaugeFixedTangentLinearMap period hPeriod
          configuration
            { metricPerturbation := 0
              nonminimal := nonminimal } +
        globalPairedAbelianBRSTStateGaugeFixedTangentLinearMap period hPeriod
          configuration data 0 +
      extendedMatterGaugeFixedTangentLinearMap period hPeriod configuration 0 +
      extendedLLGaugeFixedTangentLinearMap period hPeriod configuration
        analysis 0).1 = 0
  rw [LinearMap.map_zero, LinearMap.map_zero, LinearMap.map_zero]
  simpa only [add_zero] using hDiffeomorphism

/-- Hence the concrete minimal core-to-chart map has the same explicit
nonminimal kernel. -/
theorem globalCandidateAMinimalPhysicalCoreToChart_pureDiffeomorphismNonminimal_eq_zero
    (nonminimal : GlobalDiffeomorphismNonminimalFields period hPeriod) :
    globalCandidateACanonicalSixCoreToChart period hPeriod configuration data
        analysis
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis chartData)
        (globalCandidateAMinimalPhysicalMatterLLSameActionBridge period hPeriod
          configuration data analysis chartData)
        (globalCandidateAPureDiffeomorphismNonminimalCore period hPeriod
          configuration analysis nonminimal) = 0 := by
  change
    (globalCandidateAMinimalPhysicalMatterLLSameActionBridge period hPeriod
      configuration data analysis chartData).chartBridge.tangentAnalysis
        (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
          configuration data analysis
            (globalCandidateAPureDiffeomorphismNonminimalCore period hPeriod
              configuration analysis nonminimal)) = 0
  rw [diagonalExtendedBulkMinimalPhysicalTangent_pureDiffeomorphismNonminimal_eq_zero]
  exact LinearMap.map_zero _

/-- Any isometric dense-core closure for the augmented Hilbert space forces
all typed diffeomorphism nonminimal directions to vanish. -/
theorem globalCandidateAMinimalPhysicalDenseCoreHilbertClosure_forces_diffeomorphismNonminimal_zero
    (closure : ProgramPGlobalMinimalPhysicalDenseCoreHilbertClosureData4D
      period hPeriod configuration data analysis chartData)
    (nonminimal : GlobalDiffeomorphismNonminimalFields period hPeriod) :
    nonminimal = 0 := by
  have hInjective : Function.Injective
      (globalCandidateACanonicalSixCoreToChart period hPeriod configuration data
        analysis
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis chartData)
        (globalCandidateAMinimalPhysicalMatterLLSameActionBridge period hPeriod
          configuration data analysis chartData)) :=
    globalCandidateACanonicalSixCoreToChart_injective_of_norm period hPeriod
      configuration data analysis
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis chartData)
        (globalCandidateAMinimalPhysicalMatterLLSameActionBridge period hPeriod
          configuration data analysis chartData)
        closure.norm_compatibility
  apply
    (globalCandidateAPureDiffeomorphismNonminimalCore_eq_zero_iff period hPeriod
      configuration analysis nonminimal).mp
  apply hInjective
  rw [globalCandidateAMinimalPhysicalCoreToChart_pureDiffeomorphismNonminimal_eq_zero]
  exact (globalCandidateACanonicalSixCoreToChart period hPeriod configuration
    data analysis
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis chartData)
      (globalCandidateAMinimalPhysicalMatterLLSameActionBridge period hPeriod
        configuration data analysis chartData)).map_zero.symm

/-- A single nonzero typed diffeomorphism nonminimal direction rules out the
augmented-Hilbert/minimal-chart closure certificate. -/
theorem globalCandidateAMinimalPhysicalDenseCoreHilbertClosure_not_nonempty_of_nonzero_diffeomorphismNonminimal
    (nonminimal : GlobalDiffeomorphismNonminimalFields period hPeriod)
    (hNonzero : nonminimal ≠ 0) :
    ¬ Nonempty
      (ProgramPGlobalMinimalPhysicalDenseCoreHilbertClosureData4D period hPeriod
        configuration data analysis chartData) := by
  rintro ⟨closure⟩
  exact hNonzero
    (globalCandidateAMinimalPhysicalDenseCoreHilbertClosure_forces_diffeomorphismNonminimal_zero
      period hPeriod configuration data analysis chartData closure nonminimal)

end

end
end P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalHilbertAugmentationObstruction4D
end JanusFormal
