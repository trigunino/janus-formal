import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalHilbertAugmentationObstruction4D

/-!
# Direct obstruction to the augmented common Hilbert chart

The common chart's dense-core compatibility sends every pure typed
diffeomorphism nonminimal direction to zero in the minimal chart.  Since both
the common smooth embedding and the chart equivalence are injective, existence
of such a chart forces all those directions to be trivial.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateACommonHilbertChartObstruction4D

set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option synthInstance.maxHeartbeats 1400000

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
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateADiagonalCovariantHessianResidualBridge4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateACommonHilbertChartTransport4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalHilbertAugmentationObstruction4D

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

variable
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

/-- Any augmented common Hilbert chart forces every typed diffeomorphism
nonminimal direction to vanish. -/
theorem globalCandidateACommonHilbertChart_forces_diffeomorphismNonminimal_zero
    (hilbertChart : ProgramPGlobalMinimalPhysicalCommonHilbertChart4D period
      hPeriod configuration data analysis chart sameAction)
    (nonminimal : GlobalDiffeomorphismNonminimalFields period hPeriod) :
    nonminimal = 0 := by
  let core := globalCandidateAPureDiffeomorphismNonminimalCore period hPeriod
    configuration analysis nonminimal
  have hChartZero :
      hilbertChart.toChart
          (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
            (globalCandidateAMetricBySector period hPeriod data)
            couplings.matterMassSquared data analysis core) = 0 := by
    rw [hilbertChart.smooth_core_compatibility]
    rw [diagonalExtendedBulkMinimalPhysicalTangent_pureDiffeomorphismNonminimal_eq_zero]
    exact LinearMap.map_zero _
  have hEmbeddingZero :
      diagonalExtendedBulkL2SmoothEmbedding period hPeriod
          (globalCandidateAMetricBySector period hPeriod data)
          couplings.matterMassSquared data analysis core = 0 := by
    apply hilbertChart.toChart.injective
    simpa only [map_zero] using hChartZero
  have hCoreZero : core = 0 := by
    apply diagonalExtendedBulkL2SmoothEmbedding_injective period hPeriod
      (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis
    simpa only [map_zero] using hEmbeddingZero
  exact
    (globalCandidateAPureDiffeomorphismNonminimalCore_eq_zero_iff period
      hPeriod configuration analysis nonminimal).mp hCoreZero

/-- Existence of the augmented common chart collapses the typed
diffeomorphism nonminimal carrier to a subsingleton. -/
theorem globalCandidateACommonHilbertChart_forces_diffeomorphismNonminimal_subsingleton
    (hilbertChart : ProgramPGlobalMinimalPhysicalCommonHilbertChart4D period
      hPeriod configuration data analysis chart sameAction) :
    Subsingleton (GlobalDiffeomorphismNonminimalFields period hPeriod) := by
  constructor
  intro first second
  rw [globalCandidateACommonHilbertChart_forces_diffeomorphismNonminimal_zero
      period hPeriod configuration data analysis chart sameAction hilbertChart
        first,
    globalCandidateACommonHilbertChart_forces_diffeomorphismNonminimal_zero
      period hPeriod configuration data analysis chart sameAction hilbertChart
        second]

/-- One nonzero typed diffeomorphism nonminimal direction directly rules out
the augmented common Hilbert chart. -/
theorem globalCandidateACommonHilbertChart_not_nonempty_of_nonzero_diffeomorphismNonminimal
    (nonminimal : GlobalDiffeomorphismNonminimalFields period hPeriod)
    (hNonzero : nonminimal ≠ 0) :
    ¬ Nonempty
      (ProgramPGlobalMinimalPhysicalCommonHilbertChart4D period hPeriod
        configuration data analysis chart sameAction) := by
  rintro ⟨hilbertChart⟩
  exact hNonzero
    (globalCandidateACommonHilbertChart_forces_diffeomorphismNonminimal_zero
      period hPeriod configuration data analysis chart sameAction hilbertChart
        nonminimal)

end
end P0EFTJanusProgramPGlobalCandidateACommonHilbertChartObstruction4D
end JanusFormal
