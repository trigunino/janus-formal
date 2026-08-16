import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiveSectorHilbertCoordinates4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAExtendedBulkCoreCoordinates4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D

/-!
# Five-sector coordinates on the actual Candidate-A completion

A five-sector coordinate decomposition of the completed common Hilbert space is
accepted only when it agrees with the already canonical dense-core split:

* the metric, Abelian and finite-boundary/BV projectors add up to the genuine
  diagonal-bulk projector;
* the primitive matter projector is the existing SpinC coordinate projector;
* the longitudinal projector is the existing full LL coordinate projector.

Thus the five completed subspaces cannot be selected independently of the
actual Candidate-A field coordinates. The only remaining construction is the
internal three-way refinement of the diagonal-bulk factor.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAFiveSectorCompletionCoordinates4D

set_option autoImplicit false
set_option maxHeartbeats 3600000
set_option synthInstance.maxHeartbeats 1800000
noncomputable section

open scoped InnerProductSpace
open P0EFTJanusProgramPFiveSectorHilbertCoordinates4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateAExtendedBulkCoreCoordinates4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev CommonCore
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :=
  GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod data analysis

private abbrev CommonHilbert
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :=
  GlobalCandidateADiagonalExtendedBulkL2Hilbert period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
    couplings.matterMassSquared data analysis

local instance (priority := 30000) commonHilbertNormedAddCommGroup
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    NormedAddCommGroup
      (CommonHilbert period hPeriod configuration data analysis) :=
  diagonalL2ExtendedBulkNormedAddCommGroup period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
    couplings.matterMassSquared data analysis

local instance (priority := 30000) commonHilbertInnerProductSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    InnerProductSpace Real
      (CommonHilbert period hPeriod configuration data analysis) :=
  diagonalL2ExtendedBulkInnerProductSpace period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
    couplings.matterMassSquared data analysis

local instance (priority := 30000) commonHilbertNormedSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    NormedSpace Real
      (CommonHilbert period hPeriod configuration data analysis) :=
  diagonalL2ExtendedBulkNormedSpace period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
    couplings.matterMassSquared data analysis

local instance (priority := 30000) commonHilbertModule
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    Module Real (CommonHilbert period hPeriod configuration data analysis) :=
  diagonalL2ExtendedBulkModule period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
    couplings.matterMassSquared data analysis

local instance (priority := 30000) commonHilbertCompleteSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    CompleteSpace (CommonHilbert period hPeriod configuration data analysis) :=
  diagonalL2ExtendedBulkCompleteSpace period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
    couplings.matterMassSquared data analysis

/-- Five-sector completion coordinates constrained by the exact smooth-core
coordinates. -/
structure GlobalCandidateAFiveSectorCompletionCoordinates4D
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (Metric Abelian Matter Longitudinal Boundary : Type*)
    [NormedAddCommGroup Metric] [InnerProductSpace Real Metric]
    [NormedAddCommGroup Abelian] [InnerProductSpace Real Abelian]
    [NormedAddCommGroup Matter] [InnerProductSpace Real Matter]
    [NormedAddCommGroup Longitudinal] [InnerProductSpace Real Longitudinal]
    [NormedAddCommGroup Boundary] [InnerProductSpace Real Boundary] where
  coordinates : FiveSectorHilbertCoordinates
    (E := CommonHilbert period hPeriod configuration data analysis)
    (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
    (Longitudinal := Longitudinal) (Boundary := Boundary)
  bulk_refinement_agreement : ∀ core :
      CommonCore period hPeriod configuration data analysis,
    coordinates.metricProjector
          (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
            (globalCandidateAMetricBySector period hPeriod data)
            couplings.matterMassSquared data analysis core) +
      coordinates.abelianProjector
          (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
            (globalCandidateAMetricBySector period hPeriod data)
            couplings.matterMassSquared data analysis core) +
      coordinates.boundaryProjector
          (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
            (globalCandidateAMetricBySector period hPeriod data)
            couplings.matterMassSquared data analysis core) =
      diagonalExtendedBulkL2SmoothEmbedding period hPeriod
        (globalCandidateAMetricBySector period hPeriod data)
        couplings.matterMassSquared data analysis
        (globalCandidateAExtendedBulkCoreBulkProjector period hPeriod
          configuration data analysis core)
  matter_agreement : ∀ core :
      CommonCore period hPeriod configuration data analysis,
    coordinates.matterProjector
        (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
          (globalCandidateAMetricBySector period hPeriod data)
          couplings.matterMassSquared data analysis core) =
      diagonalExtendedBulkL2SmoothEmbedding period hPeriod
        (globalCandidateAMetricBySector period hPeriod data)
        couplings.matterMassSquared data analysis
        (globalCandidateAExtendedBulkCoreMatterProjector period hPeriod
          configuration data analysis core)
  ll_agreement : ∀ core :
      CommonCore period hPeriod configuration data analysis,
    coordinates.longitudinalProjector
        (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
          (globalCandidateAMetricBySector period hPeriod data)
          couplings.matterMassSquared data analysis core) =
      diagonalExtendedBulkL2SmoothEmbedding period hPeriod
        (globalCandidateAMetricBySector period hPeriod data)
        couplings.matterMassSquared data analysis
        (globalCandidateAExtendedBulkCoreLLProjector period hPeriod
          configuration data analysis core)

/-- The five projectors reconstruct the embedded genuine smooth core. -/
theorem globalCandidateAFiveSectorCompletionCoordinates_core_decomposition
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    {Metric Abelian Matter Longitudinal Boundary : Type*}
    [NormedAddCommGroup Metric] [InnerProductSpace Real Metric]
    [NormedAddCommGroup Abelian] [InnerProductSpace Real Abelian]
    [NormedAddCommGroup Matter] [InnerProductSpace Real Matter]
    [NormedAddCommGroup Longitudinal] [InnerProductSpace Real Longitudinal]
    [NormedAddCommGroup Boundary] [InnerProductSpace Real Boundary]
    (sectorData : GlobalCandidateAFiveSectorCompletionCoordinates4D period
      hPeriod configuration data analysis Metric Abelian Matter Longitudinal
        Boundary)
    (core : CommonCore period hPeriod configuration data analysis) :
    sectorData.coordinates.metricProjector
          (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
            (globalCandidateAMetricBySector period hPeriod data)
            couplings.matterMassSquared data analysis core) +
      sectorData.coordinates.abelianProjector
          (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
            (globalCandidateAMetricBySector period hPeriod data)
            couplings.matterMassSquared data analysis core) +
      sectorData.coordinates.matterProjector
          (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
            (globalCandidateAMetricBySector period hPeriod data)
            couplings.matterMassSquared data analysis core) +
      sectorData.coordinates.longitudinalProjector
          (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
            (globalCandidateAMetricBySector period hPeriod data)
            couplings.matterMassSquared data analysis core) +
      sectorData.coordinates.boundaryProjector
          (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
            (globalCandidateAMetricBySector period hPeriod data)
            couplings.matterMassSquared data analysis core) =
      diagonalExtendedBulkL2SmoothEmbedding period hPeriod
        (globalCandidateAMetricBySector period hPeriod data)
        couplings.matterMassSquared data analysis core := by
  exact sectorData.coordinates.projectors_decompose
    (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
      (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis core)

/-- Public checkpoint: one isometric coordinate decomposition, constrained on
the genuine dense core, determines all five completed sector subspaces. -/
theorem global_candidateA_five_sector_completion_coordinates_gate
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    {Metric Abelian Matter Longitudinal Boundary : Type*}
    [NormedAddCommGroup Metric] [InnerProductSpace Real Metric]
    [NormedAddCommGroup Abelian] [InnerProductSpace Real Abelian]
    [NormedAddCommGroup Matter] [InnerProductSpace Real Matter]
    [NormedAddCommGroup Longitudinal] [InnerProductSpace Real Longitudinal]
    [NormedAddCommGroup Boundary] [InnerProductSpace Real Boundary]
    (sectorData : GlobalCandidateAFiveSectorCompletionCoordinates4D period
      hPeriod configuration data analysis Metric Abelian Matter Longitudinal
        Boundary) :
    (∀ sector x, sectorData.coordinates.sectorProjector sector
        (sectorData.coordinates.sectorProjector sector x) =
      sectorData.coordinates.sectorProjector sector x) ∧
    (∀ first second, first ≠ second → ∀ x,
      sectorData.coordinates.sectorProjector first
        (sectorData.coordinates.sectorProjector second x) = 0) ∧
    (∀ core : CommonCore period hPeriod configuration data analysis,
      sectorData.coordinates.metricProjector
            (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
              (globalCandidateAMetricBySector period hPeriod data)
              couplings.matterMassSquared data analysis core) +
        sectorData.coordinates.abelianProjector
            (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
              (globalCandidateAMetricBySector period hPeriod data)
              couplings.matterMassSquared data analysis core) +
        sectorData.coordinates.matterProjector
            (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
              (globalCandidateAMetricBySector period hPeriod data)
              couplings.matterMassSquared data analysis core) +
        sectorData.coordinates.longitudinalProjector
            (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
              (globalCandidateAMetricBySector period hPeriod data)
              couplings.matterMassSquared data analysis core) +
        sectorData.coordinates.boundaryProjector
            (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
              (globalCandidateAMetricBySector period hPeriod data)
              couplings.matterMassSquared data analysis core) =
        diagonalExtendedBulkL2SmoothEmbedding period hPeriod
          (globalCandidateAMetricBySector period hPeriod data)
          couplings.matterMassSquared data analysis core) :=
  ⟨sectorData.coordinates.sectorProjector_idempotent,
    fun _ _ h => sectorData.coordinates.sectorProjector_comp_zero h,
    globalCandidateAFiveSectorCompletionCoordinates_core_decomposition period
      hPeriod configuration data analysis sectorData⟩

end
end P0EFTJanusProgramPGlobalCandidateAFiveSectorCompletionCoordinates4D
end JanusFormal
