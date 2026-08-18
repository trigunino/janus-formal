import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAFiveSectorCompletionCoordinates4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAFiveSectorOrthogonalProduct4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiveSectorLinearIsometryResolution4D

/-!
# Dense-core bridge to the Candidate-A five-sector orthogonal resolution

The completed Candidate-A field space already carries two presentations of the
same five-sector geometry:

* `GlobalCandidateAFiveSectorCompletionCoordinates4D` records one linear
  isometry and its agreement with the genuine extended-bulk smooth core;
* `GlobalCandidateAFiveSectorOrthogonalProductData4D` is the orthogonal
  resolution consumed by the principal blocks and by the actual-kernel H12
  route.

This file identifies those presentations.  The orthogonal product data is
constructed from the existing completion isometry, so no second decomposition
or independently chosen projector is introduced.  The resulting H12
projectors agree on the embedded smooth core with the canonical bulk, primitive
SpinC matter and full longitudinal/LL coordinates.  Reconstruction and
Pythagoras therefore hold for the same dense-core embedding used by the
Candidate-A action.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAFiveSectorCompletionResolutionBridge4D

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 1200000

noncomputable section

open scoped BigOperators InnerProductSpace
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateAExtendedBulkCoreCoordinates4D
open P0EFTJanusProgramPFiveSectorHilbertCoordinates4D
open P0EFTJanusProgramPFiveSectorOrthogonalProductResolution4D
open P0EFTJanusProgramPFiveSectorOrthogonalProductPythagoras4D
open P0EFTJanusProgramPFiveSectorLinearIsometryResolution4D
open P0EFTJanusProgramPGlobalCandidateAFiveSectorCompletionCoordinates4D
open P0EFTJanusProgramPGlobalCandidateAFiveSectorOrthogonalProduct4D
open P0EFTJanusProgramPCandidateAZeroModeSector4D

attribute [local instance]
  commonHilbertNormedAddCommGroup
  commonHilbertInnerProductSpace
  commonHilbertNormedSpace
  commonHilbertModule
  commonHilbertCompleteSpace

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev CandidateACore
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :=
  GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod data analysis

private abbrev CandidateAHilbert
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

local instance (priority := 30000) candidateAHilbertNormedAddCommGroup
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    NormedAddCommGroup
      (CandidateAHilbert period hPeriod configuration data analysis) :=
  diagonalL2ExtendedBulkNormedAddCommGroup period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
    couplings.matterMassSquared data analysis

local instance (priority := 30000) candidateAHilbertInnerProductSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    InnerProductSpace Real
      (CandidateAHilbert period hPeriod configuration data analysis) :=
  diagonalL2ExtendedBulkInnerProductSpace period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
    couplings.matterMassSquared data analysis

local instance (priority := 30000) candidateAHilbertNormedSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    NormedSpace Real
      (CandidateAHilbert period hPeriod configuration data analysis) :=
  diagonalL2ExtendedBulkNormedSpace period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
    couplings.matterMassSquared data analysis

local instance (priority := 30000) candidateAHilbertModule
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    Module Real
      (CandidateAHilbert period hPeriod configuration data analysis) :=
  diagonalL2ExtendedBulkModule period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
    couplings.matterMassSquared data analysis

local instance (priority := 30000) candidateAHilbertCompleteSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    CompleteSpace
      (CandidateAHilbert period hPeriod configuration data analysis) :=
  diagonalL2ExtendedBulkCompleteSpace period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
    couplings.matterMassSquared data analysis

/-- Candidate-A sector names transported to the coordinate API used on the
smooth completion core. -/
def candidateAZeroModeSectorToFivePhysicalSector :
    CandidateAZeroModeSector → FivePhysicalSector
  | .metricDiffeomorphism => .metricDiffeomorphism
  | .abelianGauge => .abelianGauge
  | .primitiveSpinCMatter => .primitiveSpinCMatter
  | .longitudinalLL => .longitudinalLL
  | .boundaryFiniteBV => .boundaryFiniteBV

/-- The genuine extended-bulk smooth core embedded into its one Hilbert
completion. -/
def globalCandidateAFiveSectorCoreEmbedding
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (core : CandidateACore period hPeriod configuration data analysis) :
    CandidateAHilbert period hPeriod configuration data analysis :=
  diagonalExtendedBulkL2SmoothEmbedding period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
    couplings.matterMassSquared data analysis core

/-- Convert the completion isometry, already constrained on the genuine smooth
core, to the orthogonal product packet used by the Candidate-A Hessian. -/
def globalCandidateAFiveSectorOrthogonalProductOfCompletionCoordinates
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
    GlobalCandidateAFiveSectorOrthogonalProductData4D period hPeriod
      configuration data analysis Metric Abelian Matter Longitudinal Boundary where
  decomposition := sectorData.coordinates.decomposition.toContinuousLinearEquiv
  inner_map := by
    intro first second
    change fiveSectorProductInner
      (sectorData.coordinates.decomposition first)
      (sectorData.coordinates.decomposition second) = inner Real first second
    exact sectorData.inner_map first second

/-- The projectors used by the H12 orthogonal-resolution route are exactly the
projectors generated by the completion coordinates. -/
theorem globalCandidateAFiveSectorOrthogonalProjection_agreement
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
    (sector : CandidateAZeroModeSector)
    (state : CandidateAHilbert period hPeriod configuration data analysis) :
    globalCandidateAFiveSectorOrthogonalProjection period hPeriod
        (globalCandidateAFiveSectorOrthogonalProductOfCompletionCoordinates
          period hPeriod configuration data analysis sectorData)
        sector state =
      sectorData.coordinates.sectorProjector
        (candidateAZeroModeSectorToFivePhysicalSector sector) state := by
  cases sector <;>
    apply sectorData.coordinates.decomposition.injective <;>
    rfl

/-- The metric, Abelian and boundary/BV H12 projectors refine exactly the
canonical diagonal-bulk smooth-core projector. -/
theorem globalCandidateAFiveSectorOrthogonalProjection_bulk_core_agreement
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
    (core : CandidateACore period hPeriod configuration data analysis) :
    let resolution :=
      globalCandidateAFiveSectorOrthogonalProductOfCompletionCoordinates
        period hPeriod configuration data analysis sectorData
    globalCandidateAFiveSectorOrthogonalProjection period hPeriod resolution
          .metricDiffeomorphism
          (globalCandidateAFiveSectorCoreEmbedding period hPeriod configuration
            data analysis core) +
      globalCandidateAFiveSectorOrthogonalProjection period hPeriod resolution
          .abelianGauge
          (globalCandidateAFiveSectorCoreEmbedding period hPeriod configuration
            data analysis core) +
      globalCandidateAFiveSectorOrthogonalProjection period hPeriod resolution
          .boundaryFiniteBV
          (globalCandidateAFiveSectorCoreEmbedding period hPeriod configuration
            data analysis core) =
      globalCandidateAFiveSectorCoreEmbedding period hPeriod configuration data
        analysis
        (globalCandidateAExtendedBulkCoreBulkProjector period hPeriod
          configuration data analysis core) := by
  dsimp only
  simpa [globalCandidateAFiveSectorCoreEmbedding,
      globalCandidateAFiveSectorOrthogonalProjection_agreement,
      candidateAZeroModeSectorToFivePhysicalSector,
      FiveSectorHilbertCoordinates.sectorProjector] using
    sectorData.bulk_refinement_agreement core

/-- The primitive SpinC H12 projector is the completed canonical matter
projector on the genuine smooth core. -/
theorem globalCandidateAFiveSectorOrthogonalProjection_matter_core_agreement
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
    (core : CandidateACore period hPeriod configuration data analysis) :
    let resolution :=
      globalCandidateAFiveSectorOrthogonalProductOfCompletionCoordinates
        period hPeriod configuration data analysis sectorData
    globalCandidateAFiveSectorOrthogonalProjection period hPeriod resolution
        .primitiveSpinCMatter
        (globalCandidateAFiveSectorCoreEmbedding period hPeriod configuration
          data analysis core) =
      globalCandidateAFiveSectorCoreEmbedding period hPeriod configuration data
        analysis
        (globalCandidateAExtendedBulkCoreMatterProjector period hPeriod
          configuration data analysis core) := by
  dsimp only
  simpa [globalCandidateAFiveSectorCoreEmbedding,
      globalCandidateAFiveSectorOrthogonalProjection_agreement,
      candidateAZeroModeSectorToFivePhysicalSector,
      FiveSectorHilbertCoordinates.sectorProjector] using
    sectorData.matter_agreement core

/-- The longitudinal/LL H12 projector is the completed canonical full-LL
projector on the genuine smooth core. -/
theorem globalCandidateAFiveSectorOrthogonalProjection_ll_core_agreement
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
    (core : CandidateACore period hPeriod configuration data analysis) :
    let resolution :=
      globalCandidateAFiveSectorOrthogonalProductOfCompletionCoordinates
        period hPeriod configuration data analysis sectorData
    globalCandidateAFiveSectorOrthogonalProjection period hPeriod resolution
        .longitudinalLL
        (globalCandidateAFiveSectorCoreEmbedding period hPeriod configuration
          data analysis core) =
      globalCandidateAFiveSectorCoreEmbedding period hPeriod configuration data
        analysis
        (globalCandidateAExtendedBulkCoreLLProjector period hPeriod configuration
          data analysis core) := by
  dsimp only
  simpa [globalCandidateAFiveSectorCoreEmbedding,
      globalCandidateAFiveSectorOrthogonalProjection_agreement,
      candidateAZeroModeSectorToFivePhysicalSector,
      FiveSectorHilbertCoordinates.sectorProjector] using
    sectorData.ll_agreement core

/-- The five H12 projectors reconstruct every vector coming from the genuine
Candidate-A smooth core. -/
theorem globalCandidateAFiveSectorOrthogonalProjection_core_decomposition
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
    (core : CandidateACore period hPeriod configuration data analysis) :
    let resolution :=
      globalCandidateAFiveSectorOrthogonalProductOfCompletionCoordinates
        period hPeriod configuration data analysis sectorData
    let state := globalCandidateAFiveSectorCoreEmbedding period hPeriod
      configuration data analysis core
    globalCandidateAFiveSectorOrthogonalProjection period hPeriod resolution
          .metricDiffeomorphism state +
      globalCandidateAFiveSectorOrthogonalProjection period hPeriod resolution
          .abelianGauge state +
      globalCandidateAFiveSectorOrthogonalProjection period hPeriod resolution
          .primitiveSpinCMatter state +
      globalCandidateAFiveSectorOrthogonalProjection period hPeriod resolution
          .longitudinalLL state +
      globalCandidateAFiveSectorOrthogonalProjection period hPeriod resolution
          .boundaryFiniteBV state = state := by
  dsimp only
  simpa [globalCandidateAFiveSectorCoreEmbedding,
      globalCandidateAFiveSectorOrthogonalProjection_agreement,
      candidateAZeroModeSectorToFivePhysicalSector,
      FiveSectorHilbertCoordinates.sectorProjector] using
    globalCandidateAFiveSectorCompletionCoordinates_core_decomposition period
      hPeriod configuration data analysis sectorData core

/-- Pythagoras on the same embedded smooth core, for the same orthogonal
resolution that is subsequently restricted to `(ker H)ᗮ`. -/
theorem globalCandidateAFiveSectorOrthogonalProjection_core_norm_sq
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
    (core : CandidateACore period hPeriod configuration data analysis) :
    let resolution :=
      (globalCandidateAFiveSectorOrthogonalProductOfCompletionCoordinates
        period hPeriod configuration data analysis sectorData).toGeneric
    let state := globalCandidateAFiveSectorCoreEmbedding period hPeriod
      configuration data analysis core
    ‖state‖ ^ 2 =
      ∑ sector : FiveSectorSlot, ‖resolution.projection sector state‖ ^ 2 := by
  dsimp only
  exact fiveSectorProjection_norm_sq_sum
    (globalCandidateAFiveSectorOrthogonalProductOfCompletionCoordinates
      period hPeriod configuration data analysis sectorData).toGeneric
    (globalCandidateAFiveSectorCoreEmbedding period hPeriod configuration data
      analysis core)

/-- Public checkpoint: the completion coordinates and the H12 orthogonal
resolution are now one and the same five-sector decomposition on the genuine
Candidate-A dense core. -/
theorem global_candidateA_five_sector_completion_resolution_bridge_gate
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
    (∀ core : CandidateACore period hPeriod configuration data analysis,
      let resolution :=
        globalCandidateAFiveSectorOrthogonalProductOfCompletionCoordinates
          period hPeriod configuration data analysis sectorData
      let state := globalCandidateAFiveSectorCoreEmbedding period hPeriod
        configuration data analysis core
      globalCandidateAFiveSectorOrthogonalProjection period hPeriod resolution
            .metricDiffeomorphism state +
        globalCandidateAFiveSectorOrthogonalProjection period hPeriod resolution
            .abelianGauge state +
        globalCandidateAFiveSectorOrthogonalProjection period hPeriod resolution
            .primitiveSpinCMatter state +
        globalCandidateAFiveSectorOrthogonalProjection period hPeriod resolution
            .longitudinalLL state +
        globalCandidateAFiveSectorOrthogonalProjection period hPeriod resolution
            .boundaryFiniteBV state = state) ∧
    (∀ core : CandidateACore period hPeriod configuration data analysis,
      let resolution :=
        (globalCandidateAFiveSectorOrthogonalProductOfCompletionCoordinates
          period hPeriod configuration data analysis sectorData).toGeneric
      let state := globalCandidateAFiveSectorCoreEmbedding period hPeriod
        configuration data analysis core
      ‖state‖ ^ 2 =
        ∑ sector : FiveSectorSlot, ‖resolution.projection sector state‖ ^ 2) :=
  ⟨globalCandidateAFiveSectorOrthogonalProjection_core_decomposition period
      hPeriod configuration data analysis sectorData,
    globalCandidateAFiveSectorOrthogonalProjection_core_norm_sq period hPeriod
      configuration data analysis sectorData⟩

end
end P0EFTJanusProgramPGlobalCandidateAFiveSectorCompletionResolutionBridge4D
end JanusFormal
