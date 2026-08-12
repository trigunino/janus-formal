import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAFiveSectorCompletionResolutionBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAActionSymmetrySectors4D

/-!
# Action-generated zero modes in the unique Candidate-A five-sector ranges

The Candidate-A action-symmetry packet already proves local invariance of the
genuine augmented action and hence annihilation of every named generator by the
actual Hessian.  Separately, the completion-resolution bridge identifies one
orthogonal five-sector decomposition on the physical Hilbert space and on the
genuine smooth core.

This file joins those two constructions.  A sector label is accepted only when
the corresponding action-generated vector is fixed by the projector generated
from that one completion decomposition.  Consequently:

* every named symmetry generator belongs to its physical sector range;
* every different sector projector kills it;
* generators assigned to distinct sectors are automatically orthogonal;
* action invariance and the actual Hessian kernel equation are retained.

No independently chosen zero-mode subspace or second family of projectors is
introduced.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAFiveSectorActionSymmetryModes4D

set_option autoImplicit false
set_option maxHeartbeats 6200000
set_option synthInstance.maxHeartbeats 3100000

noncomputable section

open Set Topology MeasureTheory
open scoped BigOperators Manifold ContDiff InnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D
open P0EFTJanusProgramPGlobalCandidateAActionTranslationZeroModes4D
open P0EFTJanusProgramPGlobalCandidateAActionSymmetrySectors4D
open P0EFTJanusProgramPGlobalCandidateANamedZeroModeSectors4D
open P0EFTJanusProgramPGlobalCandidateAFiveSectorOrthogonalProduct4D
open P0EFTJanusProgramPGlobalCandidateAFiveSectorCompletionCoordinates4D
open P0EFTJanusProgramPGlobalCandidateAFiveSectorCompletionResolutionBridge4D
open P0EFTJanusProgramPFiveSectorOrthogonalProductResolution4D
open P0EFTJanusMappingTorusGlobalLLVariation4D

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

private abbrev CandidateAHilbert
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :=
  GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration data
    analysis

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
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkNormedAddCommGroup
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
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
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkInnerProductSpace
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
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
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkNormedSpace
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
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
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkModule
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
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
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkCompleteSpace
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

/-- The Candidate-A sector-name transport is injective.  Thus different
physical labels remain different coordinate slots. -/
theorem candidateAZeroModeSectorToFiveSectorSlot_injective :
    Function.Injective candidateAZeroModeSectorToFiveSectorSlot := by
  intro first second h
  cases first <;> cases second <;>
    simp [candidateAZeroModeSectorToFiveSectorSlot] at h ⊢

/-- Action-generated zero modes together with their realization inside the
ranges of the unique completion-derived five-sector resolution. -/
structure GlobalCandidateAFiveSectorActionSymmetryModes4D
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
    (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis chart sameAction)
    (Metric Abelian Matter Longitudinal Boundary : Type*)
    [NormedAddCommGroup Metric] [InnerProductSpace Real Metric]
    [NormedAddCommGroup Abelian] [InnerProductSpace Real Abelian]
    [NormedAddCommGroup Matter] [InnerProductSpace Real Matter]
    [NormedAddCommGroup Longitudinal] [InnerProductSpace Real Longitudinal]
    [NormedAddCommGroup Boundary] [InnerProductSpace Real Boundary]
    (ZeroMode : Type*) [Fintype ZeroMode] : Prop where
  coordinates : GlobalCandidateAFiveSectorCompletionCoordinates4D period
    hPeriod configuration data analysis Metric Abelian Matter Longitudinal
      Boundary
  actionSectors : GlobalCandidateAActionSymmetrySectorData4D period hPeriod
    configuration data analysis chart sameAction physical ZeroMode
  sector_fixed : ∀ mode,
    globalCandidateAFiveSectorOrthogonalProjection period hPeriod
        (globalCandidateAFiveSectorOrthogonalProductOfCompletionCoordinates
          period hPeriod configuration data analysis coordinates)
        (actionSectors.classification.sectorOf mode)
        (actionSectors.symmetry.translations.vector mode) =
      actionSectors.symmetry.translations.vector mode

namespace GlobalCandidateAFiveSectorActionSymmetryModes4D

/-- The orthogonal product data used by all subsequent sector statements. -/
def resolution
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    {chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure}
    {sameAction : ProgramPGlobalMinimalPhysicalLocalMatterLLSameActionBridge4D
      period hPeriod configuration data analysis chart}
    {physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis chart sameAction}
    {Metric Abelian Matter Longitudinal Boundary : Type*}
    [NormedAddCommGroup Metric] [InnerProductSpace Real Metric]
    [NormedAddCommGroup Abelian] [InnerProductSpace Real Abelian]
    [NormedAddCommGroup Matter] [InnerProductSpace Real Matter]
    [NormedAddCommGroup Longitudinal] [InnerProductSpace Real Longitudinal]
    [NormedAddCommGroup Boundary] [InnerProductSpace Real Boundary]
    {ZeroMode : Type*} [Fintype ZeroMode]
    (input : GlobalCandidateAFiveSectorActionSymmetryModes4D period hPeriod
      configuration data analysis chart sameAction physical Metric Abelian Matter
        Longitudinal Boundary ZeroMode) :=
  globalCandidateAFiveSectorOrthogonalProductOfCompletionCoordinates period
    hPeriod configuration data analysis input.coordinates

/-- Every action-generated mode belongs to the range selected by its physical
sector label. -/
theorem vector_mem_sectorRange
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    {chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure}
    {sameAction : ProgramPGlobalMinimalPhysicalLocalMatterLLSameActionBridge4D
      period hPeriod configuration data analysis chart}
    {physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis chart sameAction}
    {Metric Abelian Matter Longitudinal Boundary : Type*}
    [NormedAddCommGroup Metric] [InnerProductSpace Real Metric]
    [NormedAddCommGroup Abelian] [InnerProductSpace Real Abelian]
    [NormedAddCommGroup Matter] [InnerProductSpace Real Matter]
    [NormedAddCommGroup Longitudinal] [InnerProductSpace Real Longitudinal]
    [NormedAddCommGroup Boundary] [InnerProductSpace Real Boundary]
    {ZeroMode : Type*} [Fintype ZeroMode]
    (input : GlobalCandidateAFiveSectorActionSymmetryModes4D period hPeriod
      configuration data analysis chart sameAction physical Metric Abelian Matter
        Longitudinal Boundary ZeroMode)
    (mode : ZeroMode) :
    input.actionSectors.symmetry.translations.vector mode ∈
      (globalCandidateAFiveSectorOrthogonalProjection period hPeriod
        input.resolution
        (input.actionSectors.classification.sectorOf mode)).range := by
  exact ⟨input.actionSectors.symmetry.translations.vector mode,
    input.sector_fixed mode⟩

/-- Every projector with a different sector label kills the named mode. -/
theorem projection_eq_zero_of_ne
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    {chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure}
    {sameAction : ProgramPGlobalMinimalPhysicalLocalMatterLLSameActionBridge4D
      period hPeriod configuration data analysis chart}
    {physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis chart sameAction}
    {Metric Abelian Matter Longitudinal Boundary : Type*}
    [NormedAddCommGroup Metric] [InnerProductSpace Real Metric]
    [NormedAddCommGroup Abelian] [InnerProductSpace Real Abelian]
    [NormedAddCommGroup Matter] [InnerProductSpace Real Matter]
    [NormedAddCommGroup Longitudinal] [InnerProductSpace Real Longitudinal]
    [NormedAddCommGroup Boundary] [InnerProductSpace Real Boundary]
    {ZeroMode : Type*} [Fintype ZeroMode]
    (input : GlobalCandidateAFiveSectorActionSymmetryModes4D period hPeriod
      configuration data analysis chart sameAction physical Metric Abelian Matter
        Longitudinal Boundary ZeroMode)
    (mode : ZeroMode) (sector : CandidateAZeroModeSector)
    (hDifferent : sector ≠ input.actionSectors.classification.sectorOf mode) :
    globalCandidateAFiveSectorOrthogonalProjection period hPeriod
        input.resolution sector
        (input.actionSectors.symmetry.translations.vector mode) = 0 := by
  let ownSector := input.actionSectors.classification.sectorOf mode
  let vector := input.actionSectors.symmetry.translations.vector mode
  have hSlots :
      candidateAZeroModeSectorToFiveSectorSlot sector ≠
        candidateAZeroModeSectorToFiveSectorSlot ownSector := by
    intro hSame
    exact hDifferent
      (candidateAZeroModeSectorToFiveSectorSlot_injective hSame)
  have hComp := input.resolution.toGeneric.projection_comp_zero
    (candidateAZeroModeSectorToFiveSectorSlot sector)
    (candidateAZeroModeSectorToFiveSectorSlot ownSector) hSlots
  have hApplied := congrArg
    (fun operator : CandidateAHilbert period hPeriod configuration data analysis
        →L[Real] CandidateAHilbert period hPeriod configuration data analysis =>
      operator vector) hComp
  calc
    globalCandidateAFiveSectorOrthogonalProjection period hPeriod
        input.resolution sector vector =
      globalCandidateAFiveSectorOrthogonalProjection period hPeriod
        input.resolution sector
        (globalCandidateAFiveSectorOrthogonalProjection period hPeriod
          input.resolution ownSector vector) := by
      rw [input.sector_fixed mode]
    _ = 0 := by
      simpa [globalCandidateAFiveSectorOrthogonalProjection] using hApplied

/-- Modes assigned to different physical sectors are orthogonal because their
projectors come from one orthogonal product decomposition. -/
theorem vectors_inner_eq_zero_of_sector_ne
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    {chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure}
    {sameAction : ProgramPGlobalMinimalPhysicalLocalMatterLLSameActionBridge4D
      period hPeriod configuration data analysis chart}
    {physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis chart sameAction}
    {Metric Abelian Matter Longitudinal Boundary : Type*}
    [NormedAddCommGroup Metric] [InnerProductSpace Real Metric]
    [NormedAddCommGroup Abelian] [InnerProductSpace Real Abelian]
    [NormedAddCommGroup Matter] [InnerProductSpace Real Matter]
    [NormedAddCommGroup Longitudinal] [InnerProductSpace Real Longitudinal]
    [NormedAddCommGroup Boundary] [InnerProductSpace Real Boundary]
    {ZeroMode : Type*} [Fintype ZeroMode]
    (input : GlobalCandidateAFiveSectorActionSymmetryModes4D period hPeriod
      configuration data analysis chart sameAction physical Metric Abelian Matter
        Longitudinal Boundary ZeroMode)
    (first second : ZeroMode)
    (hDifferent : input.actionSectors.classification.sectorOf first ≠
      input.actionSectors.classification.sectorOf second) :
    inner Real
        (input.actionSectors.symmetry.translations.vector first)
        (input.actionSectors.symmetry.translations.vector second) = 0 := by
  let firstSector := input.actionSectors.classification.sectorOf first
  let secondSector := input.actionSectors.classification.sectorOf second
  let firstVector := input.actionSectors.symmetry.translations.vector first
  let secondVector := input.actionSectors.symmetry.translations.vector second
  have hSlots :
      candidateAZeroModeSectorToFiveSectorSlot firstSector ≠
        candidateAZeroModeSectorToFiveSectorSlot secondSector := by
    intro hSame
    exact hDifferent
      (candidateAZeroModeSectorToFiveSectorSlot_injective hSame)
  calc
    inner Real firstVector secondVector =
      inner Real
        (globalCandidateAFiveSectorOrthogonalProjection period hPeriod
          input.resolution firstSector firstVector)
        (globalCandidateAFiveSectorOrthogonalProjection period hPeriod
          input.resolution secondSector secondVector) := by
      rw [input.sector_fixed first, input.sector_fixed second]
    _ = 0 := by
      exact input.resolution.toGeneric.projection_orthogonal
        (candidateAZeroModeSectorToFiveSectorSlot firstSector)
        (candidateAZeroModeSectorToFiveSectorSlot secondSector)
        hSlots firstVector secondVector

/-- The sector-range refinement retains the original local action invariance. -/
theorem action_translation_invariant
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    {chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure}
    {sameAction : ProgramPGlobalMinimalPhysicalLocalMatterLLSameActionBridge4D
      period hPeriod configuration data analysis chart}
    {physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis chart sameAction}
    {Metric Abelian Matter Longitudinal Boundary : Type*}
    [NormedAddCommGroup Metric] [InnerProductSpace Real Metric]
    [NormedAddCommGroup Abelian] [InnerProductSpace Real Abelian]
    [NormedAddCommGroup Matter] [InnerProductSpace Real Matter]
    [NormedAddCommGroup Longitudinal] [InnerProductSpace Real Longitudinal]
    [NormedAddCommGroup Boundary] [InnerProductSpace Real Boundary]
    {ZeroMode : Type*} [Fintype ZeroMode]
    (input : GlobalCandidateAFiveSectorActionSymmetryModes4D period hPeriod
      configuration data analysis chart sameAction physical Metric Abelian Matter
        Longitudinal Boundary ZeroMode)
    (mode : ZeroMode) :
    ActionTranslationEventuallyInvariantAt
      (globalCandidateACommonAugmentedAction period hPeriod configuration data
        analysis chart sameAction physical)
      0 (input.actionSectors.symmetry.translations.vector mode) :=
  input.actionSectors.symmetry.translations.action_translation_invariant mode

/-- Every sector-realized symmetry generator satisfies the actual operator
kernel equation obtained by differentiating the same action. -/
theorem vector_annihilated
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    {chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure}
    {sameAction : ProgramPGlobalMinimalPhysicalLocalMatterLLSameActionBridge4D
      period hPeriod configuration data analysis chart}
    {physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis chart sameAction}
    {Metric Abelian Matter Longitudinal Boundary : Type*}
    [NormedAddCommGroup Metric] [InnerProductSpace Real Metric]
    [NormedAddCommGroup Abelian] [InnerProductSpace Real Abelian]
    [NormedAddCommGroup Matter] [InnerProductSpace Real Matter]
    [NormedAddCommGroup Longitudinal] [InnerProductSpace Real Longitudinal]
    [NormedAddCommGroup Boundary] [InnerProductSpace Real Boundary]
    {ZeroMode : Type*} [Fintype ZeroMode]
    (input : GlobalCandidateAFiveSectorActionSymmetryModes4D period hPeriod
      configuration data analysis chart sameAction physical Metric Abelian Matter
        Longitudinal Boundary ZeroMode)
    (mode : ZeroMode) :
    globalCandidateAActualKernelOperator period hPeriod configuration data
        analysis chart sameAction physical
        (input.actionSectors.symmetry.translations.vector mode) = 0 :=
  (input.actionSectors.symmetry.translations.toGradientModes period hPeriod).
    vector_annihilated period hPeriod mode

/-- Public checkpoint: named zero modes now simultaneously come from exact
action invariance and lie in the ranges of the one physical five-sector
resolution. -/
theorem global_candidateA_five_sector_action_symmetry_modes_gate
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    {chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure}
    {sameAction : ProgramPGlobalMinimalPhysicalLocalMatterLLSameActionBridge4D
      period hPeriod configuration data analysis chart}
    {physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis chart sameAction}
    {Metric Abelian Matter Longitudinal Boundary : Type*}
    [NormedAddCommGroup Metric] [InnerProductSpace Real Metric]
    [NormedAddCommGroup Abelian] [InnerProductSpace Real Abelian]
    [NormedAddCommGroup Matter] [InnerProductSpace Real Matter]
    [NormedAddCommGroup Longitudinal] [InnerProductSpace Real Longitudinal]
    [NormedAddCommGroup Boundary] [InnerProductSpace Real Boundary]
    {ZeroMode : Type*} [Fintype ZeroMode]
    (input : GlobalCandidateAFiveSectorActionSymmetryModes4D period hPeriod
      configuration data analysis chart sameAction physical Metric Abelian Matter
        Longitudinal Boundary ZeroMode) :
    (∀ mode,
      ActionTranslationEventuallyInvariantAt
        (globalCandidateACommonAugmentedAction period hPeriod configuration data
          analysis chart sameAction physical)
        0 (input.actionSectors.symmetry.translations.vector mode)) ∧
    (∀ mode,
      input.actionSectors.symmetry.translations.vector mode ∈
        (globalCandidateAFiveSectorOrthogonalProjection period hPeriod
          input.resolution
          (input.actionSectors.classification.sectorOf mode)).range) ∧
    (∀ mode sector,
      sector ≠ input.actionSectors.classification.sectorOf mode →
      globalCandidateAFiveSectorOrthogonalProjection period hPeriod
          input.resolution sector
          (input.actionSectors.symmetry.translations.vector mode) = 0) ∧
    (∀ mode,
      globalCandidateAActualKernelOperator period hPeriod configuration data
          analysis chart sameAction physical
          (input.actionSectors.symmetry.translations.vector mode) = 0) ∧
    (∀ first second,
      input.actionSectors.classification.sectorOf first ≠
          input.actionSectors.classification.sectorOf second →
      inner Real
          (input.actionSectors.symmetry.translations.vector first)
          (input.actionSectors.symmetry.translations.vector second) = 0) :=
  ⟨input.action_translation_invariant period hPeriod,
    input.vector_mem_sectorRange period hPeriod,
    input.projection_eq_zero_of_ne period hPeriod,
    input.vector_annihilated period hPeriod,
    input.vectors_inner_eq_zero_of_sector_ne period hPeriod⟩

end GlobalCandidateAFiveSectorActionSymmetryModes4D

end
end P0EFTJanusProgramPGlobalCandidateAFiveSectorActionSymmetryModes4D
end JanusFormal
