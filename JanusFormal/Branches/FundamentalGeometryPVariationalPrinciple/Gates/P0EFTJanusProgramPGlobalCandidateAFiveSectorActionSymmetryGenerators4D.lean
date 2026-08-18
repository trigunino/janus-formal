import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAFiveSectorActualHessianCommutation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAActionTranslationZeroModes4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANamedZeroModeSectors4D

/-!
# Five-sector Candidate-A generators from exact action symmetries

This is the non-circular zero-mode layer of the preferred Hessian route.
It contains no Gårding estimate, no finite-kernel hypothesis and no assumed
identification of the named family with the complete kernel.

The input is only:

* a finite family of translations preserving the genuine augmented action;
* a physical sector label for every generator;
* the one completion-derived five-sector geometry already used by H12;
* the statement that each generator is fixed by its labelled projector.

Differentiating the exact action identity proves `H v = 0`.  The single
orthogonal product decomposition then proves sector-range membership,
annihilation by every other projector and cross-sector orthogonality.
Thus the symmetry construction is logically prior to Gårding and can later be
combined with coercivity to exclude hidden modes.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAFiveSectorActionSymmetryGenerators4D

set_option autoImplicit false
set_option maxHeartbeats 6800000
set_option synthInstance.maxHeartbeats 3400000

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
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateAFaithfulFredholmSum4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D
open P0EFTJanusProgramPGlobalCandidateAActionTranslationZeroModes4D
open P0EFTJanusProgramPGlobalCandidateANamedZeroModeSectors4D
open P0EFTJanusProgramPGlobalCandidateAFiveSectorOrthogonalProduct4D
open P0EFTJanusProgramPGlobalCandidateAFiveSectorActualHessianCommutation4D
open P0EFTJanusProgramPFiveSectorOrthogonalProductResolution4D
open P0EFTJanusProgramPCandidateAZeroModeSector4D
open P0EFTJanusProgramPActionTranslationSymmetryHessianKernel4D
open P0EFTJanusMappingTorusGlobalLLVariation4D

attribute [local instance]
  actualKernelNormedAddCommGroup
  actualKernelInnerProductSpace
  actualKernelNormedSpace
  actualKernelModule
  actualKernelCompleteSpace

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

local instance (priority := 30000) generatorNormedAddCommGroup
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

local instance (priority := 30000) generatorInnerProductSpace
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

local instance (priority := 30000) generatorNormedSpace
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

local instance (priority := 30000) generatorModule
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

local instance (priority := 30000) generatorCompleteSpace
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

private theorem candidateASectorSlot_injective :
    Function.Injective candidateAZeroModeSectorToFiveSectorSlot := by
  intro first second h
  cases first <;> cases second <;>
    simp [candidateAZeroModeSectorToFiveSectorSlot] at h ⊢

/-- Finite exact-action generators placed in the ranges of the one physical
five-sector resolution.  No coercivity or kernel-completeness premise appears. -/
structure GlobalCandidateAFiveSectorActionSymmetryGenerators4D
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
    (geometry : GlobalCandidateAFiveSectorActualHessianOffDiagonalZero4D period
      hPeriod configuration data analysis chart sameAction physical Metric Abelian
        Matter Longitudinal Boundary)
    (ZeroMode : Type*) [Fintype ZeroMode] where
  translations : GlobalCandidateAActionTranslationSymmetryModes4D period hPeriod
    configuration data analysis chart sameAction physical ZeroMode
  classification : CandidateAZeroModeSectorClassification ZeroMode
  sector_fixed : ∀ mode,
    globalCandidateAFiveSectorOrthogonalProjection period hPeriod
        geometry.orthogonalResolution (classification.sectorOf mode)
        (translations.vector mode) =
      translations.vector mode

namespace GlobalCandidateAFiveSectorActionSymmetryGenerators4D

/-- Every generator satisfies the actual operator equation obtained by
differentiating invariance of the same augmented action. -/
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
    {geometry : GlobalCandidateAFiveSectorActualHessianOffDiagonalZero4D period
      hPeriod configuration data analysis chart sameAction physical Metric Abelian
        Matter Longitudinal Boundary}
    {ZeroMode : Type*} [Fintype ZeroMode]
    (input : GlobalCandidateAFiveSectorActionSymmetryGenerators4D period hPeriod
      configuration data analysis chart sameAction physical Metric Abelian Matter
        Longitudinal Boundary geometry ZeroMode)
    (mode : ZeroMode) :
    globalCandidateAActualKernelOperator period hPeriod configuration data
        analysis chart sameAction physical (input.translations.vector mode) = 0 :=
  (input.translations.toGradientModes period hPeriod).vector_annihilated
    period hPeriod mode

/-- The same generator, now typed as an element of the genuine actual kernel. -/
def kernelVector
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
    {geometry : GlobalCandidateAFiveSectorActualHessianOffDiagonalZero4D period
      hPeriod configuration data analysis chart sameAction physical Metric Abelian
        Matter Longitudinal Boundary}
    {ZeroMode : Type*} [Fintype ZeroMode]
    (input : GlobalCandidateAFiveSectorActionSymmetryGenerators4D period hPeriod
      configuration data analysis chart sameAction physical Metric Abelian Matter
        Longitudinal Boundary geometry ZeroMode)
    (mode : ZeroMode) :
    (globalCandidateAActualKernelOperator period hPeriod configuration data
      analysis chart sameAction physical).ker :=
  ⟨input.translations.vector mode,
    LinearMap.mem_ker.mpr (input.vector_annihilated period hPeriod mode)⟩

/-- Every generator lies in the range of its labelled physical projector. -/
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
    {geometry : GlobalCandidateAFiveSectorActualHessianOffDiagonalZero4D period
      hPeriod configuration data analysis chart sameAction physical Metric Abelian
        Matter Longitudinal Boundary}
    {ZeroMode : Type*} [Fintype ZeroMode]
    (input : GlobalCandidateAFiveSectorActionSymmetryGenerators4D period hPeriod
      configuration data analysis chart sameAction physical Metric Abelian Matter
        Longitudinal Boundary geometry ZeroMode)
    (mode : ZeroMode) :
    input.translations.vector mode ∈
      (globalCandidateAFiveSectorOrthogonalProjection period hPeriod
        geometry.orthogonalResolution (input.classification.sectorOf mode)).range :=
  ⟨input.translations.vector mode, input.sector_fixed mode⟩

/-- Every projector with a distinct label annihilates the generator. -/
theorem projection_eq_zero_of_sector_ne
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
    {geometry : GlobalCandidateAFiveSectorActualHessianOffDiagonalZero4D period
      hPeriod configuration data analysis chart sameAction physical Metric Abelian
        Matter Longitudinal Boundary}
    {ZeroMode : Type*} [Fintype ZeroMode]
    (input : GlobalCandidateAFiveSectorActionSymmetryGenerators4D period hPeriod
      configuration data analysis chart sameAction physical Metric Abelian Matter
        Longitudinal Boundary geometry ZeroMode)
    (mode : ZeroMode) (sector : CandidateAZeroModeSector)
    (hDifferent : sector ≠ input.classification.sectorOf mode) :
    globalCandidateAFiveSectorOrthogonalProjection period hPeriod
        geometry.orthogonalResolution sector (input.translations.vector mode) = 0 := by
  let ownSector := input.classification.sectorOf mode
  let vector := input.translations.vector mode
  have hSlots :
      candidateAZeroModeSectorToFiveSectorSlot sector ≠
        candidateAZeroModeSectorToFiveSectorSlot ownSector := by
    intro hSame
    exact hDifferent (candidateASectorSlot_injective hSame)
  have hComp := geometry.orthogonalResolution.toGeneric.projection_comp_zero
    (candidateAZeroModeSectorToFiveSectorSlot sector)
    (candidateAZeroModeSectorToFiveSectorSlot ownSector) hSlots
  have hApplied := congrArg (fun operator => operator vector) hComp
  calc
    globalCandidateAFiveSectorOrthogonalProjection period hPeriod
        geometry.orthogonalResolution sector vector =
      globalCandidateAFiveSectorOrthogonalProjection period hPeriod
        geometry.orthogonalResolution sector
        (globalCandidateAFiveSectorOrthogonalProjection period hPeriod
          geometry.orthogonalResolution ownSector vector) := by
      rw [input.sector_fixed mode]
    _ = 0 := by
      change
        geometry.orthogonalResolution.toGeneric.projection
            (candidateAZeroModeSectorToFiveSectorSlot sector)
          (geometry.orthogonalResolution.toGeneric.projection
            (candidateAZeroModeSectorToFiveSectorSlot ownSector) vector) = 0
      simpa only [ContinuousLinearMap.comp_apply, zero_apply] using hApplied

/-- Distinct-sector action generators are automatically orthogonal. -/
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
    {geometry : GlobalCandidateAFiveSectorActualHessianOffDiagonalZero4D period
      hPeriod configuration data analysis chart sameAction physical Metric Abelian
        Matter Longitudinal Boundary}
    {ZeroMode : Type*} [Fintype ZeroMode]
    (input : GlobalCandidateAFiveSectorActionSymmetryGenerators4D period hPeriod
      configuration data analysis chart sameAction physical Metric Abelian Matter
        Longitudinal Boundary geometry ZeroMode)
    (first second : ZeroMode)
    (hDifferent : input.classification.sectorOf first ≠
      input.classification.sectorOf second) :
    inner Real (input.translations.vector first)
        (input.translations.vector second) = 0 := by
  let firstSector := input.classification.sectorOf first
  let secondSector := input.classification.sectorOf second
  have hSlots :
      candidateAZeroModeSectorToFiveSectorSlot firstSector ≠
        candidateAZeroModeSectorToFiveSectorSlot secondSector := by
    intro hSame
    exact hDifferent (candidateASectorSlot_injective hSame)
  calc
    inner Real (input.translations.vector first)
        (input.translations.vector second) =
      inner Real
        (globalCandidateAFiveSectorOrthogonalProjection period hPeriod
          geometry.orthogonalResolution firstSector
            (input.translations.vector first))
        (globalCandidateAFiveSectorOrthogonalProjection period hPeriod
          geometry.orthogonalResolution secondSector
            (input.translations.vector second)) := by
      rw [input.sector_fixed first, input.sector_fixed second]
    _ = 0 :=
      geometry.orthogonalResolution.toGeneric.projection_orthogonal
        (candidateAZeroModeSectorToFiveSectorSlot firstSector)
        (candidateAZeroModeSectorToFiveSectorSlot secondSector)
        hSlots (input.translations.vector first) (input.translations.vector second)

/-- Exact action invariance remains visible in the sector-refined packet. -/
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
    {geometry : GlobalCandidateAFiveSectorActualHessianOffDiagonalZero4D period
      hPeriod configuration data analysis chart sameAction physical Metric Abelian
        Matter Longitudinal Boundary}
    {ZeroMode : Type*} [Fintype ZeroMode]
    (input : GlobalCandidateAFiveSectorActionSymmetryGenerators4D period hPeriod
      configuration data analysis chart sameAction physical Metric Abelian Matter
        Longitudinal Boundary geometry ZeroMode)
    (mode : ZeroMode) :
    ActionTranslationEventuallyInvariantAt
      (globalCandidateACommonAugmentedAction period hPeriod configuration data
        analysis chart sameAction physical)
      0 (input.translations.vector mode) :=
  input.translations.action_translation_invariant mode

/-- Public non-circular symmetry-generator checkpoint. -/
theorem global_candidateA_five_sector_action_symmetry_generators_gate
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
    {geometry : GlobalCandidateAFiveSectorActualHessianOffDiagonalZero4D period
      hPeriod configuration data analysis chart sameAction physical Metric Abelian
        Matter Longitudinal Boundary}
    {ZeroMode : Type*} [Fintype ZeroMode]
    (input : GlobalCandidateAFiveSectorActionSymmetryGenerators4D period hPeriod
      configuration data analysis chart sameAction physical Metric Abelian Matter
        Longitudinal Boundary geometry ZeroMode) :
    (∀ mode,
      ActionTranslationEventuallyInvariantAt
        (globalCandidateACommonAugmentedAction period hPeriod configuration data
          analysis chart sameAction physical)
        0 (input.translations.vector mode)) ∧
    (∀ mode,
      globalCandidateAActualKernelOperator period hPeriod configuration data
          analysis chart sameAction physical (input.translations.vector mode) = 0) ∧
    (∀ mode,
      input.translations.vector mode ∈
        (globalCandidateAFiveSectorOrthogonalProjection period hPeriod
          geometry.orthogonalResolution
          (input.classification.sectorOf mode)).range) ∧
    (∀ mode sector,
      sector ≠ input.classification.sectorOf mode →
      globalCandidateAFiveSectorOrthogonalProjection period hPeriod
          geometry.orthogonalResolution sector (input.translations.vector mode) =
        0) ∧
    (∀ first second,
      input.classification.sectorOf first ≠
          input.classification.sectorOf second →
      inner Real (input.translations.vector first)
        (input.translations.vector second) = 0) :=
  ⟨input.action_translation_invariant period hPeriod,
    input.vector_annihilated period hPeriod,
    input.vector_mem_sectorRange period hPeriod,
    input.projection_eq_zero_of_sector_ne period hPeriod,
    input.vectors_inner_eq_zero_of_sector_ne period hPeriod⟩

end GlobalCandidateAFiveSectorActionSymmetryGenerators4D

end
end P0EFTJanusProgramPGlobalCandidateAFiveSectorActionSymmetryGenerators4D
end JanusFormal
