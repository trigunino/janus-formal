import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPCandidateASectorSubspaceAssembly4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateASectorActionTranslationStablePhysicalForm4D

/-!
# Stable Candidate-A sector modes carried by orthogonal subspaces

This adapter removes the mode-by-mode cross-sector orthogonality premise from
the stable Candidate-A packet.  It is enough to place each finite family in one
of five mutually orthogonal physical subspaces.  The generic subspace assembly
constructs the global orthogonal mode family, after which the existing stable
Noether/Gårding chain applies unchanged.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateASectorSubspaceActionTranslationStablePhysicalForm4D

set_option autoImplicit false
set_option maxHeartbeats 13200000
set_option synthInstance.maxHeartbeats 6600000

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
open P0EFTJanusProgramPGlobalCandidateAActionTranslationStablePhysicalForm4D
open P0EFTJanusProgramPGlobalCandidateASectorActionTranslationStablePhysicalForm4D
open P0EFTJanusProgramPCandidateASectorModeAssembly4D
open P0EFTJanusProgramPCandidateASectorSubspaceAssembly4D
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

private abbrev SectorSubspaceHilbert
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :=
  GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration data
    analysis

local instance (priority := 30000) sectorSubspaceNormedAddCommGroup
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    NormedAddCommGroup
      (SectorSubspaceHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkNormedAddCommGroup
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) sectorSubspaceInnerProductSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    InnerProductSpace Real
      (SectorSubspaceHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkInnerProductSpace
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) sectorSubspaceNormedSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    NormedSpace Real
      (SectorSubspaceHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkNormedSpace
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) sectorSubspaceModule
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    Module Real
      (SectorSubspaceHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkModule
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) sectorSubspaceCompleteSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    CompleteSpace
      (SectorSubspaceHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkCompleteSpace
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)

/-- Stable packet whose mode orthogonality is inherited from five physical
subspaces. -/
structure GlobalCandidateASectorSubspaceActionTranslationStablePhysicalFormData4D
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
    (types : CandidateASectorModeTypes) : Prop where
  modes : CandidateASectorSubspaceModeFamily
    (E := SectorSubspaceHilbert period hPeriod configuration data analysis) types
  action_translation_invariant : ∀ sector mode,
    ActionTranslationEventuallyInvariantAt
      (globalCandidateACommonAugmentedAction period hPeriod configuration data
        analysis chart sameAction physical)
      0 (modes.vectors.vector sector mode)
  referenceConstant : Real
  physical_form_small : ‖physical.form‖ < referenceConstant
  defectConstant : Real
  defectConstant_nonneg : 0 ≤ defectConstant
  reference_garding : ∀ current :
      SectorSubspaceHilbert period hPeriod configuration data analysis,
    referenceConstant * ‖current‖ ^ 2 ≤
      ⟪current,
        globalCandidateACanonicalStableReferenceOperator period hPeriod
          configuration data analysis current, Real⟫ +
        defectConstant *
          ∑ mode : types.GlobalMode,
            ⟪current, modes.vectors.globalVector mode, Real⟫ ^ 2
  ll_stationary : ∀ point,
    LLStationaryAt period hPeriod
      (data.boundary.llFields period hPeriod) point

/-- Construct the general sector-stable packet after deriving cross-sector
orthogonality from subspace membership. -/
def GlobalCandidateASectorSubspaceActionTranslationStablePhysicalFormData4D.toSectorStable
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
    {types : CandidateASectorModeTypes}
    (input : GlobalCandidateASectorSubspaceActionTranslationStablePhysicalFormData4D
      period hPeriod configuration data analysis chart sameAction physical
        types) :
    GlobalCandidateASectorActionTranslationStablePhysicalFormData4D period
      hPeriod configuration data analysis chart sameAction physical types where
  modes := input.modes.toOrthogonalModeFamily
  action_translation_invariant := input.action_translation_invariant
  referenceConstant := input.referenceConstant
  physical_form_small := input.physical_form_small
  defectConstant := input.defectConstant
  defectConstant_nonneg := input.defectConstant_nonneg
  reference_garding := input.reference_garding
  ll_stationary := input.ll_stationary

/-- Public physical-subspace Candidate-A checkpoint. -/
theorem global_candidateA_sector_subspace_action_translation_stable_gate
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
    {types : CandidateASectorModeTypes}
    (input : GlobalCandidateASectorSubspaceActionTranslationStablePhysicalFormData4D
      period hPeriod configuration data analysis chart sameAction physical
        types) :
    GlobalCandidateAActualKernelGap4D period hPeriod configuration data analysis
        chart sameAction physical ∧
      Module.finrank Real
          (globalCandidateAActualKernelOperator period hPeriod configuration data
            analysis chart sameAction physical).ker =
        ∑ sector : CandidateAZeroModeSector,
          types.classification.multiplicity sector :=
  global_candidateA_sector_action_translation_stable_gate period hPeriod
    input.toSectorStable

end
end P0EFTJanusProgramPGlobalCandidateASectorSubspaceActionTranslationStablePhysicalForm4D
end JanusFormal
