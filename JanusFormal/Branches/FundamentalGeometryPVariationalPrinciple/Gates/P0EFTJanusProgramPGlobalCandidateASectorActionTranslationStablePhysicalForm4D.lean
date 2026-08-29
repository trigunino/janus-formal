import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPCandidateASectorModeAssembly4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAActionTranslationStablePhysicalForm4D

/-!
# Stable Candidate-A action symmetries assembled by physical sector

The preferred action-symmetry packet still used one opaque global mode type.
This file replaces it by the dependent sum of the five D10-free physical
sectors.  Action invariance is supplied sector by sector; nonzero and
orthogonality data are assembled by the generic sector module.

The principal Gårding estimate, smallness of the true H11 physical form and LL
stationarity are unchanged.  The resulting object is exactly the established
stable action-translation packet, so every downstream H12/H14 conclusion is
reused without a second operator or completion.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateASectorActionTranslationStablePhysicalForm4D

set_option autoImplicit false
set_option maxHeartbeats 12600000
set_option synthInstance.maxHeartbeats 6300000

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
open P0EFTJanusProgramPGlobalCandidateAActionTranslationStablePhysicalForm4D
open P0EFTJanusProgramPGlobalCandidateAActualKernelNamedGarding4D
open P0EFTJanusProgramPGlobalCandidateACanonicalStablePerturbation4D
open P0EFTJanusProgramPGlobalCandidateANamedZeroModeSectors4D
open P0EFTJanusProgramPCandidateAZeroModeSector4D
open P0EFTJanusProgramPCandidateASectorModeAssembly4D
open P0EFTJanusProgramPActionTranslationSymmetryHessianKernel4D
open P0EFTJanusMappingTorusGlobalLLVariation4D

attribute [local instance]
  actualKernelNormedAddCommGroup
  actualKernelInnerProductSpace
  actualKernelNormedSpace
  actualKernelModule
  actualKernelCompleteSpace

variable (period : Real) (hPeriod : period ≠ 0)

noncomputable local instance candidateASectorGlobalModeDecidableEq
    (types : CandidateASectorModeTypes) : DecidableEq types.GlobalMode :=
  Classical.decEq _

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

private def SectorStableHilbert
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) : Type :=
  GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration data
    analysis

local instance (priority := 30000) sectorStableNormedAddCommGroup
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    NormedAddCommGroup
      (SectorStableHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkNormedAddCommGroup
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) sectorStableInnerProductSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    InnerProductSpace Real
      (SectorStableHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkInnerProductSpace
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) sectorStableNormedSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    NormedSpace Real
      (SectorStableHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkNormedSpace
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) sectorStableModule
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    Module Real
      (SectorStableHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkModule
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) sectorStableCompleteSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    CompleteSpace
      (SectorStableHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkCompleteSpace
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

/-- Five-sector action invariance and stable principal-coercivity packet. -/
structure GlobalCandidateASectorActionTranslationStablePhysicalFormData4D
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
    (types : CandidateASectorModeTypes) : Type where
  modes : CandidateASectorOrthogonalModeFamily
    (E := SectorStableHilbert period hPeriod configuration data analysis) types
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
      SectorStableHilbert period hPeriod configuration data analysis,
    referenceConstant * ‖current‖ ^ 2 ≤
      ⟪current,
        globalCandidateACanonicalStableReferenceOperator period hPeriod
          configuration data analysis current⟫_Real +
        defectConstant *
          ∑ mode : types.GlobalMode,
            ⟪current, modes.vectors.globalVector mode⟫_Real ^ 2
  ll_stationary : ∀ point,
    LLStationaryAt period hPeriod
      (data.boundary.llFields period hPeriod) point

/-- Assemble the sector-local action identities into the established global
translation packet. -/
def GlobalCandidateASectorActionTranslationStablePhysicalFormData4D.toTranslations
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
    (input : GlobalCandidateASectorActionTranslationStablePhysicalFormData4D
      period hPeriod configuration data analysis chart sameAction physical
        types) :
    GlobalCandidateAActionTranslationSymmetryModes4D period hPeriod
      configuration data analysis chart sameAction physical types.GlobalMode where
  vector := input.modes.vectors.globalVector
  action_translation_invariant := by
    rintro ⟨sector, mode⟩
    exact input.action_translation_invariant sector mode

/-- Forget the sector packaging and obtain the strongest existing stable
physical-form packet. -/
def GlobalCandidateASectorActionTranslationStablePhysicalFormData4D.toStable
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
    (input : GlobalCandidateASectorActionTranslationStablePhysicalFormData4D
      period hPeriod configuration data analysis chart sameAction physical
        types) :
    GlobalCandidateAActionTranslationStablePhysicalFormData4D period hPeriod
      configuration data analysis chart sameAction physical types.GlobalMode where
  translations := input.toTranslations period hPeriod
  nonzero := input.modes.global_nonzero
  orthogonal := input.modes.global_orthogonal
  referenceConstant := input.referenceConstant
  physical_form_small := input.physical_form_small
  defectConstant := input.defectConstant
  defectConstant_nonneg := input.defectConstant_nonneg
  reference_garding := input.reference_garding
  ll_stationary := input.ll_stationary

/-- The exact actual-kernel dimension is the sum of the five sector
multiplicities. -/
theorem GlobalCandidateASectorActionTranslationStablePhysicalFormData4D.kernel_finrank_eq_sector_sum
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
    (input : GlobalCandidateASectorActionTranslationStablePhysicalFormData4D
      period hPeriod configuration data analysis chart sameAction physical
        types) :
    Module.finrank Real
        (globalCandidateAActualKernelOperator period hPeriod configuration data
          analysis chart sameAction physical).ker =
      ∑ sector : CandidateAZeroModeSector,
        types.classification.multiplicity sector := by
  let named := (input.toStable period hPeriod).toNamedGarding period hPeriod
  calc
    Module.finrank Real
        (globalCandidateAActualKernelOperator period hPeriod configuration data
          analysis chart sameAction physical).ker =
      Fintype.card types.GlobalMode :=
        named.kernel_finrank_eq_card period hPeriod
    _ = ∑ sector : CandidateAZeroModeSector,
        types.classification.multiplicity sector :=
      types.classification.sum_multiplicity.symm

/-- Public sector-stable Candidate-A checkpoint. -/
def global_candidateA_sector_action_translation_stable_gate
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
    (input : GlobalCandidateASectorActionTranslationStablePhysicalFormData4D
      period hPeriod configuration data analysis chart sameAction physical
        types) :
    PSigma fun _ :
      GlobalCandidateAActualKernelGap4D period hPeriod configuration data analysis
        chart sameAction physical =>
      Module.finrank Real
          (globalCandidateAActualKernelOperator period hPeriod configuration data
            analysis chart sameAction physical).ker =
        ∑ sector : CandidateAZeroModeSector,
          types.classification.multiplicity sector :=
  ⟨(input.toStable period hPeriod).toNamedGarding.toGap period hPeriod,
    input.kernel_finrank_eq_sector_sum period hPeriod⟩

end
end P0EFTJanusProgramPGlobalCandidateASectorActionTranslationStablePhysicalForm4D
end JanusFormal
