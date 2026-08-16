import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAActionTranslationZeroModes4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateACanonicalPhysicalFormStablePerturbation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteKernelOrthogonalNamedModeGarding4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAActualKernelNamedGarding4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPNamedModeGardingPerturbation4D

/-!
# Action symmetries stable under the canonical physical Hessian

This is the strongest action-level zero-mode packet.  The named vectors are
specified by local translation invariance of the genuine augmented Candidate-A
action:

`S (x + t • v) = S x`.

Differentiation gives the actual Hessian equations.  Nonzero pairwise
orthogonality gives independence.  A Gårding estimate for the canonical
BRST--SpinC--LL principal operator and strict smallness of the H11 physical form
produce Gårding for the full Hessian.  Thus no separate fields for `H v = 0`,
linear independence or total-Hessian coercivity remain.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAActionTranslationStablePhysicalForm4D

set_option autoImplicit false
set_option maxHeartbeats 11600000
set_option synthInstance.maxHeartbeats 5800000

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
open P0EFTJanusProgramPGlobalCandidateAInfinitesimalSymmetryZeroModes4D
open P0EFTJanusProgramPGlobalCandidateAActualKernelNamedGarding4D
open P0EFTJanusProgramPGlobalCandidateACanonicalStablePerturbation4D
open P0EFTJanusProgramPGlobalCandidateACanonicalPhysicalFormStablePerturbation4D
open P0EFTJanusProgramPFiniteKernelOrthogonalNamedModeGarding4D
open P0EFTJanusProgramPNamedModeGardingPerturbation4D
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

private abbrev ActionStableHilbert
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :=
  GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration data
    analysis

local instance (priority := 30000) actionStableNormedAddCommGroup
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    NormedAddCommGroup
      (ActionStableHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkNormedAddCommGroup
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) actionStableInnerProductSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    InnerProductSpace Real
      (ActionStableHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkInnerProductSpace
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) actionStableNormedSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    NormedSpace Real
      (ActionStableHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkNormedSpace
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) actionStableModule
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    Module Real
      (ActionStableHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkModule
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) actionStableCompleteSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    CompleteSpace
      (ActionStableHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkCompleteSpace
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)

/-- Action-level symmetry and principal-coercivity packet. -/
structure GlobalCandidateAActionTranslationStablePhysicalFormData4D
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
    (ZeroMode : Type*) [Fintype ZeroMode] : Prop where
  translations : GlobalCandidateAActionTranslationSymmetryModes4D period hPeriod
    configuration data analysis chart sameAction physical ZeroMode
  nonzero : ∀ mode, translations.vector mode ≠ 0
  orthogonal : Pairwise fun first second =>
    ⟪translations.vector first, translations.vector second, Real⟫ = 0
  referenceConstant : Real
  physical_form_small : ‖physical.form‖ < referenceConstant
  defectConstant : Real
  defectConstant_nonneg : 0 ≤ defectConstant
  reference_garding : ∀ current :
      ActionStableHilbert period hPeriod configuration data analysis,
    referenceConstant * ‖current‖ ^ 2 ≤
      ⟪current,
        globalCandidateACanonicalStableReferenceOperator period hPeriod
          configuration data analysis current, Real⟫ +
        defectConstant *
          ∑ mode : ZeroMode,
            ⟪current, translations.vector mode, Real⟫ ^ 2
  ll_stationary : ∀ point,
    LLStationaryAt period hPeriod
      (data.boundary.llFields period hPeriod) point

/-- Strict smallness of the actual physical Riesz perturbation. -/
theorem GlobalCandidateAActionTranslationStablePhysicalFormData4D.physical_operator_small
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
    {ZeroMode : Type*} [Fintype ZeroMode]
    (input : GlobalCandidateAActionTranslationStablePhysicalFormData4D period
      hPeriod configuration data analysis chart sameAction physical ZeroMode) :
    ‖globalCandidateACanonicalStablePhysicalPerturbation period hPeriod
        configuration data analysis chart sameAction physical‖ <
      input.referenceConstant :=
  lt_of_le_of_lt
    (globalCandidateACanonicalStablePhysicalPerturbation_opNorm_le_form period
      hPeriod configuration data analysis chart sameAction physical)
    input.physical_form_small

/-- Build the exact orthogonal named-mode Gårding packet for the total Hessian. -/
def GlobalCandidateAActionTranslationStablePhysicalFormData4D.toOrthogonalGarding
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
    {ZeroMode : Type*} [Fintype ZeroMode]
    (input : GlobalCandidateAActionTranslationStablePhysicalFormData4D period
      hPeriod configuration data analysis chart sameAction physical ZeroMode) :
    FiniteKernelOrthogonalNamedModeGardingData
      (globalCandidateAActualKernelOperator period hPeriod configuration data
        analysis chart sameAction physical) ZeroMode where
  vector := input.translations.vector
  annihilated :=
    (input.translations.toGradientModes period hPeriod).vector_annihilated
      period hPeriod
  nonzero := input.nonzero
  orthogonal := input.orthogonal
  constant := input.referenceConstant -
    ‖globalCandidateACanonicalStablePhysicalPerturbation period hPeriod
      configuration data analysis chart sameAction physical‖
  constant_pos := sub_pos.mpr (input.physical_operator_small period hPeriod)
  defectConstant := input.defectConstant
  defectConstant_nonneg := input.defectConstant_nonneg
  garding := by
    intro current
    have hReference := input.reference_garding current
    have hPerturbation := perturbation_real_inner_lower_bound
      (globalCandidateACanonicalStablePhysicalPerturbation period hPeriod
        configuration data analysis chart sameAction physical) current
    rw [globalCandidateAActualKernelOperator_eq_canonicalStableSum period hPeriod
      configuration data analysis chart sameAction physical,
      ContinuousLinearMap.add_apply, inner_add_right]
    linarith

/-- Convert to the established Candidate-A named Gårding packet. -/
def GlobalCandidateAActionTranslationStablePhysicalFormData4D.toNamedGarding
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
    {ZeroMode : Type*} [Fintype ZeroMode]
    (input : GlobalCandidateAActionTranslationStablePhysicalFormData4D period
      hPeriod configuration data analysis chart sameAction physical ZeroMode) :
    GlobalCandidateAActualKernelNamedGarding4D period hPeriod configuration data
      analysis chart sameAction physical ZeroMode where
  garding := input.toOrthogonalGarding.toAutomaticSplit.toNoHidden.toNamedGarding
  ll_stationary := input.ll_stationary

/-- Public action-symmetry/stable-perturbation checkpoint. -/
theorem global_candidateA_action_translation_stable_physical_form_gate
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
    {ZeroMode : Type*} [Fintype ZeroMode]
    (input : GlobalCandidateAActionTranslationStablePhysicalFormData4D period
      hPeriod configuration data analysis chart sameAction physical ZeroMode) :
    GlobalCandidateAActualKernelGap4D period hPeriod configuration data analysis
        chart sameAction physical ∧
      Module.finrank Real
          (globalCandidateAActualKernelOperator period hPeriod configuration data
            analysis chart sameAction physical).ker =
        Fintype.card ZeroMode :=
  global_candidateA_actual_kernel_named_garding_gate period hPeriod
    (input.toNamedGarding period hPeriod)

end
end P0EFTJanusProgramPGlobalCandidateAActionTranslationStablePhysicalForm4D
end JanusFormal
