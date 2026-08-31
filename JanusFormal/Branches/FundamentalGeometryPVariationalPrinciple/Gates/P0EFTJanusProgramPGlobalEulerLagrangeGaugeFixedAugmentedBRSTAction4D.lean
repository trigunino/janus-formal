import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateASevenPhysicalCanonicalExtensionsOfReducedHilbertChart4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticEuler4D

/-!
# Gauge-fixed augmented BRST action from the reduced physical chart

The minimal physical chart cannot remember a nonzero diffeomorphism
`c/cbar/B` triplet.  This gate keeps that reduced chart for the nonlinear
physical action, but uses it only to construct the seven bounded physical
Hessian extensions on the already existing diagonal gauge-fixed Hilbert graph.

Thus no metric degree of freedom is duplicated: the completed graph contains
the two metric perturbations and one shared diffeomorphism triplet.  Its
quadratic action is `C²`, has the advertised Riesz representative, and agrees
on the dense smooth core with the genuine BRST gauge-fixing action plus the
seven physical Hessian blocks.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedAugmentedBRSTAction4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 3600000

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff InnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalPairedAbelianBRSTGaugeFermion4D
open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalLocalHessianBridge4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalBlockExtensions4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalCanonicalExtensions4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalCanonicalExtensionsOfReducedHilbertChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedHilbert4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCoreToChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCompletedCanonicalAvailableQuadraticEuler4D
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

local instance gaugeFixedCanonicalLorentzVolumeFinite :
    IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  canonicalLorentzVolumeFinite period hPeriod

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace

/-! ## Canonical physical extension on the faithful augmented graph -/

/-- The separated canonical extensions canonically sum to the physical form
expected by the common augmented action. -/
def globalCandidateASevenPhysicalCommonDomainExtension_of_canonical
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
    (extensions : GlobalCandidateASevenPhysicalCanonicalContinuousExtensions4D
      period hPeriod configuration data analysis chart sameAction) :
    GlobalCandidateASevenPhysicalCommonDomainExtension4D period hPeriod
      configuration data analysis chart sameAction :=
  globalCandidateASevenPhysicalCommonDomainExtension_of_blocks period hPeriod
    configuration data analysis chart sameAction
    (globalCandidateASevenPhysicalBlockExtensions_of_canonical period hPeriod
      configuration data analysis chart sameAction extensions)

section ReducedChart

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
    (reducedChart : ProgramPGlobalMinimalPhysicalReducedHilbertChart4D period
      hPeriod configuration data analysis chartData)

private abbrev MinimalChart :=
  globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
    configuration data analysis chartData

private abbrev SameAction :=
  globalCandidateAMinimalPhysicalMatterLLSameActionBridge period hPeriod
    configuration data analysis chartData

private abbrev SmoothCore :=
  GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod analysis

private abbrev AugmentedModel :=
  CommonAugmentedHilbert period hPeriod configuration data analysis

/-- The reduced physical chart supplies the seven physical extensions, while
the target remains the faithful gauge-fixed graph containing `c/cbar/B`. -/
def globalCandidateAGaugeFixedAugmentedPhysicalExtension :
    GlobalCandidateASevenPhysicalCommonDomainExtension4D period hPeriod
      configuration data analysis
      (MinimalChart period hPeriod configuration data analysis chartData)
      (SameAction period hPeriod configuration data analysis chartData) :=
  globalCandidateASevenPhysicalCommonDomainExtension_of_canonical period hPeriod
    configuration data analysis
    (MinimalChart period hPeriod configuration data analysis chartData)
    (SameAction period hPeriod configuration data analysis chartData)
    (globalCandidateASevenPhysicalCanonicalContinuousExtensions_of_reducedHilbertChart
      period hPeriod configuration data analysis chartData reducedChart)

/-- Canonical quadratic gauge-fixed action on the faithful augmented model. -/
def globalCandidateAGaugeFixedAugmentedBRSTAction :
    AugmentedModel period hPeriod configuration data analysis → Real :=
  globalCandidateACommonAugmentedAction period hPeriod configuration data
    analysis
    (MinimalChart period hPeriod configuration data analysis chartData)
    (SameAction period hPeriod configuration data analysis chartData)
    (globalCandidateAGaugeFixedAugmentedPhysicalExtension period hPeriod
      configuration data analysis chartData reducedChart)

/-- Strong Riesz representative of the augmented action's first variation. -/
def globalCandidateAGaugeFixedAugmentedBRSTRieszOperator :
    AugmentedModel period hPeriod configuration data analysis →L[Real]
      AugmentedModel period hPeriod configuration data analysis :=
  globalCandidateACommonAugmentedRieszOperator period hPeriod configuration
    data analysis
    (MinimalChart period hPeriod configuration data analysis chartData)
    (SameAction period hPeriod configuration data analysis chartData)
    (globalCandidateAGaugeFixedAugmentedPhysicalExtension period hPeriod
      configuration data analysis chartData reducedChart)

theorem globalCandidateAGaugeFixedAugmentedBRSTAction_contDiff_two :
    ContDiff Real 2
      (globalCandidateAGaugeFixedAugmentedBRSTAction period hPeriod
        configuration data analysis chartData reducedChart) :=
  globalCandidateACommonAugmentedAction_contDiff_two period hPeriod
    configuration data analysis
    (MinimalChart period hPeriod configuration data analysis chartData)
    (SameAction period hPeriod configuration data analysis chartData)
    (globalCandidateAGaugeFixedAugmentedPhysicalExtension period hPeriod
      configuration data analysis chartData reducedChart)

theorem globalCandidateAGaugeFixedAugmentedBRSTAction_fderiv
    (state : AugmentedModel period hPeriod configuration data analysis) :
    fderiv Real
        (globalCandidateAGaugeFixedAugmentedBRSTAction period hPeriod
          configuration data analysis chartData reducedChart) state =
      globalCandidateACommonAugmentedHessian period hPeriod configuration data
        analysis
        (MinimalChart period hPeriod configuration data analysis chartData)
        (SameAction period hPeriod configuration data analysis chartData)
        (globalCandidateAGaugeFixedAugmentedPhysicalExtension period hPeriod
          configuration data analysis chartData reducedChart) state :=
  globalCandidateACommonAugmentedAction_fderiv period hPeriod configuration
    data analysis
    (MinimalChart period hPeriod configuration data analysis chartData)
    (SameAction period hPeriod configuration data analysis chartData)
    (globalCandidateAGaugeFixedAugmentedPhysicalExtension period hPeriod
      configuration data analysis chartData reducedChart) state

theorem globalCandidateAGaugeFixedAugmentedBRSTRieszOperator_pairing
    (state test : AugmentedModel period hPeriod configuration data analysis) :
    inner Real
        (globalCandidateAGaugeFixedAugmentedBRSTRieszOperator period hPeriod
          configuration data analysis chartData reducedChart state) test =
      fderiv Real
        (globalCandidateAGaugeFixedAugmentedBRSTAction period hPeriod
          configuration data analysis chartData reducedChart) state test := by
  rw [globalCandidateAGaugeFixedAugmentedBRSTAction_fderiv]
  exact globalCandidateACommonAugmentedRieszOperator_pairing period hPeriod
    configuration data analysis
    (MinimalChart period hPeriod configuration data analysis chartData)
    (SameAction period hPeriod configuration data analysis chartData)
    (globalCandidateAGaugeFixedAugmentedPhysicalExtension period hPeriod
      configuration data analysis chartData reducedChart) state test

/-- Unlike the minimal projection, the augmented graph and typed tangent keep
the whole smooth core injectively. -/
theorem globalCandidateAGaugeFixedAugmentedTypedCore_injective :
    Function.Injective
      (diagonalExtendedBulkL2GraphTypedCoreLinearMap period hPeriod
        configuration data analysis) :=
  diagonalExtendedBulkL2GraphTypedCoreLinearMap_injective period hPeriod
    configuration data analysis

/-- Explicit same-action identity on the dense smooth core.  The first term is
the genuine shared-triplet diffeomorphism BRST variation; the last term is the
quadratic contribution of the seven remaining physical blocks. -/
theorem globalCandidateAGaugeFixedAugmentedBRSTAction_smooth_eq
    (core : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod
      analysis) :
    globalCandidateAGaugeFixedAugmentedBRSTAction period hPeriod configuration
        data analysis chartData reducedChart
        (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
          (globalCandidateAMetricBySector period hPeriod data)
          couplings.matterMassSquared data analysis core) =
      globalCandidateADiagonalDiffeomorphismGaugeFermionBRSTVariation
          period hPeriod couplings
          (globalCandidateAMetricBySector period hPeriod data) core.1 +
        globalPairedAbelianGaugeFermionBRSTAction period hPeriod
          (globalCandidateAMetricBySector period hPeriod data) core.2.1
          (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) +
        programPPrimitiveSpinCMatterGraphAction period hPeriod
          couplings.matterMassSquared
          (programPPrimitiveSpinCMatterGraphFiniteRealLinearMap period hPeriod
            couplings.matterMassSquared core.2.2.1) +
        globalCandidateAFullLLGraphAction period hPeriod data analysis
          (globalCandidateAFullLLSmoothEmbedding period hPeriod data analysis
            core.2.2.2) +
        (1 / 2 : Real) *
          diagonalExtendedBulkMinimalPhysicalLocalActionHessianOnCore period
            hPeriod configuration data analysis
            (MinimalChart period hPeriod configuration data analysis chartData)
            (SameAction period hPeriod configuration data analysis
              chartData).chartBridge core core := by
  let physical := globalCandidateAGaugeFixedAugmentedPhysicalExtension period
    hPeriod configuration data analysis chartData reducedChart
  let embedding := diagonalExtendedBulkL2SmoothEmbedding period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
    couplings.matterMassSquared data analysis
  have hGraph :=
    diagonalExtendedBulkL2Action_smooth_eq_BRSTAndSectorActions period hPeriod
      (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis core
  have hPhysical := physical.smooth_agreement core core
  unfold globalCandidateAGaugeFixedAugmentedBRSTAction
    globalCandidateACommonAugmentedAction
    globalCandidateACommonAugmentedHessian
  change
    (1 / 2 : Real) *
        (diagonalExtendedBulkL2Hessian period hPeriod
            (globalCandidateAMetricBySector period hPeriod data)
            couplings.matterMassSquared data analysis
            (embedding core) (embedding core) +
          physical.form (embedding core) (embedding core)) = _
  rw [hPhysical]
  unfold diagonalExtendedBulkL2Action at hGraph
  linarith

/-- Gate 221: the reduced physical chart canonically yields a faithful
gauge-fixed augmented action certificate without a common-chart inverse. -/
theorem global_candidateA_gaugeFixed_augmented_BRST_action_gate :
    GlobalCandidateACommonAugmentedAnalyticDomainCertificate4D period hPeriod
      configuration data analysis
      (MinimalChart period hPeriod configuration data analysis chartData)
      (SameAction period hPeriod configuration data analysis chartData)
      (globalCandidateAGaugeFixedAugmentedPhysicalExtension period hPeriod
        configuration data analysis chartData reducedChart) :=
  global_candidateA_h11_common_augmented_domain_gate period hPeriod
    configuration data analysis
    (MinimalChart period hPeriod configuration data analysis chartData)
    (SameAction period hPeriod configuration data analysis chartData)
    (globalCandidateAGaugeFixedAugmentedPhysicalExtension period hPeriod
      configuration data analysis chartData reducedChart)

end ReducedChart

end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedAugmentedBRSTAction4D
end JanusFormal
