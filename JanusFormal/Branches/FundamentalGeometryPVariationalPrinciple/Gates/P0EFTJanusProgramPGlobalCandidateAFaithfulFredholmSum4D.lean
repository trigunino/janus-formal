import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAMatterFiniteGraphVariationalChart4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalLocalHessianBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateACommonAnalyticDomainClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusTruePTFullLLFirstVariationBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusLinearPMapProdIdentityFredholm4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusBoundedSelfAdjointFredholmReduction4D

/-!
# Faithful graph sum toward the global Candidate-A Fredholm Hessian

This is the sole P4 assembly file of `HESSIAN-GLOBAL-01`.  It records the
already proved faithful typed multiplicities and the two genuine same-action
matter/LL blocks.  The bounded Riesz operator below is the existing
BRST--SpinC--LL graph representative; it is not called the total physical
Hessian because the seven retained physical blocks must first be added by the
minimal local Hessian bridge.  This file also keeps the remaining matter--LL comparison visible:
the local chart bridge currently identifies only the base configuration, not
the supplied action datum, so its mismatch cannot be erased for an arbitrary
chart.

No reduced `Fin 9` spectral packet is substituted for the nine distinct
nonminimal smooth species, and no Fredholm hypothesis is stored here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAFaithfulFredholmSum4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 600000

noncomputable section

open scoped Manifold ContDiff LinearPMap
open MeasureTheory Set
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
open P0EFTJanusDifferentialLLFullCurveActionDecomposition4D
open P0EFTJanusIntegratedPTFullLLHessianVariation4D
open P0EFTJanusTruePTFullLLFirstVariationBridge4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalBoundaryCompletion4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateAMatterFiniteGraphVariationalChart4D
open P0EFTJanusProgramPGlobalHessianFrontier4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPGlobalFullLLGraphRiesz4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalLocalHessianBridge4D
open P0EFTJanusProgramPGlobalCandidateACommonAnalyticDomainClosure4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D
open P0EFTJanusProgramPPrimitiveSpinCGeometricSignedFredholm4D
open P0EFTJanusProgramPGlobalFullLLOnShellFredholmReduction4D
open P0EFTJanusComplexDiagonalMaximalOperator4D
open P0EFTJanusLinearPMapProdIdentityFredholm4D
open P0EFTJanusMappingTorusGlobalLLVariation4D
open P0EFTJanusMappingTorusPTSymmetricLLH1RieszOperator4D
open P0EFTJanusBoundedSelfAdjointFredholmReduction4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

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

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance effectiveThroatCompactSpace :
    CompactSpace (EffectiveThroat period hPeriod) :=
  P0EFTJanusMappingTorusCompactQuotient.fixedThroatQuotientCompactSpace
    period hPeriod

local instance effectiveThroatMeasurableSpace :
    MeasurableSpace (EffectiveThroat period hPeriod) := borel _

local instance effectiveThroatBorelSpace :
    BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

local instance effectiveThroatFiniteMeasure :
    IsFiniteMeasure
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod

local instance effectiveThroatOpenPosMeasure :
    Measure.IsOpenPosMeasure
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  intrinsicCanonicalThroatVolumeMeasure_isOpenPosMeasure period hPeriod

local instance faithfulFredholmL2NormedAddCommGroup
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    NormedAddCommGroup
      (GlobalCandidateADiagonalExtendedBulkL2Hilbert period hPeriod metric
        couplings.matterMassSquared data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkNormedAddCommGroup
    period hPeriod metric couplings.matterMassSquared data analysis

local instance faithfulFredholmL2InnerProductSpace
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    InnerProductSpace Real
      (GlobalCandidateADiagonalExtendedBulkL2Hilbert period hPeriod metric
        couplings.matterMassSquared data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkInnerProductSpace
    period hPeriod metric couplings.matterMassSquared data analysis

local instance faithfulFredholmL2NormedSpace
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    NormedSpace Real
      (GlobalCandidateADiagonalExtendedBulkL2Hilbert period hPeriod metric
        couplings.matterMassSquared data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkNormedSpace
    period hPeriod metric couplings.matterMassSquared data analysis

local instance faithfulFredholmL2Module
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    Module Real
      (GlobalCandidateADiagonalExtendedBulkL2Hilbert period hPeriod metric
        couplings.matterMassSquared data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkModule
    period hPeriod metric couplings.matterMassSquared data analysis

local instance faithfulFredholmL2CompleteSpace
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    CompleteSpace
      (GlobalCandidateADiagonalExtendedBulkL2Hilbert period hPeriod metric
        couplings.matterMassSquared data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkCompleteSpace
    period hPeriod metric couplings.matterMassSquared data analysis

local instance (priority := 10000)
    matterFiniteGraphCoreNormedAddCommGroup
    (massSquared : Real) :
    NormedAddCommGroup
      (GlobalCandidateAMatterFiniteGraphCore
        period hPeriod massSquared) :=
  globalCandidateAMatterFiniteGraphCoreNormedAddCommGroup
    period hPeriod massSquared

local instance (priority := 10000)
    matterFiniteGraphCoreNormedSpace
    (massSquared : Real) :
    NormedSpace Real
      (GlobalCandidateAMatterFiniteGraphCore
        period hPeriod massSquared) :=
  globalCandidateAMatterFiniteGraphCoreNormedSpace
    period hPeriod massSquared

noncomputable local instance globalCandidateAMatterLLGraphAmbientInnerProduct
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    InnerProductSpace Real
      (GlobalFullLLGraphAmbient period hPeriod data analysis) := by
  infer_instance

noncomputable local instance globalCandidateAMatterLLGraphInnerProduct
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    InnerProductSpace Real
      (GlobalFullLLGraphHilbert period hPeriod data analysis) :=
  Submodule.innerProductSpace
    (globalCandidateAFullLLGraphSubmodule period hPeriod data analysis)

local instance globalCandidateAMatterLLFieldProjectionKernelClosed
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    IsClosed
      ((globalCandidateAFullLLFieldProjection period hPeriod data analysis).ker :
        Set (GlobalFullLLGraphHilbert period hPeriod data analysis)) :=
  (globalCandidateAFullLLFieldProjection period hPeriod
    data analysis).isClosed_ker

/-! ## Faithful typed multiplicities -/

/-- The nonminimal packet is exactly two sector-indexed Abelian triples and
one diffeomorphism triple: `2 * 3 + 3 = 9` distinct smooth species. -/
def globalCandidateAFaithfulFredholmSum_typedNonminimalEquiv :
    GlobalTypedNonminimalFields period hPeriod ≃
      (Sector → GlobalAbelianNonminimalFields period hPeriod) ×
        GlobalDiffeomorphismNonminimalFields period hPeriod :=
  globalTypedNonminimalFieldsEquiv period hPeriod

/-- The exact smooth graph core retains all physical and typed coordinates
faithfully; no multiplicity is supplied by the historical `Fin 9` model. -/
theorem globalCandidateAFaithfulFredholmSum_typedCore_injective
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    Function.Injective
      (diagonalExtendedBulkGraphTypedCoreLinearMap period hPeriod
        configuration data analysis) :=
  diagonalExtendedBulkGraphTypedCoreLinearMap_injective period hPeriod
    configuration data analysis

/-! ## Canonical faithful graph same-action realization -/

/-- The already constructed L2 graph completion carrying the diagonal
diffeomorphism triplet, both Abelian triplets, SpinC matter and full LL block.
This is the faithful typed realization; the historical `Fin 9` packet does
not occur in its definition. -/
abbrev GlobalCandidateAFaithfulSameActionHilbert
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

/-- The exact bounded Riesz representative of the unchanged BRST, SpinC and
LL graph same-action sum on the faithful typed completion.  The seven physical
action blocks are not part of this operator. -/
def globalCandidateAFaithfulSameActionRieszOperator
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration
        data analysis →L[Real]
      GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration
        data analysis :=
  diagonalExtendedBulkL2RieszOperator period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
    couplings.matterMassSquared data analysis

/-- The smooth core of the faithful realization still injects jointly into
the completed graph and the corrected nine-field tangent. -/
theorem globalCandidateAFaithfulSameAction_typedL2Core_injective
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    Function.Injective
      (diagonalExtendedBulkL2GraphTypedCoreLinearMap period hPeriod
        configuration data analysis) :=
  diagonalExtendedBulkL2GraphTypedCoreLinearMap_injective period hPeriod
    configuration data analysis

theorem globalCandidateAFaithfulSameActionRieszOperator_pairing
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (first second : GlobalCandidateAFaithfulSameActionHilbert period hPeriod
      configuration data analysis) :
    inner Real
        (globalCandidateAFaithfulSameActionRieszOperator period hPeriod
          configuration data analysis first) second =
      diagonalExtendedBulkL2Hessian period hPeriod
        (globalCandidateAMetricBySector period hPeriod data)
        couplings.matterMassSquared data analysis first second :=
  diagonalExtendedBulkL2RieszOperator_pairing period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
    couplings.matterMassSquared data analysis first second

def globalCandidateAFaithfulSameActionRieszOperator_isSelfAdjoint
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :=
  diagonalExtendedBulkL2RieszOperator_isSelfAdjoint period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
    couplings.matterMassSquared data analysis

/-- Abstract reduction for the existing graph operator.  This is useful for
blockwise checks, but it is not the terminal Candidate-A Fredholm theorem:
the seven physical action blocks must first be realized on the common domain. -/
theorem globalCandidateAFaithfulSameActionRieszOperator_fredholm_of_closedRange_finiteKernel
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (hClosed : IsClosed
      ((globalCandidateAFaithfulSameActionRieszOperator period hPeriod
        configuration data analysis).range :
        Set (GlobalCandidateAFaithfulSameActionHilbert period hPeriod
          configuration data analysis)))
    (hKernel : FiniteDimensional Real
      (globalCandidateAFaithfulSameActionRieszOperator period hPeriod
        configuration data analysis).ker) :
    IsClosed
        ((globalCandidateAFaithfulSameActionRieszOperator period hPeriod
          configuration data analysis).range :
          Set (GlobalCandidateAFaithfulSameActionHilbert period hPeriod
            configuration data analysis)) ∧
      FiniteDimensional Real
        (globalCandidateAFaithfulSameActionRieszOperator period hPeriod
          configuration data analysis).ker ∧
      FiniteDimensional Real
        (GlobalCandidateAFaithfulSameActionHilbert period hPeriod
            configuration data analysis ⧸
          (globalCandidateAFaithfulSameActionRieszOperator period hPeriod
            configuration data analysis).range) := by
  letI : NormedAddCommGroup
      (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration
        data analysis) :=
    faithfulFredholmL2NormedAddCommGroup period hPeriod
      (globalCandidateAMetricBySector period hPeriod data) data analysis
  letI : InnerProductSpace Real
      (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration
        data analysis) :=
    faithfulFredholmL2InnerProductSpace period hPeriod
      (globalCandidateAMetricBySector period hPeriod data) data analysis
  letI : CompleteSpace
      (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration
        data analysis) :=
    faithfulFredholmL2CompleteSpace period hPeriod
      (globalCandidateAMetricBySector period hPeriod data) data analysis
  exact @boundedSelfAdjoint_fredholm_of_closedRange_finiteKernel
    (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration
      data analysis)
    (faithfulFredholmL2NormedAddCommGroup period hPeriod
      (globalCandidateAMetricBySector period hPeriod data) data analysis)
    (faithfulFredholmL2InnerProductSpace period hPeriod
      (globalCandidateAMetricBySector period hPeriod data) data analysis)
    (faithfulFredholmL2CompleteSpace period hPeriod
      (globalCandidateAMetricBySector period hPeriod data) data analysis)
    (globalCandidateAFaithfulSameActionRieszOperator period hPeriod
      configuration data analysis)
    (globalCandidateAFaithfulSameActionRieszOperator_isSelfAdjoint period
      hPeriod configuration data analysis) hClosed hKernel

/-- The faithful graph same-action index is forced to be zero once the two
analytic estimates above are proved.  The terminal total index is stated only
after augmentation by the physical action blocks. -/
theorem globalCandidateAFaithfulSameActionRieszOperator_index_zero_of_closedRange_finiteKernel
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (hClosed : IsClosed
      ((globalCandidateAFaithfulSameActionRieszOperator period hPeriod
        configuration data analysis).range :
        Set (GlobalCandidateAFaithfulSameActionHilbert period hPeriod
          configuration data analysis)))
    (hKernel : FiniteDimensional Real
      (globalCandidateAFaithfulSameActionRieszOperator period hPeriod
        configuration data analysis).ker) :
    (globalCandidateAFaithfulSameActionRieszOperator period hPeriod
      configuration data analysis).toLinearMap.index = 0 := by
  letI : NormedAddCommGroup
      (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration
        data analysis) :=
    faithfulFredholmL2NormedAddCommGroup period hPeriod
      (globalCandidateAMetricBySector period hPeriod data) data analysis
  letI : InnerProductSpace Real
      (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration
        data analysis) :=
    faithfulFredholmL2InnerProductSpace period hPeriod
      (globalCandidateAMetricBySector period hPeriod data) data analysis
  letI : CompleteSpace
      (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration
        data analysis) :=
    faithfulFredholmL2CompleteSpace period hPeriod
      (globalCandidateAMetricBySector period hPeriod data) data analysis
  exact @boundedSelfAdjoint_index_zero
    (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration
      data analysis)
    (faithfulFredholmL2NormedAddCommGroup period hPeriod
      (globalCandidateAMetricBySector period hPeriod data) data analysis)
    (faithfulFredholmL2InnerProductSpace period hPeriod
      (globalCandidateAMetricBySector period hPeriod data) data analysis)
    (faithfulFredholmL2CompleteSpace period hPeriod
      (globalCandidateAMetricBySector period hPeriod data) data analysis)
    (globalCandidateAFaithfulSameActionRieszOperator period hPeriod
      configuration data analysis)
    (globalCandidateAFaithfulSameActionRieszOperator_isSelfAdjoint period
      hPeriod configuration data analysis) hClosed hKernel

/-! ## Existing same-action blocks -/

/-- The primitive SpinC graph form is the Hessian of a genuine restriction of
the unchanged Candidate-A covariant action. -/
theorem globalCandidateAFaithfulFredholmSum_matter_sameAction
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (measure : Measure (EffectiveQuotient period hPeriod))
    (core first second : GlobalCandidateAMatterFiniteGraphCore
      period hPeriod couplings.matterMassSquared) :
    globalCandidateAHessian period hPeriod
        (globalCandidateAMatterFiniteGraphVariationalChart
          period hPeriod data measure) core first second =
      programPPrimitiveSpinCMatterGraphForm
        period hPeriod couplings.matterMassSquared
        (globalCandidateAMatterFiniteGraphInclusion
          period hPeriod couplings.matterMassSquared first)
        (globalCandidateAMatterFiniteGraphInclusion
          period hPeriod couplings.matterMassSquared second) :=
  globalCandidateAMatterFiniteGraph_sameActionHessian
    period hPeriod data measure core first second

/-- The complete three-slot LL graph form agrees on its dense smooth core
with the unchanged LL action Hessian. -/
theorem globalCandidateAFaithfulFredholmSum_ll_sameAction
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (first second : GlobalFullLLSmooth period hPeriod analysis) :
    globalCandidateAFullLLContinuousHessian period hPeriod data analysis
        (globalCandidateAFullLLSmoothEmbedding period hPeriod
          data analysis first)
        (globalCandidateAFullLLSmoothEmbedding period hPeriod
          data analysis second) =
      globalCandidateAFullLLSameActionHessian period hPeriod
        data first second :=
  globalCandidateAFullLLContinuousHessian_smooth period hPeriod
    data analysis first second

/-! ## Concrete common matter--LL action chart -/

/-- Two independent scalar parameters inserted in the genuine primitive
SpinC and true three-slot LL summands of the unchanged Candidate-A action. -/
def globalCandidateAMatterLLCommonTwoParameterAction
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (matter : GlobalCandidateAMatterFiniteGraphCore
      period hPeriod couplings.matterMassSquared)
    (ll : GlobalFullLLSmooth period hPeriod analysis)
    (matterParameter llParameter : Real) : Real :=
  globalCandidateAMatterAction period hPeriod
      (globalCandidateAMatterFiniteGraphConfiguration period hPeriod
        configuration couplings.matterMassSquared (matterParameter • matter))
      couplings +
    globalPTSymmetricDifferentialLLAction period hPeriod
      (canonicalDivergenceFreeLLFrame period hPeriod)
      (differentialLLFullCurve period hPeriod
        (data.boundary.llFields period hPeriod)
        ll.1.1 ll.1.2 ll.2.toTest llParameter)
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod)

/-- At every fixed matter parameter, differentiating the common action in
the LL parameter gives the existing true full-LL first variation. -/
theorem globalCandidateAMatterLLCommonTwoParameterAction_ll_hasDerivAt
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (matter : GlobalCandidateAMatterFiniteGraphCore
      period hPeriod couplings.matterMassSquared)
    (ll : GlobalFullLLSmooth period hPeriod analysis)
    (matterParameter : Real) :
    HasDerivAt
      (fun llParameter =>
        globalCandidateAMatterLLCommonTwoParameterAction period hPeriod
          data analysis matter ll matterParameter llParameter)
      (globalPTFullLLFirstVariation period hPeriod
        (canonicalDivergenceFreeLLFrame period hPeriod)
        (data.boundary.llFields period hPeriod)
        (globalCandidateAFullLLDirection period hPeriod ll)
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod)) 0 := by
  letI : IsFiniteMeasure
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
    intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod
  have hLL := truePTAction_fullCurve_hasDerivAt_fullFirstVariation
    period hPeriod
    (canonicalDivergenceFreeLLFrame period hPeriod)
    (data.boundary.llFields period hPeriod)
    (globalCandidateAFullLLDirection period hPeriod ll)
    (intrinsicCanonicalThroatVolumeMeasure period hPeriod)
  have hConstant := hasDerivAt_const (x := (0 : Real))
    (c := globalCandidateAMatterAction period hPeriod
      (globalCandidateAMatterFiniteGraphConfiguration period hPeriod
        configuration couplings.matterMassSquared (matterParameter • matter))
      couplings)
  change HasDerivAt
    ((fun _ : Real =>
        globalCandidateAMatterAction period hPeriod
          (globalCandidateAMatterFiniteGraphConfiguration period hPeriod
            configuration couplings.matterMassSquared
            (matterParameter • matter)) couplings) +
      fun llParameter =>
        globalPTSymmetricDifferentialLLAction period hPeriod
          (canonicalDivergenceFreeLLFrame period hPeriod)
          (differentialLLFullCurve period hPeriod
            (data.boundary.llFields period hPeriod)
            ll.1.1 ll.1.2 ll.2.toTest llParameter)
          (intrinsicCanonicalThroatVolumeMeasure period hPeriod))
      (globalPTFullLLFirstVariation period hPeriod
        (canonicalDivergenceFreeLLFrame period hPeriod)
        (data.boundary.llFields period hPeriod)
        (globalCandidateAFullLLDirection period hPeriod ll)
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod)) 0
  simpa only [zero_add,
    globalCandidateAFullLLDirection_llAuxMetric,
    globalCandidateAFullLLDirection_llMeasure,
    globalCandidateAFullLLDirection_llField] using hConstant.add hLL

/-- The actual mixed matter--LL derivative vanishes on the concrete common
two-parameter action: after the genuine LL derivative, no matter parameter
remains. -/
theorem globalCandidateAMatterLLCommonTwoParameterAction_mixed_deriv_eq_zero
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (matter : GlobalCandidateAMatterFiniteGraphCore
      period hPeriod couplings.matterMassSquared)
    (ll : GlobalFullLLSmooth period hPeriod analysis) :
    deriv
      (fun matterParameter =>
        deriv
          (fun llParameter =>
            globalCandidateAMatterLLCommonTwoParameterAction period hPeriod
              data analysis matter ll matterParameter llParameter) 0) 0 = 0 := by
  let coefficient := globalPTFullLLFirstVariation period hPeriod
    (canonicalDivergenceFreeLLFrame period hPeriod)
    (data.boundary.llFields period hPeriod)
    (globalCandidateAFullLLDirection period hPeriod ll)
    (intrinsicCanonicalThroatVolumeMeasure period hPeriod)
  have hInner :
      (fun matterParameter =>
        deriv
          (fun llParameter =>
            globalCandidateAMatterLLCommonTwoParameterAction period hPeriod
              data analysis matter ll matterParameter llParameter) 0) =
        fun _ : Real => coefficient := by
    funext matterParameter
    exact (globalCandidateAMatterLLCommonTwoParameterAction_ll_hasDerivAt
      period hPeriod data analysis matter ll matterParameter).deriv
  rw [hInner]
  exact (hasDerivAt_const (x := (0 : Real)) (c := coefficient)).deriv

/-! ## Exact remaining P4 frontier -/

/-- For the present generic local bridge, equality with the augmented graph
is equivalent to the sole displayed matter--LL mismatch.  The terminal P4
step must prove this mismatch from the concrete common chart, not assume it. -/
def globalCandidateAFaithfulFredholmSum_eq_augmented_iff :=
  @diagonalExtendedBulkMinimalPhysicalLocalGaugeFixed_eq_augmented_iff

/-! ## Actual SpinC--LL Fredholm product -/

private abbrev GlobalCandidateAMatterLLSpinCHilbert :=
  ComplexDiagonalHilbert PrimitiveSpinCGeometricSignedMode

local instance (priority := 10000)
    globalCandidateAMatterLLSpinCRealInnerProduct :
    InnerProductSpace Real GlobalCandidateAMatterLLSpinCHilbert :=
  InnerProductSpace.complexToReal

/-- The primitive SpinC maximal operator summed with the positive LL
completion.  On shell this completion is exactly equivalent to the full-graph
quotient, whose Riesz operator is the identity by the reduction exposed below. -/
def globalCandidateAMatterLLFredholmOperator
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    WithLp 2
        (GlobalCandidateAMatterLLSpinCHilbert ×
          LLH1Space period hPeriod
            (analysis.llH1Data period hPeriod)) →ₗ.[Real]
      WithLp 2
        (GlobalCandidateAMatterLLSpinCHilbert ×
          LLH1Space period hPeriod
            (analysis.llH1Data period hPeriod)) :=
  linearPMapProdIdentity
    (E := GlobalCandidateAMatterLLSpinCHilbert)
    (F := LLH1Space period hPeriod (analysis.llH1Data period hPeriod))
    (primitiveSpinCGeometricSignedMassRealOperator
      period hPeriod couplings.matterMassSquared)

/-- The existing primitive SpinC criterion gives Fredholmness of the
SpinC--LL stationary direct sum. -/
def globalCandidateAMatterLLFredholmOperator_fredholm
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    (analysis : GlobalAnalysisData period hPeriod configuration) :=
  linearPMapProdIdentity_fredholm
    (E := GlobalCandidateAMatterLLSpinCHilbert)
    (F := LLH1Space period hPeriod (analysis.llH1Data period hPeriod))
    (primitiveSpinCGeometricSignedMassRealOperator
      period hPeriod couplings.matterMassSquared)
    (primitiveSpinCGeometricSignedMassRealOperator_fredholm
      period hPeriod couplings.matterMassSquared)

/-- LL stationarity identifies the actual full-graph quotient Riesz block
with the identity factor used in the preceding Fredholm sum. -/
def globalCandidateAMatterLL_actualLL_eq_identity_of_stationary
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (hStationary : ∀ point,
      LLStationaryAt period hPeriod
        (data.boundary.llFields period hPeriod) point) :=
  globalCandidateAFullLLFieldQuotientRieszOperator_eq_id period hPeriod
    data analysis
      (llField_eq_zero_of_stationary period hPeriod
        (data.boundary.llFields period hPeriod) hStationary)

/-! The two component certificates remain exposed without changing domains. -/
def globalCandidateAFaithfulFredholmSum_spinC_fredholm :=
  globalCandidateACommonAnalyticDomain_spinC_fredholm

def globalCandidateAFaithfulFredholmSum_ll_fredholm_of_stationary :=
  @globalCandidateACommonAnalyticDomain_ll_fredholm_of_stationary

def globalCandidateAFaithfulFredholmSum_ll_index_zero_of_stationary :=
  @globalCandidateACommonAnalyticDomain_ll_index_zero_of_stationary

end
end P0EFTJanusProgramPGlobalCandidateAFaithfulFredholmSum4D
end JanusFormal
