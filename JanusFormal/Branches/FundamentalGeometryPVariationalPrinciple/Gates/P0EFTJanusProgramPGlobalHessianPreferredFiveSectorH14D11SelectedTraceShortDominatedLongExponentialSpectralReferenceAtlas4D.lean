import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11SelectedTraceInvariantDomainSchwarzSpectralReferenceAtlas4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPReferenceNuclearHeatFinitePartSelectedTraceShortDominatedLongExponentialCanonicalSchwarzAssembly4D

/-!
# Candidate-A selected-trace atlas with exponential long-time domination

The base reference and every local spectral-cut reference now use

* a general dominated short-time region;
* a long-time half-line with an automatically integrable exponential majorant;
* exponential decay of the terminal primitive;
* the logarithmic operator and nuclear trace already selected by the chart;
* canonical Schwarz symmetry of the Mellin continuation.

The adapter constructs the former selected-trace Candidate-A frontend.  Hence
all relative coefficients, the physical C1 kernel family and the determinant
atlas are preserved while the long-time `bound_integrable` fields disappear.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11SelectedTraceShortDominatedLongExponentialSpectralReferenceAtlas4D

set_option autoImplicit false
set_option maxHeartbeats 420000000
set_option synthInstance.maxHeartbeats 210000000
noncomputable section

open Filter Set Topology MeasureTheory
open scoped BigOperators Manifold ContDiff InnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyH10Reduction4D
open P0EFTJanusProgramPGlobalCandidateACanonicalSixDenseCore4D
open P0EFTJanusProgramPIntrinsicNuclearTrace4D
open P0EFTJanusProgramPNuclearDuhamelSemigroupRankOneAverage4D
open P0EFTJanusProgramPReferenceNuclearHeatFinitePartSelectedTraceShortDominatedLongExponentialCanonicalSchwarzAssembly4D
open P0EFTJanusProgramPRelativeHeatMellinAnalyticDifferenceFamily4D
open P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D
open P0EFTJanusProgramPRelativeZetaDeterminantConnection4D
open P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D
open P0EFTJanusProgramPUnitaryActualZetaFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorResolvedKernelFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11OperatorNormUnitaryFrame4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11SelectedTraceInvariantDomainSchwarzSpectralReferenceAtlas4D
open P0EFTJanusProgramPDenseCoreChartBilinearBound4D

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
    BorelSpace (EffectiveQuotient period hPeriod) where measurable_eq := rfl

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

variable
    {Slice ShortCutoff LongCutoff : Type*}
    [MeasurableSpace Slice]
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    {einsteinScale : Real}
    {hTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric}
    {family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D
      period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale}
    {chartBound : DenseCoreChartMapBound
      (globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
        data analysis)
      (globalCandidateACanonicalSixCoreToChart period hPeriod configuration data
        analysis
          (globalCandidateAActualKernelChart period hPeriod configuration data
            analysis einsteinScale hTransverse family)
          (globalCandidateAActualKernelSameAction period hPeriod configuration
            data analysis einsteinScale hTransverse family))}
    {Metric Abelian Matter Longitudinal Boundary : Type*}
    [NormedAddCommGroup Metric] [InnerProductSpace Real Metric]
    [NormedAddCommGroup Abelian] [InnerProductSpace Real Abelian]
    [NormedAddCommGroup Matter] [InnerProductSpace Real Matter]
    [NormedAddCommGroup Longitudinal] [InnerProductSpace Real Longitudinal]
    [NormedAddCommGroup Boundary] [InnerProductSpace Real Boundary]
    {ZeroMode : Type*} [Fintype ZeroMode] [DecidableEq ZeroMode]
    {fold : Fold} {Index : Type*}

private abbrev OldAtlas
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index) :=
  input.familyIndex

private abbrev BaseReduced
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index) :=
  SelfAdjointKernelComplement
    ((OldAtlas period hPeriod input).baseFamily.actualOperator 0)

structure GlobalHessianPreferredFiveSectorH14D11SelectedTraceShortDominatedLongExponentialSpectralReferenceData
    (sliceMeasure : Measure Slice) [IsProbabilityMeasure sliceMeasure]
    (shortCutoffFilter : Filter ShortCutoff) [NeBot shortCutoffFilter]
    (longCutoffFilter : Filter LongCutoff) [NeBot longCutoffFilter]
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index) where
  actual : UnitaryActualZetaFamilyData (E := BaseReduced period hPeriod input)
  baseReferenceFamily : RelativeHeatMellinZetaFamilyData
  baseDifference : RelativeHeatMellinAnalyticDifferenceFamilyData
    (OldAtlas period hPeriod input).baseFamily.familyIndex.zetaFamily
    actual.family baseReferenceFamily
  baseShortTimeRegion : Set Real
  baseLongTimeStart : Real
  baseAssembly :
    ReferenceNuclearHeatFinitePartSelectedTraceShortDominatedLongExponentialCanonicalSchwarzAssemblyData
      (E := BaseReduced period hPeriod input) sliceMeasure shortCutoffFilter
        longCutoffFilter (OldAtlas period hPeriod input).baseFamily.referenceOperator
          (OldAtlas period hPeriod input).baseFamily.familyIndex.referenceTrace
            baseReferenceFamily baseShortTimeRegion baseLongTimeStart
  baseSliceAverage : NuclearDuhamelSemigroupRankOneAverageData sliceMeasure
    baseAssembly.nuclear
  baseShortSemigroup_eq :
    baseAssembly.toDominatedExponentialCanonicalSchwarzAssembly.
        toSelectedTraceExponentialCanonicalSchwarzAssembly.
          toSelectedTraceCanonicalSchwarzAssembly.spectralBoundary.
            toFullySpectralBoundaryLimits.shortTime.semigroup =
      baseSliceAverage.toSemigroupProbabilityFamily
  baseLongSemigroup_eq :
    baseAssembly.toDominatedExponentialCanonicalSchwarzAssembly.
        toSelectedTraceExponentialCanonicalSchwarzAssembly.
          toSelectedTraceCanonicalSchwarzAssembly.spectralBoundary.
            toFullySpectralBoundaryLimits.longTime.semigroup =
      baseSliceAverage.toSemigroupProbabilityFamily
  localReferenceFamily : Index → RelativeHeatMellinZetaFamilyData
  localDifference : ∀ index,
    RelativeHeatMellinAnalyticDifferenceFamilyData
      ((OldAtlas period hPeriod input).localFamily index)
      actual.family (localReferenceFamily index)
  localShortTimeRegion : Index → Set Real
  localLongTimeStart : Index → Real
  localAssembly : ∀ index,
    ReferenceNuclearHeatFinitePartSelectedTraceShortDominatedLongExponentialCanonicalSchwarzAssemblyData
      (E := BaseReduced period hPeriod input) sliceMeasure shortCutoffFilter
        longCutoffFilter ((OldAtlas period hPeriod input).referenceOperator index)
          ((OldAtlas period hPeriod input).referenceTrace index)
            (localReferenceFamily index) (localShortTimeRegion index)
              (localLongTimeStart index)
  localSliceAverage : ∀ index,
    NuclearDuhamelSemigroupRankOneAverageData sliceMeasure
      (localAssembly index).nuclear
  localShortSemigroup_eq : ∀ index,
    (localAssembly index).toDominatedExponentialCanonicalSchwarzAssembly.
        toSelectedTraceExponentialCanonicalSchwarzAssembly.
          toSelectedTraceCanonicalSchwarzAssembly.spectralBoundary.
            toFullySpectralBoundaryLimits.shortTime.semigroup =
      (localSliceAverage index).toSemigroupProbabilityFamily
  localLongSemigroup_eq : ∀ index,
    (localAssembly index).toDominatedExponentialCanonicalSchwarzAssembly.
        toSelectedTraceExponentialCanonicalSchwarzAssembly.
          toSelectedTraceCanonicalSchwarzAssembly.spectralBoundary.
            toFullySpectralBoundaryLimits.longTime.semigroup =
      (localSliceAverage index).toSemigroupProbabilityFamily

namespace GlobalHessianPreferredFiveSectorH14D11SelectedTraceShortDominatedLongExponentialSpectralReferenceData

/-- Build the former selected-trace Candidate-A frontend. -/
def toSelectedTraceSpectralReferenceData
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {shortCutoffFilter : Filter ShortCutoff} [NeBot shortCutoffFilter]
    {longCutoffFilter : Filter LongCutoff} [NeBot longCutoffFilter]
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (spectral :
      GlobalHessianPreferredFiveSectorH14D11SelectedTraceShortDominatedLongExponentialSpectralReferenceData
        period hPeriod sliceMeasure shortCutoffFilter longCutoffFilter input) :
    GlobalHessianPreferredFiveSectorH14D11SelectedTraceInvariantDomainSchwarzSpectralReferenceData
      period hPeriod sliceMeasure shortCutoffFilter longCutoffFilter input where
  actual := spectral.actual
  baseReferenceFamily := spectral.baseReferenceFamily
  baseDifference := spectral.baseDifference
  baseShortTimeRegion := spectral.baseShortTimeRegion
  baseLongTimeRegion := Set.Ioi spectral.baseLongTimeStart
  baseAssembly :=
    spectral.baseAssembly.toDominatedExponentialCanonicalSchwarzAssembly.
      toSelectedTraceExponentialCanonicalSchwarzAssembly.
        toSelectedTraceCanonicalSchwarzAssembly
  baseSliceAverage := spectral.baseSliceAverage
  baseShortSemigroup_eq := spectral.baseShortSemigroup_eq
  baseLongSemigroup_eq := spectral.baseLongSemigroup_eq
  localReferenceFamily := spectral.localReferenceFamily
  localDifference := spectral.localDifference
  localShortTimeRegion := spectral.localShortTimeRegion
  localLongTimeRegion := fun index => Set.Ioi (spectral.localLongTimeStart index)
  localAssembly := fun index =>
    (spectral.localAssembly index).
      toDominatedExponentialCanonicalSchwarzAssembly.
        toSelectedTraceExponentialCanonicalSchwarzAssembly.
          toSelectedTraceCanonicalSchwarzAssembly
  localSliceAverage := spectral.localSliceAverage
  localShortSemigroup_eq := spectral.localShortSemigroup_eq
  localLongSemigroup_eq := spectral.localLongSemigroup_eq

/-- Physical Candidate-A closure with exponential long-time domination on all
reference charts. -/
def toPhysicalReferenceClosure
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {shortCutoffFilter : Filter ShortCutoff} [NeBot shortCutoffFilter]
    {longCutoffFilter : Filter LongCutoff} [NeBot longCutoffFilter]
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (frame : GlobalHessianPreferredFiveSectorD11OperatorNormUnitaryFrame4D
      period hPeriod input natural)
    (spectral :
      GlobalHessianPreferredFiveSectorH14D11SelectedTraceShortDominatedLongExponentialSpectralReferenceData
        period hPeriod sliceMeasure shortCutoffFilter longCutoffFilter input)
    (zeroTrace : IntrinsicNuclearTraceData
      (0 : BaseReduced period hPeriod input →L[Real]
        BaseReduced period hPeriod input)) :
    GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D period hPeriod
      configuration data analysis einsteinScale hTransverse family chartBound
        Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index :=
  (spectral.toSelectedTraceSpectralReferenceData period hPeriod input).
    toPhysicalReferenceClosure period hPeriod input natural frame zeroTrace

/-- Public strongest current Candidate-A reference checkpoint. -/
theorem global_hessian_preferred_five_sector_H14_D11_selected_trace_short_dominated_long_exponential_spectral_reference_atlas_gate
    (sliceMeasure : Measure Slice) [IsProbabilityMeasure sliceMeasure]
    (shortCutoffFilter : Filter ShortCutoff) [NeBot shortCutoffFilter]
    (longCutoffFilter : Filter LongCutoff) [NeBot longCutoffFilter]
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (frame : GlobalHessianPreferredFiveSectorD11OperatorNormUnitaryFrame4D
      period hPeriod input natural)
    (spectral :
      GlobalHessianPreferredFiveSectorH14D11SelectedTraceShortDominatedLongExponentialSpectralReferenceData
        period hPeriod sliceMeasure shortCutoffFilter longCutoffFilter input)
    (zeroTrace : IntrinsicNuclearTraceData
      (0 : BaseReduced period hPeriod input →L[Real]
        BaseReduced period hPeriod input)) :
    let selected := spectral.toSelectedTraceSpectralReferenceData period hPeriod input
    let closure := spectral.toPhysicalReferenceClosure period hPeriod input
      natural frame zeroTrace
    (∀ parameter,
      Integrable
        (P0EFTJanusProgramPLongTimeExponentialDominatingFunction4D.
          longTimeExponentialBound
            (spectral.baseAssembly.spectralBoundary.longTime.weighted.scale
              parameter)
            (spectral.baseAssembly.spectralBoundary.longTime.weighted.rate
              parameter))
        (volume.restrict (Set.Ioi spectral.baseLongTimeStart))) ∧
    (∀ index parameter,
      Integrable
        (P0EFTJanusProgramPLongTimeExponentialDominatingFunction4D.
          longTimeExponentialBound
            ((spectral.localAssembly index).spectralBoundary.longTime.weighted.
              scale parameter)
            ((spectral.localAssembly index).spectralBoundary.longTime.weighted.
              rate parameter))
        (volume.restrict (Set.Ioi (spectral.localLongTimeStart index)))) ∧
    (∀ parameter,
      relativeZetaConnectionCoefficient
          spectral.baseReferenceFamily.toZetaFamily parameter =
        -((OldAtlas period hPeriod input).baseFamily.familyIndex.referenceTrace.
          trace parameter : Complex)) ∧
    (∀ index parameter,
      relativeZetaConnectionCoefficient
          (spectral.localReferenceFamily index).toZetaFamily parameter =
        -((OldAtlas period hPeriod input).referenceTrace index |>.trace parameter :
          Complex)) ∧
    GlobalHessianPreferredFiveSectorResolvedKernelFamily4D period hPeriod closure ∧
    GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D period
      hPeriod closure := by
  dsimp only
  let selected :=
    spectral.toSelectedTraceSpectralReferenceData period hPeriod input
  let closure := spectral.toPhysicalReferenceClosure period hPeriod input natural
    frame zeroTrace
  have hSelected :=
    selected.
      global_hessian_preferred_five_sector_H14_D11_selected_trace_invariant_domain_schwarz_spectral_reference_atlas_gate
        period hPeriod sliceMeasure shortCutoffFilter longCutoffFilter input
          natural frame zeroTrace
  exact
    ⟨spectral.baseAssembly.longTime_bound_integrable,
      fun index => (spectral.localAssembly index).longTime_bound_integrable,
      hSelected.1,
      hSelected.2.1,
      hSelected.2.2.2.1,
      hSelected.2.2.2.2⟩

end GlobalHessianPreferredFiveSectorH14D11SelectedTraceShortDominatedLongExponentialSpectralReferenceData

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11SelectedTraceShortDominatedLongExponentialSpectralReferenceAtlas4D
end JanusFormal
