import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11SelectedTraceShortDominatedLongExponentialSpectralReferenceAtlas4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPReferenceNuclearHeatFinitePartSelectedTraceShortDominatedProductThroatLongTimeCanonicalSchwarzAssembly4D

/-!
# Candidate-A selected-trace atlas with product-throat long-time analysis

The base reference and every local spectral-cut reference are now equipped with
a genuine circle-times-monopole-sphere spectral model.  For every chart the
same product spectrum generates

* the positive heat gap `1 / R^2`;
* the exponential majorant of the inserted Duhamel trace;
* integrability of the long-time weighted derivative;
* exponential decay of the terminal primitive.

The short-time region keeps its local dominated subtraction packet.  The
selected intrinsic logarithmic traces, canonical Mellin Schwarz reflection,
relative coefficients and physical D11 kernel family are unchanged.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11SelectedTraceShortDominatedProductThroatLongTimeSpectralReferenceAtlas4D

set_option autoImplicit false
set_option maxHeartbeats 448000000
set_option synthInstance.maxHeartbeats 224000000
noncomputable section

open Filter Set Topology MeasureTheory
open scoped BigOperators Manifold ContDiff InnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyH10Reduction4D
open P0EFTJanusProgramPGlobalCandidateACanonicalSixDenseCore4D
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusProgramPGlobalHessianDiracGreenBoundedClosure4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalBlockBounds4D
open P0EFTJanusProgramPGlobalHessianActualKernelFrontier4D
open P0EFTJanusProgramPGlobalCandidateAFaithfulFredholmSum4D
open P0EFTJanusProgramPIntrinsicNuclearTrace4D
open P0EFTJanusProgramPNuclearDuhamelSemigroupRankOneAverage4D
open P0EFTJanusProgramPReferenceNuclearHeatFinitePartSelectedTraceShortDominatedProductThroatLongTimeCanonicalSchwarzAssembly4D
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
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11PhysicalReferenceClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11SelectedTraceInvariantDomainSchwarzSpectralReferenceAtlas4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11SelectedTraceShortDominatedLongExponentialSpectralReferenceAtlas4D
open P0EFTJanusProductThroatPositiveHeatGapLongTime4D
open P0EFTJanusProgramPLongTimeExponentialDominatingFunction4D
open P0EFTJanusProgramPDenseCoreChartBilinearBound4D

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace
  P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D.actualKernelNormedAddCommGroup
  P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D.actualKernelInnerProductSpace
  P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D.actualKernelNormedSpace
  P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D.actualKernelModule
  P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D.actualKernelCompleteSpace
  P0EFTJanusProgramPGlobalHessianPreferredFiveSectorBismutFreedFamily4D.candidateAHilbertNormedAddCommGroup
  P0EFTJanusProgramPGlobalHessianPreferredFiveSectorBismutFreedFamily4D.candidateAHilbertInnerProductSpace
  P0EFTJanusProgramPGlobalHessianPreferredFiveSectorBismutFreedFamily4D.candidateAHilbertNormedSpace
  P0EFTJanusProgramPGlobalHessianPreferredFiveSectorBismutFreedFamily4D.candidateAHilbertModule
  P0EFTJanusProgramPGlobalHessianPreferredFiveSectorBismutFreedFamily4D.candidateAHilbertCompleteSpace

variable (period : Real) (hPeriod : period ≠ 0)

universe v x y z

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

variable {measure : Measure (EffectiveQuotient period hPeriod)}

variable
    {Slice : Type x} {ShortCutoff : Type y} {LongCutoff : Type z}
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
      (measure := measure) period hPeriod configuration data analysis
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
    {Metric Abelian Matter Longitudinal Boundary : Type}
    [NormedAddCommGroup Metric] [InnerProductSpace Real Metric]
    [NormedAddCommGroup Abelian] [InnerProductSpace Real Abelian]
    [NormedAddCommGroup Matter] [InnerProductSpace Real Matter]
    [NormedAddCommGroup Longitudinal] [InnerProductSpace Real Longitudinal]
    [NormedAddCommGroup Boundary] [InnerProductSpace Real Boundary]
    {ZeroMode : Type} [Fintype ZeroMode] [DecidableEq ZeroMode]
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

/-- Candidate-A reference atlas whose complete long-time analysis is generated
by one product-throat spectrum per chart. -/
structure GlobalHessianPreferredFiveSectorH14D11SelectedTraceShortDominatedProductThroatLongTimeSpectralReferenceData
    (sliceMeasure : Measure Slice) [IsProbabilityMeasure sliceMeasure]
    (shortCutoffFilter : Filter ShortCutoff) [NeBot shortCutoffFilter]
    (longCutoffFilter : Filter LongCutoff) [NeBot longCutoffFilter]
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index) where
  actual : UnitaryActualZetaFamilyData.{0, v}
    (E := BaseReduced period hPeriod input)
  baseReferenceFamily : RelativeHeatMellinZetaFamilyData
  baseDifference : RelativeHeatMellinAnalyticDifferenceFamilyData
    (OldAtlas period hPeriod input).baseFamily.familyIndex.zetaFamily
    actual.family baseReferenceFamily
  baseProductData : ProductThroatSpectralData
  baseTwist : CircleTwist
  baseShortTimeRegion : Set Real
  baseLongTimeStart : Real
  baseAssembly :
    ReferenceNuclearHeatFinitePartSelectedTraceShortDominatedProductThroatLongTimeCanonicalSchwarzAssemblyData.{0, 0, x, y, z}
      (E := BaseReduced period hPeriod input) baseProductData fold baseTwist
        sliceMeasure shortCutoffFilter longCutoffFilter
          (OldAtlas period hPeriod input).baseFamily.referenceOperator
            (OldAtlas period hPeriod input).baseFamily.familyIndex.referenceTrace
              baseReferenceFamily baseShortTimeRegion baseLongTimeStart
  baseSliceAverage : NuclearDuhamelSemigroupRankOneAverageData.{x, 0, 0} sliceMeasure
    baseAssembly.nuclear
  baseShortSemigroup_eq :
    baseAssembly.toShortDominatedLongExponentialCanonicalSchwarzAssembly.toDominatedExponentialCanonicalSchwarzAssembly.toSelectedTraceExponentialCanonicalSchwarzAssembly.toSelectedTraceCanonicalSchwarzAssembly.spectralBoundary.toFullySpectralBoundaryLimits.shortTime.semigroup =
      baseSliceAverage.toSemigroupProbabilityFamily
  baseLongSemigroup_eq :
    baseAssembly.toShortDominatedLongExponentialCanonicalSchwarzAssembly.toDominatedExponentialCanonicalSchwarzAssembly.toSelectedTraceExponentialCanonicalSchwarzAssembly.toSelectedTraceCanonicalSchwarzAssembly.spectralBoundary.toFullySpectralBoundaryLimits.longTime.semigroup =
      baseSliceAverage.toSemigroupProbabilityFamily
  localReferenceFamily : Index → RelativeHeatMellinZetaFamilyData
  localDifference : ∀ index,
    RelativeHeatMellinAnalyticDifferenceFamilyData
      ((OldAtlas period hPeriod input).localFamily index)
      actual.family (localReferenceFamily index)
  localProductData : Index → ProductThroatSpectralData
  localTwist : Index → CircleTwist
  localShortTimeRegion : Index → Set Real
  localLongTimeStart : Index → Real
  localAssembly : ∀ index,
    ReferenceNuclearHeatFinitePartSelectedTraceShortDominatedProductThroatLongTimeCanonicalSchwarzAssemblyData.{0, 0, x, y, z}
      (E := BaseReduced period hPeriod input) (localProductData index) fold
        (localTwist index) sliceMeasure shortCutoffFilter longCutoffFilter
          ((OldAtlas period hPeriod input).referenceOperator index)
            ((OldAtlas period hPeriod input).referenceTrace index)
              (localReferenceFamily index) (localShortTimeRegion index)
                (localLongTimeStart index)
  localSliceAverage : ∀ index,
    NuclearDuhamelSemigroupRankOneAverageData.{x, 0, 0} sliceMeasure
      (localAssembly index).nuclear
  localShortSemigroup_eq : ∀ index,
    (localAssembly index).toShortDominatedLongExponentialCanonicalSchwarzAssembly.toDominatedExponentialCanonicalSchwarzAssembly.toSelectedTraceExponentialCanonicalSchwarzAssembly.toSelectedTraceCanonicalSchwarzAssembly.spectralBoundary.toFullySpectralBoundaryLimits.shortTime.semigroup =
      (localSliceAverage index).toSemigroupProbabilityFamily
  localLongSemigroup_eq : ∀ index,
    (localAssembly index).toShortDominatedLongExponentialCanonicalSchwarzAssembly.toDominatedExponentialCanonicalSchwarzAssembly.toSelectedTraceExponentialCanonicalSchwarzAssembly.toSelectedTraceCanonicalSchwarzAssembly.spectralBoundary.toFullySpectralBoundaryLimits.longTime.semigroup =
      (localSliceAverage index).toSemigroupProbabilityFamily

namespace GlobalHessianPreferredFiveSectorH14D11SelectedTraceShortDominatedProductThroatLongTimeSpectralReferenceData

/-- Forget the concrete spectral origin only after generating the existing
short-dominated/long-exponential Candidate-A atlas. -/
def toShortDominatedLongExponentialSpectralReferenceData
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {shortCutoffFilter : Filter ShortCutoff} [NeBot shortCutoffFilter]
    {longCutoffFilter : Filter LongCutoff} [NeBot longCutoffFilter]
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (spectral :
      GlobalHessianPreferredFiveSectorH14D11SelectedTraceShortDominatedProductThroatLongTimeSpectralReferenceData
        period hPeriod sliceMeasure shortCutoffFilter longCutoffFilter input) :
    GlobalHessianPreferredFiveSectorH14D11SelectedTraceShortDominatedLongExponentialSpectralReferenceData
      period hPeriod sliceMeasure shortCutoffFilter longCutoffFilter input where
  actual := spectral.actual
  baseReferenceFamily := spectral.baseReferenceFamily
  baseDifference := spectral.baseDifference
  baseShortTimeRegion := spectral.baseShortTimeRegion
  baseLongTimeStart := spectral.baseLongTimeStart
  baseAssembly :=
    spectral.baseAssembly.toShortDominatedLongExponentialCanonicalSchwarzAssembly
  baseSliceAverage := spectral.baseSliceAverage
  baseShortSemigroup_eq := spectral.baseShortSemigroup_eq
  baseLongSemigroup_eq := spectral.baseLongSemigroup_eq
  localReferenceFamily := spectral.localReferenceFamily
  localDifference := spectral.localDifference
  localShortTimeRegion := spectral.localShortTimeRegion
  localLongTimeStart := spectral.localLongTimeStart
  localAssembly := fun index =>
    (spectral.localAssembly index).toShortDominatedLongExponentialCanonicalSchwarzAssembly
  localSliceAverage := spectral.localSliceAverage
  localShortSemigroup_eq := spectral.localShortSemigroup_eq
  localLongSemigroup_eq := spectral.localLongSemigroup_eq

/-- Physical D11 closure generated from the concrete product-throat spectra. -/
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
      GlobalHessianPreferredFiveSectorH14D11SelectedTraceShortDominatedProductThroatLongTimeSpectralReferenceData
        period hPeriod sliceMeasure shortCutoffFilter longCutoffFilter input)
    (zeroTrace : IntrinsicNuclearTraceData
      (0 : BaseReduced period hPeriod input →L[Real]
        BaseReduced period hPeriod input)) :
    GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D period hPeriod
      configuration data analysis einsteinScale hTransverse family chartBound
        Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index :=
  (spectral.toShortDominatedLongExponentialSpectralReferenceData period hPeriod input)
    |>.toPhysicalReferenceClosure period hPeriod input natural frame zeroTrace

/-- Public Candidate-A product-throat spectral checkpoint. -/
theorem global_hessian_preferred_five_sector_H14_D11_selected_trace_short_dominated_product_throat_long_time_spectral_reference_atlas_gate
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
      GlobalHessianPreferredFiveSectorH14D11SelectedTraceShortDominatedProductThroatLongTimeSpectralReferenceData
        period hPeriod sliceMeasure shortCutoffFilter longCutoffFilter input)
    (zeroTrace : IntrinsicNuclearTraceData
      (0 : BaseReduced period hPeriod input →L[Real]
        BaseReduced period hPeriod input)) :
    let exponential :=
      spectral.toShortDominatedLongExponentialSpectralReferenceData period hPeriod
        input
    let selected := exponential.toSelectedTraceSpectralReferenceData period hPeriod
      input
    let closure := spectral.toPhysicalReferenceClosure period hPeriod input
      natural frame zeroTrace
    0 < productThroatPositiveHeatGap spectral.baseProductData ∧
    (∀ index,
      0 < productThroatPositiveHeatGap (spectral.localProductData index)) ∧
    (∀ parameter,
      Integrable
        (longTimeExponentialBound
          (spectral.baseAssembly.spectralBoundary.longTime.weighted.longTimeScale parameter)
          (productThroatPositiveHeatGap spectral.baseProductData))
        (volume.restrict (Set.Ioi spectral.baseLongTimeStart))) ∧
    (∀ index parameter,
      Integrable
        (longTimeExponentialBound
          ((spectral.localAssembly index).spectralBoundary.longTime.weighted.longTimeScale parameter)
          (productThroatPositiveHeatGap (spectral.localProductData index)))
        (volume.restrict (Set.Ioi (spectral.localLongTimeStart index)))) ∧
    (∀ parameter,
      relativeZetaConnectionCoefficient
          spectral.baseReferenceFamily.toZetaFamily parameter =
        -((OldAtlas period hPeriod input).baseFamily.familyIndex.referenceTrace.trace parameter : Complex)) ∧
    (∀ index parameter,
      relativeZetaConnectionCoefficient
          (spectral.localReferenceFamily index).toZetaFamily parameter =
        -((OldAtlas period hPeriod input).referenceTrace index |>.trace parameter :
          Complex)) ∧
    GlobalHessianPreferredFiveSectorResolvedKernelFamily4D period hPeriod closure ∧
    GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D period
      hPeriod closure := by
  dsimp only
  let exponential :=
    spectral.toShortDominatedLongExponentialSpectralReferenceData period hPeriod
      input
  let selected := exponential.toSelectedTraceSpectralReferenceData period hPeriod
    input
  let closure := spectral.toPhysicalReferenceClosure period hPeriod input natural
    frame zeroTrace
  have hSelected :=
    selected.global_hessian_preferred_five_sector_H14_D11_selected_trace_invariant_domain_schwarz_spectral_reference_atlas_gate
        period hPeriod sliceMeasure shortCutoffFilter longCutoffFilter input
          natural frame zeroTrace
  exact
    ⟨productThroatPositiveHeatGap_pos spectral.baseProductData,
      fun index =>
        productThroatPositiveHeatGap_pos (spectral.localProductData index),
      spectral.baseAssembly.longTime_bound_integrable,
      fun index => (spectral.localAssembly index).longTime_bound_integrable,
      spectral.baseAssembly.connectionCoefficient_eq_neg_selectedTrace,
      fun index =>
        (spectral.localAssembly index).connectionCoefficient_eq_neg_selectedTrace,
      hSelected.2.2.2.2.1,
      hSelected.2.2.2.2.2⟩

end GlobalHessianPreferredFiveSectorH14D11SelectedTraceShortDominatedProductThroatLongTimeSpectralReferenceData

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11SelectedTraceShortDominatedProductThroatLongTimeSpectralReferenceAtlas4D
end JanusFormal
