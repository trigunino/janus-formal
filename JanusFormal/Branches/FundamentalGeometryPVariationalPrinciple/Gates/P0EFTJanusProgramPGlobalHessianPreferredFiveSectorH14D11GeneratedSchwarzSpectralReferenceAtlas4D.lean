import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPReferenceNuclearHeatFinitePartGeneratedSchwarzAssembly4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11SchwarzSpectralReferenceAtlas4D

/-!
# Candidate-A atlas from primitive Mellin Schwarz data

This frontend replaces the normalized Mellin-candidate conjugation identity for
the base reference and every local spectral-cut reference by the two primitive
statements

```text
Gamma(s) = conj (Gamma(conj s)),
I(s)     = conj (I(conj s)).
```

The normalized candidate symmetry, Schwarz reflection of the analytic
continuation, real-axis germ, reality of `zeta'(0)` and all reference/relative
connection coefficients are generated downstream.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11GeneratedSchwarzSpectralReferenceAtlas4D

set_option autoImplicit false
set_option maxHeartbeats 328000000
set_option synthInstance.maxHeartbeats 164000000
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
open P0EFTJanusProgramPReferenceNuclearHeatFinitePartGeneratedSchwarzAssembly4D
open P0EFTJanusProgramPRelativeHeatMellinAnalyticDifferenceFamily4D
open P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D
open P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D
open P0EFTJanusProgramPUnitaryActualZetaFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorResolvedKernelFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11OperatorNormUnitaryFrame4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11SchwarzSpectralReferenceAtlas4D
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

/-- Candidate-A reference data with primitive Gamma/Mellin conjugation for the
base and local reference families. -/
structure GlobalHessianPreferredFiveSectorH14D11GeneratedSchwarzSpectralReferenceData
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
  baseLongTimeRegion : Set Real
  baseAssembly : ReferenceNuclearHeatFinitePartGeneratedSchwarzAssemblyData
    (E := BaseReduced period hPeriod input) sliceMeasure shortCutoffFilter
      longCutoffFilter baseReferenceFamily baseShortTimeRegion baseLongTimeRegion
  baseTrace_eq :
    baseAssembly.spectralBoundary.toCollapsedBoundaryLimits.toCollapsedBoundary.
        toBoundaryMatching.toOperatorIdentity.logarithmicTrace =
      (OldAtlas period hPeriod input).baseFamily.familyIndex.referenceTrace.trace
  baseSliceAverage : NuclearDuhamelSemigroupRankOneAverageData sliceMeasure
    baseAssembly.nuclear
  baseShortSemigroup_eq :
    baseAssembly.spectralBoundary.shortTime.semigroup =
      baseSliceAverage.toSemigroupProbabilityFamily
  baseLongSemigroup_eq :
    baseAssembly.spectralBoundary.longTime.semigroup =
      baseSliceAverage.toSemigroupProbabilityFamily
  localReferenceFamily : Index → RelativeHeatMellinZetaFamilyData
  localDifference : ∀ index,
    RelativeHeatMellinAnalyticDifferenceFamilyData
      ((OldAtlas period hPeriod input).localFamily index)
      actual.family (localReferenceFamily index)
  localShortTimeRegion : Index → Set Real
  localLongTimeRegion : Index → Set Real
  localAssembly : ∀ index,
    ReferenceNuclearHeatFinitePartGeneratedSchwarzAssemblyData
      (E := BaseReduced period hPeriod input) sliceMeasure shortCutoffFilter
        longCutoffFilter (localReferenceFamily index)
          (localShortTimeRegion index) (localLongTimeRegion index)
  localTrace_eq : ∀ index,
    (localAssembly index).spectralBoundary.toCollapsedBoundaryLimits.
        toCollapsedBoundary.toBoundaryMatching.toOperatorIdentity.
          logarithmicTrace =
      ((OldAtlas period hPeriod input).referenceTrace index).trace
  localSliceAverage : ∀ index,
    NuclearDuhamelSemigroupRankOneAverageData sliceMeasure
      (localAssembly index).nuclear
  localShortSemigroup_eq : ∀ index,
    (localAssembly index).spectralBoundary.shortTime.semigroup =
      (localSliceAverage index).toSemigroupProbabilityFamily
  localLongSemigroup_eq : ∀ index,
    (localAssembly index).spectralBoundary.longTime.semigroup =
      (localSliceAverage index).toSemigroupProbabilityFamily

namespace GlobalHessianPreferredFiveSectorH14D11GeneratedSchwarzSpectralReferenceData

/-- Convert primitive Mellin symmetry to the normalized Schwarz Candidate-A
packet. -/
def toSchwarzSpectralReferenceData
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {shortCutoffFilter : Filter ShortCutoff} [NeBot shortCutoffFilter]
    {longCutoffFilter : Filter LongCutoff} [NeBot longCutoffFilter]
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (spectral :
      GlobalHessianPreferredFiveSectorH14D11GeneratedSchwarzSpectralReferenceData
        period hPeriod sliceMeasure shortCutoffFilter longCutoffFilter input) :
    GlobalHessianPreferredFiveSectorH14D11SchwarzSpectralReferenceData
      period hPeriod sliceMeasure shortCutoffFilter longCutoffFilter input where
  actual := spectral.actual
  baseReferenceFamily := spectral.baseReferenceFamily
  baseDifference := spectral.baseDifference
  baseShortTimeRegion := spectral.baseShortTimeRegion
  baseLongTimeRegion := spectral.baseLongTimeRegion
  baseAssembly := spectral.baseAssembly.toSchwarzSpectralAssembly
  baseTrace_eq := spectral.baseTrace_eq
  baseSliceAverage := spectral.baseSliceAverage
  baseShortSemigroup_eq := spectral.baseShortSemigroup_eq
  baseLongSemigroup_eq := spectral.baseLongSemigroup_eq
  localReferenceFamily := spectral.localReferenceFamily
  localDifference := spectral.localDifference
  localShortTimeRegion := spectral.localShortTimeRegion
  localLongTimeRegion := spectral.localLongTimeRegion
  localAssembly := fun index =>
    (spectral.localAssembly index).toSchwarzSpectralAssembly
  localTrace_eq := spectral.localTrace_eq
  localSliceAverage := spectral.localSliceAverage
  localShortSemigroup_eq := spectral.localShortSemigroup_eq
  localLongSemigroup_eq := spectral.localLongSemigroup_eq

/-- Physical D11 kernel/reference closure generated from primitive Mellin
conjugation. -/
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
      GlobalHessianPreferredFiveSectorH14D11GeneratedSchwarzSpectralReferenceData
        period hPeriod sliceMeasure shortCutoffFilter longCutoffFilter input)
    (zeroTrace : IntrinsicNuclearTraceData
      (0 : BaseReduced period hPeriod input →L[Real]
        BaseReduced period hPeriod input)) :
    GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D period hPeriod
      configuration data analysis einsteinScale hTransverse family chartBound
        Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index :=
  (spectral.toSchwarzSpectralReferenceData period hPeriod input).
    toPhysicalReferenceClosure period hPeriod input natural frame zeroTrace

/-- Public primitive-Mellin Candidate-A checkpoint. -/
theorem global_hessian_preferred_five_sector_H14_D11_generated_schwarz_spectral_reference_atlas_gate
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
      GlobalHessianPreferredFiveSectorH14D11GeneratedSchwarzSpectralReferenceData
        period hPeriod sliceMeasure shortCutoffFilter longCutoffFilter input)
    (zeroTrace : IntrinsicNuclearTraceData
      (0 : BaseReduced period hPeriod input →L[Real]
        BaseReduced period hPeriod input)) :
    let closure := spectral.toPhysicalReferenceClosure period hPeriod input
      natural frame zeroTrace
    (∀ parameter spectralParameter,
      P0EFTJanusProgramPRelativeHeatMellinZetaContinuation4D.
          relativeHeatMellinZetaCandidate
            (spectral.baseReferenceFamily.finitePartFamily.heatTrace parameter)
            spectralParameter =
        Complex.conj
          (P0EFTJanusProgramPRelativeHeatMellinZetaContinuation4D.
            relativeHeatMellinZetaCandidate
              (spectral.baseReferenceFamily.finitePartFamily.heatTrace parameter)
              (Complex.conj spectralParameter))) ∧
    (∀ index parameter spectralParameter,
      P0EFTJanusProgramPRelativeHeatMellinZetaContinuation4D.
          relativeHeatMellinZetaCandidate
            ((spectral.localReferenceFamily index).finitePartFamily.heatTrace
              parameter) spectralParameter =
        Complex.conj
          (P0EFTJanusProgramPRelativeHeatMellinZetaContinuation4D.
            relativeHeatMellinZetaCandidate
              ((spectral.localReferenceFamily index).finitePartFamily.heatTrace
                parameter) (Complex.conj spectralParameter))) ∧
    GlobalHessianPreferredFiveSectorResolvedKernelFamily4D period hPeriod closure ∧
    GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D period
      hPeriod closure := by
  dsimp only
  let schwarz := spectral.toSchwarzSpectralReferenceData period hPeriod input
  let closure := spectral.toPhysicalReferenceClosure period hPeriod input natural
    frame zeroTrace
  have hSchwarz :=
    GlobalHessianPreferredFiveSectorH14D11SchwarzSpectralReferenceData.
      global_hessian_preferred_five_sector_H14_D11_schwarz_spectral_reference_atlas_gate
        period hPeriod sliceMeasure shortCutoffFilter longCutoffFilter input
          natural frame schwarz zeroTrace
  exact
    ⟨fun parameter =>
        (spectral.baseAssembly.zetaGeneratedSchwarz parameter).mellinSchwarz.
          candidate_schwarz,
      fun index parameter =>
        ((spectral.localAssembly index).zetaGeneratedSchwarz parameter).
          mellinSchwarz.candidate_schwarz,
      hSchwarz.2.2.1,
      hSchwarz.2.2.2⟩

end GlobalHessianPreferredFiveSectorH14D11GeneratedSchwarzSpectralReferenceData

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11GeneratedSchwarzSpectralReferenceAtlas4D
end JanusFormal
