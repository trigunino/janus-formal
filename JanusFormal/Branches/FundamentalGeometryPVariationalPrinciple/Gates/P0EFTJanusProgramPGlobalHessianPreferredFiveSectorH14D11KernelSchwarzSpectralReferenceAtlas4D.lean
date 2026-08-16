import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPReferenceNuclearHeatFinitePartKernelSchwarzAssembly4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11IntegralSchwarzSpectralReferenceAtlas4D

/-!
# Candidate-A atlas from pointwise Mellin-kernel Schwarz symmetry

This frontend lowers the final reference-dependent complex symmetry to the
Mellin kernel.  The pointwise kernel identity is universal for real heat traces;
per reference one retains only compatibility of complex conjugation with its
Bochner integral.  The unnormalized integral symmetry, Gamma-normalized
candidate symmetry, analytic Schwarz reflection, derivative reality and all
connection coefficients follow.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11KernelSchwarzSpectralReferenceAtlas4D

set_option autoImplicit false
set_option maxHeartbeats 352000000
set_option synthInstance.maxHeartbeats 176000000
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
open P0EFTJanusProgramPReferenceNuclearHeatFinitePartKernelSchwarzAssembly4D
open P0EFTJanusProgramPRelativeHeatMellinAnalyticDifferenceFamily4D
open P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D
open P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D
open P0EFTJanusProgramPUnitaryActualZetaFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorResolvedKernelFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11OperatorNormUnitaryFrame4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11IntegralSchwarzSpectralReferenceAtlas4D
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

/-- Candidate-A data whose per-reference complex input is only conjugation
compatibility of the Mellin-kernel Bochner integral. -/
structure GlobalHessianPreferredFiveSectorH14D11KernelSchwarzSpectralReferenceData
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
  baseAssembly : ReferenceNuclearHeatFinitePartKernelSchwarzAssemblyData
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
    ReferenceNuclearHeatFinitePartKernelSchwarzAssemblyData
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

namespace GlobalHessianPreferredFiveSectorH14D11KernelSchwarzSpectralReferenceData

/-- Convert kernel-level Schwarz data to the integral-level Candidate-A
packet. -/
def toIntegralSchwarzSpectralReferenceData
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {shortCutoffFilter : Filter ShortCutoff} [NeBot shortCutoffFilter]
    {longCutoffFilter : Filter LongCutoff} [NeBot longCutoffFilter]
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (spectral :
      GlobalHessianPreferredFiveSectorH14D11KernelSchwarzSpectralReferenceData
        period hPeriod sliceMeasure shortCutoffFilter longCutoffFilter input) :
    GlobalHessianPreferredFiveSectorH14D11IntegralSchwarzSpectralReferenceData
      period hPeriod sliceMeasure shortCutoffFilter longCutoffFilter input where
  actual := spectral.actual
  baseReferenceFamily := spectral.baseReferenceFamily
  baseDifference := spectral.baseDifference
  baseShortTimeRegion := spectral.baseShortTimeRegion
  baseLongTimeRegion := spectral.baseLongTimeRegion
  baseAssembly := spectral.baseAssembly.toIntegralSchwarzAssembly
  baseTrace_eq := spectral.baseTrace_eq
  baseSliceAverage := spectral.baseSliceAverage
  baseShortSemigroup_eq := spectral.baseShortSemigroup_eq
  baseLongSemigroup_eq := spectral.baseLongSemigroup_eq
  localReferenceFamily := spectral.localReferenceFamily
  localDifference := spectral.localDifference
  localShortTimeRegion := spectral.localShortTimeRegion
  localLongTimeRegion := spectral.localLongTimeRegion
  localAssembly := fun index =>
    (spectral.localAssembly index).toIntegralSchwarzAssembly
  localTrace_eq := spectral.localTrace_eq
  localSliceAverage := spectral.localSliceAverage
  localShortSemigroup_eq := spectral.localShortSemigroup_eq
  localLongSemigroup_eq := spectral.localLongSemigroup_eq

/-- Physical D11 closure from pointwise Mellin-kernel symmetry. -/
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
      GlobalHessianPreferredFiveSectorH14D11KernelSchwarzSpectralReferenceData
        period hPeriod sliceMeasure shortCutoffFilter longCutoffFilter input)
    (zeroTrace : IntrinsicNuclearTraceData
      (0 : BaseReduced period hPeriod input →L[Real]
        BaseReduced period hPeriod input)) :
    GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D period hPeriod
      configuration data analysis einsteinScale hTransverse family chartBound
        Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index :=
  (spectral.toIntegralSchwarzSpectralReferenceData period hPeriod input).
    toPhysicalReferenceClosure period hPeriod input natural frame zeroTrace

/-- Public kernel-Schwarz Candidate-A checkpoint. -/
theorem global_hessian_preferred_five_sector_H14_D11_kernel_schwarz_spectral_reference_atlas_gate
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
      GlobalHessianPreferredFiveSectorH14D11KernelSchwarzSpectralReferenceData
        period hPeriod sliceMeasure shortCutoffFilter longCutoffFilter input)
    (zeroTrace : IntrinsicNuclearTraceData
      (0 : BaseReduced period hPeriod input →L[Real]
        BaseReduced period hPeriod input)) :
    let closure := spectral.toPhysicalReferenceClosure period hPeriod input
      natural frame zeroTrace
    (∀ parameter spectralParameter time,
      P0EFTJanusProgramPRelativeHeatMellinZetaContinuation4D.
          relativeHeatMellinKernel
            (spectral.baseReferenceFamily.finitePartFamily.heatTrace parameter)
            spectralParameter time =
        Complex.conj
          (P0EFTJanusProgramPRelativeHeatMellinZetaContinuation4D.
            relativeHeatMellinKernel
              (spectral.baseReferenceFamily.finitePartFamily.heatTrace parameter)
              (Complex.conj spectralParameter) time)) ∧
    (∀ index parameter spectralParameter time,
      P0EFTJanusProgramPRelativeHeatMellinZetaContinuation4D.
          relativeHeatMellinKernel
            ((spectral.localReferenceFamily index).finitePartFamily.heatTrace
              parameter) spectralParameter time =
        Complex.conj
          (P0EFTJanusProgramPRelativeHeatMellinZetaContinuation4D.
            relativeHeatMellinKernel
              ((spectral.localReferenceFamily index).finitePartFamily.heatTrace
                parameter) (Complex.conj spectralParameter) time)) ∧
    GlobalHessianPreferredFiveSectorResolvedKernelFamily4D period hPeriod closure ∧
    GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D period
      hPeriod closure := by
  dsimp only
  let integral :=
    spectral.toIntegralSchwarzSpectralReferenceData period hPeriod input
  let closure := spectral.toPhysicalReferenceClosure period hPeriod input natural
    frame zeroTrace
  have hIntegral :=
    GlobalHessianPreferredFiveSectorH14D11IntegralSchwarzSpectralReferenceData.
      global_hessian_preferred_five_sector_H14_D11_integral_schwarz_spectral_reference_atlas_gate
        period hPeriod sliceMeasure shortCutoffFilter longCutoffFilter input
          natural frame integral zeroTrace
  exact
    ⟨fun parameter =>
        P0EFTJanusProgramPRelativeHeatMellinKernelSchwarz4D.
          relativeHeatMellinKernel_schwarz
            (spectral.baseReferenceFamily.finitePartFamily.heatTrace parameter),
      fun index parameter =>
        P0EFTJanusProgramPRelativeHeatMellinKernelSchwarz4D.
          relativeHeatMellinKernel_schwarz
            ((spectral.localReferenceFamily index).finitePartFamily.heatTrace
              parameter),
      hIntegral.2.2.1,
      hIntegral.2.2.2⟩

end GlobalHessianPreferredFiveSectorH14D11KernelSchwarzSpectralReferenceData

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11KernelSchwarzSpectralReferenceAtlas4D
end JanusFormal
