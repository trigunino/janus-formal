import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11CanonicalSchwarzSpectralReferenceAtlas4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPReferenceNuclearHeatFinitePartSelectedTraceCanonicalSchwarzAssembly4D

/-!
# Candidate-A Schwarz atlas from the already selected reference traces

The canonical-Schwarz Candidate-A frontend still required two comparison
fields:

```text
generated base logarithmic trace = selected base trace,
generated local logarithmic trace = selected local trace.
```

Those comparisons are unnecessary.  The operator-generated spectral atlas
already contains one `IntrinsicLogarithmicDerivativeTraceData` for its base
reference and for every local reference.  This file feeds those packets
directly into the Duhamel endpoint construction.

The short-time remainder is therefore targeted at the selected
`G_ref H'_ref` operator and the terminal nuclear certificate is the selected
one.  Both comparison fields become definitional reductions in the adapter to
the preceding canonical-Schwarz frontend.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11SelectedTraceInvariantDomainSchwarzSpectralReferenceAtlas4D

set_option autoImplicit false
set_option maxHeartbeats 392000000
set_option synthInstance.maxHeartbeats 196000000
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
open P0EFTJanusProgramPIntrinsicLogarithmicDerivativeTrace4D
open P0EFTJanusProgramPIntrinsicNuclearTrace4D
open P0EFTJanusProgramPNuclearDuhamelSemigroupRankOneAverage4D
open P0EFTJanusProgramPReferenceNuclearHeatFinitePartSelectedTraceCanonicalSchwarzAssembly4D
open P0EFTJanusProgramPRelativeHeatMellinAnalyticDifferenceFamily4D
open P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D
open P0EFTJanusProgramPRelativeHeatMellinZetaSchwarzReflection4D
open P0EFTJanusProgramPRelativeZetaDeterminantConnection4D
open P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D
open P0EFTJanusProgramPUnitaryActualZetaFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorResolvedKernelFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11OperatorNormUnitaryFrame4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11PhysicalReferenceClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11CanonicalSchwarzSpectralReferenceAtlas4D
open P0EFTJanusProgramPDenseCoreChartBilinearBound4D
open P0EFTJanusCircleDiracHeatTraceCancellation

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

/-- Candidate-A data whose base and local Duhamel endpoints use exactly the
reference traces already selected by the existing spectral atlas. -/
structure GlobalHessianPreferredFiveSectorH14D11SelectedTraceInvariantDomainSchwarzSpectralReferenceData
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
  baseShortTimeRegion : Set Real
  baseLongTimeRegion : Set Real
  baseAssembly :
    ReferenceNuclearHeatFinitePartSelectedTraceCanonicalSchwarzAssemblyData.{0, 0, x, y, z}
      (E := BaseReduced period hPeriod input) sliceMeasure shortCutoffFilter
        longCutoffFilter (OldAtlas period hPeriod input).baseFamily.referenceOperator
          (OldAtlas period hPeriod input).baseFamily.familyIndex.referenceTrace
            baseReferenceFamily baseShortTimeRegion baseLongTimeRegion
  baseSliceAverage : NuclearDuhamelSemigroupRankOneAverageData.{x, 0, 0} sliceMeasure
    baseAssembly.nuclear
  baseShortSemigroup_eq :
    baseAssembly.spectralBoundary.toFullySpectralBoundaryLimits.shortTime.semigroup =
      baseSliceAverage.toSemigroupProbabilityFamily
  baseLongSemigroup_eq :
    baseAssembly.spectralBoundary.toFullySpectralBoundaryLimits.longTime.semigroup =
      baseSliceAverage.toSemigroupProbabilityFamily
  localReferenceFamily : Index → RelativeHeatMellinZetaFamilyData
  localDifference : ∀ index,
    RelativeHeatMellinAnalyticDifferenceFamilyData
      ((OldAtlas period hPeriod input).localFamily index)
      actual.family (localReferenceFamily index)
  localShortTimeRegion : Index → Set Real
  localLongTimeRegion : Index → Set Real
  localAssembly : ∀ index,
    ReferenceNuclearHeatFinitePartSelectedTraceCanonicalSchwarzAssemblyData.{0, 0, x, y, z}
      (E := BaseReduced period hPeriod input) sliceMeasure shortCutoffFilter
        longCutoffFilter ((OldAtlas period hPeriod input).referenceOperator index)
          ((OldAtlas period hPeriod input).referenceTrace index)
            (localReferenceFamily index) (localShortTimeRegion index)
              (localLongTimeRegion index)
  localSliceAverage : ∀ index,
    NuclearDuhamelSemigroupRankOneAverageData.{x, 0, 0} sliceMeasure
      (localAssembly index).nuclear
  localShortSemigroup_eq : ∀ index,
    (localAssembly index).spectralBoundary.toFullySpectralBoundaryLimits.shortTime.semigroup =
      (localSliceAverage index).toSemigroupProbabilityFamily
  localLongSemigroup_eq : ∀ index,
    (localAssembly index).spectralBoundary.toFullySpectralBoundaryLimits.longTime.semigroup =
      (localSliceAverage index).toSemigroupProbabilityFamily

namespace GlobalHessianPreferredFiveSectorH14D11SelectedTraceInvariantDomainSchwarzSpectralReferenceData

/-- Convert to the former canonical-Schwarz frontend.  Its two trace-comparison
fields are generated from the selected-reference reductions and are not inputs
of the present structure. -/
def toCanonicalSchwarzSpectralReferenceData
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {shortCutoffFilter : Filter ShortCutoff} [NeBot shortCutoffFilter]
    {longCutoffFilter : Filter LongCutoff} [NeBot longCutoffFilter]
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (spectral :
      GlobalHessianPreferredFiveSectorH14D11SelectedTraceInvariantDomainSchwarzSpectralReferenceData
        period hPeriod sliceMeasure shortCutoffFilter longCutoffFilter input) :
    GlobalHessianPreferredFiveSectorH14D11CanonicalSchwarzSpectralReferenceData
      period hPeriod sliceMeasure shortCutoffFilter longCutoffFilter input where
  actual := spectral.actual
  baseReferenceFamily := spectral.baseReferenceFamily
  baseDifference := spectral.baseDifference
  baseShortTimeRegion := spectral.baseShortTimeRegion
  baseLongTimeRegion := spectral.baseLongTimeRegion
  baseAssembly := spectral.baseAssembly.toCanonicalSchwarzAssembly
  baseTrace_eq := by
    funext parameter
    exact spectral.baseAssembly.generatedLogarithmicTrace_eq_selectedTrace parameter
  baseSliceAverage := spectral.baseSliceAverage
  baseShortSemigroup_eq := spectral.baseShortSemigroup_eq
  baseLongSemigroup_eq := spectral.baseLongSemigroup_eq
  localReferenceFamily := spectral.localReferenceFamily
  localDifference := spectral.localDifference
  localShortTimeRegion := spectral.localShortTimeRegion
  localLongTimeRegion := spectral.localLongTimeRegion
  localAssembly := fun index =>
    (spectral.localAssembly index).toCanonicalSchwarzAssembly
  localTrace_eq := by
    intro index
    funext parameter
    exact (spectral.localAssembly index).generatedLogarithmicTrace_eq_selectedTrace
      parameter
  localSliceAverage := spectral.localSliceAverage
  localShortSemigroup_eq := spectral.localShortSemigroup_eq
  localLongSemigroup_eq := spectral.localLongSemigroup_eq

/-- Physical D11 closure built without any generated-to-selected trace
comparison. -/
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
      GlobalHessianPreferredFiveSectorH14D11SelectedTraceInvariantDomainSchwarzSpectralReferenceData
        period hPeriod sliceMeasure shortCutoffFilter longCutoffFilter input)
    (zeroTrace : IntrinsicNuclearTraceData
      (0 : BaseReduced period hPeriod input →L[Real]
        BaseReduced period hPeriod input)) :
    GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D period hPeriod
      configuration data analysis einsteinScale hTransverse family chartBound
        Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index :=
  (spectral.toCanonicalSchwarzSpectralReferenceData period hPeriod input)
    |>.toPhysicalReferenceClosure period hPeriod input natural frame zeroTrace

/-- Public selected-trace invariant-domain Candidate-A checkpoint. -/
theorem global_hessian_preferred_five_sector_H14_D11_selected_trace_invariant_domain_schwarz_spectral_reference_atlas_gate
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
      GlobalHessianPreferredFiveSectorH14D11SelectedTraceInvariantDomainSchwarzSpectralReferenceData
        period hPeriod sliceMeasure shortCutoffFilter longCutoffFilter input)
    (zeroTrace : IntrinsicNuclearTraceData
      (0 : BaseReduced period hPeriod input →L[Real]
        BaseReduced period hPeriod input)) :
    let closure := spectral.toPhysicalReferenceClosure period hPeriod input
      natural frame zeroTrace
    (∀ parameter,
      relativeZetaConnectionCoefficient
          spectral.baseReferenceFamily.toZetaFamily parameter =
        -((OldAtlas period hPeriod input).baseFamily.familyIndex.referenceTrace.trace
          parameter : Complex)) ∧
    (∀ index parameter,
      relativeZetaConnectionCoefficient
          (spectral.localReferenceFamily index).toZetaFamily parameter =
        -((OldAtlas period hPeriod input).referenceTrace index |>.trace parameter :
          Complex)) ∧
    (∀ parameter,
      Set.EqOn (spectral.baseReferenceFamily.continuation parameter).zeta
        (schwarzReflect
            (spectral.baseReferenceFamily.continuation parameter).zeta)
        (spectral.baseAssembly.zetaCanonicalSchwarz parameter).domain) ∧
    (∀ index parameter,
      Set.EqOn ((spectral.localReferenceFamily index).continuation parameter).zeta
        (schwarzReflect
            ((spectral.localReferenceFamily index).continuation parameter).zeta)
        ((spectral.localAssembly index).zetaCanonicalSchwarz parameter).domain) ∧
    GlobalHessianPreferredFiveSectorResolvedKernelFamily4D period hPeriod closure ∧
    GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D period
      hPeriod closure := by
  dsimp only
  let canonical :=
    spectral.toCanonicalSchwarzSpectralReferenceData period hPeriod input
  let closure := spectral.toPhysicalReferenceClosure period hPeriod input natural
    frame zeroTrace
  have hCanonical :=
    GlobalHessianPreferredFiveSectorH14D11CanonicalSchwarzSpectralReferenceData.global_hessian_preferred_five_sector_H14_D11_canonical_schwarz_spectral_reference_atlas_gate
        period hPeriod sliceMeasure shortCutoffFilter longCutoffFilter input
          natural frame canonical zeroTrace
  exact
    ⟨spectral.baseAssembly.connectionCoefficient_eq_neg_selectedTrace,
      fun index =>
        (spectral.localAssembly index).connectionCoefficient_eq_neg_selectedTrace,
      hCanonical.1,
      hCanonical.2.1,
      hCanonical.2.2.1,
      hCanonical.2.2.2⟩

end GlobalHessianPreferredFiveSectorH14D11SelectedTraceInvariantDomainSchwarzSpectralReferenceData

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11SelectedTraceInvariantDomainSchwarzSpectralReferenceAtlas4D
end JanusFormal
