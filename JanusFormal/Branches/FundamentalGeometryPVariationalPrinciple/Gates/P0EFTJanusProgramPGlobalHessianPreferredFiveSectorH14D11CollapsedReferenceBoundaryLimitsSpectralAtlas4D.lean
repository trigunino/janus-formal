import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPReferenceNuclearHeatFinitePartCollapsedBoundaryLimitsAssembly4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11CollapsedReferenceSpectralAtlas4D

/-!
# Candidate-A atlas from collapsed reference endpoint limits

This frontend carries the strongest generic standalone-reference packet into
the preferred Candidate-A spectral atlas.  For the base reference and every
local spectral-cut reference, it receives

* the probability-averaged Duhamel slice family;
* semigroup-collapsed rank-one expansions of `H'_a K_a(t)`;
* coefficient integration on the short- and long-time regions;
* convergence of the short-time cutoff counterterm and cutoff integral;
* convergence of their renormalized remainder to the logarithmic derivative;
* a finite long-time primitive identity and decay of its terminal value.

The short/long boundary equalities and every downstream zeta coefficient are
outputs.  The resulting closure keeps the original Candidate-A operator,
reference atlas, family-index payload and D11-transported physical kernel.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11CollapsedReferenceBoundaryLimitsSpectralAtlas4D

set_option autoImplicit false
set_option maxHeartbeats 282000000
set_option synthInstance.maxHeartbeats 141000000
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
open P0EFTJanusProgramPIntrinsicNuclearTrace4D
open P0EFTJanusProgramPReferenceNuclearHeatFinitePartCollapsedBoundaryLimitsAssembly4D
open P0EFTJanusProgramPRelativeHeatMellinAnalyticDifferenceFamily4D
open P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D
open P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D
open P0EFTJanusProgramPUnitaryActualZetaFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorResolvedKernelFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11OperatorNormUnitaryFrame4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11PhysicalReferenceClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11CollapsedReferenceSpectralAtlas4D
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

universe v w x y z

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

/-- Candidate-A spectral data generated from short/long endpoint limits. -/
structure GlobalHessianPreferredFiveSectorH14D11CollapsedReferenceBoundaryLimitsSpectralData
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
  baseLimitAssembly :
    ReferenceNuclearHeatFinitePartCollapsedBoundaryLimitsAssemblyData.{0, w, x, y, z}
      (E := BaseReduced period hPeriod input) sliceMeasure shortCutoffFilter
        longCutoffFilter baseReferenceFamily baseShortTimeRegion baseLongTimeRegion
  baseTrace_eq :
    baseLimitAssembly.boundaryLimits.toCollapsedBoundary.toBoundaryMatching.toOperatorIdentity.logarithmicTrace =
      (OldAtlas period hPeriod input).baseFamily.familyIndex.referenceTrace.trace
  localReferenceFamily : Index → RelativeHeatMellinZetaFamilyData
  localDifference : ∀ index,
    RelativeHeatMellinAnalyticDifferenceFamilyData
      ((OldAtlas period hPeriod input).localFamily index)
      actual.family (localReferenceFamily index)
  localShortTimeRegion : Index → Set Real
  localLongTimeRegion : Index → Set Real
  localLimitAssembly : ∀ index,
    ReferenceNuclearHeatFinitePartCollapsedBoundaryLimitsAssemblyData.{0, w, x, y, z}
      (E := BaseReduced period hPeriod input) sliceMeasure shortCutoffFilter
        longCutoffFilter (localReferenceFamily index)
          (localShortTimeRegion index) (localLongTimeRegion index)
  localTrace_eq : ∀ index,
    (localLimitAssembly index).boundaryLimits.toCollapsedBoundary.toBoundaryMatching.toOperatorIdentity.logarithmicTrace =
      ((OldAtlas period hPeriod input).referenceTrace index).trace

namespace GlobalHessianPreferredFiveSectorH14D11CollapsedReferenceBoundaryLimitsSpectralData

/-- Convert endpoint-limit data to the collapsed Candidate-A reference atlas. -/
def toCollapsedReferenceSpectralData
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {shortCutoffFilter : Filter ShortCutoff} [NeBot shortCutoffFilter]
    {longCutoffFilter : Filter LongCutoff} [NeBot longCutoffFilter]
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (spectral :
      GlobalHessianPreferredFiveSectorH14D11CollapsedReferenceBoundaryLimitsSpectralData
        period hPeriod sliceMeasure shortCutoffFilter longCutoffFilter input) :
    GlobalHessianPreferredFiveSectorH14D11CollapsedReferenceSpectralData
      period hPeriod sliceMeasure input where
  actual := spectral.actual
  baseReferenceFamily := spectral.baseReferenceFamily
  baseDifference := spectral.baseDifference
  baseShortTimeRegion := spectral.baseShortTimeRegion
  baseLongTimeRegion := spectral.baseLongTimeRegion
  baseCollapsedAssembly := spectral.baseLimitAssembly.toCollapsedBoundaryAssembly
  baseTrace_eq := spectral.baseTrace_eq
  localReferenceFamily := spectral.localReferenceFamily
  localDifference := spectral.localDifference
  localShortTimeRegion := spectral.localShortTimeRegion
  localLongTimeRegion := spectral.localLongTimeRegion
  localCollapsedAssembly := fun index =>
    (spectral.localLimitAssembly index).toCollapsedBoundaryAssembly
  localTrace_eq := spectral.localTrace_eq

/-- Physical D11 kernel/reference closure generated from endpoint limits. -/
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
      GlobalHessianPreferredFiveSectorH14D11CollapsedReferenceBoundaryLimitsSpectralData
        period hPeriod sliceMeasure shortCutoffFilter longCutoffFilter input)
    (zeroTrace : IntrinsicNuclearTraceData
      (0 : BaseReduced period hPeriod input →L[Real]
        BaseReduced period hPeriod input)) :
    GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D period hPeriod
      configuration data analysis einsteinScale hTransverse family chartBound
        Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index :=
  (spectral.toCollapsedReferenceSpectralData period hPeriod input)
    |>.toPhysicalReferenceClosure period hPeriod input natural frame zeroTrace

/-- Public Candidate-A endpoint-limit spectral checkpoint. -/
theorem global_hessian_preferred_five_sector_H14_D11_collapsed_reference_boundary_limits_spectral_atlas_gate
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
      GlobalHessianPreferredFiveSectorH14D11CollapsedReferenceBoundaryLimitsSpectralData
        period hPeriod sliceMeasure shortCutoffFilter longCutoffFilter input)
    (zeroTrace : IntrinsicNuclearTraceData
      (0 : BaseReduced period hPeriod input →L[Real]
        BaseReduced period hPeriod input)) :
    let collapsed := spectral.toCollapsedReferenceSpectralData period hPeriod input
    let closure := spectral.toPhysicalReferenceClosure period hPeriod input
      natural frame zeroTrace
    (∀ parameter,
      spectral.baseLimitAssembly.boundaryLimits.countertermOperator parameter -
          spectral.baseLimitAssembly.boundaryLimits.shortTime.integratedOperator
            parameter =
        spectral.baseLimitAssembly.boundaryLimits.logarithmicDerivativeOperator
            parameter +
          spectral.baseLimitAssembly.boundaryLimits.matchingOperator parameter) ∧
    (∀ parameter,
      spectral.baseLimitAssembly.boundaryLimits.longTime.integratedOperator
          parameter =
        spectral.baseLimitAssembly.boundaryLimits.matchingOperator parameter) ∧
    (∀ index parameter,
      (spectral.localLimitAssembly index).boundaryLimits.countertermOperator
          parameter -
          (spectral.localLimitAssembly index).boundaryLimits.shortTime.integratedOperator
            parameter =
        (spectral.localLimitAssembly index).boundaryLimits.logarithmicDerivativeOperator
            parameter +
          (spectral.localLimitAssembly index).boundaryLimits.matchingOperator
            parameter) ∧
    (∀ index parameter,
      (spectral.localLimitAssembly index).boundaryLimits.longTime.integratedOperator
          parameter =
        (spectral.localLimitAssembly index).boundaryLimits.matchingOperator
          parameter) ∧
    GlobalHessianPreferredFiveSectorResolvedKernelFamily4D period hPeriod closure ∧
    GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D period
      hPeriod closure := by
  dsimp only
  let collapsed := spectral.toCollapsedReferenceSpectralData period hPeriod input
  let closure := spectral.toPhysicalReferenceClosure period hPeriod input natural
    frame zeroTrace
  have hCollapsed :=
    GlobalHessianPreferredFiveSectorH14D11CollapsedReferenceSpectralData.global_hessian_preferred_five_sector_H14_D11_collapsed_reference_spectral_atlas_gate
        period hPeriod sliceMeasure input natural frame collapsed zeroTrace
  exact
    ⟨spectral.baseLimitAssembly.boundaryLimits.shortBoundaryIdentity,
      spectral.baseLimitAssembly.boundaryLimits.longBoundaryIdentity,
      fun index =>
        (spectral.localLimitAssembly index).boundaryLimits.shortBoundaryIdentity,
      fun index =>
        (spectral.localLimitAssembly index).boundaryLimits.longBoundaryIdentity,
      hCollapsed.2.2.2.2.1,
      hCollapsed.2.2.2.2.2⟩

end GlobalHessianPreferredFiveSectorH14D11CollapsedReferenceBoundaryLimitsSpectralData

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11CollapsedReferenceBoundaryLimitsSpectralAtlas4D
end JanusFormal
