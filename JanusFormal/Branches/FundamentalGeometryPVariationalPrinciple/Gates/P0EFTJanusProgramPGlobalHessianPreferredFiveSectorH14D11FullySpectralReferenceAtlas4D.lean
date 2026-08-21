import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPNuclearDuhamelSemigroupRankOneAverage4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11CollapsedReferenceBoundaryLimitsSpectralAtlas4D

/-!
# Fully spectral Candidate-A reference atlas

The endpoint-limit Candidate-A atlas still contained semigroup-probability
packets whose scalar slice-average equality could, in principle, be supplied
directly.  This file constrains every such packet to be the output of a common
rank-one slice-average construction.

For the base reference and every local reference, one fully spectral Duhamel
family is shared by the short- and long-time regions.  Its pointwise slice
expansions derive the genuine averaged Duhamel trace; cyclicity and the heat
semigroup law derive its collapse to `Tr(H' K_t)`.  Equality fields identify
both regional packets with that generated family.

The resulting Candidate-A closure therefore has no independently supplied
scalar simplex-average identity.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11FullySpectralReferenceAtlas4D

set_option autoImplicit false
set_option maxHeartbeats 292000000
set_option synthInstance.maxHeartbeats 146000000
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
open P0EFTJanusProgramPNuclearDuhamelSemigroupRankOneAverage4D
open P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorResolvedKernelFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11OperatorNormUnitaryFrame4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11PhysicalReferenceClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11CollapsedReferenceBoundaryLimitsSpectralAtlas4D
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

/-- Endpoint-limit Candidate-A data together with generated rank-one simplex
averages for the base and local reference families. -/
structure GlobalHessianPreferredFiveSectorH14D11FullySpectralReferenceData
    (sliceMeasure : Measure Slice) [IsProbabilityMeasure sliceMeasure]
    (shortCutoffFilter : Filter ShortCutoff) [NeBot shortCutoffFilter]
    (longCutoffFilter : Filter LongCutoff) [NeBot longCutoffFilter]
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index) where
  endpoint :
    GlobalHessianPreferredFiveSectorH14D11CollapsedReferenceBoundaryLimitsSpectralData.{v, w, x, y, z}
      period hPeriod sliceMeasure shortCutoffFilter longCutoffFilter input
  baseSliceAverage : NuclearDuhamelSemigroupRankOneAverageData.{x, 0, w} sliceMeasure
    endpoint.baseLimitAssembly.nuclear
  baseShortSemigroup_eq :
    endpoint.baseLimitAssembly.boundaryLimits.shortTime.semigroup =
      baseSliceAverage.toSemigroupProbabilityFamily
  baseLongSemigroup_eq :
    endpoint.baseLimitAssembly.boundaryLimits.longTime.semigroup =
      baseSliceAverage.toSemigroupProbabilityFamily
  localSliceAverage : ∀ index,
    NuclearDuhamelSemigroupRankOneAverageData.{x, 0, w} sliceMeasure
      (endpoint.localLimitAssembly index).nuclear
  localShortSemigroup_eq : ∀ index,
    (endpoint.localLimitAssembly index).boundaryLimits.shortTime.semigroup =
      (localSliceAverage index).toSemigroupProbabilityFamily
  localLongSemigroup_eq : ∀ index,
    (endpoint.localLimitAssembly index).boundaryLimits.longTime.semigroup =
      (localSliceAverage index).toSemigroupProbabilityFamily

namespace GlobalHessianPreferredFiveSectorH14D11FullySpectralReferenceData

/-- Physical closure inherited from the endpoint-limit atlas. -/
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
    (spectral : GlobalHessianPreferredFiveSectorH14D11FullySpectralReferenceData
      period hPeriod sliceMeasure shortCutoffFilter longCutoffFilter input)
    (zeroTrace : IntrinsicNuclearTraceData
      (0 : BaseReduced period hPeriod input →L[Real]
        BaseReduced period hPeriod input)) :
    GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D period hPeriod
      configuration data analysis einsteinScale hTransverse family chartBound
        Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index :=
  spectral.endpoint.toPhysicalReferenceClosure period hPeriod input natural frame
    zeroTrace

/-- The base Duhamel trace is generated by the rank-one simplex average. -/
theorem baseDuhamelTrace_eq_collapsedTrace
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {shortCutoffFilter : Filter ShortCutoff} [NeBot shortCutoffFilter]
    {longCutoffFilter : Filter LongCutoff} [NeBot longCutoffFilter]
    {input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index}
    (spectral : GlobalHessianPreferredFiveSectorH14D11FullySpectralReferenceData
      period hPeriod sliceMeasure shortCutoffFilter longCutoffFilter input)
    (parameter : Real) (time : P0EFTJanusCircleDiracHeatTraceCancellation.HeatTime) :
    spectral.endpoint.baseLimitAssembly.nuclear.duhamelTrace parameter time =
      intrinsicNuclearTrace
        (spectral.baseSliceAverage.collapsedTraceClass parameter time) :=
  spectral.baseSliceAverage.duhamelTrace_eq_insertionFullHeatTrace parameter time

/-- Every local reference Duhamel trace is generated in the same way. -/
theorem localDuhamelTrace_eq_collapsedTrace
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    {shortCutoffFilter : Filter ShortCutoff} [NeBot shortCutoffFilter]
    {longCutoffFilter : Filter LongCutoff} [NeBot longCutoffFilter]
    {input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index}
    (spectral : GlobalHessianPreferredFiveSectorH14D11FullySpectralReferenceData
      period hPeriod sliceMeasure shortCutoffFilter longCutoffFilter input)
    (index : Index) (parameter : Real)
    (time : P0EFTJanusCircleDiracHeatTraceCancellation.HeatTime) :
    (spectral.endpoint.localLimitAssembly index).nuclear.duhamelTrace parameter
        time =
      intrinsicNuclearTrace
        ((spectral.localSliceAverage index).collapsedTraceClass parameter time) :=
  (spectral.localSliceAverage index).duhamelTrace_eq_insertionFullHeatTrace
    parameter time

/-- Public fully spectral Candidate-A checkpoint. -/
theorem global_hessian_preferred_five_sector_H14_D11_fully_spectral_reference_atlas_gate
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
    (spectral : GlobalHessianPreferredFiveSectorH14D11FullySpectralReferenceData
      period hPeriod sliceMeasure shortCutoffFilter longCutoffFilter input)
    (zeroTrace : IntrinsicNuclearTraceData
      (0 : BaseReduced period hPeriod input →L[Real]
        BaseReduced period hPeriod input)) :
    let closure := spectral.toPhysicalReferenceClosure period hPeriod input
      natural frame zeroTrace
    (∀ parameter time,
      spectral.endpoint.baseLimitAssembly.nuclear.duhamelTrace parameter time =
        intrinsicNuclearTrace
          (spectral.baseSliceAverage.collapsedTraceClass parameter time)) ∧
    (∀ index parameter time,
      (spectral.endpoint.localLimitAssembly index).nuclear.duhamelTrace parameter
          time =
        intrinsicNuclearTrace
          ((spectral.localSliceAverage index).collapsedTraceClass parameter
            time)) ∧
    GlobalHessianPreferredFiveSectorResolvedKernelFamily4D period hPeriod closure ∧
    GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D period
      hPeriod closure := by
  dsimp only
  let closure := spectral.toPhysicalReferenceClosure period hPeriod input natural
    frame zeroTrace
  have hEndpoint :=
    GlobalHessianPreferredFiveSectorH14D11CollapsedReferenceBoundaryLimitsSpectralData.global_hessian_preferred_five_sector_H14_D11_collapsed_reference_boundary_limits_spectral_atlas_gate
        period hPeriod sliceMeasure shortCutoffFilter longCutoffFilter input
          natural frame spectral.endpoint zeroTrace
  exact
    ⟨spectral.baseDuhamelTrace_eq_collapsedTrace,
      spectral.localDuhamelTrace_eq_collapsedTrace,
      hEndpoint.2.2.2.2.1,
      hEndpoint.2.2.2.2.2⟩

end GlobalHessianPreferredFiveSectorH14D11FullySpectralReferenceData

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11FullySpectralReferenceAtlas4D
end JanusFormal
