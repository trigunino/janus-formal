import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPReferenceNuclearHeatFinitePartCollapsedBoundaryAssembly4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11BoundaryMatchedReferenceSpectralAtlas4D

/-!
# Candidate-A atlas from semigroup-collapsed reference Duhamel spectra

This is the strongest current Candidate-A reference frontend.  For the base
reference and every local spectral-cut reference, the auxiliary Duhamel
simplex is integrated against one probability measure.  Nuclear cyclicity and
the heat semigroup law prove that every slice has the trace of `H'_a K_a(t)`.
Only this collapsed operator is expanded spectrally.

The short- and long-time coefficient integrals produce nuclear regional
operators, which meet through the common temporal boundary term.  The complete
physical D11 kernel/reference atlas is then reconstructed without requiring

* an expansion of the averaged Duhamel operator;
* scalar identities `integral Tr = Tr integral`;
* a global scalar Duhamel--Green identity;
* standalone or relative zeta coefficient equalities.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11CollapsedReferenceSpectralAtlas4D

set_option autoImplicit false
set_option maxHeartbeats 272000000
set_option synthInstance.maxHeartbeats 136000000
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
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyH10Reduction4D
open P0EFTJanusProgramPGlobalCandidateACanonicalSixDenseCore4D
open P0EFTJanusProgramPIntrinsicNuclearTrace4D
open P0EFTJanusProgramPReferenceNuclearHeatFinitePartCollapsedBoundaryAssembly4D
open P0EFTJanusProgramPRelativeHeatMellinAnalyticDifferenceFamily4D
open P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D
open P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D
open P0EFTJanusProgramPUnitaryActualZetaFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorResolvedKernelFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11OperatorNormUnitaryFrame4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11BoundaryMatchedReferenceSpectralAtlas4D
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
    {Slice : Type*} [MeasurableSpace Slice]
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

/-- Candidate-A spectral data whose reference coefficients are generated from
semigroup-collapsed Duhamel spectra. -/
structure GlobalHessianPreferredFiveSectorH14D11CollapsedReferenceSpectralData
    (sliceMeasure : Measure Slice) [IsProbabilityMeasure sliceMeasure]
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
  baseCollapsedAssembly :
    ReferenceNuclearHeatFinitePartCollapsedBoundaryAssemblyData
      (E := BaseReduced period hPeriod input) sliceMeasure baseReferenceFamily
        baseShortTimeRegion baseLongTimeRegion
  baseTrace_eq :
    baseCollapsedAssembly.collapsedBoundary.toBoundaryMatching.toOperatorIdentity.
        logarithmicTrace =
      (OldAtlas period hPeriod input).baseFamily.familyIndex.referenceTrace.trace
  localReferenceFamily : Index → RelativeHeatMellinZetaFamilyData
  localDifference : ∀ index,
    RelativeHeatMellinAnalyticDifferenceFamilyData
      ((OldAtlas period hPeriod input).localFamily index)
      actual.family (localReferenceFamily index)
  localShortTimeRegion : Index → Set Real
  localLongTimeRegion : Index → Set Real
  localCollapsedAssembly : ∀ index,
    ReferenceNuclearHeatFinitePartCollapsedBoundaryAssemblyData
      (E := BaseReduced period hPeriod input) sliceMeasure
        (localReferenceFamily index) (localShortTimeRegion index)
          (localLongTimeRegion index)
  localTrace_eq : ∀ index,
    (localCollapsedAssembly index).collapsedBoundary.toBoundaryMatching.
        toOperatorIdentity.logarithmicTrace =
      ((OldAtlas period hPeriod input).referenceTrace index).trace

namespace GlobalHessianPreferredFiveSectorH14D11CollapsedReferenceSpectralData

/-- Convert semigroup-collapsed spectral inputs to the boundary-matched
Candidate-A atlas. -/
def toBoundaryMatchedReferenceSpectralData
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (spectral :
      GlobalHessianPreferredFiveSectorH14D11CollapsedReferenceSpectralData
        period hPeriod sliceMeasure input) :
    GlobalHessianPreferredFiveSectorH14D11BoundaryMatchedReferenceSpectralData
      period hPeriod input where
  actual := spectral.actual
  baseReferenceFamily := spectral.baseReferenceFamily
  baseDifference := spectral.baseDifference
  baseShortTimeRegion := spectral.baseShortTimeRegion
  baseLongTimeRegion := spectral.baseLongTimeRegion
  baseBoundaryAssembly := spectral.baseCollapsedAssembly.toBoundaryAssembly
  baseTrace_eq := spectral.baseTrace_eq
  localReferenceFamily := spectral.localReferenceFamily
  localDifference := spectral.localDifference
  localShortTimeRegion := spectral.localShortTimeRegion
  localLongTimeRegion := spectral.localLongTimeRegion
  localBoundaryAssembly := fun index =>
    (spectral.localCollapsedAssembly index).toBoundaryAssembly
  localTrace_eq := spectral.localTrace_eq

/-- Physical D11 kernel/reference closure generated without expanding the
averaged Duhamel operator. -/
def toPhysicalReferenceClosure
    {sliceMeasure : Measure Slice} [IsProbabilityMeasure sliceMeasure]
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (frame : GlobalHessianPreferredFiveSectorD11OperatorNormUnitaryFrame4D
      period hPeriod input natural)
    (spectral :
      GlobalHessianPreferredFiveSectorH14D11CollapsedReferenceSpectralData
        period hPeriod sliceMeasure input)
    (zeroTrace : IntrinsicNuclearTraceData
      (0 : BaseReduced period hPeriod input →L[Real]
        BaseReduced period hPeriod input)) :
    GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D period hPeriod
      configuration data analysis einsteinScale hTransverse family chartBound
        Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index :=
  (spectral.toBoundaryMatchedReferenceSpectralData period hPeriod input).
    toPhysicalReferenceClosure period hPeriod input natural frame zeroTrace

/-- Public Candidate-A collapsed-reference spectral checkpoint. -/
theorem global_hessian_preferred_five_sector_H14_D11_collapsed_reference_spectral_atlas_gate
    (sliceMeasure : Measure Slice) [IsProbabilityMeasure sliceMeasure]
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (frame : GlobalHessianPreferredFiveSectorD11OperatorNormUnitaryFrame4D
      period hPeriod input natural)
    (spectral :
      GlobalHessianPreferredFiveSectorH14D11CollapsedReferenceSpectralData
        period hPeriod sliceMeasure input)
    (zeroTrace : IntrinsicNuclearTraceData
      (0 : BaseReduced period hPeriod input →L[Real]
        BaseReduced period hPeriod input)) :
    let boundarySpectral :=
      spectral.toBoundaryMatchedReferenceSpectralData period hPeriod input
    let closure := spectral.toPhysicalReferenceClosure period hPeriod input
      natural frame zeroTrace
    (∀ parameter time,
      spectral.baseCollapsedAssembly.nuclear.duhamelTrace parameter time =
        intrinsicNuclearTrace
          (spectral.baseCollapsedAssembly.collapsedBoundary.shortTime.semigroup.
            collapsedTraceClass parameter time)) ∧
    (∀ index parameter time,
      (spectral.localCollapsedAssembly index).nuclear.duhamelTrace parameter time =
        intrinsicNuclearTrace
          ((spectral.localCollapsedAssembly index).collapsedBoundary.shortTime.
            semigroup.collapsedTraceClass parameter time)) ∧
    (∀ parameter,
      (∫ time in spectral.baseShortTimeRegion,
        spectral.baseCollapsedAssembly.nuclear.extendedDuhamelTrace parameter
          time) =
        intrinsicNuclearTrace
          (spectral.baseCollapsedAssembly.collapsedBoundary.shortTime.
            integratedTraceClass parameter)) ∧
    (∀ parameter,
      (∫ time in spectral.baseLongTimeRegion,
        spectral.baseCollapsedAssembly.nuclear.extendedDuhamelTrace parameter
          time) =
        intrinsicNuclearTrace
          (spectral.baseCollapsedAssembly.collapsedBoundary.longTime.
            integratedTraceClass parameter)) ∧
    GlobalHessianPreferredFiveSectorResolvedKernelFamily4D period hPeriod closure ∧
    GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D period
      hPeriod closure := by
  dsimp only
  let boundarySpectral :=
    spectral.toBoundaryMatchedReferenceSpectralData period hPeriod input
  let closure := spectral.toPhysicalReferenceClosure period hPeriod input natural
    frame zeroTrace
  have hBoundary :=
    GlobalHessianPreferredFiveSectorH14D11BoundaryMatchedReferenceSpectralData.
      global_hessian_preferred_five_sector_H14_D11_boundary_matched_reference_spectral_atlas_gate
        period hPeriod input natural frame boundarySpectral zeroTrace
  exact
    ⟨spectral.baseCollapsedAssembly.collapsedBoundary.shortTime.semigroup.
        duhamelTrace_eq_insertionFullHeatTrace,
      fun index =>
        (spectral.localCollapsedAssembly index).collapsedBoundary.shortTime.
          semigroup.duhamelTrace_eq_insertionFullHeatTrace,
      spectral.baseCollapsedAssembly.collapsedBoundary.
        shortTimeIntegral_eq_trace,
      spectral.baseCollapsedAssembly.collapsedBoundary.
        longTimeIntegral_eq_trace,
      hBoundary.2.2.2.2.1,
      hBoundary.2.2.2.2.2⟩

end GlobalHessianPreferredFiveSectorH14D11CollapsedReferenceSpectralData

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11CollapsedReferenceSpectralAtlas4D
end JanusFormal
