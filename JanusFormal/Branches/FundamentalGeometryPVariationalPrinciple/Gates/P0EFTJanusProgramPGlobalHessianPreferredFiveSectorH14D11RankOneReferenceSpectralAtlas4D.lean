import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPReferenceNuclearHeatFinitePartRankOneBoundaryAssembly4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11BoundaryMatchedReferenceSpectralAtlas4D

/-!
# Candidate-A spectral atlas from rank-one reference Duhamel expansions

This is the strongest current reference frontend.  For the base reference and
every local spectral-cut reference it receives common rank-one expansions of
the Duhamel operator on the short- and long-time regions.  Integrated
coefficients and one certified exchange of sum and time integral construct the
operator-valued regional integrals and prove their scalar trace formulas.

The two integrated operators then satisfy the local boundary matching laws

```text
C - D_short = G H' + B,
D_long       = B.
```

All later identities -- the global operator equality, intrinsic trace formula,
finite-part derivative, standalone reference coefficient, relative coefficient,
physical D11 kernel transport and spectral-cut atlas -- are outputs.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11RankOneReferenceSpectralAtlas4D

set_option autoImplicit false
set_option maxHeartbeats 262000000
set_option synthInstance.maxHeartbeats 131000000
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
open P0EFTJanusProgramPReferenceNuclearHeatFinitePartRankOneBoundaryAssembly4D
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

/-- Candidate-A reference spectral data from rank-one Duhamel expansions. -/
structure GlobalHessianPreferredFiveSectorH14D11RankOneReferenceSpectralData
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
  baseRankOneAssembly :
    ReferenceNuclearHeatFinitePartRankOneBoundaryAssemblyData
      (E := BaseReduced period hPeriod input) baseReferenceFamily
        baseShortTimeRegion baseLongTimeRegion
  baseTrace_eq :
    baseRankOneAssembly.rankOneBoundary.toBoundaryMatching.toOperatorIdentity.
        logarithmicTrace =
      (OldAtlas period hPeriod input).baseFamily.familyIndex.referenceTrace.trace
  localReferenceFamily : Index → RelativeHeatMellinZetaFamilyData
  localDifference : ∀ index,
    RelativeHeatMellinAnalyticDifferenceFamilyData
      ((OldAtlas period hPeriod input).localFamily index)
      actual.family (localReferenceFamily index)
  localShortTimeRegion : Index → Set Real
  localLongTimeRegion : Index → Set Real
  localRankOneAssembly : ∀ index,
    ReferenceNuclearHeatFinitePartRankOneBoundaryAssemblyData
      (E := BaseReduced period hPeriod input) (localReferenceFamily index)
        (localShortTimeRegion index) (localLongTimeRegion index)
  localTrace_eq : ∀ index,
    (localRankOneAssembly index).rankOneBoundary.toBoundaryMatching.
        toOperatorIdentity.logarithmicTrace =
      ((OldAtlas period hPeriod input).referenceTrace index).trace

namespace GlobalHessianPreferredFiveSectorH14D11RankOneReferenceSpectralData

/-- Convert rank-one spectral inputs to the boundary-matched Candidate-A
reference atlas. -/
def toBoundaryMatchedReferenceSpectralData
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (spectral :
      GlobalHessianPreferredFiveSectorH14D11RankOneReferenceSpectralData
        period hPeriod input) :
    GlobalHessianPreferredFiveSectorH14D11BoundaryMatchedReferenceSpectralData
      period hPeriod input where
  actual := spectral.actual
  baseReferenceFamily := spectral.baseReferenceFamily
  baseDifference := spectral.baseDifference
  baseShortTimeRegion := spectral.baseShortTimeRegion
  baseLongTimeRegion := spectral.baseLongTimeRegion
  baseBoundaryAssembly := spectral.baseRankOneAssembly.toBoundaryAssembly
  baseTrace_eq := spectral.baseTrace_eq
  localReferenceFamily := spectral.localReferenceFamily
  localDifference := spectral.localDifference
  localShortTimeRegion := spectral.localShortTimeRegion
  localLongTimeRegion := spectral.localLongTimeRegion
  localBoundaryAssembly := fun index =>
    (spectral.localRankOneAssembly index).toBoundaryAssembly
  localTrace_eq := spectral.localTrace_eq

/-- Physical D11 kernel/reference closure generated from rank-one reference
Duhamel expansions. -/
def toPhysicalReferenceClosure
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (frame : GlobalHessianPreferredFiveSectorD11OperatorNormUnitaryFrame4D
      period hPeriod input natural)
    (spectral :
      GlobalHessianPreferredFiveSectorH14D11RankOneReferenceSpectralData
        period hPeriod input)
    (zeroTrace : IntrinsicNuclearTraceData
      (0 : BaseReduced period hPeriod input →L[Real]
        BaseReduced period hPeriod input)) :
    GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D period hPeriod
      configuration data analysis einsteinScale hTransverse family chartBound
        Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index :=
  (spectral.toBoundaryMatchedReferenceSpectralData period hPeriod input).
    toPhysicalReferenceClosure period hPeriod input natural frame zeroTrace

/-- Public Candidate-A rank-one reference spectral checkpoint. -/
theorem global_hessian_preferred_five_sector_H14_D11_rank_one_reference_spectral_atlas_gate
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (frame : GlobalHessianPreferredFiveSectorD11OperatorNormUnitaryFrame4D
      period hPeriod input natural)
    (spectral :
      GlobalHessianPreferredFiveSectorH14D11RankOneReferenceSpectralData
        period hPeriod input)
    (zeroTrace : IntrinsicNuclearTraceData
      (0 : BaseReduced period hPeriod input →L[Real]
        BaseReduced period hPeriod input)) :
    let boundarySpectral :=
      spectral.toBoundaryMatchedReferenceSpectralData period hPeriod input
    let closure := spectral.toPhysicalReferenceClosure period hPeriod input
      natural frame zeroTrace
    (∀ parameter,
      (∫ time in spectral.baseShortTimeRegion,
        spectral.baseRankOneAssembly.nuclear.extendedDuhamelTrace parameter
          time) =
        intrinsicNuclearTrace
          (spectral.baseRankOneAssembly.rankOneBoundary.shortTime.
            integratedTraceClass parameter)) ∧
    (∀ parameter,
      (∫ time in spectral.baseLongTimeRegion,
        spectral.baseRankOneAssembly.nuclear.extendedDuhamelTrace parameter
          time) =
        intrinsicNuclearTrace
          (spectral.baseRankOneAssembly.rankOneBoundary.longTime.
            integratedTraceClass parameter)) ∧
    (∀ index parameter,
      (∫ time in spectral.localShortTimeRegion index,
        (spectral.localRankOneAssembly index).nuclear.extendedDuhamelTrace
          parameter time) =
        intrinsicNuclearTrace
          ((spectral.localRankOneAssembly index).rankOneBoundary.shortTime.
            integratedTraceClass parameter)) ∧
    (∀ index parameter,
      (∫ time in spectral.localLongTimeRegion index,
        (spectral.localRankOneAssembly index).nuclear.extendedDuhamelTrace
          parameter time) =
        intrinsicNuclearTrace
          ((spectral.localRankOneAssembly index).rankOneBoundary.longTime.
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
    ⟨spectral.baseRankOneAssembly.rankOneBoundary.shortTimeIntegral_eq_trace,
      spectral.baseRankOneAssembly.rankOneBoundary.longTimeIntegral_eq_trace,
      fun index =>
        (spectral.localRankOneAssembly index).rankOneBoundary.
          shortTimeIntegral_eq_trace,
      fun index =>
        (spectral.localRankOneAssembly index).rankOneBoundary.
          longTimeIntegral_eq_trace,
      hBoundary.2.2.2.2.1,
      hBoundary.2.2.2.2.2⟩

end GlobalHessianPreferredFiveSectorH14D11RankOneReferenceSpectralData

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11RankOneReferenceSpectralAtlas4D
end JanusFormal
