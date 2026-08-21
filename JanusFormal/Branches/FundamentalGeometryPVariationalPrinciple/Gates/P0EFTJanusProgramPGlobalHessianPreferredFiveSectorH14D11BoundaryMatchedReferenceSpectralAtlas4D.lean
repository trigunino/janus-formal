import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPReferenceNuclearHeatFinitePartBoundaryAssembly4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11OperatorIdentityReferenceSpectralAtlas4D

/-!
# Candidate-A reference atlas from short/long Duhamel boundary matching

This frontend is one layer stronger than the operator-identity reference atlas.
For the base reference and every local spectral-cut reference, the global
identity

```text
(C - D_short) - D_long = G H'
```

is no longer supplied.  Instead, the short- and long-time proofs meet through
one named matching operator:

```text
C - D_short = G H' + B,
D_long       = B.
```

The common boundary term is cancelled before the packet is converted to the
operator-identity atlas.  All physical D11 kernel, reference, zeta, determinant
and Quillen outputs are therefore inherited while the remaining spectral work
is localized to the two time regions.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11BoundaryMatchedReferenceSpectralAtlas4D

set_option autoImplicit false
set_option maxHeartbeats 254000000
set_option synthInstance.maxHeartbeats 127000000
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
open P0EFTJanusProgramPReferenceNuclearHeatFinitePartBoundaryAssembly4D
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
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11OperatorIdentityReferenceSpectralAtlas4D
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

universe v w

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

/-- Candidate-A spectral data with base and local short/long boundary matching
packets. -/
structure GlobalHessianPreferredFiveSectorH14D11BoundaryMatchedReferenceSpectralData
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
  baseBoundaryAssembly : ReferenceNuclearHeatFinitePartBoundaryAssemblyData.{0, w}
    (E := BaseReduced period hPeriod input) baseReferenceFamily
      baseShortTimeRegion baseLongTimeRegion
  baseTrace_eq :
    baseBoundaryAssembly.boundaryMatching.toOperatorIdentity.logarithmicTrace =
      (OldAtlas period hPeriod input).baseFamily.familyIndex.referenceTrace.trace
  localReferenceFamily : Index → RelativeHeatMellinZetaFamilyData
  localDifference : ∀ index,
    RelativeHeatMellinAnalyticDifferenceFamilyData
      ((OldAtlas period hPeriod input).localFamily index)
      actual.family (localReferenceFamily index)
  localShortTimeRegion : Index → Set Real
  localLongTimeRegion : Index → Set Real
  localBoundaryAssembly : ∀ index,
    ReferenceNuclearHeatFinitePartBoundaryAssemblyData.{0, w}
      (E := BaseReduced period hPeriod input) (localReferenceFamily index)
        (localShortTimeRegion index) (localLongTimeRegion index)
  localTrace_eq : ∀ index,
    (localBoundaryAssembly index).boundaryMatching.toOperatorIdentity.logarithmicTrace =
      ((OldAtlas period hPeriod input).referenceTrace index).trace

namespace GlobalHessianPreferredFiveSectorH14D11BoundaryMatchedReferenceSpectralData

/-- Convert local time-boundary data to the operator-identity atlas. -/
def toOperatorIdentityReferenceSpectralData
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (spectral :
      GlobalHessianPreferredFiveSectorH14D11BoundaryMatchedReferenceSpectralData
        period hPeriod input) :
    GlobalHessianPreferredFiveSectorH14D11OperatorIdentityReferenceSpectralData
      period hPeriod input where
  actual := spectral.actual
  baseReferenceFamily := spectral.baseReferenceFamily
  baseDifference := spectral.baseDifference
  baseShortTimeRegion := spectral.baseShortTimeRegion
  baseLongTimeRegion := spectral.baseLongTimeRegion
  baseOperatorAssembly := spectral.baseBoundaryAssembly.toOperatorAssembly
  baseTrace_eq := spectral.baseTrace_eq
  localReferenceFamily := spectral.localReferenceFamily
  localDifference := spectral.localDifference
  localShortTimeRegion := spectral.localShortTimeRegion
  localLongTimeRegion := spectral.localLongTimeRegion
  localOperatorAssembly := fun index =>
    (spectral.localBoundaryAssembly index).toOperatorAssembly
  localTrace_eq := spectral.localTrace_eq

/-- Physical D11 kernel/reference closure generated from locally matched time
regions. -/
def toPhysicalReferenceClosure
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (frame : GlobalHessianPreferredFiveSectorD11OperatorNormUnitaryFrame4D
      period hPeriod input natural)
    (spectral :
      GlobalHessianPreferredFiveSectorH14D11BoundaryMatchedReferenceSpectralData
        period hPeriod input)
    (zeroTrace : IntrinsicNuclearTraceData
      (0 : BaseReduced period hPeriod input →L[Real]
        BaseReduced period hPeriod input)) :
    GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D period hPeriod
      configuration data analysis einsteinScale hTransverse family chartBound
        Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index :=
  (spectral.toOperatorIdentityReferenceSpectralData period hPeriod input)
    |>.toPhysicalReferenceClosure period hPeriod input natural frame zeroTrace

/-- Public Candidate-A boundary-matched spectral checkpoint. -/
theorem global_hessian_preferred_five_sector_H14_D11_boundary_matched_reference_spectral_atlas_gate
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (frame : GlobalHessianPreferredFiveSectorD11OperatorNormUnitaryFrame4D
      period hPeriod input natural)
    (spectral :
      GlobalHessianPreferredFiveSectorH14D11BoundaryMatchedReferenceSpectralData
        period hPeriod input)
    (zeroTrace : IntrinsicNuclearTraceData
      (0 : BaseReduced period hPeriod input →L[Real]
        BaseReduced period hPeriod input)) :
    let operatorSpectral :=
      spectral.toOperatorIdentityReferenceSpectralData period hPeriod input
    let closure := spectral.toPhysicalReferenceClosure period hPeriod input
      natural frame zeroTrace
    (∀ parameter,
      spectral.baseBoundaryAssembly.boundaryMatching.countertermOperator
          parameter -
          spectral.baseBoundaryAssembly.boundaryMatching.shortTime.integratedOperator
            parameter =
        spectral.baseBoundaryAssembly.boundaryMatching.logarithmicDerivativeOperator
            parameter +
          spectral.baseBoundaryAssembly.boundaryMatching.matchingOperator
            parameter) ∧
    (∀ parameter,
      spectral.baseBoundaryAssembly.boundaryMatching.longTime.integratedOperator
          parameter =
        spectral.baseBoundaryAssembly.boundaryMatching.matchingOperator parameter) ∧
    (∀ index parameter,
      (spectral.localBoundaryAssembly index).boundaryMatching.countertermOperator
          parameter -
          (spectral.localBoundaryAssembly index).boundaryMatching.shortTime.integratedOperator
            parameter =
        (spectral.localBoundaryAssembly index).boundaryMatching.logarithmicDerivativeOperator
          parameter +
          (spectral.localBoundaryAssembly index).boundaryMatching.matchingOperator
            parameter) ∧
    (∀ index parameter,
      (spectral.localBoundaryAssembly index).boundaryMatching.longTime.integratedOperator
          parameter =
        (spectral.localBoundaryAssembly index).boundaryMatching.matchingOperator
          parameter) ∧
    GlobalHessianPreferredFiveSectorResolvedKernelFamily4D period hPeriod closure ∧
    GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D period
      hPeriod closure := by
  dsimp only
  let operatorSpectral :=
    spectral.toOperatorIdentityReferenceSpectralData period hPeriod input
  let closure := spectral.toPhysicalReferenceClosure period hPeriod input natural
    frame zeroTrace
  have hOperator :=
    GlobalHessianPreferredFiveSectorH14D11OperatorIdentityReferenceSpectralData.global_hessian_preferred_five_sector_H14_D11_operator_identity_reference_spectral_atlas_gate
        period hPeriod input natural frame operatorSpectral zeroTrace
  exact
    ⟨spectral.baseBoundaryAssembly.boundaryMatching.shortBoundaryIdentity,
      spectral.baseBoundaryAssembly.boundaryMatching.longBoundaryIdentity,
      fun index =>
        (spectral.localBoundaryAssembly index).boundaryMatching.shortBoundaryIdentity,
      fun index =>
        (spectral.localBoundaryAssembly index).boundaryMatching.longBoundaryIdentity,
      hOperator.2.2.1,
      hOperator.2.2.2⟩

end GlobalHessianPreferredFiveSectorH14D11BoundaryMatchedReferenceSpectralData

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11BoundaryMatchedReferenceSpectralAtlas4D
end JanusFormal
