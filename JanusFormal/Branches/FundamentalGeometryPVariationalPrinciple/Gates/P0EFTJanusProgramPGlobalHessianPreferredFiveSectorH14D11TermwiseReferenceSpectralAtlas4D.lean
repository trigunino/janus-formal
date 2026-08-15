import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeHeatFinitePartTermwiseVariation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11ReferenceVariationSpectralAtlas4D

/-!
# Candidate-A spectral atlas from termwise reference heat variations

The direct reference finite-part variation theorem is now decomposed into the
three analytically distinct contributions of the existing renormalization:

```text
counterterm finite contribution,
renormalized short-time integral,
long-time integral.
```

For the base reference and every local spectral-cut reference, this file accepts

* a termwise finite-part variation packet;
* an equality between the sum of the three derivatives and the intrinsic
  logarithmic trace `Tr(G_ref H'_ref)`;
* reality of the regularized reference zeta derivative at zero.

It then reconstructs the direct `HasDerivAt` theorem, every standalone
reference coefficient, all analytic relative coefficient agreements, and the
physical D11 kernel/reference atlas closure.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11TermwiseReferenceSpectralAtlas4D

set_option autoImplicit false
set_option maxHeartbeats 220000000
set_option synthInstance.maxHeartbeats 110000000
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
open P0EFTJanusProgramPRelativeHeatFinitePartTermwiseVariation4D
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
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11ReferenceVariationSpectralAtlas4D
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

/-- Candidate-A spectral data controlled by termwise reference finite-part
variations. -/
structure GlobalHessianPreferredFiveSectorH14D11TermwiseReferenceSpectralData
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index) where
  actual : UnitaryActualZetaFamilyData (E := BaseReduced period hPeriod input)
  baseReferenceFamily : RelativeHeatMellinZetaFamilyData
  baseDifference : RelativeHeatMellinAnalyticDifferenceFamilyData
    (OldAtlas period hPeriod input).baseFamily.familyIndex.zetaFamily
    actual.family baseReferenceFamily
  baseTermwise : RelativeHeatFinitePartTermwiseVariationData
    baseReferenceFamily.finitePartFamily
  baseTotalDerivative_eq_trace : ∀ parameter,
    baseTermwise.totalDerivative parameter =
      (OldAtlas period hPeriod input).baseFamily.familyIndex.referenceTrace.trace
        parameter
  baseZetaPrimeAtZero_real : ∀ parameter,
    (baseReferenceFamily.zetaPrimeAtZero parameter).im = 0
  localReferenceFamily : Index → RelativeHeatMellinZetaFamilyData
  localDifference : ∀ index,
    RelativeHeatMellinAnalyticDifferenceFamilyData
      ((OldAtlas period hPeriod input).localFamily index)
      actual.family (localReferenceFamily index)
  localTermwise : ∀ index,
    RelativeHeatFinitePartTermwiseVariationData
      (localReferenceFamily index).finitePartFamily
  localTotalDerivative_eq_trace : ∀ index parameter,
    (localTermwise index).totalDerivative parameter =
      ((OldAtlas period hPeriod input).referenceTrace index).trace parameter
  localZetaPrimeAtZero_real : ∀ index parameter,
    ((localReferenceFamily index).zetaPrimeAtZero parameter).im = 0

namespace GlobalHessianPreferredFiveSectorH14D11TermwiseReferenceSpectralData

/-- Base termwise reference trace packet. -/
def baseTermwiseTrace
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (spectral :
      GlobalHessianPreferredFiveSectorH14D11TermwiseReferenceSpectralData
        period hPeriod input) :
    ReferenceHeatFinitePartTermwiseTraceData spectral.baseReferenceFamily where
  termwise := spectral.baseTermwise
  logarithmicTrace :=
    (OldAtlas period hPeriod input).baseFamily.familyIndex.referenceTrace.trace
  totalDerivative_eq_trace := spectral.baseTotalDerivative_eq_trace
  zetaPrimeAtZero_real := spectral.baseZetaPrimeAtZero_real

/-- Local termwise reference trace packet. -/
def localTermwiseTrace
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (spectral :
      GlobalHessianPreferredFiveSectorH14D11TermwiseReferenceSpectralData
        period hPeriod input)
    (index : Index) :
    ReferenceHeatFinitePartTermwiseTraceData
      (spectral.localReferenceFamily index) where
  termwise := spectral.localTermwise index
  logarithmicTrace := ((OldAtlas period hPeriod input).referenceTrace index).trace
  totalDerivative_eq_trace := spectral.localTotalDerivative_eq_trace index
  zetaPrimeAtZero_real := spectral.localZetaPrimeAtZero_real index

/-- Convert the three termwise derivatives to direct finite-part variation
theorems. -/
def toReferenceVariationSpectralData
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (spectral :
      GlobalHessianPreferredFiveSectorH14D11TermwiseReferenceSpectralData
        period hPeriod input) :
    GlobalHessianPreferredFiveSectorH14D11ReferenceVariationSpectralData
      period hPeriod input where
  actual := spectral.actual
  baseReferenceFamily := spectral.baseReferenceFamily
  baseDifference := spectral.baseDifference
  baseHasDerivAt_finitePartLog :=
    (spectral.baseTermwiseTrace period hPeriod input).
      toReferenceFinitePartTraceVariation.hasDerivAt_finitePartLog
  baseZetaPrimeAtZero_real := spectral.baseZetaPrimeAtZero_real
  localReferenceFamily := spectral.localReferenceFamily
  localDifference := spectral.localDifference
  localHasDerivAt_finitePartLog := fun index =>
    (spectral.localTermwiseTrace period hPeriod input index).
      toReferenceFinitePartTraceVariation.hasDerivAt_finitePartLog
  localZetaPrimeAtZero_real := spectral.localZetaPrimeAtZero_real

/-- Physical reference closure generated from termwise finite-part variations. -/
def toPhysicalReferenceClosure
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (frame : GlobalHessianPreferredFiveSectorD11OperatorNormUnitaryFrame4D
      period hPeriod input natural)
    (spectral :
      GlobalHessianPreferredFiveSectorH14D11TermwiseReferenceSpectralData
        period hPeriod input)
    (zeroTrace : IntrinsicNuclearTraceData
      (0 : BaseReduced period hPeriod input →L[Real]
        BaseReduced period hPeriod input)) :
    GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D period hPeriod
      configuration data analysis einsteinScale hTransverse family chartBound
        Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index :=
  (spectral.toReferenceVariationSpectralData period hPeriod input).
    toPhysicalReferenceClosure period hPeriod input natural frame zeroTrace

/-- Public termwise-reference Candidate-A spectral checkpoint. -/
theorem global_hessian_preferred_five_sector_H14_D11_termwise_reference_spectral_atlas_gate
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (frame : GlobalHessianPreferredFiveSectorD11OperatorNormUnitaryFrame4D
      period hPeriod input natural)
    (spectral :
      GlobalHessianPreferredFiveSectorH14D11TermwiseReferenceSpectralData
        period hPeriod input)
    (zeroTrace : IntrinsicNuclearTraceData
      (0 : BaseReduced period hPeriod input →L[Real]
        BaseReduced period hPeriod input)) :
    let closure := spectral.toPhysicalReferenceClosure period hPeriod input
      natural frame zeroTrace
    GlobalHessianPreferredFiveSectorResolvedKernelFamily4D period hPeriod closure ∧
    GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D period
      hPeriod closure ∧
    (∀ parameter,
      relativeZetaConnectionCoefficient
          closure.familyIndex.baseFamily.familyIndex.zetaFamily.toZetaFamily
          parameter =
        (closure.familyIndex.baseFamily.familyIndex.referenceTrace.trace parameter :
          Real)) ∧
    (∀ index parameter,
      relativeZetaConnectionCoefficient
          (closure.familyIndex.localFamily index).toZetaFamily parameter =
        (closure.familyIndex.referenceTrace index).trace parameter) ∧
    (∀ parameter,
      spectral.baseReferenceFamily.finitePartFamily.logDerivative parameter =
        spectral.baseTermwise.totalDerivative parameter) ∧
    (∀ index parameter,
      (spectral.localReferenceFamily index).finitePartFamily.logDerivative
          parameter = (spectral.localTermwise index).totalDerivative parameter) := by
  dsimp only
  let direct := spectral.toReferenceVariationSpectralData period hPeriod input
  let closure := spectral.toPhysicalReferenceClosure period hPeriod input natural
    frame zeroTrace
  exact
    ⟨physicalReferenceResolvedKernelFamily period hPeriod input natural frame
        zeroTrace
        ((direct.toRealReferenceSpectralData period hPeriod input).
          baseCoefficientAgreement period hPeriod input)
        ((direct.toRealReferenceSpectralData period hPeriod input).
          localCoefficientAgreement period hPeriod input),
      physicalReferenceRegularity period hPeriod input natural frame zeroTrace
        ((direct.toRealReferenceSpectralData period hPeriod input).
          baseCoefficientAgreement period hPeriod input)
        ((direct.toRealReferenceSpectralData period hPeriod input).
          localCoefficientAgreement period hPeriod input),
      (direct.toRealReferenceSpectralData period hPeriod input).
        baseCoefficientAgreement period hPeriod input,
      (direct.toRealReferenceSpectralData period hPeriod input).
        localCoefficientAgreement period hPeriod input,
      spectral.baseTermwise.namedLogDerivative_eq_totalDerivative,
      fun index =>
        (spectral.localTermwise index).namedLogDerivative_eq_totalDerivative⟩

end GlobalHessianPreferredFiveSectorH14D11TermwiseReferenceSpectralData

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11TermwiseReferenceSpectralAtlas4D
end JanusFormal
