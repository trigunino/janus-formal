import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeHeatIntegralVariation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11TermwiseReferenceSpectralAtlas4D

/-!
# Candidate-A spectral atlas from differentiated reference heat integrals

The base and local reference finite-part variations are now supplied at the
level of their actual analytic pieces:

* one differentiable counterterm contribution;
* one differentiated short-time integral;
* one differentiated long-time integral;
* the identity between the sum of these derivatives and
  `Tr(G_ref H'_ref)`.

The integral packets retain the pointwise heat-kernel derivative and the exact
integral of that derivative, so future Duhamel and domination proofs feed this
layer directly.  All higher finite-part, zeta, Bismut--Freed and spectral-atlas
conclusions are reconstructed automatically.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11IntegralReferenceSpectralAtlas4D

set_option autoImplicit false
set_option maxHeartbeats 226000000
set_option synthInstance.maxHeartbeats 113000000
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
open P0EFTJanusProgramPRelativeHeatIntegralVariation4D
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
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11TermwiseReferenceSpectralAtlas4D
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

universe v

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

/-- Candidate-A spectral data whose reference variations are supplied by
counterterm/short-time/long-time integral assemblies. -/
structure GlobalHessianPreferredFiveSectorH14D11IntegralReferenceSpectralData
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
  baseIntegralAssembly : ReferenceHeatFinitePartIntegralAssemblyData
    baseReferenceFamily baseShortTimeRegion baseLongTimeRegion
  baseTrace_eq : baseIntegralAssembly.logarithmicTrace =
    (OldAtlas period hPeriod input).baseFamily.familyIndex.referenceTrace.trace
  localReferenceFamily : Index → RelativeHeatMellinZetaFamilyData
  localDifference : ∀ index,
    RelativeHeatMellinAnalyticDifferenceFamilyData
      ((OldAtlas period hPeriod input).localFamily index)
      actual.family (localReferenceFamily index)
  localShortTimeRegion : Index → Set Real
  localLongTimeRegion : Index → Set Real
  localIntegralAssembly : ∀ index,
    ReferenceHeatFinitePartIntegralAssemblyData
      (localReferenceFamily index) (localShortTimeRegion index)
        (localLongTimeRegion index)
  localTrace_eq : ∀ index,
    (localIntegralAssembly index).logarithmicTrace =
      ((OldAtlas period hPeriod input).referenceTrace index).trace

namespace GlobalHessianPreferredFiveSectorH14D11IntegralReferenceSpectralData

/-- Convert the integral assemblies to termwise reference data. -/
def toTermwiseReferenceSpectralData
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (spectral :
      GlobalHessianPreferredFiveSectorH14D11IntegralReferenceSpectralData
        period hPeriod input) :
    GlobalHessianPreferredFiveSectorH14D11TermwiseReferenceSpectralData
      period hPeriod input where
  actual := spectral.actual
  baseReferenceFamily := spectral.baseReferenceFamily
  baseDifference := spectral.baseDifference
  baseTermwise := spectral.baseIntegralAssembly.toTermwiseVariation
  baseTotalDerivative_eq_trace := by
    intro parameter
    rw [← spectral.baseTrace_eq]
    exact spectral.baseIntegralAssembly.integratedDerivative_eq_trace parameter
  baseZetaPrimeAtZero_real :=
    spectral.baseIntegralAssembly.zetaPrimeAtZero_real
  localReferenceFamily := spectral.localReferenceFamily
  localDifference := spectral.localDifference
  localTermwise := fun index =>
    (spectral.localIntegralAssembly index).toTermwiseVariation
  localTotalDerivative_eq_trace := by
    intro index parameter
    rw [← spectral.localTrace_eq index]
    exact (spectral.localIntegralAssembly index).integratedDerivative_eq_trace
      parameter
  localZetaPrimeAtZero_real := fun index =>
    (spectral.localIntegralAssembly index).zetaPrimeAtZero_real

/-- Physical D11 kernel/reference closure generated from differentiated heat
integrals. -/
def toPhysicalReferenceClosure
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (frame : GlobalHessianPreferredFiveSectorD11OperatorNormUnitaryFrame4D
      period hPeriod input natural)
    (spectral :
      GlobalHessianPreferredFiveSectorH14D11IntegralReferenceSpectralData
        period hPeriod input)
    (zeroTrace : IntrinsicNuclearTraceData
      (0 : BaseReduced period hPeriod input →L[Real]
        BaseReduced period hPeriod input)) :
    GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D period hPeriod
      configuration data analysis einsteinScale hTransverse family chartBound
        Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index :=
  (spectral.toTermwiseReferenceSpectralData period hPeriod input).toPhysicalReferenceClosure
    period hPeriod input natural frame zeroTrace

/-- Public integral-reference Candidate-A spectral checkpoint. -/
theorem global_hessian_preferred_five_sector_H14_D11_integral_reference_spectral_atlas_gate
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (frame : GlobalHessianPreferredFiveSectorD11OperatorNormUnitaryFrame4D
      period hPeriod input natural)
    (spectral :
      GlobalHessianPreferredFiveSectorH14D11IntegralReferenceSpectralData
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
      HasDerivAt spectral.baseIntegralAssembly.shortTime.contribution
        (spectral.baseIntegralAssembly.shortTime.derivativeContribution parameter)
        parameter) ∧
    (∀ index parameter,
      HasDerivAt
        (spectral.localIntegralAssembly index).longTime.contribution
        ((spectral.localIntegralAssembly index).longTime.derivativeContribution
          parameter) parameter) := by
  dsimp only
  let termwise := spectral.toTermwiseReferenceSpectralData period hPeriod input
  let closure := spectral.toPhysicalReferenceClosure period hPeriod input natural
    frame zeroTrace
  exact
    ⟨physicalReferenceResolvedKernelFamily period hPeriod input natural frame
        zeroTrace
        ((termwise.toReferenceVariationSpectralData period hPeriod input
          |>.toRealReferenceSpectralData period hPeriod input).baseCoefficientAgreement
            period hPeriod input)
        ((termwise.toReferenceVariationSpectralData period hPeriod input
          |>.toRealReferenceSpectralData period hPeriod input).localCoefficientAgreement
            period hPeriod input),
      physicalReferenceRegularity period hPeriod input natural frame zeroTrace
        ((termwise.toReferenceVariationSpectralData period hPeriod input
          |>.toRealReferenceSpectralData period hPeriod input).baseCoefficientAgreement
            period hPeriod input)
        ((termwise.toReferenceVariationSpectralData period hPeriod input
          |>.toRealReferenceSpectralData period hPeriod input).localCoefficientAgreement
            period hPeriod input),
      (termwise.toReferenceVariationSpectralData period hPeriod input
        |>.toRealReferenceSpectralData period hPeriod input).baseCoefficientAgreement
          period hPeriod input,
      (termwise.toReferenceVariationSpectralData period hPeriod input
        |>.toRealReferenceSpectralData period hPeriod input).localCoefficientAgreement
          period hPeriod input,
      spectral.baseIntegralAssembly.shortTime.hasDerivAt_integral,
      fun index =>
        (spectral.localIntegralAssembly index).longTime.hasDerivAt_integral⟩

end GlobalHessianPreferredFiveSectorH14D11IntegralReferenceSpectralData

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11IntegralReferenceSpectralAtlas4D
end JanusFormal
