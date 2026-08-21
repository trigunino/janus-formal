import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPReferenceNuclearHeatFinitePartAssembly4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11DuhamelReferenceSpectralAtlas4D

/-!
# Candidate-A spectral atlas from nuclear reference heat operators

This is the operator-level reference frontend of the preferred spectral atlas.
For the base reference and every local spectral-cut reference it accepts

* nuclear heat operators;
* nuclear heat derivative operators;
* nuclear Duhamel operators;
* the operator identity `K'_a(t) = -t D_a(t)`;
* differentiability of the intrinsic scalar heat trace;
* short- and long-time differentiation-under-the-integral certificates;
* the counterterm variation;
* the integrated identity with the intrinsic logarithmic reference trace;
* reality of the regularized reference zeta derivative at zero.

All scalar Duhamel formulas, finite-part derivatives, standalone reference
coefficients, relative coefficients and the physical D11 kernel/reference atlas
are outputs.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11NuclearReferenceSpectralAtlas4D

set_option autoImplicit false
set_option maxHeartbeats 238000000
set_option synthInstance.maxHeartbeats 119000000
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
open P0EFTJanusProgramPReferenceNuclearHeatFinitePartAssembly4D
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
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11DuhamelReferenceSpectralAtlas4D
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

/-- Candidate-A spectral data with nuclear reference heat variation packets. -/
structure GlobalHessianPreferredFiveSectorH14D11NuclearReferenceSpectralData
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
  baseNuclearAssembly : ReferenceNuclearHeatFinitePartAssemblyData.{0, w}
    (E := BaseReduced period hPeriod input) baseReferenceFamily
      baseShortTimeRegion baseLongTimeRegion
  baseTrace_eq : baseNuclearAssembly.logarithmicTrace =
    (OldAtlas period hPeriod input).baseFamily.familyIndex.referenceTrace.trace
  localReferenceFamily : Index → RelativeHeatMellinZetaFamilyData
  localDifference : ∀ index,
    RelativeHeatMellinAnalyticDifferenceFamilyData
      ((OldAtlas period hPeriod input).localFamily index)
      actual.family (localReferenceFamily index)
  localShortTimeRegion : Index → Set Real
  localLongTimeRegion : Index → Set Real
  localNuclearAssembly : ∀ index,
    ReferenceNuclearHeatFinitePartAssemblyData.{0, w}
      (E := BaseReduced period hPeriod input) (localReferenceFamily index)
        (localShortTimeRegion index) (localLongTimeRegion index)
  localTrace_eq : ∀ index,
    (localNuclearAssembly index).logarithmicTrace =
      ((OldAtlas period hPeriod input).referenceTrace index).trace

namespace GlobalHessianPreferredFiveSectorH14D11NuclearReferenceSpectralData

/-- Convert operator-level nuclear reference data to the scalar Duhamel atlas. -/
def toDuhamelReferenceSpectralData
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (spectral :
      GlobalHessianPreferredFiveSectorH14D11NuclearReferenceSpectralData
        period hPeriod input) :
    GlobalHessianPreferredFiveSectorH14D11DuhamelReferenceSpectralData
      period hPeriod input where
  actual := spectral.actual
  baseReferenceFamily := spectral.baseReferenceFamily
  baseDifference := spectral.baseDifference
  baseShortTimeRegion := spectral.baseShortTimeRegion
  baseLongTimeRegion := spectral.baseLongTimeRegion
  baseDuhamelAssembly := spectral.baseNuclearAssembly.toDuhamelFinitePartAssembly
  baseTrace_eq := spectral.baseTrace_eq
  localReferenceFamily := spectral.localReferenceFamily
  localDifference := spectral.localDifference
  localShortTimeRegion := spectral.localShortTimeRegion
  localLongTimeRegion := spectral.localLongTimeRegion
  localDuhamelAssembly := fun index =>
    (spectral.localNuclearAssembly index).toDuhamelFinitePartAssembly
  localTrace_eq := spectral.localTrace_eq

/-- Physical D11 kernel/reference closure generated from nuclear reference heat
operators. -/
def toPhysicalReferenceClosure
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (frame : GlobalHessianPreferredFiveSectorD11OperatorNormUnitaryFrame4D
      period hPeriod input natural)
    (spectral :
      GlobalHessianPreferredFiveSectorH14D11NuclearReferenceSpectralData
        period hPeriod input)
    (zeroTrace : IntrinsicNuclearTraceData
      (0 : BaseReduced period hPeriod input →L[Real]
        BaseReduced period hPeriod input)) :
    GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D period hPeriod
      configuration data analysis einsteinScale hTransverse family chartBound
        Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index :=
  (spectral.toDuhamelReferenceSpectralData period hPeriod input).toPhysicalReferenceClosure
    period hPeriod input natural frame zeroTrace

/-- Public nuclear-reference Candidate-A spectral checkpoint. -/
theorem global_hessian_preferred_five_sector_H14_D11_nuclear_reference_spectral_atlas_gate
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (frame : GlobalHessianPreferredFiveSectorD11OperatorNormUnitaryFrame4D
      period hPeriod input natural)
    (spectral :
      GlobalHessianPreferredFiveSectorH14D11NuclearReferenceSpectralData
        period hPeriod input)
    (zeroTrace : IntrinsicNuclearTraceData
      (0 : BaseReduced period hPeriod input →L[Real]
        BaseReduced period hPeriod input)) :
    let closure := spectral.toPhysicalReferenceClosure period hPeriod input
      natural frame zeroTrace
    GlobalHessianPreferredFiveSectorResolvedKernelFamily4D period hPeriod closure ∧
    GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D period
      hPeriod closure ∧
    (∀ parameter time,
      HasDerivAt
        (fun current => spectral.baseNuclearAssembly.nuclear.heatTrace current time)
        (-(time.1) *
          spectral.baseNuclearAssembly.nuclear.duhamelTrace parameter time)
        parameter) ∧
    (∀ index parameter time,
      HasDerivAt
        (fun current =>
          (spectral.localNuclearAssembly index).nuclear.heatTrace current time)
        (-(time.1) *
          (spectral.localNuclearAssembly index).nuclear.duhamelTrace parameter
            time) parameter) ∧
    (∀ parameter,
      relativeZetaConnectionCoefficient
          closure.familyIndex.baseFamily.familyIndex.zetaFamily.toZetaFamily
          parameter =
        (closure.familyIndex.baseFamily.familyIndex.referenceTrace.trace parameter :
          Real)) ∧
    (∀ index parameter,
      relativeZetaConnectionCoefficient
          (closure.familyIndex.localFamily index).toZetaFamily parameter =
        (closure.familyIndex.referenceTrace index).trace parameter) := by
  dsimp only
  let duhamel := spectral.toDuhamelReferenceSpectralData period hPeriod input
  let closure := spectral.toPhysicalReferenceClosure period hPeriod input natural
    frame zeroTrace
  exact
    ⟨physicalReferenceResolvedKernelFamily period hPeriod input natural frame
        zeroTrace
        ((duhamel.toIntegralReferenceSpectralData period hPeriod input
          |>.toTermwiseReferenceSpectralData period hPeriod input
          |>.toReferenceVariationSpectralData period hPeriod input
          |>.toRealReferenceSpectralData period hPeriod input).baseCoefficientAgreement
            period hPeriod input)
        ((duhamel.toIntegralReferenceSpectralData period hPeriod input
          |>.toTermwiseReferenceSpectralData period hPeriod input
          |>.toReferenceVariationSpectralData period hPeriod input
          |>.toRealReferenceSpectralData period hPeriod input).localCoefficientAgreement
            period hPeriod input),
      physicalReferenceRegularity period hPeriod input natural frame zeroTrace
        ((duhamel.toIntegralReferenceSpectralData period hPeriod input
          |>.toTermwiseReferenceSpectralData period hPeriod input
          |>.toReferenceVariationSpectralData period hPeriod input
          |>.toRealReferenceSpectralData period hPeriod input).baseCoefficientAgreement
            period hPeriod input)
        ((duhamel.toIntegralReferenceSpectralData period hPeriod input
          |>.toTermwiseReferenceSpectralData period hPeriod input
          |>.toReferenceVariationSpectralData period hPeriod input
          |>.toRealReferenceSpectralData period hPeriod input).localCoefficientAgreement
            period hPeriod input),
      spectral.baseNuclearAssembly.nuclear.heatTrace_hasDerivAt,
      fun index =>
        (spectral.localNuclearAssembly index).nuclear.heatTrace_hasDerivAt,
      (duhamel.toIntegralReferenceSpectralData period hPeriod input
        |>.toTermwiseReferenceSpectralData period hPeriod input
        |>.toReferenceVariationSpectralData period hPeriod input
        |>.toRealReferenceSpectralData period hPeriod input).baseCoefficientAgreement
          period hPeriod input,
      (duhamel.toIntegralReferenceSpectralData period hPeriod input
        |>.toTermwiseReferenceSpectralData period hPeriod input
        |>.toReferenceVariationSpectralData period hPeriod input
        |>.toRealReferenceSpectralData period hPeriod input).localCoefficientAgreement
          period hPeriod input⟩

end GlobalHessianPreferredFiveSectorH14D11NuclearReferenceSpectralData

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11NuclearReferenceSpectralAtlas4D
end JanusFormal
