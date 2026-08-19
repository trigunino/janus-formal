import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeZetaReferenceAtlasDerivation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11PhysicalReferenceClosure4D

/-!
# Candidate-A spectral atlas derived from actual/reference analytic families

The physical/reference closure previously accepted one coefficient equality for
the base reference and one for every local spectral-cut reference.  Those
identities are now consequences of analytic zeta subtraction.

This file supplies the Candidate-A specialization.  Its input is

* one actual zeta family with zero coefficient in the D11 unitary frame;
* one standalone zeta family for the base reference and for every local
  reference;
* analytic difference comparisons with the already selected relative zeta
  families;
* the standalone identities `T_ref = -Tr(G_ref H'_ref)`.

The base and local relative coefficients are then derived and fed directly into
the physical D11 kernel/reference atlas closure.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11DerivedSpectralAtlas4D

set_option autoImplicit false
set_option maxHeartbeats 196000000
set_option synthInstance.maxHeartbeats 98000000
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
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyH10Reduction4D
open P0EFTJanusProgramPGlobalCandidateACanonicalSixDenseCore4D
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusProgramPGlobalHessianDiracGreenBoundedClosure4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalBlockBounds4D
open P0EFTJanusProgramPGlobalHessianActualKernelFrontier4D
open P0EFTJanusProgramPGlobalCandidateAFaithfulFredholmSum4D
open P0EFTJanusProgramPIntrinsicNuclearTrace4D
open P0EFTJanusProgramPRelativeHeatMellinAnalyticDifferenceFamily4D
open P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D
open P0EFTJanusProgramPRelativeZetaDeterminantConnection4D
open P0EFTJanusProgramPRelativeZetaReferenceAtlasDerivation4D
open P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11OperatorNormUnitaryFrame4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11PhysicalReferenceClosure4D
open P0EFTJanusProgramPDenseCoreChartBilinearBound4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorResolvedKernelFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
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

/-- Analytic actual/reference data tied to the already selected Candidate-A
relative zeta charts. -/
structure GlobalHessianPreferredFiveSectorH14D11SpectralDerivationData
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index) where
  actualFamily : RelativeHeatMellinZetaFamilyData
  actualCoefficient_zero : ∀ parameter,
    relativeZetaConnectionCoefficient actualFamily.toZetaFamily parameter = 0
  baseReferenceFamily : RelativeHeatMellinZetaFamilyData
  baseDifference : RelativeHeatMellinAnalyticDifferenceFamilyData
    (OldAtlas period hPeriod input).baseFamily.familyIndex.zetaFamily
    actualFamily baseReferenceFamily
  baseReferenceCoefficient : ∀ parameter,
    relativeZetaConnectionCoefficient baseReferenceFamily.toZetaFamily parameter =
      -((OldAtlas period hPeriod input).baseFamily.familyIndex.referenceTrace.trace
        parameter)
  localReferenceFamily : Index → RelativeHeatMellinZetaFamilyData
  localDifference : ∀ index,
    RelativeHeatMellinAnalyticDifferenceFamilyData
      ((OldAtlas period hPeriod input).localFamily index)
      actualFamily (localReferenceFamily index)
  localReferenceCoefficient : ∀ index parameter,
    relativeZetaConnectionCoefficient
        (localReferenceFamily index).toZetaFamily parameter =
      -((OldAtlas period hPeriod input).referenceTrace index).trace parameter

namespace GlobalHessianPreferredFiveSectorH14D11SpectralDerivationData

/-- Forget Candidate-A labels and expose the generic reference-atlas derivation
packet. -/
def toReferenceAtlasDerivation
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (spectral : GlobalHessianPreferredFiveSectorH14D11SpectralDerivationData
      period hPeriod input) :
    RelativeZetaReferenceAtlasDerivationData Index where
  actualFamily := spectral.actualFamily
  actualCoefficient_zero := spectral.actualCoefficient_zero
  baseRelativeFamily :=
    (OldAtlas period hPeriod input).baseFamily.familyIndex.zetaFamily
  baseReferenceFamily := spectral.baseReferenceFamily
  baseReferenceTrace :=
    (OldAtlas period hPeriod input).baseFamily.familyIndex.referenceTrace.trace
  baseDifference := spectral.baseDifference
  baseReferenceCoefficient := spectral.baseReferenceCoefficient
  localRelativeFamily := (OldAtlas period hPeriod input).localFamily
  localReferenceFamily := spectral.localReferenceFamily
  localReferenceTrace := fun index =>
    ((OldAtlas period hPeriod input).referenceTrace index).trace
  localDifference := spectral.localDifference
  localReferenceCoefficient := spectral.localReferenceCoefficient

/-- Base coefficient agreement derived from analytic subtraction. -/
theorem baseCoefficientAgreement
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (spectral : GlobalHessianPreferredFiveSectorH14D11SpectralDerivationData
      period hPeriod input)
    (parameter : Real) :
    relativeZetaConnectionCoefficient
        (OldAtlas period hPeriod input).baseFamily.familyIndex.zetaFamily.toZetaFamily
          parameter =
      ((OldAtlas period hPeriod input).baseFamily.familyIndex.referenceTrace.trace
        parameter : Real) :=
  (spectral.toReferenceAtlasDerivation period hPeriod input
    |>.baseCoefficient_eq_referenceTrace parameter)

/-- Local coefficient agreements derived for every spectral-cut reference. -/
theorem localCoefficientAgreement
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (spectral : GlobalHessianPreferredFiveSectorH14D11SpectralDerivationData
      period hPeriod input)
    (index : Index) (parameter : Real) :
    relativeZetaConnectionCoefficient
        ((OldAtlas period hPeriod input).localFamily index).toZetaFamily parameter =
      ((OldAtlas period hPeriod input).referenceTrace index).trace parameter :=
  (spectral.toReferenceAtlasDerivation period hPeriod input
    |>.localCoefficient_eq_referenceTrace index parameter)

/-- Physical D11 kernel/reference closure with all zeta coefficient agreements
derived rather than supplied. -/
def toPhysicalReferenceClosure
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (frame : GlobalHessianPreferredFiveSectorD11OperatorNormUnitaryFrame4D
      period hPeriod input natural)
    (spectral : GlobalHessianPreferredFiveSectorH14D11SpectralDerivationData
      period hPeriod input)
    (zeroTrace : IntrinsicNuclearTraceData
      (0 : BaseReduced period hPeriod input →L[Real]
        BaseReduced period hPeriod input)) :
    GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D period hPeriod
      configuration data analysis einsteinScale hTransverse family chartBound
        Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index :=
  physicalReferenceNamedKernelClosure period hPeriod input natural frame zeroTrace
    (spectral.baseCoefficientAgreement period hPeriod input)
    (spectral.localCoefficientAgreement period hPeriod input)

/-- Public fully derived Candidate-A spectral-atlas checkpoint. -/
theorem global_hessian_preferred_five_sector_H14_D11_derived_spectral_atlas_gate
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (frame : GlobalHessianPreferredFiveSectorD11OperatorNormUnitaryFrame4D
      period hPeriod input natural)
    (spectral : GlobalHessianPreferredFiveSectorH14D11SpectralDerivationData
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
        (closure.familyIndex.referenceTrace index).trace parameter) := by
  dsimp only
  let closure := spectral.toPhysicalReferenceClosure period hPeriod input natural
    frame zeroTrace
  exact
    ⟨physicalReferenceResolvedKernelFamily period hPeriod input natural frame
        zeroTrace
        (spectral.baseCoefficientAgreement period hPeriod input)
        (spectral.localCoefficientAgreement period hPeriod input),
      physicalReferenceRegularity period hPeriod input natural frame zeroTrace
        (spectral.baseCoefficientAgreement period hPeriod input)
        (spectral.localCoefficientAgreement period hPeriod input),
      spectral.baseCoefficientAgreement period hPeriod input,
      spectral.localCoefficientAgreement period hPeriod input⟩

end GlobalHessianPreferredFiveSectorH14D11SpectralDerivationData

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11DerivedSpectralAtlas4D
end JanusFormal
