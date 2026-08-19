import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPReferenceZetaTraceCoefficient4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11UnitaryHeatSpectralAtlas4D

/-!
# Candidate-A spectral atlas from real reference trace identities

The unitary-heat Candidate-A atlas still accepted the complex standalone
reference identities

```text
T_reference = -Tr(G_reference H'_reference).
```

The reference trace functions are already fixed by the original atlas.  It is
enough to prove for each standalone reference zeta family that

```text
finitePartLogDerivative = reference logarithmic trace,
Im(zeta'(0)) = 0.
```

The generic reference theorem then generates the complex coefficient identity,
and the analytic actual/reference subtraction generates every base and local
relative coefficient.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11RealReferenceSpectralAtlas4D

set_option autoImplicit false
set_option maxHeartbeats 208000000
set_option synthInstance.maxHeartbeats 104000000
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
open P0EFTJanusProgramPReferenceZetaTraceCoefficient4D
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
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11UnitaryHeatSpectralAtlas4D
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

/-- Candidate-A spectral data whose reference coefficient identities are
generated from real finite-part trace statements. -/
structure GlobalHessianPreferredFiveSectorH14D11RealReferenceSpectralData
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index) where
  actual : UnitaryActualZetaFamilyData.{0, v}
    (E := BaseReduced period hPeriod input)
  baseReferenceFamily : RelativeHeatMellinZetaFamilyData
  baseDifference : RelativeHeatMellinAnalyticDifferenceFamilyData
    (OldAtlas period hPeriod input).baseFamily.familyIndex.zetaFamily
    actual.family baseReferenceFamily
  baseFinitePartLogDerivative_eq_trace : ∀ parameter,
    baseReferenceFamily.finitePartFamily.logDerivative parameter =
      (OldAtlas period hPeriod input).baseFamily.familyIndex.referenceTrace.trace
        parameter
  baseZetaPrimeAtZero_real : ∀ parameter,
    (baseReferenceFamily.zetaPrimeAtZero parameter).im = 0
  localReferenceFamily : Index → RelativeHeatMellinZetaFamilyData
  localDifference : ∀ index,
    RelativeHeatMellinAnalyticDifferenceFamilyData
      ((OldAtlas period hPeriod input).localFamily index)
      actual.family (localReferenceFamily index)
  localFinitePartLogDerivative_eq_trace : ∀ index parameter,
    (localReferenceFamily index).finitePartFamily.logDerivative parameter =
      ((OldAtlas period hPeriod input).referenceTrace index).trace parameter
  localZetaPrimeAtZero_real : ∀ index parameter,
    ((localReferenceFamily index).zetaPrimeAtZero parameter).im = 0

namespace GlobalHessianPreferredFiveSectorH14D11RealReferenceSpectralData

/-- Standalone base reference coefficient packet. -/
def baseReferenceData
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (spectral : GlobalHessianPreferredFiveSectorH14D11RealReferenceSpectralData
      period hPeriod input) :
    ReferenceZetaTraceCoefficientData spectral.baseReferenceFamily where
  logarithmicTrace :=
    (OldAtlas period hPeriod input).baseFamily.familyIndex.referenceTrace.trace
  finitePartLogDerivative_eq_trace :=
    spectral.baseFinitePartLogDerivative_eq_trace
  zetaPrimeAtZero_real := spectral.baseZetaPrimeAtZero_real

/-- Standalone local reference coefficient packet. -/
def localReferenceData
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (spectral : GlobalHessianPreferredFiveSectorH14D11RealReferenceSpectralData
      period hPeriod input)
    (index : Index) :
    ReferenceZetaTraceCoefficientData (spectral.localReferenceFamily index) where
  logarithmicTrace := ((OldAtlas period hPeriod input).referenceTrace index).trace
  finitePartLogDerivative_eq_trace :=
    spectral.localFinitePartLogDerivative_eq_trace index
  zetaPrimeAtZero_real := spectral.localZetaPrimeAtZero_real index

/-- Convert real reference data into the preceding unitary-heat spectral
packet. -/
def toUnitaryHeatSpectralDerivation
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (spectral : GlobalHessianPreferredFiveSectorH14D11RealReferenceSpectralData
      period hPeriod input) :
    GlobalHessianPreferredFiveSectorH14D11UnitaryHeatSpectralDerivationData
      period hPeriod input where
  actual := spectral.actual
  baseReferenceFamily := spectral.baseReferenceFamily
  baseDifference := spectral.baseDifference
  baseReferenceCoefficient :=
    (spectral.baseReferenceData period hPeriod input).connectionCoefficient_eq_neg_trace
  localReferenceFamily := spectral.localReferenceFamily
  localDifference := spectral.localDifference
  localReferenceCoefficient := fun index =>
    (spectral.localReferenceData period hPeriod input index).connectionCoefficient_eq_neg_trace

/-- The base relative coefficient follows from the two real reference inputs. -/
theorem baseCoefficientAgreement
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (spectral : GlobalHessianPreferredFiveSectorH14D11RealReferenceSpectralData
      period hPeriod input)
    (parameter : Real) :
    relativeZetaConnectionCoefficient
        (OldAtlas period hPeriod input).baseFamily.familyIndex.zetaFamily.toZetaFamily
          parameter =
      ((OldAtlas period hPeriod input).baseFamily.familyIndex.referenceTrace.trace
        parameter : Real) :=
  (spectral.toUnitaryHeatSpectralDerivation period hPeriod input).baseCoefficientAgreement
    period hPeriod input parameter

/-- Every local relative coefficient follows from its two real reference
inputs. -/
theorem localCoefficientAgreement
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (spectral : GlobalHessianPreferredFiveSectorH14D11RealReferenceSpectralData
      period hPeriod input)
    (index : Index) (parameter : Real) :
    relativeZetaConnectionCoefficient
        ((OldAtlas period hPeriod input).localFamily index).toZetaFamily parameter =
      ((OldAtlas period hPeriod input).referenceTrace index).trace parameter :=
  (spectral.toUnitaryHeatSpectralDerivation period hPeriod input).localCoefficientAgreement
    period hPeriod input index parameter

/-- Physical reference closure with all complex coefficient identities
derived. -/
def toPhysicalReferenceClosure
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (frame : GlobalHessianPreferredFiveSectorD11OperatorNormUnitaryFrame4D
      period hPeriod input natural)
    (spectral : GlobalHessianPreferredFiveSectorH14D11RealReferenceSpectralData
      period hPeriod input)
    (zeroTrace : IntrinsicNuclearTraceData
      (0 : BaseReduced period hPeriod input →L[Real]
        BaseReduced period hPeriod input)) :
    GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D period hPeriod
      configuration data analysis einsteinScale hTransverse family chartBound
        Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index :=
  (spectral.toUnitaryHeatSpectralDerivation period hPeriod input).toPhysicalReferenceClosure
    period hPeriod input natural frame zeroTrace

/-- Public real-reference Candidate-A spectral checkpoint. -/
theorem global_hessian_preferred_five_sector_H14_D11_real_reference_spectral_atlas_gate
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (frame : GlobalHessianPreferredFiveSectorD11OperatorNormUnitaryFrame4D
      period hPeriod input natural)
    (spectral : GlobalHessianPreferredFiveSectorH14D11RealReferenceSpectralData
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
      (spectral.baseReferenceFamily.parameterDerivative parameter).im = 0) ∧
    (∀ index parameter,
      ((spectral.localReferenceFamily index).parameterDerivative parameter).im =
        0) ∧
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
  let derived := spectral.toUnitaryHeatSpectralDerivation period hPeriod input
  let closure := spectral.toPhysicalReferenceClosure period hPeriod input natural
    frame zeroTrace
  exact
    ⟨physicalReferenceResolvedKernelFamily period hPeriod input natural frame
        zeroTrace
        (derived.baseCoefficientAgreement period hPeriod input)
        (derived.localCoefficientAgreement period hPeriod input),
      physicalReferenceRegularity period hPeriod input natural frame zeroTrace
        (derived.baseCoefficientAgreement period hPeriod input)
        (derived.localCoefficientAgreement period hPeriod input),
      (spectral.baseReferenceData period hPeriod input).parameterDerivative_im_zero,
      fun index =>
        (spectral.localReferenceData period hPeriod input index).parameterDerivative_im_zero,
      spectral.baseCoefficientAgreement period hPeriod input,
      spectral.localCoefficientAgreement period hPeriod input⟩

end GlobalHessianPreferredFiveSectorH14D11RealReferenceSpectralData

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11RealReferenceSpectralAtlas4D
end JanusFormal
