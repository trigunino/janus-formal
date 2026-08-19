import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteUnitaryKernelComplementGreenTrivialization4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11UnitaryGreenContinuation4D

/-!
# Fixed-coordinate Candidate-A Green trivialization

The D11 unitary Green continuation is a conjugate family.  In the canonical
H12 complement coordinates selected by its unitary frame, both the genuine
reduced Candidate-A operator and its Green operator are literally constant.

This supplies the strongest possible C1 statement for the transported family:
all fixed-coordinate vectors are differentiable because they are equal to their
basepoint values.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11UnitaryGreenTrivialization4D

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 500000
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
open P0EFTJanusProgramPFiniteUnitaryKernelComplementGreenFrame4D
open P0EFTJanusProgramPFiniteUnitaryIntertwiningOperatorFrame4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorRepresentation4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11UnitaryGreenContinuation4D
open P0EFTJanusProgramPDenseCoreChartBilinearBound4D
open P0EFTJanusCircleDiracHeatTraceCancellation

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace
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

private abbrev DirectContinuation
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (d11Green :
      GlobalHessianPreferredFiveSectorD11UnitaryGreenContinuation4D
        period hPeriod input natural) :=
  d11Green.toUnitaryGreenContinuation period hPeriod input natural

/-- Candidate-A reduced operator in fixed H12 complement coordinates. -/
def trivializedReducedOperator
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (d11Green :
      GlobalHessianPreferredFiveSectorD11UnitaryGreenContinuation4D
        period hPeriod input natural)
    (parameter : Real)
    (vector : (input.familyIndex.baseFamily.actualOperator 0).kerᗮ) :=
  (DirectContinuation period hPeriod input natural d11Green).unitaryFrame.frameData
    |>.trivializedReducedOperator d11Green.basepointGreen parameter vector

/-- Candidate-A Green operator in fixed H12 complement coordinates. -/
def trivializedGreen
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (d11Green :
      GlobalHessianPreferredFiveSectorD11UnitaryGreenContinuation4D
        period hPeriod input natural)
    (parameter : Real)
    (vector : (input.familyIndex.baseFamily.actualOperator 0).kerᗮ) :=
  (DirectContinuation period hPeriod input natural d11Green).unitaryFrame.frameData
    |>.trivializedGreen d11Green.basepointGreen parameter vector

/-- Exact fixed-coordinate reduced-operator identity. -/
theorem trivializedReducedOperator_eq_basepoint
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (d11Green :
      GlobalHessianPreferredFiveSectorD11UnitaryGreenContinuation4D
        period hPeriod input natural)
    (parameter : Real)
    (vector : (input.familyIndex.baseFamily.actualOperator 0).kerᗮ) :
    trivializedReducedOperator period hPeriod input natural d11Green parameter
        vector =
      d11Green.basepointGreen.reducedOperator vector :=
  (DirectContinuation period hPeriod input natural d11Green).unitaryFrame.frameData
    |>.trivializedReducedOperator_eq_basepoint d11Green.basepointGreen parameter
      vector

/-- Exact fixed-coordinate Green identity. -/
theorem trivializedGreen_eq_basepoint
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (d11Green :
      GlobalHessianPreferredFiveSectorD11UnitaryGreenContinuation4D
        period hPeriod input natural)
    (parameter : Real)
    (vector : (input.familyIndex.baseFamily.actualOperator 0).kerᗮ) :
    trivializedGreen period hPeriod input natural d11Green parameter vector =
      d11Green.basepointGreen.green vector :=
  (DirectContinuation period hPeriod input natural d11Green).unitaryFrame.frameData
    |>.trivializedGreen_eq_basepoint d11Green.basepointGreen parameter vector

/-- Fixed-coordinate Candidate-A Green vectors are differentiable constants. -/
theorem trivializedGreen_differentiable
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (d11Green :
      GlobalHessianPreferredFiveSectorD11UnitaryGreenContinuation4D
        period hPeriod input natural)
    (vector : (input.familyIndex.baseFamily.actualOperator 0).kerᗮ) :
    Differentiable Real
      (fun parameter : Real =>
        trivializedGreen period hPeriod input natural d11Green parameter vector) :=
  (DirectContinuation period hPeriod input natural d11Green).unitaryFrame.frameData
    |>.trivializedGreen_differentiable d11Green.basepointGreen vector

/-- Public fixed-coordinate Candidate-A Green checkpoint. -/
theorem global_hessian_preferred_five_sector_D11_unitary_green_trivialization_gate
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (d11Green :
      GlobalHessianPreferredFiveSectorD11UnitaryGreenContinuation4D
        period hPeriod input natural) :
    (∀ parameter vector,
      trivializedReducedOperator period hPeriod input natural d11Green parameter
          vector = d11Green.basepointGreen.reducedOperator vector) ∧
    (∀ parameter vector,
      trivializedGreen period hPeriod input natural d11Green parameter vector =
        d11Green.basepointGreen.green vector) ∧
    (∀ vector,
      Differentiable Real
        (fun parameter : Real =>
          trivializedGreen period hPeriod input natural d11Green parameter
            vector)) :=
  ⟨trivializedReducedOperator_eq_basepoint period hPeriod input natural d11Green,
    trivializedGreen_eq_basepoint period hPeriod input natural d11Green,
    trivializedGreen_differentiable period hPeriod input natural d11Green⟩

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11UnitaryGreenTrivialization4D
end JanusFormal
