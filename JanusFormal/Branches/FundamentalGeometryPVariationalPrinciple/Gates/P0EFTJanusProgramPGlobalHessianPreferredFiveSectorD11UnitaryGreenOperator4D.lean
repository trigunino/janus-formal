import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteUnitaryKernelComplementGreenOperator4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11UnitaryGreenContinuation4D

/-!
# Bundled Candidate-A reduced and Green operators from D11

The D11 unitary Green continuation already provides pointwise reduced and Green
maps on each canonical fibre `(ker H_a)ᗮ`.  This layer packages them as
continuous linear endomorphisms and exposes the exact inverse identities in the
operator category.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11UnitaryGreenOperator4D

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

/-- Genuine Candidate-A reduced operator bundled on one current canonical
reduced fibre. -/
def reducedOperatorCLM
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (d11Green :
      GlobalHessianPreferredFiveSectorD11UnitaryGreenContinuation4D
        period hPeriod input natural)
    (parameter : Real) :
    (input.familyIndex.baseFamily.actualOperator parameter).kerᗮ →L[Real]
      (input.familyIndex.baseFamily.actualOperator parameter).kerᗮ :=
  (DirectContinuation period hPeriod input natural d11Green).unitaryFrame.frameData.transportedReducedOperatorCLM
    d11Green.basepointGreen parameter

/-- Candidate-A reduced Green bundled on one current canonical reduced fibre. -/
def greenCLM
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (d11Green :
      GlobalHessianPreferredFiveSectorD11UnitaryGreenContinuation4D
        period hPeriod input natural)
    (parameter : Real) :
    (input.familyIndex.baseFamily.actualOperator parameter).kerᗮ →L[Real]
      (input.familyIndex.baseFamily.actualOperator parameter).kerᗮ :=
  (DirectContinuation period hPeriod input natural d11Green).unitaryFrame.frameData.transportedGreenCLM
    d11Green.basepointGreen parameter

/-- Ambient value of the bundled reduced Candidate-A operator. -/
theorem reducedOperatorCLM_apply_val
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (d11Green :
      GlobalHessianPreferredFiveSectorD11UnitaryGreenContinuation4D
        period hPeriod input natural)
    (parameter : Real)
    (vector : (input.familyIndex.baseFamily.actualOperator parameter).kerᗮ) :
    (reducedOperatorCLM period hPeriod input natural d11Green parameter vector).1 =
      input.familyIndex.baseFamily.actualOperator parameter vector.1 :=
  (DirectContinuation period hPeriod input natural d11Green).unitaryFrame.frameData.transportedReducedOperatorCLM_apply_val
    d11Green.basepointGreen parameter
      vector

/-- Bundled reduced operator followed by bundled Green is identity. -/
theorem reducedOperatorCLM_comp_greenCLM
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (d11Green :
      GlobalHessianPreferredFiveSectorD11UnitaryGreenContinuation4D
        period hPeriod input natural)
    (parameter : Real) :
    (reducedOperatorCLM period hPeriod input natural d11Green parameter).comp
        (greenCLM period hPeriod input natural d11Green parameter) =
      ContinuousLinearMap.id Real
        (input.familyIndex.baseFamily.actualOperator parameter).kerᗮ :=
  (DirectContinuation period hPeriod input natural d11Green).unitaryFrame.frameData.transportedReducedOperatorCLM_comp_greenCLM
    d11Green.basepointGreen parameter

/-- Bundled Green followed by bundled reduced operator is identity. -/
theorem greenCLM_comp_reducedOperatorCLM
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (d11Green :
      GlobalHessianPreferredFiveSectorD11UnitaryGreenContinuation4D
        period hPeriod input natural)
    (parameter : Real) :
    (greenCLM period hPeriod input natural d11Green parameter).comp
        (reducedOperatorCLM period hPeriod input natural d11Green parameter) =
      ContinuousLinearMap.id Real
        (input.familyIndex.baseFamily.actualOperator parameter).kerᗮ :=
  (DirectContinuation period hPeriod input natural d11Green).unitaryFrame.frameData.transportedGreenCLM_comp_reducedOperatorCLM
    d11Green.basepointGreen parameter

/-- Uniform operator-norm bound for the bundled Candidate-A Green family. -/
theorem norm_greenCLM_le
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (d11Green :
      GlobalHessianPreferredFiveSectorD11UnitaryGreenContinuation4D
        period hPeriod input natural)
    (parameter : Real) :
    ‖greenCLM period hPeriod input natural d11Green parameter‖ ≤
      ‖d11Green.basepointGreen.green‖ :=
  (DirectContinuation period hPeriod input natural d11Green).unitaryFrame.frameData.norm_transportedGreenCLM_le
    d11Green.basepointGreen parameter

/-- Public bundled Candidate-A Green-family checkpoint. -/
theorem global_hessian_preferred_five_sector_D11_unitary_green_operator_gate
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (d11Green :
      GlobalHessianPreferredFiveSectorD11UnitaryGreenContinuation4D
        period hPeriod input natural) :
    (∀ parameter vector,
      (reducedOperatorCLM period hPeriod input natural d11Green parameter vector).1 =
        input.familyIndex.baseFamily.actualOperator parameter vector.1) ∧
    (∀ parameter,
      (reducedOperatorCLM period hPeriod input natural d11Green parameter).comp
          (greenCLM period hPeriod input natural d11Green parameter) =
        ContinuousLinearMap.id Real
          (input.familyIndex.baseFamily.actualOperator parameter).kerᗮ) ∧
    (∀ parameter,
      (greenCLM period hPeriod input natural d11Green parameter).comp
          (reducedOperatorCLM period hPeriod input natural d11Green parameter) =
        ContinuousLinearMap.id Real
          (input.familyIndex.baseFamily.actualOperator parameter).kerᗮ) ∧
    (∀ parameter,
      ‖greenCLM period hPeriod input natural d11Green parameter‖ ≤
        ‖d11Green.basepointGreen.green‖) :=
  ⟨reducedOperatorCLM_apply_val period hPeriod input natural d11Green,
    reducedOperatorCLM_comp_greenCLM period hPeriod input natural d11Green,
    greenCLM_comp_reducedOperatorCLM period hPeriod input natural d11Green,
    norm_greenCLM_le period hPeriod input natural d11Green⟩

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11UnitaryGreenOperator4D
end JanusFormal
