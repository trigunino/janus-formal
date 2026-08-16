import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14BasepointFredholmGreenAdapter4D

/-!
# Concrete H14--D11 unitary Fredholm--Green closure

The generic unitary Fredholm--Green continuation no longer needs separately
supplied basepoint analytic packets.  The preferred H14 closure already contains
its genuine actual-kernel gap, canonical reduced Green operator and inverse-gap
norm estimate.  The basepoint adapter identifies those data with the literal
zero fibre of the selected D11 family.

Consequently a unitary represented D11 admissible-isomorphism frame is now the
only family-geometric input needed to obtain, from the existing H14 endpoint,

* a globally sector-resolved C1 basis of the true kernels;
* a C1 unitary trivialization of the true orthogonal kernel complements;
* the unchanged H14 gap at every parameter;
* bundled two-sided reduced Green operators;
* the uniform inverse-gap Green bound;
* exact constancy of the Green family in the unitary frame.

No second operator, Green, gap, completion or family-index datum is introduced.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11UnitaryFredholmGreenClosure4D

set_option autoImplicit false
set_option maxHeartbeats 144000000
set_option synthInstance.maxHeartbeats 72000000
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
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorResolvedKernelFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11UnitaryAdmissibleIsomorphismFrame4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11UnitaryFredholmGreenClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14BasepointFredholmGreenAdapter4D
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

/-- The complete continuation structure obtained from the concrete H14
basepoint and one unitary D11 frame. -/
def concreteH14D11UnitaryFredholmGreenClosure
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (d11Unitary :
      GlobalHessianPreferredFiveSectorD11UnitaryAdmissibleIsomorphismFrame4D
        period hPeriod input natural) :
    GlobalHessianPreferredFiveSectorD11UnitaryFredholmGreenClosure4D
      period hPeriod input natural :=
  toD11UnitaryFredholmGreenClosure period hPeriod input natural d11Unitary

/-- The family gap is literally the H14 basepoint gap, not a newly selected
constant. -/
@[simp]
theorem concreteH14D11UnitaryFredholmGreenClosure_gap
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (d11Unitary :
      GlobalHessianPreferredFiveSectorD11UnitaryAdmissibleIsomorphismFrame4D
        period hPeriod input natural) :
    (concreteH14D11UnitaryFredholmGreenClosure period hPeriod input natural
      d11Unitary).basepointGap.gap =
      (input.familyIndex.baseFamily.quillen.intrinsicFamily.basepoint.intrinsic.
        closure.frontier.analytic.toActualKernelGap).gapData.gap :=
  rfl

/-- Terminal concrete H14--D11 continuation checkpoint. -/
theorem global_hessian_preferred_five_sector_H14_D11_unitary_fredholm_green_closure_gate
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (d11Unitary :
      GlobalHessianPreferredFiveSectorD11UnitaryAdmissibleIsomorphismFrame4D
        period hPeriod input natural) :
    let closure :=
      concreteH14D11UnitaryFredholmGreenClosure period hPeriod input natural
        d11Unitary
    let output := closure.fredholmFrame period hPeriod input natural
    GlobalHessianPreferredFiveSectorResolvedKernelFamily4D
        period hPeriod output.physical.closure ∧
    GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
        period hPeriod output.physical.closure ∧
    output.physical.closure.familyIndex = input.familyIndex ∧
    (∀ parameter vector,
      vector ∈ (input.familyIndex.baseFamily.actualOperator parameter).kerᗮ →
        closure.basepointGap.gap * ‖vector‖ ≤
          ‖input.familyIndex.baseFamily.actualOperator parameter vector‖) ∧
    (∀ parameter,
      (closure.reducedOperatorCLM period hPeriod input natural parameter).comp
          (closure.greenCLM period hPeriod input natural parameter) =
        ContinuousLinearMap.id Real
          (input.familyIndex.baseFamily.actualOperator parameter).kerᗮ) ∧
    (∀ parameter,
      (closure.greenCLM period hPeriod input natural parameter).comp
          (closure.reducedOperatorCLM period hPeriod input natural parameter) =
        ContinuousLinearMap.id Real
          (input.familyIndex.baseFamily.actualOperator parameter).kerᗮ) ∧
    (∀ parameter,
      ‖closure.greenCLM period hPeriod input natural parameter‖ ≤
        closure.basepointGap.gap⁻¹) ∧
    (∀ parameter vector,
      P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11UnitaryGreenTrivialization4D.
          trivializedGreen period hPeriod input natural
            (closure.greenContinuation period hPeriod input natural) parameter
            vector = closure.basepointGreen.green vector) ∧
    (∀ vector,
      Differentiable Real
        (fun parameter : Real =>
          (output.complementTransport 0 parameter vector).1)) := by
  dsimp only
  exact
    global_hessian_preferred_five_sector_D11_unitary_fredholm_green_closure_gate
      period hPeriod input natural
        (concreteH14D11UnitaryFredholmGreenClosure period hPeriod input natural
          d11Unitary)

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11UnitaryFredholmGreenClosure4D
end JanusFormal
