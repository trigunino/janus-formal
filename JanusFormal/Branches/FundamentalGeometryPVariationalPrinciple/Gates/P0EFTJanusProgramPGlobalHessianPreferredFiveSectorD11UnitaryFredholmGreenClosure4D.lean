import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11UnitaryGreenOperator4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11UnitaryGreenTrivialization4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorUnitaryGapContinuation4D

/-!
# Terminal D11 unitary Fredholm--Green closure

This layer assembles the complete geometric Fredholm continuation packet for the
preferred Candidate-A family from three basepoint ingredients:

* a unitary represented D11 admissible-isomorphism frame;
* the genuine H12 reduced Green operator;
* the genuine H12 reduced norm gap.

The Green norm is required once to be bounded by the inverse basepoint gap.  All
family-level consequences are then derived:

* globally sector-pure C1 actual-kernel basis;
* C1 unitary trivialization of `(ker H_a)ᗮ`;
* the same uniform reduced gap at every parameter;
* bundled two-sided reduced Green operators;
* uniform Green operator norm bound by `gap⁻¹`;
* exact constancy of reduced and Green operators in the D11 unitary frame.

The family-index, relative heat, zeta and spectral-cut structures are inherited
unchanged from the original Candidate-A family closure.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11UnitaryFredholmGreenClosure4D

set_option autoImplicit false
set_option maxHeartbeats 132000000
set_option synthInstance.maxHeartbeats 66000000
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
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalLocalActionFamilyH10Reduction4D
open P0EFTJanusProgramPGlobalCandidateACanonicalSixDenseCore4D
open P0EFTJanusProgramPFiniteUnitaryKernelComplementGapTransport4D
open P0EFTJanusProgramPFiniteUnitaryKernelComplementGreenFrame4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorResolvedKernelFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11UnitaryAdmissibleIsomorphismFrame4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11UnitaryGreenContinuation4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11UnitaryGreenOperator4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11UnitaryGreenTrivialization4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorUnitaryGapContinuation4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorUnitaryFredholmFrame4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorPhysicalKernelContinuation4D
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

/-- Complete unitary D11 Fredholm--Green continuation datum. -/
structure GlobalHessianPreferredFiveSectorD11UnitaryFredholmGreenClosure4D
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input) where
  d11Unitary :
    GlobalHessianPreferredFiveSectorD11UnitaryAdmissibleIsomorphismFrame4D
      period hPeriod input natural
  basepointGreen : FiniteKernelComplementBasepointGreenData
    input.familyIndex.baseFamily.actualOperator
  basepointGap : FiniteKernelComplementBasepointNormGapData
    input.familyIndex.baseFamily.actualOperator
  green_norm_le_gap_inv :
    ‖basepointGreen.green‖ ≤ basepointGap.gap⁻¹

namespace GlobalHessianPreferredFiveSectorD11UnitaryFredholmGreenClosure4D

/-- Direct D11 unitary Green continuation. -/
def greenContinuation
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (closure : GlobalHessianPreferredFiveSectorD11UnitaryFredholmGreenClosure4D
      period hPeriod input natural) :
    GlobalHessianPreferredFiveSectorD11UnitaryGreenContinuation4D
      period hPeriod input natural where
  d11Unitary := closure.d11Unitary
  basepointGreen := closure.basepointGreen

/-- Direct unitary gap continuation using the same D11 frame. -/
def gapContinuation
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (closure : GlobalHessianPreferredFiveSectorD11UnitaryFredholmGreenClosure4D
      period hPeriod input natural) :
    GlobalHessianPreferredFiveSectorUnitaryGapContinuation4D
      period hPeriod input natural where
  unitaryFrame :=
    closure.d11Unitary.toUnitaryAmbientFrame period hPeriod input natural
  basepointGap := closure.basepointGap

/-- Route-independent physical kernel and complement frame. -/
def fredholmFrame
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (closure : GlobalHessianPreferredFiveSectorD11UnitaryFredholmGreenClosure4D
      period hPeriod input natural) :
    GlobalHessianPreferredFiveSectorUnitaryFredholmFrameOutput4D
      period hPeriod input :=
  (closure.greenContinuation period hPeriod input natural).fredholmFrame period
    hPeriod input natural

/-- Bundled genuine reduced operator on one moving fibre. -/
def reducedOperatorCLM
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (closure : GlobalHessianPreferredFiveSectorD11UnitaryFredholmGreenClosure4D
      period hPeriod input natural)
    (parameter : Real) :=
  P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11UnitaryGreenOperator4D.
    reducedOperatorCLM period hPeriod input natural
      (closure.greenContinuation period hPeriod input natural) parameter

/-- Bundled reduced Green on one moving fibre. -/
def greenCLM
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (closure : GlobalHessianPreferredFiveSectorD11UnitaryFredholmGreenClosure4D
      period hPeriod input natural)
    (parameter : Real) :=
  P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11UnitaryGreenOperator4D.
    greenCLM period hPeriod input natural
      (closure.greenContinuation period hPeriod input natural) parameter

/-- Uniform reduced gap on every current canonical complement. -/
theorem global_norm_gap
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (closure : GlobalHessianPreferredFiveSectorD11UnitaryFredholmGreenClosure4D
      period hPeriod input natural)
    (parameter : Real)
    (vector : GlobalCandidateAFaithfulSameActionHilbert period hPeriod
      configuration data analysis)
    (hVector : vector ∈
      (input.familyIndex.baseFamily.actualOperator parameter).kerᗮ) :
    closure.basepointGap.gap * ‖vector‖ ≤
      ‖input.familyIndex.baseFamily.actualOperator parameter vector‖ :=
  (closure.gapContinuation period hPeriod input natural).global_norm_gap period
    hPeriod input natural parameter vector hVector

/-- Every reduced Green operator has norm at most the inverse uniform gap. -/
theorem norm_greenCLM_le_gap_inv
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (closure : GlobalHessianPreferredFiveSectorD11UnitaryFredholmGreenClosure4D
      period hPeriod input natural)
    (parameter : Real) :
    ‖closure.greenCLM period hPeriod input natural parameter‖ ≤
      closure.basepointGap.gap⁻¹ :=
  le_trans
    (P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11UnitaryGreenOperator4D.
      norm_greenCLM_le period hPeriod input natural
        (closure.greenContinuation period hPeriod input natural) parameter)
    closure.green_norm_le_gap_inv

/-- Exact fixed-coordinate reduced-operator identity. -/
theorem trivializedReducedOperator_eq_basepoint
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (closure : GlobalHessianPreferredFiveSectorD11UnitaryFredholmGreenClosure4D
      period hPeriod input natural)
    (parameter : Real)
    (vector : (input.familyIndex.baseFamily.actualOperator 0).kerᗮ) :
    P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11UnitaryGreenTrivialization4D.
        trivializedReducedOperator period hPeriod input natural
          (closure.greenContinuation period hPeriod input natural) parameter vector =
      closure.basepointGreen.reducedOperator vector :=
  P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11UnitaryGreenTrivialization4D.
    trivializedReducedOperator_eq_basepoint period hPeriod input natural
      (closure.greenContinuation period hPeriod input natural) parameter vector

/-- Exact fixed-coordinate Green identity. -/
theorem trivializedGreen_eq_basepoint
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (closure : GlobalHessianPreferredFiveSectorD11UnitaryFredholmGreenClosure4D
      period hPeriod input natural)
    (parameter : Real)
    (vector : (input.familyIndex.baseFamily.actualOperator 0).kerᗮ) :
    P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11UnitaryGreenTrivialization4D.
        trivializedGreen period hPeriod input natural
          (closure.greenContinuation period hPeriod input natural) parameter vector =
      closure.basepointGreen.green vector :=
  P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11UnitaryGreenTrivialization4D.
    trivializedGreen_eq_basepoint period hPeriod input natural
      (closure.greenContinuation period hPeriod input natural) parameter vector

/-- Public terminal D11 Fredholm--Green checkpoint. -/
theorem global_hessian_preferred_five_sector_D11_unitary_fredholm_green_closure_gate
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (closure : GlobalHessianPreferredFiveSectorD11UnitaryFredholmGreenClosure4D
      period hPeriod input natural) :
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
  let output := closure.fredholmFrame period hPeriod input natural
  let greenContinuation := closure.greenContinuation period hPeriod input natural
  exact
    ⟨output.physical.resolved,
      output.physical.regularity,
      output.physical.familyIndex_eq,
      closure.global_norm_gap period hPeriod input natural,
      P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11UnitaryGreenOperator4D.
        reducedOperatorCLM_comp_greenCLM period hPeriod input natural
          greenContinuation,
      P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11UnitaryGreenOperator4D.
        greenCLM_comp_reducedOperatorCLM period hPeriod input natural
          greenContinuation,
      closure.norm_greenCLM_le_gap_inv period hPeriod input natural,
      closure.trivializedGreen_eq_basepoint period hPeriod input natural,
      output.complement_vector_differentiable⟩

end GlobalHessianPreferredFiveSectorD11UnitaryFredholmGreenClosure4D

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11UnitaryFredholmGreenClosure4D
end JanusFormal