import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11UnitaryAdmissibleIsomorphismFrame4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorUnitaryGreenContinuation4D

/-!
# Candidate-A Green continuation from unitary D11 pullbacks

This terminal D11 layer combines

* the represented admissible-isomorphism unitary frame;
* C1 transport of the H12 kernel and complement vectors;
* the existing basepoint reduced Green operator.

It produces the globally sector-pure physical kernel family, the C1 unitary
trivialization of `(ker H_a)ᗮ`, and the transported two-sided Green family for
the genuine Candidate-A operator.  All fibres keep the original family-index,
heat, zeta and spectral-cut data.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11UnitaryGreenContinuation4D

set_option autoImplicit false
set_option maxHeartbeats 122000000
set_option synthInstance.maxHeartbeats 61000000
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
open P0EFTJanusProgramPFiniteUnitaryKernelComplementGreenFrame4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorResolvedKernelFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11UnitaryAdmissibleIsomorphismFrame4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorUnitaryGreenContinuation4D
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

/-- Unitary D11 frame and the existing basepoint Candidate-A reduced Green
operator. -/
structure GlobalHessianPreferredFiveSectorD11UnitaryGreenContinuation4D
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

namespace GlobalHessianPreferredFiveSectorD11UnitaryGreenContinuation4D

/-- Adapter to the direct Candidate-A unitary Green continuation. -/
def toUnitaryGreenContinuation
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (d11Green :
      GlobalHessianPreferredFiveSectorD11UnitaryGreenContinuation4D
        period hPeriod input natural) :
    GlobalHessianPreferredFiveSectorUnitaryGreenContinuation4D
      period hPeriod input natural where
  unitaryFrame :=
    d11Green.d11Unitary.toUnitaryAmbientFrame period hPeriod input natural
  basepointGreen := d11Green.basepointGreen

/-- Physical kernel and C1 unitary complement-frame output. -/
def fredholmFrame
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (d11Green :
      GlobalHessianPreferredFiveSectorD11UnitaryGreenContinuation4D
        period hPeriod input natural) :
    GlobalHessianPreferredFiveSectorUnitaryFredholmFrameOutput4D
      period hPeriod input :=
  (d11Green.toUnitaryGreenContinuation period hPeriod input natural).
    fredholmFrame period hPeriod input natural

/-- Transported reduced Green on one current fibre. -/
def green
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (d11Green :
      GlobalHessianPreferredFiveSectorD11UnitaryGreenContinuation4D
        period hPeriod input natural)
    (parameter : Real)
    (vector : (input.familyIndex.baseFamily.actualOperator parameter).kerᗮ) :=
  (d11Green.toUnitaryGreenContinuation period hPeriod input natural).green
    period hPeriod input natural parameter vector

/-- Genuine reduced operator on one current fibre. -/
def reducedOperator
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (d11Green :
      GlobalHessianPreferredFiveSectorD11UnitaryGreenContinuation4D
        period hPeriod input natural)
    (parameter : Real)
    (vector : (input.familyIndex.baseFamily.actualOperator parameter).kerᗮ) :=
  (d11Green.toUnitaryGreenContinuation period hPeriod input natural).
    reducedOperator period hPeriod input natural parameter vector

/-- Public terminal D11 unitary Green-continuation checkpoint. -/
theorem global_hessian_preferred_five_sector_D11_unitary_green_continuation_gate
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (d11Green :
      GlobalHessianPreferredFiveSectorD11UnitaryGreenContinuation4D
        period hPeriod input natural) :
    let direct :=
      d11Green.toUnitaryGreenContinuation period hPeriod input natural
    let output := d11Green.fredholmFrame period hPeriod input natural
    GlobalHessianPreferredFiveSectorResolvedKernelFamily4D
        period hPeriod output.physical.closure ∧
    GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
        period hPeriod output.physical.closure ∧
    output.physical.closure.familyIndex = input.familyIndex ∧
    (∀ parameter vector,
      (d11Green.reducedOperator period hPeriod input natural parameter vector).1 =
        input.familyIndex.baseFamily.actualOperator parameter vector.1) ∧
    (∀ parameter vector,
      d11Green.reducedOperator period hPeriod input natural parameter
          (d11Green.green period hPeriod input natural parameter vector) =
        vector) ∧
    (∀ parameter vector,
      d11Green.green period hPeriod input natural parameter
          (d11Green.reducedOperator period hPeriod input natural parameter
            vector) =
        vector) ∧
    (∀ parameter vector,
      ‖d11Green.green period hPeriod input natural parameter vector‖ ≤
        ‖d11Green.basepointGreen.green‖ * ‖vector‖) ∧
    (∀ vector,
      Differentiable Real
        (fun parameter : Real =>
          (output.complementTransport 0 parameter vector).1)) := by
  dsimp only
  let direct :=
    d11Green.toUnitaryGreenContinuation period hPeriod input natural
  let output := d11Green.fredholmFrame period hPeriod input natural
  exact
    ⟨output.physical.resolved,
      output.physical.regularity,
      output.physical.familyIndex_eq,
      direct.reducedOperator_apply_val period hPeriod input natural,
      direct.reducedOperator_green period hPeriod input natural,
      direct.green_reducedOperator period hPeriod input natural,
      direct.green_norm_le period hPeriod input natural,
      output.complement_vector_differentiable⟩

end GlobalHessianPreferredFiveSectorD11UnitaryGreenContinuation4D

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11UnitaryGreenContinuation4D
end JanusFormal