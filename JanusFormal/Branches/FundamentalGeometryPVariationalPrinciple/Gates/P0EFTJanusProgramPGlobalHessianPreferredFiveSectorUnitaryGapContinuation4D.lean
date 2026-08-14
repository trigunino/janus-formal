import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteUnitaryKernelComplementGapTransport4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorUnitaryFredholmFrame4D

/-!
# Uniform Candidate-A gap from the unitary Fredholm frame

Once the preferred Candidate-A family is trivialized by one sector-preserving
unitary frame, a basepoint norm gap on `(ker H_0)ᗮ` propagates to every
parameter with exactly the same constant.  This file combines that spectral
fact with the physical-kernel/C1-complement output.

It does not introduce a new reduced operator: all estimates are stated for the
same genuine `actualOperator a` and its canonical orthogonal kernel complement.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorUnitaryGapContinuation4D

set_option autoImplicit false
set_option maxHeartbeats 108000000
set_option synthInstance.maxHeartbeats 54000000
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
open P0EFTJanusProgramPFiniteUnitaryKernelComplementGapTransport4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorResolvedKernelFamily4D
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

/-- Unitary Candidate-A frame together with one basepoint norm gap. -/
structure GlobalHessianPreferredFiveSectorUnitaryGapContinuation4D
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input) where
  unitaryFrame : GlobalHessianPreferredFiveSectorUnitaryAmbientFrame4D
    period hPeriod input natural
  basepointGap : FiniteKernelComplementBasepointNormGapData
    input.familyIndex.baseFamily.actualOperator

namespace GlobalHessianPreferredFiveSectorUnitaryGapContinuation4D

/-- C1 physical-kernel and complement frame output. -/
def fredholmFrame
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (continuation : GlobalHessianPreferredFiveSectorUnitaryGapContinuation4D
      period hPeriod input natural) :
    GlobalHessianPreferredFiveSectorUnitaryFredholmFrameOutput4D
      period hPeriod input :=
  continuation.unitaryFrame.toUnitaryFredholmFrameOutput period hPeriod input
    natural

/-- The same gap constant controls every true orthogonal kernel complement. -/
theorem global_norm_gap
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (continuation : GlobalHessianPreferredFiveSectorUnitaryGapContinuation4D
      period hPeriod input natural)
    (parameter : Real) (vector :
      GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration data
        analysis)
    (hVector : vector ∈
      (input.familyIndex.baseFamily.actualOperator parameter).kerᗮ) :
    continuation.basepointGap.gap * ‖vector‖ ≤
      ‖input.familyIndex.baseFamily.actualOperator parameter vector‖ :=
  continuation.unitaryFrame.frameData.kernelComplement_norm_gap
    continuation.basepointGap parameter vector hVector

/-- Every actual operator is injective on its canonical reduced fibre. -/
theorem reduced_injective
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (continuation : GlobalHessianPreferredFiveSectorUnitaryGapContinuation4D
      period hPeriod input natural)
    (parameter : Real) :
    Function.Injective
      (fun vector :
          (input.familyIndex.baseFamily.actualOperator parameter).kerᗮ =>
        input.familyIndex.baseFamily.actualOperator parameter vector.1) :=
  continuation.unitaryFrame.frameData.kernelComplement_operator_injective
    continuation.basepointGap parameter

/-- Public uniform-gap continuation checkpoint. -/
theorem global_hessian_preferred_five_sector_unitary_gap_continuation_gate
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (continuation : GlobalHessianPreferredFiveSectorUnitaryGapContinuation4D
      period hPeriod input natural) :
    let output := continuation.fredholmFrame period hPeriod input natural
    GlobalHessianPreferredFiveSectorResolvedKernelFamily4D
        period hPeriod output.physical.closure ∧
    GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
        period hPeriod output.physical.closure ∧
    output.physical.closure.familyIndex = input.familyIndex ∧
    (∀ parameter vector,
      vector ∈ (input.familyIndex.baseFamily.actualOperator parameter).kerᗮ →
        continuation.basepointGap.gap * ‖vector‖ ≤
          ‖input.familyIndex.baseFamily.actualOperator parameter vector‖) ∧
    (∀ parameter,
      Function.Injective
        (fun vector :
            (input.familyIndex.baseFamily.actualOperator parameter).kerᗮ =>
          input.familyIndex.baseFamily.actualOperator parameter vector.1)) ∧
    (∀ vector,
      Differentiable Real
        (fun parameter : Real =>
          (output.complementTransport 0 parameter vector).1)) := by
  dsimp only
  let output := continuation.fredholmFrame period hPeriod input natural
  exact
    ⟨output.physical.resolved,
      output.physical.regularity,
      output.physical.familyIndex_eq,
      continuation.global_norm_gap period hPeriod input natural,
      continuation.reduced_injective period hPeriod input natural,
      output.complement_vector_differentiable⟩

end GlobalHessianPreferredFiveSectorUnitaryGapContinuation4D

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorUnitaryGapContinuation4D
end JanusFormal