import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteUnitaryKernelComplementGreenFrame4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorUnitaryFredholmFrame4D

/-!
# Candidate-A reduced Green continuation through the unitary frame

A sector-preserving unitary Candidate-A frame already transports the true
finite kernel and the canonical orthogonal complements.  Supplying the existing
basepoint reduced Green operator now determines the whole reduced Green family
by

```text
G_a = F_a G_0 F_a⁻¹.
```

The transported reduced operator is the genuine `actualOperator a` restricted
to `(ker H_a)ᗮ`; `G_a` is a two-sided inverse and inherits the basepoint norm
bound pointwise.  The same output retains the physical C1 kernel family and C1
complement frame.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorUnitaryGreenContinuation4D

set_option autoImplicit false
set_option maxHeartbeats 116000000
set_option synthInstance.maxHeartbeats 58000000
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

/-- Candidate-A unitary frame and its basepoint reduced Green operator. -/
structure GlobalHessianPreferredFiveSectorUnitaryGreenContinuation4D
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input) where
  unitaryFrame : GlobalHessianPreferredFiveSectorUnitaryAmbientFrame4D
    period hPeriod input natural
  basepointGreen : FiniteKernelComplementBasepointGreenData
    input.familyIndex.baseFamily.actualOperator

namespace GlobalHessianPreferredFiveSectorUnitaryGreenContinuation4D

/-- Physical kernel and C1 unitary complement-frame output. -/
def fredholmFrame
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (continuation : GlobalHessianPreferredFiveSectorUnitaryGreenContinuation4D
      period hPeriod input natural) :
    GlobalHessianPreferredFiveSectorUnitaryFredholmFrameOutput4D
      period hPeriod input :=
  continuation.unitaryFrame.toUnitaryFredholmFrameOutput period hPeriod input
    natural

/-- Genuine reduced operator on one moving orthogonal complement. -/
def reducedOperator
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (continuation : GlobalHessianPreferredFiveSectorUnitaryGreenContinuation4D
      period hPeriod input natural)
    (parameter : Real)
    (vector : (input.familyIndex.baseFamily.actualOperator parameter).kerᗮ) :=
  continuation.unitaryFrame.frameData.transportedReducedOperator
    continuation.basepointGreen parameter vector

/-- Transported reduced Green operator on one moving fibre. -/
def green
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (continuation : GlobalHessianPreferredFiveSectorUnitaryGreenContinuation4D
      period hPeriod input natural)
    (parameter : Real)
    (vector : (input.familyIndex.baseFamily.actualOperator parameter).kerᗮ) :=
  continuation.unitaryFrame.frameData.transportedGreen
    continuation.basepointGreen parameter vector

/-- The transported reduced operator is exactly the genuine Candidate-A
operator on the current reduced fibre. -/
theorem reducedOperator_apply_val
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (continuation : GlobalHessianPreferredFiveSectorUnitaryGreenContinuation4D
      period hPeriod input natural)
    (parameter : Real)
    (vector : (input.familyIndex.baseFamily.actualOperator parameter).kerᗮ) :
    (continuation.reducedOperator period hPeriod input natural parameter vector).1 =
      input.familyIndex.baseFamily.actualOperator parameter vector.1 :=
  continuation.unitaryFrame.frameData.transportedReducedOperator_apply_val
    continuation.basepointGreen parameter vector

/-- The transported Green is a right inverse. -/
theorem reducedOperator_green
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (continuation : GlobalHessianPreferredFiveSectorUnitaryGreenContinuation4D
      period hPeriod input natural)
    (parameter : Real)
    (vector : (input.familyIndex.baseFamily.actualOperator parameter).kerᗮ) :
    continuation.reducedOperator period hPeriod input natural parameter
        (continuation.green period hPeriod input natural parameter vector) =
      vector :=
  continuation.unitaryFrame.frameData.transportedReducedOperator_green
    continuation.basepointGreen parameter vector

/-- The transported Green is a left inverse. -/
theorem green_reducedOperator
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (continuation : GlobalHessianPreferredFiveSectorUnitaryGreenContinuation4D
      period hPeriod input natural)
    (parameter : Real)
    (vector : (input.familyIndex.baseFamily.actualOperator parameter).kerᗮ) :
    continuation.green period hPeriod input natural parameter
        (continuation.reducedOperator period hPeriod input natural parameter
          vector) =
      vector :=
  continuation.unitaryFrame.frameData.transportedGreen_reducedOperator
    continuation.basepointGreen parameter vector

/-- Uniform pointwise bound inherited from the basepoint Green operator. -/
theorem green_norm_le
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (continuation : GlobalHessianPreferredFiveSectorUnitaryGreenContinuation4D
      period hPeriod input natural)
    (parameter : Real)
    (vector : (input.familyIndex.baseFamily.actualOperator parameter).kerᗮ) :
    ‖continuation.green period hPeriod input natural parameter vector‖ ≤
      ‖continuation.basepointGreen.green‖ * ‖vector‖ :=
  continuation.unitaryFrame.frameData.transportedGreen_norm_le
    continuation.basepointGreen parameter vector

/-- Public Candidate-A unitary Green-continuation checkpoint. -/
theorem global_hessian_preferred_five_sector_unitary_green_continuation_gate
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (continuation : GlobalHessianPreferredFiveSectorUnitaryGreenContinuation4D
      period hPeriod input natural) :
    let output := continuation.fredholmFrame period hPeriod input natural
    GlobalHessianPreferredFiveSectorResolvedKernelFamily4D
        period hPeriod output.physical.closure ∧
    GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
        period hPeriod output.physical.closure ∧
    output.physical.closure.familyIndex = input.familyIndex ∧
    (∀ parameter vector,
      (continuation.reducedOperator period hPeriod input natural parameter
        vector).1 =
        input.familyIndex.baseFamily.actualOperator parameter vector.1) ∧
    (∀ parameter vector,
      continuation.reducedOperator period hPeriod input natural parameter
          (continuation.green period hPeriod input natural parameter vector) =
        vector) ∧
    (∀ parameter vector,
      continuation.green period hPeriod input natural parameter
          (continuation.reducedOperator period hPeriod input natural parameter
            vector) =
        vector) ∧
    (∀ parameter vector,
      ‖continuation.green period hPeriod input natural parameter vector‖ ≤
        ‖continuation.basepointGreen.green‖ * ‖vector‖) := by
  dsimp only
  let output := continuation.fredholmFrame period hPeriod input natural
  exact
    ⟨output.physical.resolved,
      output.physical.regularity,
      output.physical.familyIndex_eq,
      continuation.reducedOperator_apply_val period hPeriod input natural,
      continuation.reducedOperator_green period hPeriod input natural,
      continuation.green_reducedOperator period hPeriod input natural,
      continuation.green_norm_le period hPeriod input natural⟩

end GlobalHessianPreferredFiveSectorUnitaryGreenContinuation4D

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorUnitaryGreenContinuation4D
end JanusFormal