import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPDifferentiableFredholmSplittingFamily4D

/-!
# C1 Fredholm splitting of the preferred Candidate-A family

This layer combines the differentiable named physical zero modes with C1
regularity of the already existing unitary trivialization of the genuine
kernel complements.  The operator, self-adjointness proof and complement
trivialization are exactly those of the Candidate-A Bismut--Freed family.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorDifferentiableFredholmSplitting4D

set_option autoImplicit false
set_option maxHeartbeats 30000000
set_option synthInstance.maxHeartbeats 15000000

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
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
open P0EFTJanusProgramPDifferentiableKernelComplementTrivialization4D
open P0EFTJanusProgramPDifferentiableFredholmSplittingFamily4D
open P0EFTJanusProgramPDenseCoreChartBilinearBound4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)

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

/-- Exact C1 regularity inputs for both pieces of the preferred Candidate-A
Fredholm splitting. -/
structure GlobalHessianPreferredFiveSectorDifferentiableFredholmSplitting4D
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index) : Prop where
  kernels :
    GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
      period hPeriod input
  complement :
    DifferentiableKernelComplementTrivializationData
      input.familyIndex.baseFamily.familyIndex.actualGap.trivialization

namespace GlobalHessianPreferredFiveSectorDifferentiableFredholmSplitting4D

/-- Forget to the generic C1 Fredholm splitting packet. -/
def toDifferentiableFredholmSplitting
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (regularity : GlobalHessianPreferredFiveSectorDifferentiableFredholmSplitting4D
      period hPeriod input) :
    DifferentiableFredholmSplittingFamilyData
      input.familyIndex.baseFamily.actualOperator ZeroMode where
  selfAdjoint := input.familyIndex.baseFamily.familyIndex.actual_selfAdjoint
  kernels := regularity.kernels.toDifferentiableKernelFamily period hPeriod input
  complementTrivialization :=
    input.familyIndex.baseFamily.familyIndex.actualGap.trivialization
  complementRegularity := regularity.complement

/-- Public preferred Candidate-A C1 Fredholm splitting checkpoint. -/
theorem global_hessian_preferred_five_sector_differentiable_fredholm_splitting_gate
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (regularity : GlobalHessianPreferredFiveSectorDifferentiableFredholmSplitting4D
      period hPeriod input) :
    (∀ mode,
      Differentiable Real
        (fun parameter : Real => input.kernels.vector parameter mode)) ∧
    (∀ vector : P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D.
        SelfAdjointKernelComplement
          (input.familyIndex.baseFamily.actualOperator 0),
      Differentiable Real
        (fun parameter : Real =>
          ((input.familyIndex.baseFamily.familyIndex.actualGap.trivialization.
              transport parameter vector :
            P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D.
              SelfAdjointKernelComplement
                (input.familyIndex.baseFamily.actualOperator parameter)) :
            GlobalCandidateAFaithfulSameActionHilbert
              period hPeriod configuration data analysis))) := by
  let splitting := regularity.toDifferentiableFredholmSplitting period hPeriod input
  exact ⟨splitting.kernelVector_differentiable,
    splitting.complementVector_differentiable⟩

end GlobalHessianPreferredFiveSectorDifferentiableFredholmSplitting4D

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorDifferentiableFredholmSplitting4D
end JanusFormal
