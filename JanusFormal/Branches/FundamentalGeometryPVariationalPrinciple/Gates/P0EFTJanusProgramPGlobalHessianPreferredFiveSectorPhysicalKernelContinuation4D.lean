import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelCanonicalLeakage4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelTransportCommutation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11LinearPullbackTransport4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorPhysicalKernelContinuationOutput4D

/-!
# Unified physical-kernel continuation output

There are now several mathematically distinct ways to continue the exact H12
physical zero modes through the Candidate-A family:

* prove global noncrossing of the projected Gram family;
* prove a canonically conditioned projection-leakage estimate;
* prove that the already selected named-kernel transport commutes with the
  physical kernel projectors;
* construct coherent linear D11 pullback isomorphisms.

All routes should feed the same downstream Fredholm--zeta architecture.  This
file defines one terminal output containing

* a named-kernel family closure with the original family-index data;
* a genuinely sector-resolved basis of every actual kernel;
* C1 dependence in the common ambient Candidate-A Hilbert space;
* exact agreement with the original H12 basis.

Constructors from each continuation route are provided.  Thus downstream files
need not depend on which global proof was used.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorPhysicalKernelContinuation4D

set_option autoImplicit false
set_option maxHeartbeats 92000000
set_option synthInstance.maxHeartbeats 46000000
noncomputable section

open Set Filter Topology MeasureTheory
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
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorBismutFreedFamily4D
open P0EFTJanusProgramPGlobalCandidateAFiveSectorCompletionResolutionBridge4D
open P0EFTJanusProgramPFiniteKernelBasisFamily4D
open P0EFTJanusProgramPFiveSectorHilbertCoordinates4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorRepresentation4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorResolvedKernelFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorResolvedKernelFamily4D.GlobalHessianPreferredFiveSectorResolvedKernelFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedResolvedKernelFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelRegularChart4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedPhysicalNamedKernelFamilyClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelCanonicalLeakage4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelTransportCommutation4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11LinearPullbackTransport4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorSectorPreservingKernelTransport4D
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
local instance effectiveQuotientChartedSpaceMain :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance effectiveQuotientIsManifoldMain :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance effectiveQuotientMeasurableSpaceMain :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _
local instance effectiveQuotientBorelSpaceMain :
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

namespace GlobalHessianPreferredFiveSectorPhysicalKernelContinuationOutput4D

/-- The continued physical family still uses the literal original actual
operator family. -/
theorem actualOperator_eq
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (output : GlobalHessianPreferredFiveSectorPhysicalKernelContinuationOutput4D
      period hPeriod input)
    (parameter : Real) :
    output.closure.familyIndex.baseFamily.actualOperator parameter =
      input.familyIndex.baseFamily.actualOperator parameter := by
  rw [output.familyIndex_eq]

/-- Exact H12 action-generator identification is retained. -/
theorem vector_zero_eq_actionGenerator
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (output : GlobalHessianPreferredFiveSectorPhysicalKernelContinuationOutput4D
      period hPeriod input)
    (mode : ZeroMode) :
    output.closure.kernels.vector 0 mode =
      input.familyIndex.baseFamily.quillen.intrinsicFamily.basepoint.intrinsic.closure.frontier.generators.translations.vector
        mode := by
  rw [output.basis_zero_agreement mode]
  exact input.vector_zero_eq_actionGenerator period hPeriod mode

/-- Every continued named vector lies in the true actual kernel and its assigned
physical sector. -/
theorem vector_mem_sectorKernel
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (output : GlobalHessianPreferredFiveSectorPhysicalKernelContinuationOutput4D
      period hPeriod input)
    (parameter : Real) (mode : ZeroMode) :
    output.closure.kernels.vector parameter mode ∈
      sectorKernel period hPeriod output.closure parameter
        (namedModeFiveSector period hPeriod output.closure mode) :=
  output.resolved.vector_mem_sectorKernel period hPeriod output.closure parameter
    mode

/-- Public route-independent physical-kernel output checkpoint. -/
theorem physical_kernel_continuation_output_gate
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (output : GlobalHessianPreferredFiveSectorPhysicalKernelContinuationOutput4D
      period hPeriod input) :
    output.closure.familyIndex = input.familyIndex ∧
    GlobalHessianPreferredFiveSectorResolvedKernelFamily4D
      period hPeriod output.closure ∧
    GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
      period hPeriod output.closure ∧
    (∀ parameter mode,
      output.closure.kernels.vector parameter mode ∈
        sectorKernel period hPeriod output.closure parameter
          (namedModeFiveSector period hPeriod output.closure mode)) ∧
    (∀ mode,
      output.closure.kernels.vector 0 mode =
        input.familyIndex.baseFamily.quillen.intrinsicFamily.basepoint.intrinsic.closure.frontier.generators.translations.vector
          mode) :=
  ⟨output.familyIndex_eq,
    output.resolved,
    output.regularity,
    output.vector_mem_sectorKernel period hPeriod input,
    output.vector_zero_eq_actionGenerator period hPeriod input⟩

end GlobalHessianPreferredFiveSectorPhysicalKernelContinuationOutput4D

/-- The projected-Gram route gives the unified continuation output. -/
def physicalKernelContinuationOfRegularSetEqUniv
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (regularity : GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
      period hPeriod input)
    (hRegular : projectedKernelRegularSet period hPeriod input = Set.univ) :
    GlobalHessianPreferredFiveSectorPhysicalKernelContinuationOutput4D
      period hPeriod input := by
  let physicalClosure :=
    projectedPhysicalNamedKernelFamilyClosure period hPeriod input natural hRegular
  refine
    { closure := physicalClosure
      familyIndex_eq :=
        projectedPhysicalNamedKernelFamilyClosure_familyIndex period hPeriod input
          natural hRegular
      resolved := ?_
      regularity :=
        projectedPhysicalNamedKernelFamilyRegularity period hPeriod input natural
          regularity hRegular
      basis_zero_agreement := ?_ }
  · refine
      { basis_fixed_by_sector := ?_ }
    intro parameter mode
    change
      (preferredCandidateAFiveSectorHilbertCoordinates period hPeriod input).sectorProjector
          (namedModeFiveSector period hPeriod input mode)
          (physicalClosure.kernels.vector parameter mode) =
        physicalClosure.kernels.vector parameter mode
    rw [projectedPhysicalNamedKernelFamilyClosure_vector period hPeriod input
      natural hRegular]
    exact projectedNamedKernelVector_fixed_by_sector period hPeriod input parameter
      mode
  · intro mode
    rw [projectedPhysicalNamedKernelFamilyClosure_vector period hPeriod input
      natural hRegular]
    exact projectedNamedKernelVector_zero period hPeriod input mode

/-- Canonically conditioned projection leakage gives the unified continuation
output through the projected-Gram route. -/
def physicalKernelContinuationOfCanonicalLeakage
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (regularity : GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
      period hPeriod input)
    (leakage :
      GlobalHessianPreferredFiveSectorProjectedKernelCanonicalLeakage4D
        period hPeriod input) :
    GlobalHessianPreferredFiveSectorPhysicalKernelContinuationOutput4D
      period hPeriod input :=
  physicalKernelContinuationOfRegularSetEqUniv period hPeriod input natural
    regularity (leakage.regularSet_eq_univ period hPeriod input)

/-- Coherent linear D11 pullback isomorphisms give the unified continuation
output through direct transport of the H12 basis. -/
def physicalKernelContinuationOfD11LinearPullback
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (d11Transport :
      GlobalHessianPreferredFiveSectorD11LinearPullbackTransport4D
        period hPeriod input natural) :
    GlobalHessianPreferredFiveSectorPhysicalKernelContinuationOutput4D
      period hPeriod input := by
  let kernelTransport :=
    d11Transport.toSectorPreservingKernelTransport period hPeriod input natural
  let physicalClosure :=
    d11Transport.physicalNamedKernelFamilyClosure period hPeriod input natural
  refine
    { closure := physicalClosure
      familyIndex_eq := rfl
      resolved := d11Transport.physicalResolvedKernelFamily period hPeriod input
        natural
      regularity := d11Transport.physicalRegularity period hPeriod input natural
      basis_zero_agreement := ?_ }
  intro mode
  change
    ((kernelTransport.physicalKernels period hPeriod input natural).basis 0 mode).1 =
      (input.kernels.basis 0 mode).1
  have hBasisZero :=
    kernelTransport.physicalKernels_basis_zero period hPeriod input natural
  exact congrArg (fun basis => (basis mode).1) hBasisZero

/-- If the already selected named-kernel coordinate transport commutes with the
physical projectors, the original closure itself is the unified output. -/
def physicalKernelContinuationOfNamedTransportCommutation
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (regularity : GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
      period hPeriod input)
    (commutation :
      GlobalHessianPreferredFiveSectorNamedKernelTransportCommutation4D
        period hPeriod input natural) :
    GlobalHessianPreferredFiveSectorPhysicalKernelContinuationOutput4D
      period hPeriod input where
  closure := input
  familyIndex_eq := rfl
  resolved := commutation.toResolvedKernelFamily period hPeriod input natural
  regularity := regularity
  basis_zero_agreement := fun _ => rfl

/-- Public multi-route construction checkpoint. -/
theorem physical_kernel_continuation_routes_gate
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (regularity : GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
      period hPeriod input) :
    (projectedKernelRegularSet period hPeriod input = Set.univ →
      Nonempty
        (GlobalHessianPreferredFiveSectorPhysicalKernelContinuationOutput4D
          period hPeriod input)) ∧
    (GlobalHessianPreferredFiveSectorProjectedKernelCanonicalLeakage4D
        period hPeriod input →
      Nonempty
        (GlobalHessianPreferredFiveSectorPhysicalKernelContinuationOutput4D
          period hPeriod input)) ∧
    (GlobalHessianPreferredFiveSectorD11LinearPullbackTransport4D
        period hPeriod input natural →
      Nonempty
        (GlobalHessianPreferredFiveSectorPhysicalKernelContinuationOutput4D
          period hPeriod input)) ∧
    (GlobalHessianPreferredFiveSectorNamedKernelTransportCommutation4D
        period hPeriod input natural →
      Nonempty
        (GlobalHessianPreferredFiveSectorPhysicalKernelContinuationOutput4D
          period hPeriod input)) :=
  ⟨fun hRegular =>
      ⟨physicalKernelContinuationOfRegularSetEqUniv period hPeriod input natural
        regularity hRegular⟩,
    fun leakage =>
      ⟨physicalKernelContinuationOfCanonicalLeakage period hPeriod input natural
        regularity leakage⟩,
    fun d11Transport =>
      ⟨physicalKernelContinuationOfD11LinearPullback period hPeriod input natural
        d11Transport⟩,
    fun commutation =>
      ⟨physicalKernelContinuationOfNamedTransportCommutation period hPeriod input
        natural regularity commutation⟩⟩

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorPhysicalKernelContinuation4D
end JanusFormal
