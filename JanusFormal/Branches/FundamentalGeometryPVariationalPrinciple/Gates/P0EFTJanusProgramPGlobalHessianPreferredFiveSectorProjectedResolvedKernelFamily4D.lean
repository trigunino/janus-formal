import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorResolvedKernelBasepoint4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalFamilyCommutation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D

/-!
# Canonical C1 sector-projected zero-mode family

The existing named basis need not be assumed sector-resolved away from the
basepoint.  Once the represented D11 family commutes with the fixed five
physical projectors, there is a canonical replacement candidate:

`e~_i(a) = P_{s(i)} e_i(a)`.

Every such vector is automatically

* a genuine zero mode of `H_a`;
* contained in the assigned physical sector;
* C1 in the common ambient Hilbert space;
* exactly equal to the original action-generated vector at `a = 0`.

The only remaining issue for replacing the named basis globally is therefore
finite-dimensional completeness/linear independence of these projected
vectors, not their physical sector membership.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedResolvedKernelFamily4D

set_option autoImplicit false
set_option maxHeartbeats 40000000
set_option synthInstance.maxHeartbeats 20000000
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
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorBismutFreedFamily4D
open P0EFTJanusProgramPGlobalCandidateAFiveSectorCompletionResolutionBridge4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorRepresentation4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalFamilyCommutation4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorResolvedKernelBasepoint4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorResolvedKernelFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorResolvedKernelFamily4D.GlobalHessianPreferredFiveSectorResolvedKernelFamily4D
open P0EFTJanusProgramPFiveSectorHilbertCoordinates4D
open P0EFTJanusProgramPDenseCoreChartBilinearBound4D
open P0EFTJanusCircleDiracHeatTraceCancellation

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace
  P0EFTJanusProgramPGlobalHessianPreferredFiveSectorBismutFreedFamily4D.candidateAHilbertNormedAddCommGroup
  P0EFTJanusProgramPGlobalHessianPreferredFiveSectorBismutFreedFamily4D.candidateAHilbertInnerProductSpace
  P0EFTJanusProgramPGlobalHessianPreferredFiveSectorBismutFreedFamily4D.candidateAHilbertNormedSpace
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

private abbrev Coordinates
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index) :=
  preferredCandidateAFiveSectorHilbertCoordinates period hPeriod input

/-- Canonical physically projected named zero-mode candidate. -/
def projectedNamedKernelVector
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (parameter : Real) (mode : ZeroMode) :
    GlobalHessianPreferredFiveSectorBismutFreedHilbert4D period hPeriod
      configuration data analysis :=
  preferredSectorProjectorApply period hPeriod input
    (namedModeFiveSector period hPeriod input mode)
    (namedKernelVectorValue period hPeriod input parameter mode)

/-- The projected candidate is a genuine zero mode for every parameter once the
D11 family gives all-parameter sector commutation. -/
theorem projectedNamedKernelVector_mem_kernel
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (parameter : Real) (mode : ZeroMode) :
    input.familyIndex.baseFamily.actualOperator parameter
        (projectedNamedKernelVector period hPeriod input parameter mode) = 0 := by
  unfold projectedNamedKernelVector
  have hKernel := namedKernelVectorValue_mem_kernel period hPeriod input
    parameter mode
  calc
    _ = _ := actualOperator_commutes_sectorProjector period hPeriod input natural
      parameter (namedModeFiveSector period hPeriod input mode)
      (namedKernelVectorValue period hPeriod input parameter mode)
    _ = 0 := by
      have hProjected := congrArg
        (fun state =>
          preferredSectorProjectorApply period hPeriod input
            (namedModeFiveSector period hPeriod input mode) state)
        hKernel
      simpa using hProjected

/-- It is fixed by its assigned physical projector. -/
theorem projectedNamedKernelVector_fixed_by_sector
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (parameter : Real) (mode : ZeroMode) :
    (Coordinates period hPeriod input).sectorProjector
        (namedModeFiveSector period hPeriod input mode)
        (projectedNamedKernelVector period hPeriod input parameter mode) =
      projectedNamedKernelVector period hPeriod input parameter mode := by
  unfold projectedNamedKernelVector preferredSectorProjectorApply
    namedKernelVectorValue
  exact (Coordinates period hPeriod input).sectorProjector_idempotent
    (namedModeFiveSector period hPeriod input mode)
    (input.kernels.vector parameter mode)

/-- Every other physical projector annihilates the candidate. -/
theorem projectedNamedKernelVector_other_sector_zero
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (parameter : Real) (mode : ZeroMode) (sector : FivePhysicalSector)
    (hSector : sector ≠ namedModeFiveSector period hPeriod input mode) :
    (Coordinates period hPeriod input).sectorProjector sector
        (projectedNamedKernelVector period hPeriod input parameter mode) = 0 := by
  unfold projectedNamedKernelVector preferredSectorProjectorApply
    namedKernelVectorValue
  exact (Coordinates period hPeriod input).sectorProjector_comp_zero hSector
    (input.kernels.vector parameter mode)

/-- At parameter zero the projection does nothing: it is exactly the existing
H12 action-generated named mode. -/
theorem projectedNamedKernelVector_zero
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (mode : ZeroMode) :
    projectedNamedKernelVector period hPeriod input 0 mode =
      input.kernels.vector 0 mode :=
  basis_fixed_by_sector_zero period hPeriod input mode

/-- Projected modes are differentiable whenever the original named basis family
is differentiable. -/
theorem projectedNamedKernelVector_differentiable
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (regularity : GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
      period hPeriod input)
    (mode : ZeroMode) :
    Differentiable Real
      (fun parameter : Real =>
        projectedNamedKernelVector period hPeriod input parameter mode) := by
  unfold projectedNamedKernelVector preferredSectorProjectorApply
    namedKernelVectorValue
  exact ((Coordinates period hPeriod input).sectorProjector
    (namedModeFiveSector period hPeriod input mode)).differentiable.comp
      (regularity.vector_differentiable mode)

/-- The projected candidate belongs to the genuine sector-kernel intersection. -/
theorem projectedNamedKernelVector_mem_sectorKernel
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (parameter : Real) (mode : ZeroMode) :
    projectedNamedKernelVector period hPeriod input parameter mode ∈
      sectorKernel period hPeriod input parameter
        (namedModeFiveSector period hPeriod input mode) := by
  constructor
  · exact LinearMap.mem_ker.mpr
      (projectedNamedKernelVector_mem_kernel period hPeriod input natural
        parameter mode)
  · refine ⟨projectedNamedKernelVector period hPeriod input parameter mode, ?_⟩
    exact projectedNamedKernelVector_fixed_by_sector period hPeriod input
      parameter mode

/-- Public canonical projected-zero-mode checkpoint. -/
theorem global_hessian_preferred_five_sector_projected_resolved_kernel_family_gate
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (regularity : GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
      period hPeriod input) :
    (∀ parameter mode,
      projectedNamedKernelVector period hPeriod input parameter mode ∈
        sectorKernel period hPeriod input parameter
          (namedModeFiveSector period hPeriod input mode)) ∧
    (∀ mode,
      Differentiable Real
        (fun parameter : Real =>
          projectedNamedKernelVector period hPeriod input parameter mode)) ∧
    (∀ mode,
      projectedNamedKernelVector period hPeriod input 0 mode =
        input.kernels.vector 0 mode) :=
  ⟨projectedNamedKernelVector_mem_sectorKernel period hPeriod input natural,
    projectedNamedKernelVector_differentiable period hPeriod input regularity,
    projectedNamedKernelVector_zero period hPeriod input⟩

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedResolvedKernelFamily4D
end JanusFormal
