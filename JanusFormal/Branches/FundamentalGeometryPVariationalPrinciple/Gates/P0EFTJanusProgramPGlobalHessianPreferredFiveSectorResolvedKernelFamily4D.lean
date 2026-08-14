import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorRepresentation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAFiveSectorCompletionResolutionBridge4D

/-!
# Physically resolved named-kernel family

A fixed sector label on a basis index is not by itself a geometric statement:
a basis vector could move into a mixture of sectors while keeping the same
label.  This file introduces the stronger family datum used from this point on.

For every parameter and named zero mode `i`, the actual ambient vector must be
fixed by the physical projector carrying its H12 sector label:

`P_{s(i)} e_i(a) = e_i(a)`.

The other four projectors then annihilate that vector automatically.  Combined
with the existing kernel equation this places each named vector in the genuine
intersection `ker H_a ∩ E_{s(i)}`.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorResolvedKernelFamily4D

set_option autoImplicit false
set_option maxHeartbeats 36000000
set_option synthInstance.maxHeartbeats 18000000
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
open P0EFTJanusProgramPGlobalCandidateAFiveSectorCompletionResolutionBridge4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorRepresentation4D
open P0EFTJanusProgramPFiveSectorHilbertCoordinates4D
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
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

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

private abbrev Coordinates
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold
          Index) :=
  preferredCandidateAFiveSectorHilbertCoordinates period hPeriod input

/-- Physical five-sector label attached to one named zero mode. -/
def namedModeFiveSector
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold
          Index)
    (mode : ZeroMode) : FivePhysicalSector :=
  candidateAZeroModeSectorToFivePhysicalSector (input.sectorOf mode)

/-- Strong family-level sector resolution of the named actual-kernel basis. -/
structure GlobalHessianPreferredFiveSectorResolvedKernelFamily4D
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold
          Index) : Prop where
  basis_fixed_by_sector : ∀ parameter mode,
    (Coordinates period hPeriod input).sectorProjector
        (namedModeFiveSector period hPeriod input mode)
        (input.kernels.vector parameter mode) =
      input.kernels.vector parameter mode

namespace GlobalHessianPreferredFiveSectorResolvedKernelFamily4D

/-- Every non-assigned physical projector annihilates the named zero mode. -/
theorem other_sector_zero
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold
          Index)
    (resolved : GlobalHessianPreferredFiveSectorResolvedKernelFamily4D
      period hPeriod input)
    (parameter : Real) (mode : ZeroMode) (sector : FivePhysicalSector)
    (hSector : sector ≠ namedModeFiveSector period hPeriod input mode) :
    (Coordinates period hPeriod input).sectorProjector sector
        (input.kernels.vector parameter mode) = 0 := by
  rw [← resolved.basis_fixed_by_sector parameter mode]
  exact (Coordinates period hPeriod input).sectorProjector_comp_zero hSector
    (input.kernels.vector parameter mode)

/-- The named vector belongs to the actual kernel at every parameter. -/
theorem vector_mem_kernel
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold
          Index)
    (_resolved : GlobalHessianPreferredFiveSectorResolvedKernelFamily4D
      period hPeriod input)
    (parameter : Real) (mode : ZeroMode) :
    input.familyIndex.baseFamily.actualOperator parameter
        (input.kernels.vector parameter mode) = 0 :=
  input.kernels.vector_mem_kernel parameter mode

/-- The named vector belongs to the actual physical sector subspace. -/
theorem vector_mem_sectorSubspace
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold
          Index)
    (resolved : GlobalHessianPreferredFiveSectorResolvedKernelFamily4D
      period hPeriod input)
    (parameter : Real) (mode : ZeroMode) :
    input.kernels.vector parameter mode ∈
      (Coordinates period hPeriod input).sectorSubspace
        (namedModeFiveSector period hPeriod input mode) := by
  refine ⟨input.kernels.vector parameter mode, ?_⟩
  exact resolved.basis_fixed_by_sector parameter mode

/-- The genuine sector-resolved kernel submodule at one parameter. -/
def sectorKernel
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold
          Index)
    (parameter : Real) (sector : FivePhysicalSector) :
    Submodule Real
      (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration
        data analysis) :=
  (input.familyIndex.baseFamily.actualOperator parameter).ker ⊓
    (Coordinates period hPeriod input).sectorSubspace sector

/-- Each named basis vector belongs to the intersection of the actual kernel
and its assigned physical sector. -/
theorem vector_mem_sectorKernel
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold
          Index)
    (resolved : GlobalHessianPreferredFiveSectorResolvedKernelFamily4D
      period hPeriod input)
    (parameter : Real) (mode : ZeroMode) :
    input.kernels.vector parameter mode ∈
      sectorKernel period hPeriod input parameter
        (namedModeFiveSector period hPeriod input mode) := by
  constructor
  · exact LinearMap.mem_ker.mpr (resolved.vector_mem_kernel period hPeriod input
      parameter mode)
  · exact resolved.vector_mem_sectorSubspace period hPeriod input parameter mode

/-- Public physically resolved named-kernel checkpoint. -/
theorem global_hessian_preferred_five_sector_resolved_kernel_family_gate
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (resolved : GlobalHessianPreferredFiveSectorResolvedKernelFamily4D
      period hPeriod input) :
    (∀ parameter mode,
      input.kernels.vector parameter mode ∈
        sectorKernel period hPeriod input parameter
          (namedModeFiveSector period hPeriod input mode)) ∧
    (∀ parameter mode sector,
      sector ≠ namedModeFiveSector period hPeriod input mode →
        (Coordinates period hPeriod input).sectorProjector sector
          (input.kernels.vector parameter mode) = 0) :=
  ⟨resolved.vector_mem_sectorKernel period hPeriod input,
    resolved.other_sector_zero period hPeriod input⟩

end GlobalHessianPreferredFiveSectorResolvedKernelFamily4D

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorResolvedKernelFamily4D
end JanusFormal
