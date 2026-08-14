import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedResolvedKernelFamily4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteKernelBasisFamily4D

/-!
# Physical projected kernel basis family

The canonical projected zero modes are already C1, sector-pure and genuine
kernel vectors.  Their only remaining finite-dimensional issue is completeness.
This file packages exactly that issue:

`e~_i(a) = P_{s(i)} e_i(a)` must form a basis of `ker H_a`.

Once such a basis is supplied, the preferred kernel transport is rebuilt from
these physical coordinates.  It transports each sector-pure named mode to the
same named sector-pure mode at the new parameter.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelBasisFamily4D

set_option autoImplicit false
set_option maxHeartbeats 38000000
set_option synthInstance.maxHeartbeats 19000000
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
open P0EFTJanusProgramPFiniteKernelBasisFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedResolvedKernelFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorResolvedKernelFamily4D
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

/-- Exact remaining finite-dimensional datum: the projected physical vectors
form the complete actual kernel basis at every parameter. -/
structure GlobalHessianPreferredFiveSectorProjectedKernelBasisFamily4D
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input) where
  basis : ∀ parameter,
    Basis ZeroMode Real (input.familyIndex.baseFamily.actualOperator parameter).ker
  basis_agreement : ∀ parameter mode,
    (basis parameter mode).1 =
      projectedNamedKernelVector period hPeriod input parameter mode

namespace GlobalHessianPreferredFiveSectorProjectedKernelBasisFamily4D

/-- Preferred physically resolved finite-kernel family. -/
def physicalKernels
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (physical : GlobalHessianPreferredFiveSectorProjectedKernelBasisFamily4D
      period hPeriod input natural) :
    FiniteKernelBasisFamilyData input.familyIndex.baseFamily.actualOperator ZeroMode where
  basis := physical.basis

/-- Ambient vector of the physical basis is exactly the canonical projected
zero mode. -/
theorem physicalKernels_vector
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (physical : GlobalHessianPreferredFiveSectorProjectedKernelBasisFamily4D
      period hPeriod input natural)
    (parameter : Real) (mode : ZeroMode) :
    (physical.physicalKernels period hPeriod input natural).vector parameter mode =
      projectedNamedKernelVector period hPeriod input parameter mode :=
  physical.basis_agreement parameter mode

/-- At the basepoint the physical basis agrees with the original H12 named
vectors in the ambient Hilbert space. -/
theorem physicalKernels_vector_zero
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (physical : GlobalHessianPreferredFiveSectorProjectedKernelBasisFamily4D
      period hPeriod input natural)
    (mode : ZeroMode) :
    (physical.physicalKernels period hPeriod input natural).vector 0 mode =
      input.kernels.vector 0 mode := by
  rw [physical.physicalKernels_vector period hPeriod input natural]
  exact projectedNamedKernelVector_zero period hPeriod input mode

/-- The new canonical physical transport maps each projected named basis vector
to the identically named projected vector. -/
theorem physicalKernelTransport_basis
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (physical : GlobalHessianPreferredFiveSectorProjectedKernelBasisFamily4D
      period hPeriod input natural)
    (first second : Real) (mode : ZeroMode) :
    (physical.physicalKernels period hPeriod input natural).kernelTransport
        first second (physical.basis first mode) =
      physical.basis second mode :=
  (physical.physicalKernels period hPeriod input natural).kernelTransport_basis
    first second mode

/-- The physical basis vectors are sector-pure at every parameter. -/
theorem physicalKernels_vector_mem_sectorKernel
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (physical : GlobalHessianPreferredFiveSectorProjectedKernelBasisFamily4D
      period hPeriod input natural)
    (parameter : Real) (mode : ZeroMode) :
    (physical.physicalKernels period hPeriod input natural).vector parameter mode ∈
      sectorKernel period hPeriod input parameter
        (namedModeFiveSector period hPeriod input mode) := by
  rw [physical.physicalKernels_vector period hPeriod input natural]
  exact projectedNamedKernelVector_mem_sectorKernel period hPeriod input natural
    parameter mode

/-- If the original named family is C1, the preferred physical basis vectors
are C1 as ambient vectors as well. -/
theorem physicalKernels_vector_differentiable
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (physical : GlobalHessianPreferredFiveSectorProjectedKernelBasisFamily4D
      period hPeriod input natural)
    (regularity : GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
      period hPeriod input)
    (mode : ZeroMode) :
    Differentiable Real
      (fun parameter : Real =>
        (physical.physicalKernels period hPeriod input natural).vector
          parameter mode) := by
  simp only [physicalKernels_vector]
  exact projectedNamedKernelVector_differentiable period hPeriod input
    regularity mode

/-- Public physical-kernel-basis checkpoint. -/
theorem global_hessian_preferred_five_sector_projected_kernel_basis_family_gate
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (physical : GlobalHessianPreferredFiveSectorProjectedKernelBasisFamily4D
      period hPeriod input natural) :
    (∀ parameter mode,
      (physical.physicalKernels period hPeriod input natural).vector parameter mode ∈
        sectorKernel period hPeriod input parameter
          (namedModeFiveSector period hPeriod input mode)) ∧
    (∀ first second mode,
      (physical.physicalKernels period hPeriod input natural).kernelTransport
          first second (physical.basis first mode) =
        physical.basis second mode) ∧
    (∀ mode,
      (physical.physicalKernels period hPeriod input natural).vector 0 mode =
        input.kernels.vector 0 mode) :=
  ⟨physical.physicalKernels_vector_mem_sectorKernel period hPeriod input natural,
    physical.physicalKernelTransport_basis period hPeriod input natural,
    physical.physicalKernels_vector_zero period hPeriod input natural⟩

end GlobalHessianPreferredFiveSectorProjectedKernelBasisFamily4D

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelBasisFamily4D
end JanusFormal
