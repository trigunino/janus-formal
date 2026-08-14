import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelBasisFamily4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorFredholmDeterminantFamily4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointFredholmZetaFullTensor4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointFredholmFullTensorBasisIndependence4D

/-!
# Physical kernel basis and the existing Fredholm--zeta determinant

A sector-pure projected basis, once proved complete, does not create a new
determinant line.  The determinant fiber is still the true

`Hom(det coker H_a, det ker H_a)`

of the same actual operator.  The self-adjoint Fredholm frame is basis
independent, so the projected physical basis changes neither that frame nor the
reduced zeta coordinate of the full tensor section.

This file ties the physical zero-mode refinement to the already constructed
Candidate-A Fredholm--zeta line without rebuilding a parallel determinant
package.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorPhysicalFredholmCompatibility4D

set_option autoImplicit false
set_option maxHeartbeats 42000000
set_option synthInstance.maxHeartbeats 21000000
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
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelBasisFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorFredholmDeterminantFamily4D
open P0EFTJanusProgramPSelfAdjointFredholmDeterminantLineFamily4D
open P0EFTJanusProgramPSelfAdjointFredholmFullTensorBasisIndependence4D
open P0EFTJanusProgramPSelfAdjointFredholmZetaFullTensor4D
open P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D
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
    [LinearOrder ZeroMode]
    {fold : Fold} {Index : Type*}

private abbrev FredholmFamily
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index) :=
  globalHessianPreferredFiveSectorFredholmDeterminantFamily period hPeriod input

/-- The full zeta section remains the same actual Fredholm tensor section after
one equips the kernel with the physically projected basis. -/
theorem physicalKernelBasis_fullTensorZeta_coordinate
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (_physical : GlobalHessianPreferredFiveSectorProjectedKernelBasisFamily4D
      period hPeriod input natural)
    (parameter : Real) :
    (FredholmFamily period hPeriod input).fullTensorDeterminantCollapse parameter
        (selfAdjointFredholmZetaFullTensorSection
          (FredholmFamily period hPeriod input)
          input.familyIndex.baseFamily.familyIndex.zetaFamily parameter) =
      relativeHeatMellinZetaFamilyDeterminant
          input.familyIndex.baseFamily.familyIndex.zetaFamily parameter •
        (FredholmFamily period hPeriod input).complexifiedDeterminantFrame
          parameter := by
  exact (FredholmFamily period hPeriod input).fullTensorSection_coordinate_only
    parameter
    (relativeHeatMellinZetaFamilyDeterminant
      input.familyIndex.baseFamily.familyIndex.zetaFamily parameter)

/-- The canonical Fredholm frame itself remains basis independent even after a
physical projected basis has been selected. -/
theorem physicalKernelBasis_does_not_change_fredholmFrame
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (_physical : GlobalHessianPreferredFiveSectorProjectedKernelBasisFamily4D
      period hPeriod input natural)
    (parameter : Real) :
    ∀ kernelVolume,
      (FredholmFamily period hPeriod input).determinantFrame parameter
          (((FredholmFamily period hPeriod input).cokernelTopKernelTopEquiv
            parameter).symm kernelVolume) =
        kernelVolume :=
  (FredholmFamily period hPeriod input).determinantFrame_matchingKernelVolume
    parameter

/-- Public physical-kernel/Fredholm compatibility checkpoint. -/
theorem global_hessian_preferred_five_sector_physical_fredholm_compatibility_gate
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
    (∀ parameter kernelVolume,
      (FredholmFamily period hPeriod input).determinantFrame parameter
          (((FredholmFamily period hPeriod input).cokernelTopKernelTopEquiv
            parameter).symm kernelVolume) =
        kernelVolume) ∧
    (∀ parameter,
      (FredholmFamily period hPeriod input).fullTensorDeterminantCollapse parameter
          (selfAdjointFredholmZetaFullTensorSection
            (FredholmFamily period hPeriod input)
            input.familyIndex.baseFamily.familyIndex.zetaFamily parameter) =
        relativeHeatMellinZetaFamilyDeterminant
            input.familyIndex.baseFamily.familyIndex.zetaFamily parameter •
          (FredholmFamily period hPeriod input).complexifiedDeterminantFrame
            parameter) :=
  ⟨physical.physicalKernels_vector_mem_sectorKernel period hPeriod input natural,
    physicalKernelBasis_does_not_change_fredholmFrame period hPeriod input
      natural physical,
    physicalKernelBasis_fullTensorZeta_coordinate period hPeriod input
      natural physical⟩

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorPhysicalFredholmCompatibility4D
end JanusFormal
