import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorSectorCovariantGeometricRegularityTerminal4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalOperatorGeometricBismutFreed4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorKernelTransportCovariance4D

/-!
# Resolved natural-geometric terminal for the preferred Candidate-A family

This terminal ties together the three family-level conditions that are genuinely
stronger than the already constructed Fredholm/zeta determinant architecture:

* C1 regularity of the named kernel and kernel-complement splitting;
* an exact sector-covariant, componentwise D11 natural elliptic realization of
  the same `actualOperator a`, carrying the geometric BF/families-index data;
* covariance of the canonical named-kernel transport with the five physical
  projectors.

The H12 basepoint sector theorem then propagates through the kernel transport,
so every named zero mode is a C1 family of genuine vectors in
`ker H_a ∩ E_sector`.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorResolvedNaturalGeometricTerminal4D

set_option autoImplicit false
set_option maxHeartbeats 48000000
set_option synthInstance.maxHeartbeats 24000000
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
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorDifferentiableFredholmSplitting4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorKernelTransportCovariance4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalOperatorGeometricBismutFreed4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorResolvedKernelFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorSectorCovariantGeometricRegularityTerminal4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalFamilyCommutation4D
open P0EFTJanusProgramPGeometricBismutFreedPathComparison4D
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
    {fold : Fold} {Index Base Tangent : Type*}

/-- Preferred combined terminal input. -/
structure GlobalHessianPreferredFiveSectorResolvedNaturalGeometricTerminalData4D
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (Base Tangent : Type*) where
  regularity :
    GlobalHessianPreferredFiveSectorDifferentiableFredholmSplitting4D
      period hPeriod input
  geometry :
    GlobalHessianPreferredFiveSectorNaturalOperatorGeometricBismutFreedData4D
      period hPeriod input Base Tangent
  kernelTransport :
    GlobalHessianPreferredFiveSectorKernelTransportCovariance4D
      period hPeriod input geometry.natural

namespace GlobalHessianPreferredFiveSectorResolvedNaturalGeometricTerminalData4D

/-- Strong physically resolved kernel family generated from transport
covariance. -/
def resolvedKernel
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (closure : GlobalHessianPreferredFiveSectorResolvedNaturalGeometricTerminalData4D
      period hPeriod input Base Tangent) :
    GlobalHessianPreferredFiveSectorResolvedKernelFamily4D period hPeriod input :=
  closure.kernelTransport.toResolvedKernelFamily period hPeriod input
    closure.geometry.natural

/-- Forget the componentwise operator and kernel-transport refinements to recover
the earlier sector-covariant geometric terminal. -/
def toSectorCovariantTerminalData
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (closure : GlobalHessianPreferredFiveSectorResolvedNaturalGeometricTerminalData4D
      period hPeriod input Base Tangent) :
    GlobalHessianPreferredFiveSectorSectorCovariantGeometricRegularityTerminalData4D
      period hPeriod input Base Tangent where
  regularity := closure.regularity
  geometry := closure.geometry.toSectorCovariantGeometricData period hPeriod input

/-- Each named zero mode is both differentiable in the ambient Hilbert space and
actually contained in its physical sector kernel for every parameter. -/
theorem differentiable_resolved_named_modes
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (closure : GlobalHessianPreferredFiveSectorResolvedNaturalGeometricTerminalData4D
      period hPeriod input Base Tangent) :
    (∀ mode,
      Differentiable Real
        (fun parameter : Real => input.kernels.vector parameter mode)) ∧
    (∀ parameter mode,
      input.kernels.vector parameter mode ∈
        sectorKernel period hPeriod input parameter
          (namedModeFiveSector period hPeriod input mode)) :=
  ⟨closure.regularity.kernels.vector_differentiable,
    (closure.resolvedKernel period hPeriod input).vector_mem_sectorKernel
      period hPeriod input⟩

/-- Public resolved natural-geometric terminal checkpoint. -/
theorem resolved_natural_geometric_terminal_gate
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (closure : GlobalHessianPreferredFiveSectorResolvedNaturalGeometricTerminalData4D
      period hPeriod input Base Tangent) :
    (∀ mode,
      Differentiable Real
        (fun parameter : Real => input.kernels.vector parameter mode)) ∧
    (∀ parameter mode,
      input.kernels.vector parameter mode ∈
        sectorKernel period hPeriod input parameter
          (namedModeFiveSector period hPeriod input mode)) ∧
    (∀ parameter sector state,
      input.familyIndex.baseFamily.actualOperator parameter
          ((preferredCandidateAFiveSectorHilbertCoordinates period hPeriod input).
            sectorProjector sector state) =
        (preferredCandidateAFiveSectorHilbertCoordinates period hPeriod input).
          sectorProjector sector
          (input.familyIndex.baseFamily.actualOperator parameter state)) ∧
    (∀ parameter,
      pulledGeometricCoefficient closure.geometry.geometry closure.geometry.path
          parameter =
        input.familyIndex.baseFamily.familyIndex.toBismutFreed.operatorTrace.
          bismutFreedCoefficient parameter) ∧
    (∀ base first second,
      closure.geometry.curvature.bismutFreedCurvature base first second =
        closure.geometry.curvature.localFamiliesIndexCurvature base first second) :=
  ⟨(closure.differentiable_resolved_named_modes period hPeriod input).1,
    (closure.differentiable_resolved_named_modes period hPeriod input).2,
    actualOperator_commutes_sectorProjector period hPeriod input
      closure.geometry.natural,
    closure.geometry.coefficient_agreement,
    closure.geometry.curvature.curvature_agreement⟩

end GlobalHessianPreferredFiveSectorResolvedNaturalGeometricTerminalData4D

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorResolvedNaturalGeometricTerminal4D
end JanusFormal
