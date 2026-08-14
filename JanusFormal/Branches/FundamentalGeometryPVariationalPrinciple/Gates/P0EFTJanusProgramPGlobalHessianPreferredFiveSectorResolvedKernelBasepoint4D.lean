import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorResolvedKernelFamily4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorCanonicalOperatorFrontier4D

/-!
# Basepoint physical resolution of the named Candidate-A kernel

The stronger sector-resolved kernel condition is not an additional assumption at
`a = 0`.  The preferred H12 frontier already proves that every action-generated
zero mode lies in its classified projector range, and the named family basis at
zero is exactly that generator basis.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorResolvedKernelBasepoint4D

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
open P0EFTJanusProgramPGlobalCandidateAFiveSectorActualHessianCommutation4D
open P0EFTJanusProgramPGlobalCandidateAFiveSectorCompletionResolutionBridge4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorCanonicalOperatorFrontier4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorRepresentation4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorResolvedKernelFamily4D
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

/-- At the H12 basepoint every named basis vector is fixed by its true physical
sector projector. -/
theorem basis_fixed_by_sector_zero
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (mode : ZeroMode) :
    (Coordinates period hPeriod input).sectorProjector
        (namedModeFiveSector period hPeriod input mode)
        (input.kernels.vector 0 mode) =
      input.kernels.vector 0 mode := by
  let frontier :=
    input.familyIndex.baseFamily.quillen.intrinsicFamily.basepoint.intrinsic.
      closure.frontier
  let sectorData := frontier.analytic.geometry.coordinates
  let candidateSector := input.sectorOf mode
  have hGenerator := (frontier.close period hPeriod).generator_in_sector mode
  have hGeneratorSector :
      frontier.generators.translations.vector mode ∈
        (Coordinates period hPeriod input).sectorSubspace
          (namedModeFiveSector period hPeriod input mode) := by
    rcases hGenerator with ⟨source, hSource⟩
    refine ⟨source, ?_⟩
    have hAgreement :=
      globalCandidateAFiveSectorOrthogonalProjection_agreement period hPeriod
        configuration data analysis sectorData candidateSector source
    calc
      (Coordinates period hPeriod input).sectorProjector
          (namedModeFiveSector period hPeriod input mode) source =
        globalCandidateAFiveSectorOrthogonalProjection period hPeriod
          (globalCandidateAFiveSectorOrthogonalProductOfCompletionCoordinates
            period hPeriod configuration data analysis sectorData)
          candidateSector source := by
            simpa [Coordinates, preferredCandidateAFiveSectorHilbertCoordinates,
              namedModeFiveSector, candidateSector, sectorData] using hAgreement.symm
      _ = frontier.generators.translations.vector mode := by
        simpa [frontier, sectorData,
          GlobalCandidateAFiveSectorActualHessianOffDiagonalZero4D.
            orthogonalResolution] using hSource
  rw [input.vector_zero_eq_actionGenerator period hPeriod mode]
  exact (Coordinates period hPeriod input).sectorProjector_eq_self_of_mem
    (namedModeFiveSector period hPeriod input mode) hGeneratorSector

/-- The basepoint resolved-kernel property is therefore theorem-level output,
not a new family hypothesis. -/
theorem resolved_kernel_basepoint_gate
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index) :
    ∀ mode,
      (Coordinates period hPeriod input).sectorProjector
          (namedModeFiveSector period hPeriod input mode)
          (input.kernels.vector 0 mode) =
        input.kernels.vector 0 mode :=
  basis_fixed_by_sector_zero period hPeriod input

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorResolvedKernelBasepoint4D
end JanusFormal
