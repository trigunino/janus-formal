import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiveSectorHilbertCoordinatesOrthogonality4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelNoCrossingCriteria4D

/-!
# Five physical blocks of the projected Candidate-A kernel Gram matrix

Every projected named zero mode is fixed by exactly one of the five canonical
Hilbert projectors.  Since the five projector ranges are pairwise orthogonal,
the full projected Gram matrix has no matrix element between two distinct
physical sectors.

This file makes that statement explicit and defines the five finite sector Gram
matrices.  The remaining uniform no-crossing estimate may therefore be attacked
on these physical blocks rather than as one opaque full matrix.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelGramBlocks4D

set_option autoImplicit false
set_option maxHeartbeats 58000000
set_option synthInstance.maxHeartbeats 29000000
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
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyH10Reduction4D
open P0EFTJanusProgramPGlobalCandidateACanonicalSixDenseCore4D
open P0EFTJanusProgramPFiniteFamilyGramLocalPersistence4D
open P0EFTJanusProgramPFiveSectorHilbertCoordinates4D
open P0EFTJanusProgramPFiveSectorHilbertCoordinatesOrthogonality4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedResolvedKernelFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelGramLocalPersistence4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelNoCrossingCriteria4D
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

private abbrev Coordinates
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index) :=
  preferredCandidateAFiveSectorHilbertCoordinates period hPeriod input

/-- Projected named zero modes with distinct physical labels are orthogonal. -/
theorem projectedNamedKernelVector_inner_eq_zero_of_sector_ne
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (parameter : Real) (first second : ZeroMode)
    (hSector : namedModeFiveSector period hPeriod input first ≠
      namedModeFiveSector period hPeriod input second) :
    inner Real
        (projectedNamedKernelVector period hPeriod input parameter first)
        (projectedNamedKernelVector period hPeriod input parameter second) = 0 := by
  apply inner_eq_zero_of_sectorProjector_fixed
    (Coordinates period hPeriod input) hSector
  · exact projectedNamedKernelVector_fixed_by_sector period hPeriod input parameter
      first
  · exact projectedNamedKernelVector_fixed_by_sector period hPeriod input parameter
      second

/-- Off-sector entries of the full projected Gram matrix vanish identically. -/
theorem projectedKernelGramMatrix_offSector_zero
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (parameter : Real) (row column : ZeroMode)
    (hSector : namedModeFiveSector period hPeriod input row ≠
      namedModeFiveSector period hPeriod input column) :
    finiteFamilyGramMatrix
        (fun mode =>
          projectedNamedKernelVector period hPeriod input parameter mode)
        row column = 0 := by
  change
    inner Real
        (projectedNamedKernelVector period hPeriod input parameter column)
        (projectedNamedKernelVector period hPeriod input parameter row) = 0
  exact projectedNamedKernelVector_inner_eq_zero_of_sector_ne period hPeriod input
    parameter column row hSector.symm

/-- Modes assigned to one physical sector. -/
abbrev ProjectedSectorMode
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (sector : FivePhysicalSector) :=
  {mode : ZeroMode // namedModeFiveSector period hPeriod input mode = sector}

/-- Gram matrix of the projected modes belonging to one physical sector. -/
def projectedKernelSectorGramMatrix
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (parameter : Real) (sector : FivePhysicalSector) :
    Matrix (ProjectedSectorMode period hPeriod input sector)
      (ProjectedSectorMode period hPeriod input sector) Real :=
  finiteFamilyGramMatrix
    (fun mode : ProjectedSectorMode period hPeriod input sector =>
      projectedNamedKernelVector period hPeriod input parameter mode.1)

/-- Determinant of one physical projected Gram block. -/
def projectedKernelSectorGramDeterminant
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (parameter : Real) (sector : FivePhysicalSector) : Real :=
  (projectedKernelSectorGramMatrix period hPeriod input parameter sector).det

/-- Each physical Gram-block determinant is continuous in the family parameter. -/
theorem continuous_projectedKernelSectorGramDeterminant
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (regularity : GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
      period hPeriod input)
    (sector : FivePhysicalSector) :
    Continuous
      (fun parameter : Real =>
        projectedKernelSectorGramDeterminant period hPeriod input parameter
          sector) := by
  exact continuous_finiteFamilyGramDeterminant
    (fun parameter (mode : ProjectedSectorMode period hPeriod input sector) =>
      projectedNamedKernelVector period hPeriod input parameter mode.1)
    (fun mode =>
      projectedNamedKernelVector_continuous period hPeriod input regularity mode.1)

/-- The regular set of one physical Gram block. -/
def projectedKernelSectorRegularSet
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (sector : FivePhysicalSector) : Set Real :=
  {parameter |
    projectedKernelSectorGramDeterminant period hPeriod input parameter sector ≠ 0}

/-- Every physical block has an open nondegeneracy set. -/
theorem isOpen_projectedKernelSectorRegularSet
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (regularity : GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
      period hPeriod input)
    (sector : FivePhysicalSector) :
    IsOpen (projectedKernelSectorRegularSet period hPeriod input sector) := by
  change IsOpen
    ((fun parameter : Real =>
      projectedKernelSectorGramDeterminant period hPeriod input parameter sector) ⁻¹'
      ({0} : Set Real)ᶜ)
  exact isOpen_compl_singleton.preimage
    (continuous_projectedKernelSectorGramDeterminant period hPeriod input
      regularity sector)

/-- Public five-block projected Gram checkpoint. -/
theorem projected_kernel_gram_blocks_gate
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (regularity : GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
      period hPeriod input) :
    (∀ parameter row column,
      namedModeFiveSector period hPeriod input row ≠
          namedModeFiveSector period hPeriod input column →
        finiteFamilyGramMatrix
            (fun mode =>
              projectedNamedKernelVector period hPeriod input parameter mode)
            row column = 0) ∧
    (∀ sector,
      Continuous
        (fun parameter : Real =>
          projectedKernelSectorGramDeterminant period hPeriod input parameter
            sector)) ∧
    (∀ sector,
      IsOpen (projectedKernelSectorRegularSet period hPeriod input sector)) :=
  ⟨projectedKernelGramMatrix_offSector_zero period hPeriod input,
    continuous_projectedKernelSectorGramDeterminant period hPeriod input
      regularity,
    isOpen_projectedKernelSectorRegularSet period hPeriod input regularity⟩

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelGramBlocks4D
end JanusFormal
