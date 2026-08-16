import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Topology.Connected.Clopen
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelGramFactorization4D

/-!
# Sectorwise no-crossing criteria for the projected Candidate-A kernel

The full projected Gram determinant is the product of its five physical block
determinants.  This file turns that identity into two sectorwise global
continuation criteria.

* A pointwise nonvanishing theorem for every sector block gives the global
  projected physical kernel basis directly.
* A positive uniform lower bound for each sector determinant produces the
  existing global uniform Gram gap with margin equal to the product of the five
  sector margins.

There is also a sectorwise topological route: because every sector regular set
is open and contains the H12 basepoint, proving each one closed forces every one
to be all of `Real`.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelSectorNoCrossing4D

set_option autoImplicit false
set_option maxHeartbeats 68000000
set_option synthInstance.maxHeartbeats 34000000
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
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedResolvedKernelFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelBasisFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelRegularChart4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelGlobalContinuation4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedPhysicalNamedKernelFamilyClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelNoCrossingCriteria4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelGramBlocks4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelGramFactorization4D
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

/-- Exact sectorwise no-crossing datum.  It asks only that each of the five
finite physical Gram blocks remain nonsingular. -/
structure GlobalHessianPreferredFiveSectorProjectedKernelSectorNoCrossing4D
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index) :
    Prop where
  determinant_ne_zero : ∀ parameter sector,
    projectedKernelSectorGramDeterminant period hPeriod input parameter sector ≠ 0

namespace GlobalHessianPreferredFiveSectorProjectedKernelSectorNoCrossing4D

/-- Every sectorwise regular chart is all of the real parameter line. -/
theorem sectorRegularSet_eq_univ
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (noCrossing :
      GlobalHessianPreferredFiveSectorProjectedKernelSectorNoCrossing4D
        period hPeriod input)
    (sector : FivePhysicalSector) :
    projectedKernelSectorRegularSet period hPeriod input sector = Set.univ := by
  ext parameter
  simp only [Set.mem_univ, iff_true]
  exact noCrossing.determinant_ne_zero parameter sector

/-- Sectorwise noncrossing closes the full Gram chart. -/
theorem regularSet_eq_univ
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (noCrossing :
      GlobalHessianPreferredFiveSectorProjectedKernelSectorNoCrossing4D
        period hPeriod input) :
    projectedKernelRegularSet period hPeriod input = Set.univ := by
  apply Set.eq_univ_of_forall
  intro parameter
  refine (mem_projectedKernelRegularSet_iff_forall_sector period hPeriod input
    parameter).mpr ?_
  intro sector
  exact noCrossing.determinant_ne_zero parameter sector

/-- Sectorwise noncrossing constructs the global projected physical kernel
basis. -/
def toProjectedPhysicalBasisFamily
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (noCrossing :
      GlobalHessianPreferredFiveSectorProjectedKernelSectorNoCrossing4D
        period hPeriod input) :
    GlobalHessianPreferredFiveSectorProjectedKernelBasisFamily4D
      period hPeriod input natural :=
  projectedPhysicalBasisFamily period hPeriod input natural
    (noCrossing.regularSet_eq_univ period hPeriod input)

/-- Sectorwise noncrossing rebuilds the existing family-index closure with the
canonical projected physical basis. -/
def toProjectedPhysicalNamedKernelFamilyClosure
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (noCrossing :
      GlobalHessianPreferredFiveSectorProjectedKernelSectorNoCrossing4D
        period hPeriod input) :
    GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index :=
  projectedPhysicalNamedKernelFamilyClosure period hPeriod input natural
    (noCrossing.regularSet_eq_univ period hPeriod input)

/-- The rebuilt projected physical family inherits the ambient C1 regularity. -/
def toProjectedPhysicalNamedKernelFamilyRegularity
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (regularity : GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
      period hPeriod input)
    (noCrossing :
      GlobalHessianPreferredFiveSectorProjectedKernelSectorNoCrossing4D
        period hPeriod input) :
    GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
      period hPeriod
        (noCrossing.toProjectedPhysicalNamedKernelFamilyClosure period hPeriod input
          natural) :=
  projectedPhysicalNamedKernelFamilyRegularity period hPeriod input natural
    regularity (noCrossing.regularSet_eq_univ period hPeriod input)

/-- Public pointwise sector-no-crossing checkpoint. -/
theorem projected_kernel_sector_no_crossing_gate
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (regularity : GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
      period hPeriod input)
    (noCrossing :
      GlobalHessianPreferredFiveSectorProjectedKernelSectorNoCrossing4D
        period hPeriod input) :
    (∀ sector,
      projectedKernelSectorRegularSet period hPeriod input sector = Set.univ) ∧
    projectedKernelRegularSet period hPeriod input = Set.univ ∧
    Nonempty
      (GlobalHessianPreferredFiveSectorProjectedKernelBasisFamily4D
        period hPeriod input natural) ∧
    GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
      period hPeriod
        (noCrossing.toProjectedPhysicalNamedKernelFamilyClosure period hPeriod input
          natural) :=
  ⟨noCrossing.sectorRegularSet_eq_univ period hPeriod input,
    noCrossing.regularSet_eq_univ period hPeriod input,
    ⟨noCrossing.toProjectedPhysicalBasisFamily period hPeriod input natural⟩,
    noCrossing.toProjectedPhysicalNamedKernelFamilyRegularity period hPeriod input
      natural regularity⟩

end GlobalHessianPreferredFiveSectorProjectedKernelSectorNoCrossing4D

/-- On the connected real parameter line, closedness of one already open
sector-regular chart forces that sector chart to be global. -/
theorem projectedKernelSectorRegularSet_eq_univ_of_isClosed
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (regularity : GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
      period hPeriod input)
    (sector : FivePhysicalSector)
    (hClosed : IsClosed
      (projectedKernelSectorRegularSet period hPeriod input sector)) :
    projectedKernelSectorRegularSet period hPeriod input sector = Set.univ := by
  apply IsClopen.eq_univ
  · exact ⟨hClosed,
      isOpen_projectedKernelSectorRegularSet period hPeriod input regularity
        sector⟩
  · exact ⟨0,
      zero_mem_projectedKernelSectorRegularSet period hPeriod input natural
        sector⟩

/-- If all five sector-regular charts are closed, the full projected physical
basis continues globally. -/
theorem projectedKernelRegularSet_eq_univ_of_all_sector_isClosed
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (regularity : GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
      period hPeriod input)
    (hClosed : ∀ sector,
      IsClosed (projectedKernelSectorRegularSet period hPeriod input sector)) :
    projectedKernelRegularSet period hPeriod input = Set.univ := by
  apply Set.eq_univ_of_forall
  intro parameter
  refine (mem_projectedKernelRegularSet_iff_forall_sector period hPeriod input
    parameter).mpr ?_
  intro sector
  have hSector := projectedKernelSectorRegularSet_eq_univ_of_isClosed period
    hPeriod input natural regularity sector (hClosed sector)
  rw [hSector]
  exact Set.mem_univ parameter

/-- Quantitative sectorwise continuation datum.  Each physical block has its
own positive determinant margin. -/
structure GlobalHessianPreferredFiveSectorProjectedKernelUniformSectorGramGap4D
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index) :
    Prop where
  margin : FivePhysicalSector → Real
  margin_pos : ∀ sector, 0 < margin sector
  determinant_lower_bound : ∀ parameter sector,
    margin sector ≤
      |projectedKernelSectorGramDeterminant period hPeriod input parameter sector|

namespace GlobalHessianPreferredFiveSectorProjectedKernelUniformSectorGramGap4D

/-- Product of the five positive sector margins. -/
def globalMargin
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (gap :
      GlobalHessianPreferredFiveSectorProjectedKernelUniformSectorGramGap4D
        period hPeriod input) : Real :=
  ∏ sector : FivePhysicalSector, gap.margin sector

/-- The product sector margin is strictly positive. -/
theorem globalMargin_pos
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (gap :
      GlobalHessianPreferredFiveSectorProjectedKernelUniformSectorGramGap4D
        period hPeriod input) :
    0 < gap.globalMargin period hPeriod input := by
  unfold globalMargin
  exact Finset.prod_pos fun sector _ => gap.margin_pos sector

/-- Every sector determinant is nonzero. -/
theorem sectorDeterminant_ne_zero
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (gap :
      GlobalHessianPreferredFiveSectorProjectedKernelUniformSectorGramGap4D
        period hPeriod input)
    (parameter : Real) (sector : FivePhysicalSector) :
    projectedKernelSectorGramDeterminant period hPeriod input parameter sector ≠ 0 := by
  apply abs_pos.mp
  exact lt_of_lt_of_le (gap.margin_pos sector)
    (gap.determinant_lower_bound parameter sector)

/-- Forgetting the numerical margins gives exact sectorwise no-crossing. -/
def toSectorNoCrossing
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (gap :
      GlobalHessianPreferredFiveSectorProjectedKernelUniformSectorGramGap4D
        period hPeriod input) :
    GlobalHessianPreferredFiveSectorProjectedKernelSectorNoCrossing4D
      period hPeriod input where
  determinant_ne_zero := gap.sectorDeterminant_ne_zero period hPeriod input

/-- The product of the five sector margins bounds the absolute full Gram
determinant from below. -/
theorem globalDeterminant_lower_bound
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (gap :
      GlobalHessianPreferredFiveSectorProjectedKernelUniformSectorGramGap4D
        period hPeriod input)
    (parameter : Real) :
    gap.globalMargin period hPeriod input ≤
      |(finiteFamilyGramMatrix
        (fun mode =>
          projectedNamedKernelVector period hPeriod input parameter mode)).det| := by
  unfold globalMargin
  rw [abs_projectedKernelGramDeterminant_eq_sectorProduct period hPeriod input
    parameter]
  exact Finset.prod_le_prod
    (fun sector _ => (gap.margin_pos sector).le)
    (fun sector _ => gap.determinant_lower_bound parameter sector)

/-- Sectorwise uniform gaps produce the existing global uniform Gram-gap
certificate. -/
def toUniformGramGap
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (gap :
      GlobalHessianPreferredFiveSectorProjectedKernelUniformSectorGramGap4D
        period hPeriod input) :
    GlobalHessianPreferredFiveSectorProjectedKernelUniformGramGap4D
      period hPeriod input where
  margin := gap.globalMargin period hPeriod input
  margin_pos := gap.globalMargin_pos period hPeriod input
  determinant_lower_bound := gap.globalDeterminant_lower_bound period hPeriod input

/-- Sectorwise uniform gaps close the global regular chart. -/
theorem regularSet_eq_univ
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (gap :
      GlobalHessianPreferredFiveSectorProjectedKernelUniformSectorGramGap4D
        period hPeriod input) :
    projectedKernelRegularSet period hPeriod input = Set.univ :=
  (gap.toSectorNoCrossing period hPeriod input).regularSet_eq_univ period hPeriod
    input

/-- Sectorwise uniform gaps construct the canonical global projected physical
basis. -/
def toProjectedPhysicalBasisFamily
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (gap :
      GlobalHessianPreferredFiveSectorProjectedKernelUniformSectorGramGap4D
        period hPeriod input) :
    GlobalHessianPreferredFiveSectorProjectedKernelBasisFamily4D
      period hPeriod input natural :=
  (gap.toUniformGramGap period hPeriod input).toProjectedPhysicalBasisFamily
    period hPeriod input natural

/-- Sectorwise uniform gaps rebuild the family-index closure with the projected
physical basis. -/
def toProjectedPhysicalNamedKernelFamilyClosure
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (gap :
      GlobalHessianPreferredFiveSectorProjectedKernelUniformSectorGramGap4D
        period hPeriod input) :
    GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index :=
  (gap.toUniformGramGap period hPeriod input).
    toProjectedPhysicalNamedKernelFamilyClosure period hPeriod input natural

/-- The rebuilt projected physical family inherits C1 regularity. -/
def toProjectedPhysicalNamedKernelFamilyRegularity
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (regularity : GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
      period hPeriod input)
    (gap :
      GlobalHessianPreferredFiveSectorProjectedKernelUniformSectorGramGap4D
        period hPeriod input) :
    GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
      period hPeriod
        (gap.toProjectedPhysicalNamedKernelFamilyClosure period hPeriod input
          natural) :=
  (gap.toUniformGramGap period hPeriod input).
    toProjectedPhysicalNamedKernelFamilyRegularity period hPeriod input natural
      regularity

/-- Public quantitative five-sector continuation checkpoint. -/
theorem projected_kernel_uniform_sector_gram_gap_gate
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (regularity : GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
      period hPeriod input)
    (gap :
      GlobalHessianPreferredFiveSectorProjectedKernelUniformSectorGramGap4D
        period hPeriod input) :
    0 < gap.globalMargin period hPeriod input ∧
    (∀ parameter,
      gap.globalMargin period hPeriod input ≤
        |(finiteFamilyGramMatrix
          (fun mode =>
            projectedNamedKernelVector period hPeriod input parameter mode)).det|) ∧
    (∀ sector,
      projectedKernelSectorRegularSet period hPeriod input sector = Set.univ) ∧
    projectedKernelRegularSet period hPeriod input = Set.univ ∧
    Nonempty
      (GlobalHessianPreferredFiveSectorProjectedKernelBasisFamily4D
        period hPeriod input natural) ∧
    GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
      period hPeriod
        (gap.toProjectedPhysicalNamedKernelFamilyClosure period hPeriod input
          natural) :=
  ⟨gap.globalMargin_pos period hPeriod input,
    gap.globalDeterminant_lower_bound period hPeriod input,
    (gap.toSectorNoCrossing period hPeriod input).sectorRegularSet_eq_univ period
      hPeriod input,
    gap.regularSet_eq_univ period hPeriod input,
    ⟨gap.toProjectedPhysicalBasisFamily period hPeriod input natural⟩,
    gap.toProjectedPhysicalNamedKernelFamilyRegularity period hPeriod input
      natural regularity⟩

end GlobalHessianPreferredFiveSectorProjectedKernelUniformSectorGramGap4D

/-- Public sectorwise topological continuation checkpoint. -/
theorem projected_kernel_all_sector_closed_gate
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (regularity : GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
      period hPeriod input)
    (hClosed : ∀ sector,
      IsClosed (projectedKernelSectorRegularSet period hPeriod input sector)) :
    projectedKernelRegularSet period hPeriod input = Set.univ ∧
    Nonempty
      (GlobalHessianPreferredFiveSectorProjectedKernelBasisFamily4D
        period hPeriod input natural) := by
  let hGlobal := projectedKernelRegularSet_eq_univ_of_all_sector_isClosed period
    hPeriod input natural regularity hClosed
  exact
    ⟨hGlobal,
      ⟨globalProjectedKernelBasisFamilyOfRegularSetEqUniv period hPeriod input
        natural hGlobal⟩⟩

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelSectorNoCrossing4D
end JanusFormal