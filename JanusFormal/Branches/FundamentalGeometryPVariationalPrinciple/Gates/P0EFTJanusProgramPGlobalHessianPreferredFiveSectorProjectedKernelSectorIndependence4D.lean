import Mathlib.Analysis.InnerProductSpace.GramMatrix
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteFamilyGramInjectivity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelSectorNoCrossing4D

/-!
# Linear-independence criteria for projected physical kernel sectors

Each physical Gram block is an ordinary finite Gram matrix, up to the harmless
row/column convention already used by the coefficient Gram endomorphism.  Over
`Real` the inner product is symmetric, so the two matrices agree exactly.

Consequently, for every parameter and physical sector, the following are
identical conditions:

* the sector Gram determinant is nonzero;
* the projected sector vectors are linearly independent;
* coefficient synthesis by those vectors is injective.

This file also supplies a quantitative sufficient condition formulated directly
on coefficient synthesis.  A positive lower norm bound in every physical sector
implies sectorwise noncrossing and therefore constructs the global projected
physical kernel basis and its C1 named-kernel closure.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelSectorIndependence4D

set_option autoImplicit false
set_option maxHeartbeats 72000000
set_option synthInstance.maxHeartbeats 36000000
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
open P0EFTJanusProgramPFiniteFamilyGramBasis4D
open P0EFTJanusProgramPFiniteFamilyGramInjectivity4D
open P0EFTJanusProgramPFiniteFamilyGramLocalPersistence4D
open P0EFTJanusProgramPFiveSectorHilbertCoordinates4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedResolvedKernelFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelBasisFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedPhysicalNamedKernelFamilyClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelGramBlocks4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelGramFactorization4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelSectorNoCrossing4D
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

private abbrev ProjectedSectorVectors
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (parameter : Real) (sector : FivePhysicalSector) :=
  fun mode : ProjectedSectorMode period hPeriod input sector =>
    projectedNamedKernelVector period hPeriod input parameter mode.1

/-- The sector matrix is the standard real Gram matrix of its projected vectors. -/
theorem projectedKernelSectorGramMatrix_eq_gram
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (parameter : Real) (sector : FivePhysicalSector) :
    projectedKernelSectorGramMatrix period hPeriod input parameter sector =
      Matrix.gram Real
        (ProjectedSectorVectors period hPeriod input parameter sector) := by
  ext row column
  simp [projectedKernelSectorGramMatrix, ProjectedSectorVectors,
    finiteFamilyGramMatrix, real_inner_comm]

/-- Sector determinant nonvanishing is exactly linear independence of the
projected physical modes in that sector. -/
theorem projectedKernelSectorGramDeterminant_ne_zero_iff_linearIndependent
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (parameter : Real) (sector : FivePhysicalSector) :
    projectedKernelSectorGramDeterminant period hPeriod input parameter sector ≠ 0 ↔
      LinearIndependent Real
        (ProjectedSectorVectors period hPeriod input parameter sector) := by
  change
    (projectedKernelSectorGramMatrix period hPeriod input parameter sector).det ≠ 0 ↔
      LinearIndependent Real
        (ProjectedSectorVectors period hPeriod input parameter sector)
  rw [projectedKernelSectorGramMatrix_eq_gram period hPeriod input parameter
    sector]
  exact Matrix.det_gram_ne_zero_iff_linearIndependent

/-- Sector determinant nonvanishing is exactly injectivity of finite coefficient
synthesis by the projected physical modes. -/
theorem projectedKernelSectorGramDeterminant_ne_zero_iff_synthesis_injective
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (parameter : Real) (sector : FivePhysicalSector) :
    projectedKernelSectorGramDeterminant period hPeriod input parameter sector ≠ 0 ↔
      Function.Injective
        (finiteFamilySynthesis
          (ProjectedSectorVectors period hPeriod input parameter sector)) := by
  simpa [projectedKernelSectorGramDeterminant,
    projectedKernelSectorGramMatrix, ProjectedSectorVectors] using
    ((finiteFamilyGramMap_injective_iff_det_ne_zero
        (ProjectedSectorVectors period hPeriod input parameter sector)).symm.trans
      (finiteFamilyGramMap_injective_iff_synthesis_injective
        (ProjectedSectorVectors period hPeriod input parameter sector)))

/-- The exact sector-no-crossing packet is equivalent to pointwise linear
independence in every physical block. -/
theorem sectorNoCrossing_iff_forall_linearIndependent
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index) :
    GlobalHessianPreferredFiveSectorProjectedKernelSectorNoCrossing4D
        period hPeriod input ↔
      ∀ parameter sector,
        LinearIndependent Real
          (ProjectedSectorVectors period hPeriod input parameter sector) := by
  constructor
  · intro noCrossing parameter sector
    exact
      (projectedKernelSectorGramDeterminant_ne_zero_iff_linearIndependent
        period hPeriod input parameter sector).mp
          (noCrossing.determinant_ne_zero parameter sector)
  · intro hIndependent
    refine ⟨?_⟩
    intro parameter sector
    exact
      (projectedKernelSectorGramDeterminant_ne_zero_iff_linearIndependent
        period hPeriod input parameter sector).mpr
          (hIndependent parameter sector)

/-- Equivalently, sector no-crossing means that every sector coefficient
synthesis map is injective. -/
theorem sectorNoCrossing_iff_forall_synthesis_injective
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index) :
    GlobalHessianPreferredFiveSectorProjectedKernelSectorNoCrossing4D
        period hPeriod input ↔
      ∀ parameter sector,
        Function.Injective
          (finiteFamilySynthesis
            (ProjectedSectorVectors period hPeriod input parameter sector)) := by
  constructor
  · intro noCrossing parameter sector
    exact
      (projectedKernelSectorGramDeterminant_ne_zero_iff_synthesis_injective
        period hPeriod input parameter sector).mp
          (noCrossing.determinant_ne_zero parameter sector)
  · intro hInjective
    refine ⟨?_⟩
    intro parameter sector
    exact
      (projectedKernelSectorGramDeterminant_ne_zero_iff_synthesis_injective
        period hPeriod input parameter sector).mpr
          (hInjective parameter sector)

/-- A uniform lower norm estimate on coefficient synthesis in each physical
sector.  This is stronger than determinant nonvanishing but is often the more
direct analytic estimate. -/
structure GlobalHessianPreferredFiveSectorProjectedKernelUniformSectorSynthesisLowerBound4D
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index) :
    Prop where
  lowerConstant : FivePhysicalSector → Real
  lowerConstant_pos : ∀ sector, 0 < lowerConstant sector
  synthesis_lower_bound : ∀ parameter sector coefficient,
    lowerConstant sector * ‖coefficient‖ ≤
      ‖finiteFamilySynthesis
        (ProjectedSectorVectors period hPeriod input parameter sector)
        coefficient‖

namespace GlobalHessianPreferredFiveSectorProjectedKernelUniformSectorSynthesisLowerBound4D

/-- A positive synthesis lower bound forces injectivity in one sector. -/
theorem synthesis_injective
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (bound :
      GlobalHessianPreferredFiveSectorProjectedKernelUniformSectorSynthesisLowerBound4D
        period hPeriod input)
    (parameter : Real) (sector : FivePhysicalSector) :
    Function.Injective
      (finiteFamilySynthesis
        (ProjectedSectorVectors period hPeriod input parameter sector)) := by
  intro first second hEqual
  have hDifference :
      finiteFamilySynthesis
          (ProjectedSectorVectors period hPeriod input parameter sector)
          (first - second) = 0 := by
    rw [map_sub, hEqual, sub_self]
  have hBound := bound.synthesis_lower_bound parameter sector (first - second)
  rw [hDifference, norm_zero] at hBound
  have hNormNonpos : ‖first - second‖ ≤ 0 := by
    apply (mul_le_mul_left (bound.lowerConstant_pos sector)).mp
    simpa using hBound
  have hNormZero : ‖first - second‖ = 0 :=
    le_antisymm hNormNonpos (norm_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp hNormZero)

/-- Synthesis lower bounds imply exact sectorwise no-crossing. -/
def toSectorNoCrossing
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (bound :
      GlobalHessianPreferredFiveSectorProjectedKernelUniformSectorSynthesisLowerBound4D
        period hPeriod input) :
    GlobalHessianPreferredFiveSectorProjectedKernelSectorNoCrossing4D
      period hPeriod input where
  determinant_ne_zero := by
    intro parameter sector
    exact
      (projectedKernelSectorGramDeterminant_ne_zero_iff_synthesis_injective
        period hPeriod input parameter sector).mpr
          (bound.synthesis_injective period hPeriod input parameter sector)

/-- Synthesis lower bounds close the full projected Gram chart. -/
theorem regularSet_eq_univ
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (bound :
      GlobalHessianPreferredFiveSectorProjectedKernelUniformSectorSynthesisLowerBound4D
        period hPeriod input) :
    projectedKernelRegularSet period hPeriod input = Set.univ :=
  (bound.toSectorNoCrossing period hPeriod input).regularSet_eq_univ period hPeriod
    input

/-- Synthesis lower bounds construct the global projected physical basis. -/
def toProjectedPhysicalBasisFamily
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (bound :
      GlobalHessianPreferredFiveSectorProjectedKernelUniformSectorSynthesisLowerBound4D
        period hPeriod input) :
    GlobalHessianPreferredFiveSectorProjectedKernelBasisFamily4D
      period hPeriod input natural :=
  (bound.toSectorNoCrossing period hPeriod input).toProjectedPhysicalBasisFamily
    period hPeriod input natural

/-- Synthesis lower bounds rebuild the family-index closure with the global
projected physical basis. -/
def toProjectedPhysicalNamedKernelFamilyClosure
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (bound :
      GlobalHessianPreferredFiveSectorProjectedKernelUniformSectorSynthesisLowerBound4D
        period hPeriod input) :
    GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index :=
  (bound.toSectorNoCrossing period hPeriod input).
    toProjectedPhysicalNamedKernelFamilyClosure period hPeriod input natural

/-- The rebuilt physical family remains C1 in the fixed ambient Hilbert space. -/
def toProjectedPhysicalNamedKernelFamilyRegularity
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (regularity : GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
      period hPeriod input)
    (bound :
      GlobalHessianPreferredFiveSectorProjectedKernelUniformSectorSynthesisLowerBound4D
        period hPeriod input) :
    GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
      period hPeriod
        (bound.toProjectedPhysicalNamedKernelFamilyClosure period hPeriod input
          natural) :=
  (bound.toSectorNoCrossing period hPeriod input).
    toProjectedPhysicalNamedKernelFamilyRegularity period hPeriod input natural
      regularity

/-- Public synthesis-lower-bound continuation checkpoint. -/
theorem projected_kernel_uniform_sector_synthesis_lower_bound_gate
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (regularity : GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
      period hPeriod input)
    (bound :
      GlobalHessianPreferredFiveSectorProjectedKernelUniformSectorSynthesisLowerBound4D
        period hPeriod input) :
    (∀ parameter sector,
      Function.Injective
        (finiteFamilySynthesis
          (ProjectedSectorVectors period hPeriod input parameter sector))) ∧
    (∀ parameter sector,
      projectedKernelSectorGramDeterminant period hPeriod input parameter sector ≠ 0) ∧
    projectedKernelRegularSet period hPeriod input = Set.univ ∧
    Nonempty
      (GlobalHessianPreferredFiveSectorProjectedKernelBasisFamily4D
        period hPeriod input natural) ∧
    GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
      period hPeriod
        (bound.toProjectedPhysicalNamedKernelFamilyClosure period hPeriod input
          natural) :=
  ⟨bound.synthesis_injective period hPeriod input,
    (bound.toSectorNoCrossing period hPeriod input).determinant_ne_zero,
    bound.regularSet_eq_univ period hPeriod input,
    ⟨bound.toProjectedPhysicalBasisFamily period hPeriod input natural⟩,
    bound.toProjectedPhysicalNamedKernelFamilyRegularity period hPeriod input
      natural regularity⟩

end GlobalHessianPreferredFiveSectorProjectedKernelUniformSectorSynthesisLowerBound4D

/-- Public exact linear-independence characterization. -/
theorem projected_kernel_sector_independence_gate
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index) :
    (∀ parameter sector,
      projectedKernelSectorGramDeterminant period hPeriod input parameter sector ≠ 0 ↔
        LinearIndependent Real
          (ProjectedSectorVectors period hPeriod input parameter sector)) ∧
    (GlobalHessianPreferredFiveSectorProjectedKernelSectorNoCrossing4D
        period hPeriod input ↔
      ∀ parameter sector,
        Function.Injective
          (finiteFamilySynthesis
            (ProjectedSectorVectors period hPeriod input parameter sector))) :=
  ⟨projectedKernelSectorGramDeterminant_ne_zero_iff_linearIndependent
      period hPeriod input,
    sectorNoCrossing_iff_forall_synthesis_injective period hPeriod input⟩

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelSectorIndependence4D
end JanusFormal