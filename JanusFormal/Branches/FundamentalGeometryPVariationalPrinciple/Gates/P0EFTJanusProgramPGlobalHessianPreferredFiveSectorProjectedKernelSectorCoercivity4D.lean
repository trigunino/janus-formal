import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteFamilyGramQuadratic4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelSectorIndependence4D

/-!
# Sectorwise quadratic coercivity for the projected physical kernel

For each physical sector, the matrix quadratic form of the projected Gram block
is exactly the squared norm of coefficient synthesis.  Hence a positive uniform
quadratic lower estimate

`c_s * ‖a‖^2 ≤ a dot G_s(parameter) a`

forces injectivity of the sector synthesis map at every parameter.  By the
preceding equivalences this rules out every sector Gram crossing, and therefore
constructs the global projected physical kernel basis and the rebuilt C1
family-index closure.

This is the analytic interface expected from a genuine sector estimate: no
explicit determinant calculation is required once the quadratic lower bound is
proved.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelSectorCoercivity4D

set_option autoImplicit false
set_option maxHeartbeats 76000000
set_option synthInstance.maxHeartbeats 38000000
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
open P0EFTJanusProgramPFiniteFamilyGramLocalPersistence4D
open P0EFTJanusProgramPFiniteFamilyGramQuadratic4D
open P0EFTJanusProgramPFiveSectorHilbertCoordinates4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedResolvedKernelFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelBasisFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedPhysicalNamedKernelFamilyClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelGramBlocks4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelSectorNoCrossing4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelSectorIndependence4D
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

/-- The matrix action of a physical Gram block is the generic coefficient Gram
endomorphism of the corresponding projected vectors. -/
theorem projectedKernelSectorGramMatrix_mulVec
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (parameter : Real) (sector : FivePhysicalSector)
    (coefficient : ProjectedSectorMode period hPeriod input sector → Real) :
    projectedKernelSectorGramMatrix period hPeriod input parameter sector *ᵥ
        coefficient =
      finiteFamilyGramMap
        (ProjectedSectorVectors period hPeriod input parameter sector)
        coefficient := by
  exact finiteFamilyGramMatrix_mulVec
    (ProjectedSectorVectors period hPeriod input parameter sector) coefficient

/-- The sector Gram matrix quadratic form is exactly the squared norm of sector
coefficient synthesis. -/
theorem projectedKernelSectorGramQuadratic_eq_norm_sq
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (parameter : Real) (sector : FivePhysicalSector)
    (coefficient : ProjectedSectorMode period hPeriod input sector → Real) :
    dotProduct coefficient
        (projectedKernelSectorGramMatrix period hPeriod input parameter sector *ᵥ
          coefficient) =
      ‖finiteFamilySynthesis
        (ProjectedSectorVectors period hPeriod input parameter sector)
        coefficient‖ ^ 2 := by
  rw [projectedKernelSectorGramMatrix_mulVec period hPeriod input parameter sector
    coefficient]
  exact finiteFamilyGramQuadratic_eq_norm_sq
    (ProjectedSectorVectors period hPeriod input parameter sector) coefficient

/-- Positive uniform quadratic coercivity of every physical projected Gram
block. -/
structure GlobalHessianPreferredFiveSectorProjectedKernelUniformSectorGramCoercivity4D
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index) :
    Prop where
  coercivityConstant : FivePhysicalSector → Real
  coercivityConstant_pos : ∀ sector, 0 < coercivityConstant sector
  quadratic_lower_bound : ∀ parameter sector coefficient,
    coercivityConstant sector * ‖coefficient‖ ^ 2 ≤
      dotProduct coefficient
        (projectedKernelSectorGramMatrix period hPeriod input parameter sector *ᵥ
          coefficient)

namespace GlobalHessianPreferredFiveSectorProjectedKernelUniformSectorGramCoercivity4D

/-- Sector Gram coercivity forces injectivity of coefficient synthesis. -/
theorem synthesis_injective
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (coercivity :
      GlobalHessianPreferredFiveSectorProjectedKernelUniformSectorGramCoercivity4D
        period hPeriod input)
    (parameter : Real) (sector : FivePhysicalSector) :
    Function.Injective
      (finiteFamilySynthesis
        (ProjectedSectorVectors period hPeriod input parameter sector)) := by
  apply finiteFamilySynthesis_injective_of_gramQuadratic_lower_bound
    (ProjectedSectorVectors period hPeriod input parameter sector)
    (coercivity.coercivityConstant sector)
    (coercivity.coercivityConstant_pos sector)
  intro coefficient
  have hBound := coercivity.quadratic_lower_bound parameter sector coefficient
  rw [projectedKernelSectorGramMatrix_mulVec period hPeriod input parameter sector
    coefficient] at hBound
  exact hBound

/-- Sector Gram coercivity rules out every physical Gram crossing. -/
def toSectorNoCrossing
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (coercivity :
      GlobalHessianPreferredFiveSectorProjectedKernelUniformSectorGramCoercivity4D
        period hPeriod input) :
    GlobalHessianPreferredFiveSectorProjectedKernelSectorNoCrossing4D
      period hPeriod input where
  determinant_ne_zero := by
    intro parameter sector
    exact
      (projectedKernelSectorGramDeterminant_ne_zero_iff_synthesis_injective
        period hPeriod input parameter sector).mpr
          (coercivity.synthesis_injective period hPeriod input parameter sector)

/-- Sector Gram coercivity closes the full projected regular chart. -/
theorem regularSet_eq_univ
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (coercivity :
      GlobalHessianPreferredFiveSectorProjectedKernelUniformSectorGramCoercivity4D
        period hPeriod input) :
    projectedKernelRegularSet period hPeriod input = Set.univ :=
  (coercivity.toSectorNoCrossing period hPeriod input).regularSet_eq_univ
    period hPeriod input

/-- Sector Gram coercivity constructs the global projected physical basis. -/
def toProjectedPhysicalBasisFamily
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (coercivity :
      GlobalHessianPreferredFiveSectorProjectedKernelUniformSectorGramCoercivity4D
        period hPeriod input) :
    GlobalHessianPreferredFiveSectorProjectedKernelBasisFamily4D
      period hPeriod input natural :=
  (coercivity.toSectorNoCrossing period hPeriod input).
    toProjectedPhysicalBasisFamily period hPeriod input natural

/-- Sector Gram coercivity rebuilds the existing family-index closure with the
projected physical basis. -/
def toProjectedPhysicalNamedKernelFamilyClosure
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (coercivity :
      GlobalHessianPreferredFiveSectorProjectedKernelUniformSectorGramCoercivity4D
        period hPeriod input) :
    GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index :=
  (coercivity.toSectorNoCrossing period hPeriod input).
    toProjectedPhysicalNamedKernelFamilyClosure period hPeriod input natural

/-- The rebuilt projected physical closure retains ambient C1 regularity. -/
def toProjectedPhysicalNamedKernelFamilyRegularity
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (regularity : GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
      period hPeriod input)
    (coercivity :
      GlobalHessianPreferredFiveSectorProjectedKernelUniformSectorGramCoercivity4D
        period hPeriod input) :
    GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
      period hPeriod
        (coercivity.toProjectedPhysicalNamedKernelFamilyClosure period hPeriod input
          natural) :=
  (coercivity.toSectorNoCrossing period hPeriod input).
    toProjectedPhysicalNamedKernelFamilyRegularity period hPeriod input natural
      regularity

/-- Public sector Gram-coercivity continuation checkpoint. -/
theorem projected_kernel_uniform_sector_gram_coercivity_gate
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (regularity : GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
      period hPeriod input)
    (coercivity :
      GlobalHessianPreferredFiveSectorProjectedKernelUniformSectorGramCoercivity4D
        period hPeriod input) :
    (∀ parameter sector coefficient,
      dotProduct coefficient
          (projectedKernelSectorGramMatrix period hPeriod input parameter sector *ᵥ
            coefficient) =
        ‖finiteFamilySynthesis
          (ProjectedSectorVectors period hPeriod input parameter sector)
          coefficient‖ ^ 2) ∧
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
        (coercivity.toProjectedPhysicalNamedKernelFamilyClosure period hPeriod input
          natural) :=
  ⟨projectedKernelSectorGramQuadratic_eq_norm_sq period hPeriod input,
    coercivity.synthesis_injective period hPeriod input,
    (coercivity.toSectorNoCrossing period hPeriod input).determinant_ne_zero,
    coercivity.regularSet_eq_univ period hPeriod input,
    ⟨coercivity.toProjectedPhysicalBasisFamily period hPeriod input natural⟩,
    coercivity.toProjectedPhysicalNamedKernelFamilyRegularity period hPeriod input
      natural regularity⟩

end GlobalHessianPreferredFiveSectorProjectedKernelUniformSectorGramCoercivity4D

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelSectorCoercivity4D
end JanusFormal