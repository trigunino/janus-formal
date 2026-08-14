import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteFamilySynthesisLowerBound4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelProjectionLeakage4D

/-!
# Named-sector conditioning and strict physical projection angle

The original named kernel vectors form a basis of the actual kernel at every
parameter.  Every subfamily selected by one physical sector label is therefore
linearly independent in the ambient Candidate-A Hilbert space.  Its coefficient
synthesis map is injective and automatically has a positive pointwise lower
bound; this pointwise conditioning is not an additional premise.

For the projected family, a still simpler sufficient condition is available.
If every nonzero named-sector coefficient combination loses strictly less than
its whole norm under projection onto the assigned physical sector, then the
projected combination cannot vanish.  This strict-angle condition rules out all
sector Gram crossings and closes the global projected physical kernel family.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelNamedSectorReference4D

set_option autoImplicit false
set_option maxHeartbeats 88000000
set_option synthInstance.maxHeartbeats 44000000
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
open P0EFTJanusProgramPFiniteFamilySynthesisLowerBound4D
open P0EFTJanusProgramPFiveSectorHilbertCoordinates4D
open P0EFTJanusProgramPFiniteKernelBasisFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedResolvedKernelFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelBasisFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedPhysicalNamedKernelFamilyClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelGramBlocks4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelSectorNoCrossing4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelSectorIndependence4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelProjectionLeakage4D
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

private abbrev NamedSectorVectors
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (parameter : Real) (sector : FivePhysicalSector) :=
  fun mode : ProjectedSectorMode period hPeriod input sector =>
    input.kernels.vector parameter mode.1

private abbrev ProjectedSectorVectors
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (parameter : Real) (sector : FivePhysicalSector) :=
  fun mode : ProjectedSectorMode period hPeriod input sector =>
    projectedNamedKernelVector period hPeriod input parameter mode.1

/-- The whole named kernel basis is linearly independent after coercion from the
kernel subtype into the ambient Hilbert space. -/
theorem namedKernelVectors_linearIndependent
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (parameter : Real) :
    LinearIndependent Real (fun mode => input.kernels.vector parameter mode) := by
  have hKernel := (input.kernels.basis parameter).linearIndependent
  have hAmbient := hKernel.map'
    (input.familyIndex.baseFamily.actualOperator parameter).ker.subtype (by simp)
  simpa [FiniteKernelBasisFamilyData.vector, Function.comp_def] using hAmbient

/-- Every physical-label subfamily of the named kernel basis is linearly
independent. -/
theorem namedSectorVectors_linearIndependent
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (parameter : Real) (sector : FivePhysicalSector) :
    LinearIndependent Real
      (NamedSectorVectors period hPeriod input parameter sector) := by
  simpa [NamedSectorVectors] using
    (namedKernelVectors_linearIndependent period hPeriod input parameter).comp
      (fun mode : ProjectedSectorMode period hPeriod input sector => mode.1)
      Subtype.val_injective

/-- Named-sector coefficient synthesis is injective at every parameter. -/
theorem namedSectorSynthesis_injective
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (parameter : Real) (sector : FivePhysicalSector) :
    Function.Injective
      (finiteFamilySynthesis
        (NamedSectorVectors period hPeriod input parameter sector)) :=
  (finiteFamilySynthesis_injective_iff_linearIndependent
    (NamedSectorVectors period hPeriod input parameter sector)).mpr
      (namedSectorVectors_linearIndependent period hPeriod input parameter sector)

/-- Canonical positive pointwise conditioning constant of the original named
sector subfamily. -/
def namedSectorSynthesisLowerConstant
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (parameter : Real) (sector : FivePhysicalSector) : Real :=
  finiteFamilySynthesisLowerConstant
    (NamedSectorVectors period hPeriod input parameter sector)
    (namedSectorSynthesis_injective period hPeriod input parameter sector)

/-- The canonical named-sector conditioning constant is positive. -/
theorem namedSectorSynthesisLowerConstant_pos
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (parameter : Real) (sector : FivePhysicalSector) :
    0 < namedSectorSynthesisLowerConstant period hPeriod input parameter sector :=
  finiteFamilySynthesisLowerConstant_pos
    (NamedSectorVectors period hPeriod input parameter sector)
    (namedSectorSynthesis_injective period hPeriod input parameter sector)

/-- Pointwise lower estimate carried automatically by the original named-sector
basis. -/
theorem namedSectorSynthesisLowerConstant_mul_norm_le
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (parameter : Real) (sector : FivePhysicalSector)
    (coefficient : ProjectedSectorMode period hPeriod input sector → Real) :
    namedSectorSynthesisLowerConstant period hPeriod input parameter sector *
        ‖coefficient‖ ≤
      ‖finiteFamilySynthesis
        (NamedSectorVectors period hPeriod input parameter sector) coefficient‖ :=
  finiteFamilySynthesisLowerConstant_mul_norm_le
    (NamedSectorVectors period hPeriod input parameter sector)
    (namedSectorSynthesis_injective period hPeriod input parameter sector)
    coefficient

/-- Strict physical projection-angle condition.  Every nonzero named-sector
combination retains a nonzero physical-sector component. -/
structure GlobalHessianPreferredFiveSectorProjectedKernelStrictProjectionAngle4D
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index) :
    Prop where
  leakage_strict : ∀ parameter sector coefficient,
    coefficient ≠ 0 →
      ‖finiteFamilySynthesis
          (NamedSectorVectors period hPeriod input parameter sector) coefficient -
        (Coordinates period hPeriod input).sectorProjector sector
          (finiteFamilySynthesis
            (NamedSectorVectors period hPeriod input parameter sector)
            coefficient)‖ <
      ‖finiteFamilySynthesis
        (NamedSectorVectors period hPeriod input parameter sector) coefficient‖

namespace GlobalHessianPreferredFiveSectorProjectedKernelStrictProjectionAngle4D

/-- A strict projection angle forces projected sector synthesis to be injective. -/
theorem projectedSynthesis_injective
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (angle :
      GlobalHessianPreferredFiveSectorProjectedKernelStrictProjectionAngle4D
        period hPeriod input)
    (parameter : Real) (sector : FivePhysicalSector) :
    Function.Injective
      (finiteFamilySynthesis
        (ProjectedSectorVectors period hPeriod input parameter sector)) := by
  intro first second hEqual
  let difference := first - second
  have hProjectedZero :
      finiteFamilySynthesis
          (ProjectedSectorVectors period hPeriod input parameter sector)
          difference = 0 := by
    dsimp [difference]
    rw [map_sub, hEqual, sub_self]
  by_contra hFirstSecond
  have hDifferenceNonzero : difference ≠ 0 := by
    exact sub_ne_zero.mpr hFirstSecond
  have hStrict :=
    angle.leakage_strict parameter sector difference hDifferenceNonzero
  have hProjectionZero :
      (Coordinates period hPeriod input).sectorProjector sector
        (finiteFamilySynthesis
          (NamedSectorVectors period hPeriod input parameter sector)
          difference) = 0 := by
    rw [← projectedSectorSynthesis_eq_sectorProjector_namedSectorSynthesis
      period hPeriod input parameter sector difference]
    exact hProjectedZero
  rw [hProjectionZero, sub_zero] at hStrict
  exact (lt_irrefl _) hStrict

/-- Strict projection angle rules out every sector Gram crossing. -/
def toSectorNoCrossing
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (angle :
      GlobalHessianPreferredFiveSectorProjectedKernelStrictProjectionAngle4D
        period hPeriod input) :
    GlobalHessianPreferredFiveSectorProjectedKernelSectorNoCrossing4D
      period hPeriod input where
  determinant_ne_zero := by
    intro parameter sector
    exact
      (projectedKernelSectorGramDeterminant_ne_zero_iff_synthesis_injective
        period hPeriod input parameter sector).mpr
          (angle.projectedSynthesis_injective period hPeriod input parameter
            sector)

/-- Strict projection angle closes the full projected regular chart. -/
theorem regularSet_eq_univ
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (angle :
      GlobalHessianPreferredFiveSectorProjectedKernelStrictProjectionAngle4D
        period hPeriod input) :
    projectedKernelRegularSet period hPeriod input = Set.univ :=
  (angle.toSectorNoCrossing period hPeriod input).regularSet_eq_univ period hPeriod
    input

/-- Strict projection angle constructs the global projected physical basis. -/
def toProjectedPhysicalBasisFamily
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (angle :
      GlobalHessianPreferredFiveSectorProjectedKernelStrictProjectionAngle4D
        period hPeriod input) :
    GlobalHessianPreferredFiveSectorProjectedKernelBasisFamily4D
      period hPeriod input natural :=
  (angle.toSectorNoCrossing period hPeriod input).
    toProjectedPhysicalBasisFamily period hPeriod input natural

/-- Strict projection angle rebuilds the existing family-index closure with the
projected physical basis. -/
def toProjectedPhysicalNamedKernelFamilyClosure
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (angle :
      GlobalHessianPreferredFiveSectorProjectedKernelStrictProjectionAngle4D
        period hPeriod input) :
    GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index :=
  (angle.toSectorNoCrossing period hPeriod input).
    toProjectedPhysicalNamedKernelFamilyClosure period hPeriod input natural

/-- The rebuilt projected physical family retains ambient C1 regularity. -/
def toProjectedPhysicalNamedKernelFamilyRegularity
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (regularity : GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
      period hPeriod input)
    (angle :
      GlobalHessianPreferredFiveSectorProjectedKernelStrictProjectionAngle4D
        period hPeriod input) :
    GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
      period hPeriod
        (angle.toProjectedPhysicalNamedKernelFamilyClosure period hPeriod input
          natural) :=
  (angle.toSectorNoCrossing period hPeriod input).
    toProjectedPhysicalNamedKernelFamilyRegularity period hPeriod input natural
      regularity

/-- Public strict-angle continuation checkpoint. -/
theorem projected_kernel_strict_projection_angle_gate
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (regularity : GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
      period hPeriod input)
    (angle :
      GlobalHessianPreferredFiveSectorProjectedKernelStrictProjectionAngle4D
        period hPeriod input) :
    (∀ parameter sector,
      LinearIndependent Real
        (NamedSectorVectors period hPeriod input parameter sector)) ∧
    (∀ parameter sector,
      0 < namedSectorSynthesisLowerConstant period hPeriod input parameter sector) ∧
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
        (angle.toProjectedPhysicalNamedKernelFamilyClosure period hPeriod input
          natural) :=
  ⟨namedSectorVectors_linearIndependent period hPeriod input,
    namedSectorSynthesisLowerConstant_pos period hPeriod input,
    angle.projectedSynthesis_injective period hPeriod input,
    (angle.toSectorNoCrossing period hPeriod input).determinant_ne_zero,
    angle.regularSet_eq_univ period hPeriod input,
    ⟨angle.toProjectedPhysicalBasisFamily period hPeriod input natural⟩,
    angle.toProjectedPhysicalNamedKernelFamilyRegularity period hPeriod input
      natural regularity⟩

end GlobalHessianPreferredFiveSectorProjectedKernelStrictProjectionAngle4D

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelNamedSectorReference4D
end JanusFormal