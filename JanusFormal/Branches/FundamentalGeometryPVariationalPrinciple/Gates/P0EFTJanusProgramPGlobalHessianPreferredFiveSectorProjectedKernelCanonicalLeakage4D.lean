import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelNamedSectorReference4D

/-!
# Canonically conditioned projection-leakage criterion

The original named sector subfamily already carries a canonically selected
positive coefficient lower bound `m(parameter, sector)`.  Therefore a global
physical continuation proof no longer needs to supply a separate reference
lower-bound packet.

It is enough to produce, for every parameter and physical sector, a leakage
constant `delta(parameter, sector)` satisfying

`delta < m`

and

`‖(1 - P_s) S_named,s(c)‖ ≤ delta ‖c‖`.

The canonical lower estimate then gives the strict projection-angle condition,
which rules out sector Gram crossings and constructs the global projected
physical basis together with its C1 family-index closure.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelCanonicalLeakage4D

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 2000000
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
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyH10Reduction4D
open P0EFTJanusProgramPGlobalCandidateACanonicalSixDenseCore4D
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusProgramPGlobalHessianDiracGreenBoundedClosure4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalBlockBounds4D
open P0EFTJanusProgramPGlobalHessianActualKernelFrontier4D
open P0EFTJanusProgramPGlobalCandidateAFaithfulFredholmSum4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorBismutFreedFamily4D
open P0EFTJanusProgramPGlobalCandidateAFiveSectorCompletionResolutionBridge4D
open P0EFTJanusProgramPFiniteFamilyGramBasis4D
open P0EFTJanusProgramPFiveSectorHilbertCoordinates4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorRepresentation4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorResolvedKernelFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedResolvedKernelFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelBasisFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedPhysicalNamedKernelFamilyClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelGramBlocks4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelSectorNoCrossing4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelSectorIndependence4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelProjectionLeakage4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelNamedSectorReference4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelRegularChart4D
open P0EFTJanusProgramPDenseCoreChartBilinearBound4D
open P0EFTJanusCircleDiracHeatTraceCancellation

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace
  P0EFTJanusProgramPGlobalHessianPreferredFiveSectorBismutFreedFamily4D.candidateAHilbertNormedAddCommGroup
  P0EFTJanusProgramPGlobalHessianPreferredFiveSectorBismutFreedFamily4D.candidateAHilbertInnerProductSpace
  P0EFTJanusProgramPGlobalHessianPreferredFiveSectorBismutFreedFamily4D.candidateAHilbertNormedSpace
  P0EFTJanusProgramPGlobalHessianPreferredFiveSectorBismutFreedFamily4D.candidateAHilbertModule
  P0EFTJanusProgramPGlobalHessianPreferredFiveSectorBismutFreedFamily4D.candidateAHilbertCompleteSpace

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

variable {measure : Measure (EffectiveQuotient period hPeriod)}

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
      (measure := measure) period hPeriod configuration data analysis
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
    {Metric Abelian Matter Longitudinal Boundary : Type}
    [NormedAddCommGroup Metric] [InnerProductSpace Real Metric]
    [NormedAddCommGroup Abelian] [InnerProductSpace Real Abelian]
    [NormedAddCommGroup Matter] [InnerProductSpace Real Matter]
    [NormedAddCommGroup Longitudinal] [InnerProductSpace Real Longitudinal]
    [NormedAddCommGroup Boundary] [InnerProductSpace Real Boundary]
    {ZeroMode : Type} [Fintype ZeroMode] [DecidableEq ZeroMode]
    {fold : Fold} {Index : Type*}

/-- Pointwise leakage constants measured against the canonical conditioning of
the original named sector subfamilies. -/
structure GlobalHessianPreferredFiveSectorProjectedKernelCanonicalLeakage4D
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index) :
    Type where
  leakageConstant : Real → FivePhysicalSector → Real
  leakageConstant_nonneg : ∀ parameter sector,
    0 ≤ leakageConstant parameter sector
  leakage_lt_namedLower : ∀ parameter sector,
    leakageConstant parameter sector <
      namedSectorSynthesisLowerConstant period hPeriod input parameter sector
  projection_leakage_bound : ∀ parameter sector coefficient,
    ‖finiteFamilySynthesis
        (NamedSectorVectors period hPeriod input parameter sector) coefficient -
      (Coordinates period hPeriod input).sectorProjector sector
        (finiteFamilySynthesis
          (NamedSectorVectors period hPeriod input parameter sector) coefficient)‖ ≤
      leakageConstant parameter sector * ‖coefficient‖

namespace GlobalHessianPreferredFiveSectorProjectedKernelCanonicalLeakage4D

/-- Canonically conditioned leakage gives the strict physical projection angle. -/
def toStrictProjectionAngle
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (leakage :
      GlobalHessianPreferredFiveSectorProjectedKernelCanonicalLeakage4D
        period hPeriod input) :
    GlobalHessianPreferredFiveSectorProjectedKernelStrictProjectionAngle4D
      period hPeriod input where
  leakage_strict := by
    intro parameter sector coefficient hCoefficient
    have hCoefficientNorm : 0 < ‖coefficient‖ := norm_pos_iff.mpr hCoefficient
    have hLeakageScaled :
        leakage.leakageConstant parameter sector * ‖coefficient‖ <
          namedSectorSynthesisLowerConstant period hPeriod input parameter sector *
            ‖coefficient‖ :=
      mul_lt_mul_of_pos_right
        (leakage.leakage_lt_namedLower parameter sector) hCoefficientNorm
    exact (leakage.projection_leakage_bound parameter sector coefficient).trans_lt
      (hLeakageScaled.trans_le
        (namedSectorSynthesisLowerConstant_mul_norm_le period hPeriod input
          parameter sector coefficient))

/-- Canonically conditioned leakage rules out all sector Gram crossings. -/
def toSectorNoCrossing
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (leakage :
      GlobalHessianPreferredFiveSectorProjectedKernelCanonicalLeakage4D
        period hPeriod input) :
    GlobalHessianPreferredFiveSectorProjectedKernelSectorNoCrossing4D
      period hPeriod input :=
  (leakage.toStrictProjectionAngle period hPeriod input).toSectorNoCrossing
    period hPeriod input

/-- Canonically conditioned leakage closes the global projected regular chart. -/
theorem regularSet_eq_univ
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (leakage :
      GlobalHessianPreferredFiveSectorProjectedKernelCanonicalLeakage4D
        period hPeriod input) :
    projectedKernelRegularSet period hPeriod input = Set.univ :=
  (leakage.toSectorNoCrossing period hPeriod input).regularSet_eq_univ period
    hPeriod input

/-- Canonically conditioned leakage constructs the global projected physical
basis. -/
def toProjectedPhysicalBasisFamily
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (leakage :
      GlobalHessianPreferredFiveSectorProjectedKernelCanonicalLeakage4D
        period hPeriod input) :
    GlobalHessianPreferredFiveSectorProjectedKernelBasisFamily4D
      period hPeriod input natural :=
  (leakage.toSectorNoCrossing period hPeriod input).toProjectedPhysicalBasisFamily
    period hPeriod input natural

/-- Canonically conditioned leakage rebuilds the existing family-index closure
with the projected physical basis. -/
def toProjectedPhysicalNamedKernelFamilyClosure
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (leakage :
      GlobalHessianPreferredFiveSectorProjectedKernelCanonicalLeakage4D
        period hPeriod input) :
    GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index :=
  (leakage.toSectorNoCrossing period hPeriod input).toProjectedPhysicalNamedKernelFamilyClosure
    period hPeriod input natural

/-- The rebuilt projected physical family retains ambient C1 regularity. -/
def toProjectedPhysicalNamedKernelFamilyRegularity
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (regularity : GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
      period hPeriod input)
    (leakage :
      GlobalHessianPreferredFiveSectorProjectedKernelCanonicalLeakage4D
        period hPeriod input) :
    GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
      period hPeriod
        (leakage.toProjectedPhysicalNamedKernelFamilyClosure period hPeriod input
          natural) :=
  (leakage.toSectorNoCrossing period hPeriod input).toProjectedPhysicalNamedKernelFamilyRegularity
    period hPeriod input natural regularity

/-- Public canonical-leakage continuation checkpoint. -/
theorem projected_kernel_canonical_leakage_gate
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (regularity : GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
      period hPeriod input)
    (leakage :
      GlobalHessianPreferredFiveSectorProjectedKernelCanonicalLeakage4D
        period hPeriod input) :
    (∀ parameter sector,
      0 < namedSectorSynthesisLowerConstant period hPeriod input parameter sector) ∧
    GlobalHessianPreferredFiveSectorProjectedKernelStrictProjectionAngle4D
      period hPeriod input ∧
    (∀ parameter sector,
      projectedKernelSectorGramDeterminant period hPeriod input parameter sector ≠ 0) ∧
    projectedKernelRegularSet period hPeriod input = Set.univ ∧
    Nonempty
      (GlobalHessianPreferredFiveSectorProjectedKernelBasisFamily4D
        period hPeriod input natural) ∧
    GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
      period hPeriod
        (leakage.toProjectedPhysicalNamedKernelFamilyClosure period hPeriod input
          natural) :=
  ⟨namedSectorSynthesisLowerConstant_pos period hPeriod input,
    leakage.toStrictProjectionAngle period hPeriod input,
    (leakage.toSectorNoCrossing period hPeriod input).determinant_ne_zero,
    leakage.regularSet_eq_univ period hPeriod input,
    ⟨leakage.toProjectedPhysicalBasisFamily period hPeriod input natural⟩,
    leakage.toProjectedPhysicalNamedKernelFamilyRegularity period hPeriod input
      natural regularity⟩

end GlobalHessianPreferredFiveSectorProjectedKernelCanonicalLeakage4D

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelCanonicalLeakage4D
end JanusFormal
