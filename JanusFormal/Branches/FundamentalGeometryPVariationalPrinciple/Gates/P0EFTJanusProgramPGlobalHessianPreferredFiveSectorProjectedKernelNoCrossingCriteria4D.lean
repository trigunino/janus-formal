import Mathlib.Topology.Connected.Clopen
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedPhysicalNamedKernelFamilyClosure4D

/-!
# Checkable global no-crossing criteria for the projected physical kernel

The global projected basis exists exactly when the open Gram-regular set is all
of `Real`.  This file provides two concrete ways to discharge that statement.

1. **Topological continuation.**  The regular set is already open and contains
   the H12 basepoint.  Since `Real` is preconnected, proving that this set is
   also closed forces it to be all of `Real`.

2. **Quantitative continuation.**  A strictly positive uniform lower bound on
   the absolute projected Gram determinant prevents every crossing directly.

Both criteria feed the same previously constructed physical named-kernel
closure.  They do not add a new operator, kernel or determinant family; they
are alternative proof routes for the one remaining scalar continuation fact.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelNoCrossingCriteria4D

set_option autoImplicit false
set_option maxHeartbeats 56000000
set_option synthInstance.maxHeartbeats 28000000
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
open P0EFTJanusProgramPFiniteFamilyGramLocalPersistence4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedResolvedKernelFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelRegularChart4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelGlobalContinuation4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelBasisFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedPhysicalNamedKernelFamilyClosure4D
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

/-- On the connected real parameter line, closedness of the already open
regular set is enough to prove global continuation. -/
theorem projectedKernelRegularSet_eq_univ_of_isClosed
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (regularity : GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
      period hPeriod input)
    (hClosed : IsClosed (projectedKernelRegularSet period hPeriod input)) :
    projectedKernelRegularSet period hPeriod input = Set.univ := by
  apply IsClopen.eq_univ
  · exact ⟨hClosed,
      isOpen_projectedKernelRegularSet period hPeriod input regularity⟩
  · exact ⟨0,
      zero_mem_projectedKernelRegularSet period hPeriod input natural⟩

/-- A positive uniform absolute-determinant lower bound rules out all projected
Gram crossings. -/
theorem projectedKernelRegularSet_eq_univ_of_uniformDeterminantBound
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (margin : Real) (hMargin : 0 < margin)
    (hBound : ∀ parameter,
      margin ≤
        |(finiteFamilyGramMatrix
          (fun mode =>
            projectedNamedKernelVector period hPeriod input parameter mode)).det|) :
    projectedKernelRegularSet period hPeriod input = Set.univ := by
  ext parameter
  simp only [Set.mem_univ, iff_true]
  change
    (finiteFamilyGramMatrix
      (fun mode =>
        projectedNamedKernelVector period hPeriod input parameter mode)).det ≠ 0
  apply abs_pos.mp
  exact lt_of_lt_of_le hMargin (hBound parameter)

/-- Quantitative all-parameter projected Gram gap.  This is a single checkable
scalar estimate, not a replacement basis premise. -/
structure GlobalHessianPreferredFiveSectorProjectedKernelUniformGramGap4D
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index) :
    Type where
  margin : Real
  margin_pos : 0 < margin
  determinant_lower_bound : ∀ parameter,
    margin ≤
      |(finiteFamilyGramMatrix
        (fun mode =>
          projectedNamedKernelVector period hPeriod input parameter mode)).det|

namespace GlobalHessianPreferredFiveSectorProjectedKernelUniformGramGap4D

/-- A uniform Gram gap closes the exact no-crossing criterion. -/
theorem regularSet_eq_univ
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (gap : GlobalHessianPreferredFiveSectorProjectedKernelUniformGramGap4D
      period hPeriod input) :
    projectedKernelRegularSet period hPeriod input = Set.univ :=
  projectedKernelRegularSet_eq_univ_of_uniformDeterminantBound period hPeriod input
    gap.margin gap.margin_pos gap.determinant_lower_bound

/-- A uniform Gram gap constructs the canonical global projected physical basis. -/
def toProjectedPhysicalBasisFamily
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (gap : GlobalHessianPreferredFiveSectorProjectedKernelUniformGramGap4D
      period hPeriod input) :
    GlobalHessianPreferredFiveSectorProjectedKernelBasisFamily4D
      period hPeriod input natural :=
  projectedPhysicalBasisFamily period hPeriod input natural
    (gap.regularSet_eq_univ period hPeriod input)

/-- A uniform Gram gap rebuilds the existing family-index closure with the C1
sector-pure physical basis. -/
def toProjectedPhysicalNamedKernelFamilyClosure
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (gap : GlobalHessianPreferredFiveSectorProjectedKernelUniformGramGap4D
      period hPeriod input) :
    GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index :=
  projectedPhysicalNamedKernelFamilyClosure period hPeriod input natural
    (gap.regularSet_eq_univ period hPeriod input)

/-- The rebuilt physical family inherits C1 regularity. -/
def toProjectedPhysicalNamedKernelFamilyRegularity
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (regularity : GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
      period hPeriod input)
    (gap : GlobalHessianPreferredFiveSectorProjectedKernelUniformGramGap4D
      period hPeriod input) :
    GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
      period hPeriod
        (gap.toProjectedPhysicalNamedKernelFamilyClosure period hPeriod input
          natural) :=
  projectedPhysicalNamedKernelFamilyRegularity period hPeriod input natural
    regularity (gap.regularSet_eq_univ period hPeriod input)

/-- Public quantitative continuation checkpoint. -/
theorem projected_kernel_uniform_gram_gap_gate
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (regularity : GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
      period hPeriod input)
    (gap : GlobalHessianPreferredFiveSectorProjectedKernelUniformGramGap4D
      period hPeriod input) :
    projectedKernelRegularSet period hPeriod input = Set.univ ∧
    Nonempty
      (GlobalHessianPreferredFiveSectorProjectedKernelBasisFamily4D
        period hPeriod input natural) ∧
    GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
      period hPeriod
        (gap.toProjectedPhysicalNamedKernelFamilyClosure period hPeriod input
          natural) :=
  ⟨gap.regularSet_eq_univ period hPeriod input,
    ⟨gap.toProjectedPhysicalBasisFamily period hPeriod input natural⟩,
    gap.toProjectedPhysicalNamedKernelFamilyRegularity period hPeriod input
      natural regularity⟩

end GlobalHessianPreferredFiveSectorProjectedKernelUniformGramGap4D

/-- Public topological continuation checkpoint. -/
theorem projected_kernel_closed_regular_set_gate
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (regularity : GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
      period hPeriod input)
    (hClosed : IsClosed (projectedKernelRegularSet period hPeriod input)) :
    projectedKernelRegularSet period hPeriod input = Set.univ ∧
    Nonempty
      (GlobalHessianPreferredFiveSectorProjectedKernelBasisFamily4D
        period hPeriod input natural) := by
  let hGlobal := projectedKernelRegularSet_eq_univ_of_isClosed period hPeriod input
    natural regularity hClosed
  exact
    ⟨hGlobal,
      ⟨globalProjectedKernelBasisFamilyOfRegularSetEqUniv period hPeriod input
        natural hGlobal⟩⟩

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelNoCrossingCriteria4D
end JanusFormal
