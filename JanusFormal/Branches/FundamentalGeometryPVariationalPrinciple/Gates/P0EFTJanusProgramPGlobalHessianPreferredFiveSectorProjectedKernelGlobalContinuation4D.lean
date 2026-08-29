import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteFamilyGramInjectivity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelBasisFamily4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelRegularTransport4D

/-!
# Exact global-continuation criterion for the projected physical kernel basis

The H12 basepoint now lies in a canonical open Gram-regular chart carrying a
complete projected physical basis and its exact coordinate transport.  The
remaining passage from this chart to the old all-real-parameter basis package
has one precise obstruction:

`det Gram(e~_i(a))` must never vanish.

This file proves exact equivalences between

* the regular set being all of `Real`;
* injectivity of the projected Gram operator at every parameter;
* the previous global Gram-nondegeneracy packet;
* existence of the global projected physical kernel basis family.

It also constructs the old downstream global basis-family interface directly
from the no-crossing statement.  Consequently global kernel continuation is no
longer hidden inside an abstract basis premise: it is exactly the assertion
that the genuine Candidate-A parameter family never leaves the already
constructed regular Fredholm chart.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelGlobalContinuation4D

set_option autoImplicit false
set_option maxHeartbeats 52000000
set_option synthInstance.maxHeartbeats 26000000
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
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedResolvedKernelFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelGram4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelBasisFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelRegularChart4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelRegularTransport4D
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

/-- The regular chart covers all real parameters exactly when the genuine
projected Gram operator is injective at every real parameter. -/
theorem projectedKernelRegularSet_eq_univ_iff
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input) :
    projectedKernelRegularSet period hPeriod input = Set.univ ↔
      ∀ parameter,
        Function.Injective
          (projectedKernelGramMap period hPeriod input natural parameter) := by
  constructor
  · intro hRegular parameter
    apply (mem_projectedKernelRegularSet_iff_gram_injective period hPeriod input
      natural parameter).mp
    rw [hRegular]
    exact Set.mem_univ parameter
  · intro hInjective
    ext parameter
    simp only [Set.mem_univ, iff_true]
    exact (mem_projectedKernelRegularSet_iff_gram_injective period hPeriod input
      natural parameter).mpr (hInjective parameter)

/-- The no-crossing statement constructs the former global Gram packet. -/
def projectedKernelGramNondegenerateOfRegularSetEqUniv
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (hRegular : projectedKernelRegularSet period hPeriod input = Set.univ) :
    GlobalHessianPreferredFiveSectorProjectedKernelGramNondegenerate4D
      period hPeriod input natural where
  gram_injective :=
    (projectedKernelRegularSet_eq_univ_iff period hPeriod input natural).mp
      hRegular

/-- Conversely, the former global Gram packet says precisely that the regular
chart is all of parameter space. -/
theorem projectedKernelRegularSet_eq_univ_of_gramNondegenerate
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (gram : GlobalHessianPreferredFiveSectorProjectedKernelGramNondegenerate4D
      period hPeriod input natural) :
    projectedKernelRegularSet period hPeriod input = Set.univ :=
  (projectedKernelRegularSet_eq_univ_iff period hPeriod input natural).mpr
    gram.gram_injective

/-- Exact equivalence between the geometric no-crossing criterion and the old
global Gram packet. -/
theorem projectedKernelRegularSet_eq_univ_iff_gramNondegenerate
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input) :
    projectedKernelRegularSet period hPeriod input = Set.univ ↔
      GlobalHessianPreferredFiveSectorProjectedKernelGramNondegenerate4D
        period hPeriod input natural :=
  ⟨projectedKernelGramNondegenerateOfRegularSetEqUniv period hPeriod input natural,
    projectedKernelRegularSet_eq_univ_of_gramNondegenerate period hPeriod input
      natural⟩

/-- A global projected physical basis family itself forces global Gram
nondegeneracy; the reverse implication was already the finite Gram-basis
construction. -/
def projectedKernelGramNondegenerateOfBasisFamily
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (physical : GlobalHessianPreferredFiveSectorProjectedKernelBasisFamily4D
      period hPeriod input natural) :
    GlobalHessianPreferredFiveSectorProjectedKernelGramNondegenerate4D
      period hPeriod input natural where
  gram_injective := by
    intro parameter
    unfold projectedKernelGramMap
    apply finiteFamilyGramMap_injective_of_synthesis_injective
    have hFamily :
        (fun mode =>
          projectedKernelSubtypeVector period hPeriod input natural parameter
            mode) =
          fun mode => physical.basis parameter mode := by
      funext mode
      apply Subtype.ext
      change
        projectedNamedKernelVector period hPeriod input parameter mode =
          (physical.basis parameter mode).1
      exact (physical.basis_agreement parameter mode).symm
    rw [hFamily]
    intro first second hEqual
    have hCoordinates :=
      congrArg (physical.basis parameter).equivFun hEqual
    simpa [finiteFamilySynthesis] using hCoordinates

/-- The global basis-family interface is reconstructed directly from the
statement that the regular chart covers all parameters. -/
def globalProjectedKernelBasisFamilyOfRegularSetEqUniv
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (hRegular : projectedKernelRegularSet period hPeriod input = Set.univ) :
    GlobalHessianPreferredFiveSectorProjectedKernelBasisFamily4D
      period hPeriod input natural :=
  (projectedKernelGramNondegenerateOfRegularSetEqUniv period hPeriod input natural
    hRegular).toProjectedKernelBasisFamily period hPeriod input natural

/-- Any global projected physical basis proves that the regular chart was
already all of parameter space. -/
theorem projectedKernelRegularSet_eq_univ_of_basisFamily
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (physical : GlobalHessianPreferredFiveSectorProjectedKernelBasisFamily4D
      period hPeriod input natural) :
    projectedKernelRegularSet period hPeriod input = Set.univ :=
  projectedKernelRegularSet_eq_univ_of_gramNondegenerate period hPeriod input
    natural
    (projectedKernelGramNondegenerateOfBasisFamily period hPeriod input natural
      physical)

/-- Existence of the downstream global physical basis package is equivalent to
the single no-Gram-crossing statement. -/
theorem nonempty_projectedKernelBasisFamily_iff_regularSet_eq_univ
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input) :
    Nonempty
        (GlobalHessianPreferredFiveSectorProjectedKernelBasisFamily4D
          period hPeriod input natural) ↔
      projectedKernelRegularSet period hPeriod input = Set.univ := by
  constructor
  · rintro ⟨physical⟩
    exact projectedKernelRegularSet_eq_univ_of_basisFamily period hPeriod input
      natural physical
  · intro hRegular
    exact ⟨globalProjectedKernelBasisFamilyOfRegularSetEqUniv period hPeriod input
      natural hRegular⟩

/-- Public exact global-continuation checkpoint. -/
theorem projected_kernel_global_continuation_gate
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input) :
    (projectedKernelRegularSet period hPeriod input = Set.univ ↔
      GlobalHessianPreferredFiveSectorProjectedKernelGramNondegenerate4D
        period hPeriod input natural) ∧
    (projectedKernelRegularSet period hPeriod input = Set.univ ↔
      Nonempty
        (GlobalHessianPreferredFiveSectorProjectedKernelBasisFamily4D
          period hPeriod input natural)) := by
  constructor
  · exact projectedKernelRegularSet_eq_univ_iff_gramNondegenerate period hPeriod
      input natural
  · exact
      (nonempty_projectedKernelBasisFamily_iff_regularSet_eq_univ period hPeriod
        input natural).symm

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelGlobalContinuation4D
end JanusFormal
