import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteFamilyGramLocalPersistence4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelGramBasepoint4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D

/-!
# Local persistence of the projected physical kernel Gram family

The projected Candidate-A zero modes live in the common ambient Hilbert space
and are differentiable there.  Their scalar Gram matrix is therefore
continuous.  The same matrix is obtained after regarding the vectors as
members of the varying true-kernel subtype: the subtype changes with the
parameter, but all scalar inner products are the ambient ones.

The projected Gram operator is already nondegenerate at the H12 basepoint.
Finite-dimensional determinant continuity now propagates this fact to a genuine
neighbourhood of `a = 0`.

Thus local completeness of the five-sector projected physical zero modes is no
longer an all-parameter premise.  The remaining global issue is continuation
beyond this basepoint neighbourhood.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelGramLocalPersistence4D

set_option autoImplicit false
set_option maxHeartbeats 44000000
set_option synthInstance.maxHeartbeats 22000000
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
open P0EFTJanusProgramPFiniteFamilyGramLocalPersistence4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalFamilyCommutation4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D.GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorResolvedKernelFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedResolvedKernelFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelGram4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelGramBasepoint4D
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

/-- Differentiability of the named basis gives continuity of the canonically
sector-projected ambient family. -/
theorem projectedNamedKernelVector_continuous
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (regularity : GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
      period hPeriod input)
    (mode : ZeroMode) :
    Continuous
      (fun parameter : Real =>
        projectedNamedKernelVector period hPeriod input parameter mode) := by
  have hNamed :=
    (global_hessian_preferred_five_sector_differentiable_named_kernel_gate
      period hPeriod input regularity).2.1 mode
  have hProjector := continuous_preferredSectorProjectorApply period hPeriod input
    (namedModeFiveSector period hPeriod input mode)
  change Continuous
    (preferredSectorProjectorApply period hPeriod input
      (namedModeFiveSector period hPeriod input mode) ∘
        fun parameter => input.kernels.vector parameter mode)
  exact hProjector.comp hNamed

/-- The ambient projected physical Gram family is nondegenerate throughout a
neighbourhood of the physical basepoint. -/
theorem eventually_projectedAmbientGram_injective
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (regularity : GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
      period hPeriod input) :
    ∀ᶠ parameter in 𝓝 (0 : Real),
      Function.Injective
        (projectedKernelGramMap period hPeriod input natural parameter) := by
  letI hNormed : NormedAddCommGroup
      (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration
        data analysis) :=
    P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkNormedAddCommGroup
      period hPeriod (globalCandidateAMetricBySector period hPeriod data)
        couplings.matterMassSquared data analysis
  letI hInner : InnerProductSpace Real
      (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration
        data analysis) :=
    P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkInnerProductSpace
      period hPeriod (globalCandidateAMetricBySector period hPeriod data)
        couplings.matterMassSquared data analysis
  have hBasepoint : Function.Injective
      (@finiteFamilyGramMap ZeroMode
        (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration
          data analysis) inferInstance hNormed hInner
        (fun mode => projectedNamedKernelVector period hPeriod input 0 mode)) := by
    simpa [projectedKernelGramMap] using
      projectedKernelGram_zero_injective period hPeriod input natural
  have hEventually := @eventually_finiteFamilyGramMap_injective Real ZeroMode
    (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration data
      analysis) inferInstance inferInstance inferInstance hNormed hInner
    (fun parameter mode =>
      projectedNamedKernelVector period hPeriod input parameter mode)
    (projectedNamedKernelVector_continuous period hPeriod input regularity)
    0 hBasepoint
  simpa [projectedKernelGramMap] using hEventually

/-- Local nondegeneracy transfers back from the common ambient Hilbert space to
the genuine varying kernel subtypes. -/
theorem eventually_projectedKernelGram_injective
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (regularity : GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
      period hPeriod input) :
    ∀ᶠ parameter in 𝓝 (0 : Real),
      Function.Injective
        (projectedKernelGramMap period hPeriod input natural parameter) :=
  eventually_projectedAmbientGram_injective period hPeriod input natural
    regularity

/-- Public Candidate-A local projected-kernel Gram checkpoint. -/
theorem projected_kernel_gram_local_persistence_gate
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (regularity : GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
      period hPeriod input) :
    (∀ mode,
      Continuous
        (fun parameter : Real =>
          projectedNamedKernelVector period hPeriod input parameter mode)) ∧
      ∀ᶠ parameter in 𝓝 (0 : Real),
        Function.Injective
          (projectedKernelGramMap period hPeriod input natural parameter) :=
  ⟨projectedNamedKernelVector_continuous period hPeriod input regularity,
    eventually_projectedKernelGram_injective period hPeriod input natural
      regularity⟩

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelGramLocalPersistence4D
end JanusFormal
