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
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyH10Reduction4D
open P0EFTJanusProgramPGlobalCandidateACanonicalSixDenseCore4D
open P0EFTJanusProgramPFiniteFamilyGramBasis4D
open P0EFTJanusProgramPFiniteFamilyGramLocalPersistence4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedResolvedKernelFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelGram4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelGramBasepoint4D
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

/-- The Gram matrix computed in the true-kernel subtype is literally the Gram
matrix of the same projected vectors in the common ambient Candidate-A Hilbert
space. -/
theorem projectedKernelGramMatrix_eq_ambient
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (parameter : Real) :
    finiteFamilyGramMatrix
        (projectedKernelSubtypeVector period hPeriod input natural parameter) =
      finiteFamilyGramMatrix
        (fun mode =>
          projectedNamedKernelVector period hPeriod input parameter mode) := by
  ext row column
  rfl

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
        projectedNamedKernelVector period hPeriod input parameter mode) :=
  (projectedNamedKernelVector_differentiable period hPeriod input regularity
    mode).continuous

/-- The ambient projected Gram map is injective at the H12 basepoint.  This is
not a new proof obligation: it is the already proved subtype statement carried
through the identical scalar Gram matrix. -/
theorem projectedAmbientGram_zero_injective
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input) :
    Function.Injective
      (finiteFamilyGramMap
        (fun mode =>
          projectedNamedKernelVector period hPeriod input 0 mode)) := by
  have hSubtypeInjective :
      Function.Injective
        (finiteFamilyGramMap
          (projectedKernelSubtypeVector period hPeriod input natural 0)) := by
    simpa [projectedKernelGramMap] using
      projectedKernelGram_zero_injective period hPeriod input natural
  have hSubtypeDet :
      (finiteFamilyGramMatrix
        (projectedKernelSubtypeVector period hPeriod input natural 0)).det ≠ 0 :=
    (finiteFamilyGramMap_injective_iff_det_ne_zero
      (projectedKernelSubtypeVector period hPeriod input natural 0)).mp
        hSubtypeInjective
  rw [projectedKernelGramMatrix_eq_ambient period hPeriod input natural 0] at
    hSubtypeDet
  exact (finiteFamilyGramMap_injective_iff_det_ne_zero
    (fun mode =>
      projectedNamedKernelVector period hPeriod input 0 mode)).mpr hSubtypeDet

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
        (finiteFamilyGramMap
          (fun mode =>
            projectedNamedKernelVector period hPeriod input parameter mode)) :=
  eventually_finiteFamilyGramMap_injective
    (fun parameter mode =>
      projectedNamedKernelVector period hPeriod input parameter mode)
    (projectedNamedKernelVector_continuous period hPeriod input regularity)
    0
    (projectedAmbientGram_zero_injective period hPeriod input natural)

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
        (projectedKernelGramMap period hPeriod input natural parameter) := by
  filter_upwards
    [eventually_projectedAmbientGram_injective period hPeriod input natural
      regularity] with parameter hAmbientInjective
  have hAmbientDet :
      (finiteFamilyGramMatrix
        (fun mode =>
          projectedNamedKernelVector period hPeriod input parameter mode)).det ≠
        0 :=
    (finiteFamilyGramMap_injective_iff_det_ne_zero
      (fun mode =>
        projectedNamedKernelVector period hPeriod input parameter mode)).mp
          hAmbientInjective
  have hSubtypeDet :
      (finiteFamilyGramMatrix
        (projectedKernelSubtypeVector period hPeriod input natural parameter)).det
          ≠ 0 := by
    rw [projectedKernelGramMatrix_eq_ambient period hPeriod input natural
      parameter]
    exact hAmbientDet
  have hSubtypeInjective :
      Function.Injective
        (finiteFamilyGramMap
          (projectedKernelSubtypeVector period hPeriod input natural parameter)) :=
    (finiteFamilyGramMap_injective_iff_det_ne_zero
      (projectedKernelSubtypeVector period hPeriod input natural parameter)).mpr
        hSubtypeDet
  simpa [projectedKernelGramMap] using hSubtypeInjective

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
