import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.InnerProductSpace.ProdL2
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalHilbertAugmentationObstruction4D

/-!
# Reduced Hilbert space for the minimal physical chart

The closed Hilbert span of the full kernel of the canonical minimal-physical
tangent map is removed by orthogonal projection.  The resulting orthogonal
complement is automatically complete, the reduction has exactly that closed
null span as kernel, and the reduced smooth core remains dense.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedHilbert4D

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff InnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalPairedAbelianBRSTGaugeFermion4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateADiagonalCovariantHessianResidualBridge4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalEulerLagrangeDenseCoreHilbertChartEquivalence4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalHilbertAugmentationObstruction4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

section

variable
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)

local instance reducedCommonNormedAddCommGroup : NormedAddCommGroup
    (CommonAugmentedHilbert period hPeriod configuration data analysis) :=
  diagonalL2ExtendedBulkNormedAddCommGroup period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance reducedCommonInnerProductSpace : InnerProductSpace Real
    (CommonAugmentedHilbert period hPeriod configuration data analysis) :=
  diagonalL2ExtendedBulkInnerProductSpace period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance reducedCommonNormedSpace : NormedSpace Real
    (CommonAugmentedHilbert period hPeriod configuration data analysis) :=
  (reducedCommonInnerProductSpace period hPeriod configuration data
    analysis).toNormedSpace

local instance reducedCommonModule : Module Real
    (CommonAugmentedHilbert period hPeriod configuration data analysis) :=
  (reducedCommonNormedSpace period hPeriod configuration data
    analysis).toModule

local instance reducedCommonCompleteSpace : CompleteSpace
    (CommonAugmentedHilbert period hPeriod configuration data analysis) :=
  diagonalL2ExtendedBulkCompleteSpace period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

/-- Smooth directions invisible to the corrected minimal physical tangent. -/
def globalCandidateAMinimalPhysicalSmoothCoreKernel : Submodule Real
    (GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod analysis) :=
  LinearMap.ker
    (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
      configuration data analysis)

/-- Inclusion of the full smooth null space into the common augmented Hilbert
completion. -/
def globalCandidateAMinimalPhysicalNullHilbertLinearMap :
    globalCandidateAMinimalPhysicalSmoothCoreKernel period hPeriod
        configuration data analysis →ₗ[Real]
      CommonAugmentedHilbert period hPeriod configuration data analysis :=
  (globalCandidateACommonHilbertSmoothCoreEmbedding period hPeriod
    configuration data analysis).comp
      (globalCandidateAMinimalPhysicalSmoothCoreKernel period hPeriod
        configuration data analysis).subtype

/-- Hilbert image of the full smooth null space. -/
def globalCandidateAMinimalPhysicalNullHilbertSubmodule : Submodule Real
    (CommonAugmentedHilbert period hPeriod configuration data analysis) :=
  LinearMap.range
    (globalCandidateAMinimalPhysicalNullHilbertLinearMap period hPeriod
      configuration data analysis)

/-- Closed Hilbert null space generated by the smooth physical kernel. -/
def globalCandidateAMinimalPhysicalClosedNullHilbertSubmodule : Submodule Real
    (CommonAugmentedHilbert period hPeriod configuration data analysis) :=
  (globalCandidateAMinimalPhysicalNullHilbertSubmodule period hPeriod
    configuration data analysis).topologicalClosure

local instance reducedClosedNullHilbertSubmoduleIsClosed : IsClosed
    (globalCandidateAMinimalPhysicalClosedNullHilbertSubmodule period hPeriod
      configuration data analysis : Set
        (CommonAugmentedHilbert period hPeriod configuration data analysis)) :=
  Submodule.isClosed_topologicalClosure _

/-- Quotient presentation of the reduced physical completion. -/
abbrev GlobalCandidateAMinimalPhysicalReducedHilbertQuotient :=
  CommonAugmentedHilbert period hPeriod configuration data analysis ⧸
    globalCandidateAMinimalPhysicalClosedNullHilbertSubmodule period hPeriod
      configuration data analysis

/-- Canonical reduced physical Hilbert space: the orthogonal complement of
the full smooth null range. -/
abbrev GlobalCandidateAMinimalPhysicalReducedHilbert :=
  (globalCandidateAMinimalPhysicalClosedNullHilbertSubmodule period hPeriod
    configuration data analysis)ᗮ

/-- The quotient and orthogonal-complement presentations are canonically
isometrically equivalent. -/
def globalCandidateAMinimalPhysicalReducedQuotientEquiv :
    GlobalCandidateAMinimalPhysicalReducedHilbertQuotient period hPeriod
        configuration data analysis ≃ₗᵢ[Real]
      GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
        configuration data analysis :=
  (globalCandidateAMinimalPhysicalClosedNullHilbertSubmodule period hPeriod
    configuration data analysis).quotientEquivOrthogonal

/-- Orthogonal reduction from the augmented completion to its physical
representative. -/
def globalCandidateAMinimalPhysicalHilbertReduction :
  CommonAugmentedHilbert period hPeriod configuration data analysis →L[Real]
      GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
        configuration data analysis :=
  ((globalCandidateAMinimalPhysicalClosedNullHilbertSubmodule period hPeriod
    configuration data analysis)ᗮ).orthogonalProjectionOnto

theorem globalCandidateAMinimalPhysicalHilbertReduction_surjective :
    Function.Surjective
      (globalCandidateAMinimalPhysicalHilbertReduction period hPeriod
        configuration data analysis) := by
  intro state
  refine ⟨state, ?_⟩
  exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self state

/-- The reduction kernel is exactly the closed Hilbert span of smooth
directions invisible to the minimal physical tangent. -/
theorem globalCandidateAMinimalPhysicalHilbertReduction_ker :
    (globalCandidateAMinimalPhysicalHilbertReduction period hPeriod
      configuration data analysis).ker =
      globalCandidateAMinimalPhysicalClosedNullHilbertSubmodule period hPeriod
        configuration data analysis := by
  rw [globalCandidateAMinimalPhysicalHilbertReduction,
    Submodule.ker_orthogonalProjectionOnto,
    Submodule.orthogonal_orthogonal_eq_closure]
  exact
    (Submodule.isClosed_topologicalClosure
      (globalCandidateAMinimalPhysicalNullHilbertSubmodule period hPeriod
        configuration data analysis)).submodule_topologicalClosure_eq

/-- Every smooth-core null vector is removed by the reduction. -/
theorem globalCandidateAMinimalPhysicalHilbertReduction_smoothCoreKernel_eq_zero
    (core : globalCandidateAMinimalPhysicalSmoothCoreKernel period hPeriod
      configuration data analysis) :
    globalCandidateAMinimalPhysicalHilbertReduction period hPeriod
        configuration data analysis
        (globalCandidateACommonHilbertSmoothCoreEmbedding period hPeriod
          configuration data analysis core) = 0 := by
  unfold globalCandidateAMinimalPhysicalHilbertReduction
  rw [Submodule.orthogonalProjectionOnto_eq_zero_iff]
  apply
    (globalCandidateAMinimalPhysicalClosedNullHilbertSubmodule period hPeriod
      configuration data analysis).le_orthogonal_orthogonal
  exact
    (globalCandidateAMinimalPhysicalNullHilbertSubmodule period hPeriod
      configuration data analysis).le_topologicalClosure ⟨core, rfl⟩

/-- Smooth augmented directions followed by orthogonal reduction. -/
def globalCandidateAMinimalPhysicalReducedSmoothCoreEmbedding :
    GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod analysis
      →ₗ[Real]
        GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
          configuration data analysis :=
  (globalCandidateAMinimalPhysicalHilbertReduction period hPeriod
    configuration data analysis).toLinearMap.comp
      (globalCandidateACommonHilbertSmoothCoreEmbedding period hPeriod
        configuration data analysis)

/-- Algebraic physical smooth core obtained by quotienting the complete
kernel of the canonical minimal tangent map. -/
abbrev GlobalCandidateAMinimalPhysicalReducedSmoothCore :=
  GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod analysis ⧸
    globalCandidateAMinimalPhysicalSmoothCoreKernel period hPeriod
      configuration data analysis

/-- The projected smooth-core embedding descends to the physical quotient
core. -/
def globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding :
    GlobalCandidateAMinimalPhysicalReducedSmoothCore period hPeriod
        configuration data analysis →ₗ[Real]
      GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
        configuration data analysis :=
  (globalCandidateAMinimalPhysicalSmoothCoreKernel period hPeriod
    configuration data analysis).liftQ
      (globalCandidateAMinimalPhysicalReducedSmoothCoreEmbedding period hPeriod
        configuration data analysis) (by
          intro core hCore
          exact LinearMap.mem_ker.mpr
            (globalCandidateAMinimalPhysicalHilbertReduction_smoothCoreKernel_eq_zero
              period hPeriod configuration data analysis ⟨core, hCore⟩))

@[simp]
theorem globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding_mk
    (core : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod
      analysis) :
    globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding period
        hPeriod configuration data analysis (Submodule.Quotient.mk core) =
      globalCandidateAMinimalPhysicalReducedSmoothCoreEmbedding period hPeriod
        configuration data analysis core :=
  rfl

theorem globalCandidateAMinimalPhysicalReducedSmoothCoreEmbedding_eq_zero_of_mem_kernel
    (core : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod analysis)
    (hCore : core ∈ globalCandidateAMinimalPhysicalSmoothCoreKernel period
      hPeriod configuration data analysis) :
    globalCandidateAMinimalPhysicalReducedSmoothCoreEmbedding period hPeriod
        configuration data analysis core = 0 := by
  exact
    globalCandidateAMinimalPhysicalHilbertReduction_smoothCoreKernel_eq_zero
      period hPeriod configuration data analysis ⟨core, hCore⟩

/-- In particular, the explicit diffeomorphism nonminimal obstruction from
the preceding gate vanishes in the reduced Hilbert space. -/
@[simp]
theorem globalCandidateAMinimalPhysicalReducedSmoothCoreEmbedding_pureDiffeomorphismNonminimal_eq_zero
    (nonminimal : GlobalDiffeomorphismNonminimalFields period hPeriod) :
    globalCandidateAMinimalPhysicalReducedSmoothCoreEmbedding period hPeriod
        configuration data analysis
        (globalCandidateAPureDiffeomorphismNonminimalCore period hPeriod
          configuration analysis nonminimal) = 0 := by
  apply
    globalCandidateAMinimalPhysicalReducedSmoothCoreEmbedding_eq_zero_of_mem_kernel
  exact
    diagonalExtendedBulkMinimalPhysicalTangent_pureDiffeomorphismNonminimal_eq_zero
      period hPeriod configuration data analysis nonminimal

/-- Quotienting the full null span preserves density of the genuine smooth
core in the reduced Hilbert space. -/
theorem globalCandidateAMinimalPhysicalReducedSmoothCoreEmbedding_denseRange :
    DenseRange
      (globalCandidateAMinimalPhysicalReducedSmoothCoreEmbedding period hPeriod
        configuration data analysis) := by
  have hCommonDense : DenseRange
      (globalCandidateACommonHilbertSmoothCoreEmbedding period hPeriod
        configuration data analysis) :=
    diagonalExtendedBulkL2SmoothEmbedding_denseRange period hPeriod
      (globalCandidateAMetricBySector period hPeriod data)
        couplings.matterMassSquared data analysis
  have hReductionDense : DenseRange
      (globalCandidateAMinimalPhysicalHilbertReduction period hPeriod
        configuration data analysis) :=
    (globalCandidateAMinimalPhysicalHilbertReduction_surjective period hPeriod
      configuration data analysis).denseRange
  change DenseRange (fun core =>
    globalCandidateAMinimalPhysicalHilbertReduction period hPeriod
      configuration data analysis
        (globalCandidateACommonHilbertSmoothCoreEmbedding period hPeriod
          configuration data analysis core))
  exact hReductionDense.comp hCommonDense
    (globalCandidateAMinimalPhysicalHilbertReduction period hPeriod
      configuration data analysis).continuous

/-- The quotient core is still dense in the reduced physical Hilbert space. -/
theorem globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding_denseRange :
    DenseRange
      (globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding period
        hPeriod configuration data analysis) := by
  let quotientEmbedding :=
    globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding period
      hPeriod configuration data analysis
  let quotientMap :=
    (globalCandidateAMinimalPhysicalSmoothCoreKernel period hPeriod
      configuration data analysis).mkQ
  have hComp : quotientEmbedding.comp quotientMap =
      globalCandidateAMinimalPhysicalReducedSmoothCoreEmbedding period hPeriod
        configuration data analysis := by
    unfold quotientEmbedding quotientMap
    exact Submodule.liftQ_mkQ _ _ _
  have hDenseComp : DenseRange (quotientEmbedding.comp quotientMap) := by
    rw [hComp]
    exact
      globalCandidateAMinimalPhysicalReducedSmoothCoreEmbedding_denseRange
        period hPeriod configuration data analysis
  apply DenseRange.of_comp (f := quotientEmbedding) (g := quotientMap)
  exact hDenseComp

end

end
end P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedHilbert4D
end JanusFormal
