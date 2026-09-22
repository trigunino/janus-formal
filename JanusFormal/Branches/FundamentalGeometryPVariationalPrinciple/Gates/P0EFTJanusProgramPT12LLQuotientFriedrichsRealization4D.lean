import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LLFullReducedFriedrichsBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IsometricPMapTransport4D

/-! Friedrichs realization on the completed LL auxiliary/measure quotient,
with explicit domain, self-adjointness, compact inverse and Fredholm certificate. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12LLQuotientFriedrichsRealization4D

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000
noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff ENNReal LinearPMap InnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusPTSymmetricLLWeakEulerJacobiOperator4D
open P0EFTJanusMappingTorusPTSymmetricLLH1RieszOperator4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalFullLLGraphRiesz4D
open P0EFTJanusProgramPT12LLSmoothL2Density4D
open P0EFTJanusProgramPT12LLFullSmoothL2Density4D
open P0EFTJanusProgramPT12LLFullJacobiClosure4D
open P0EFTJanusProgramPT12LLFullJacobiClosedSymmetry4D
open P0EFTJanusProgramPT12LLFullJacobiPureAuxMeasureL2Kernel4D
open P0EFTJanusProgramPT12ClosedNullPMapQuotient4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)

local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl
local instance : IsFiniteMeasure (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod

open P0EFTJanusProgramPT12LLFullJacobiHilbertQuotient4D
open P0EFTJanusProgramPT12LLFullSmoothReducedQuotient4D
open P0EFTJanusProgramPT12LLCanonicalH1ClosedDomain4D

open P0EFTJanusProgramPT12LLFullReducedQuotientCore4D
open P0EFTJanusProgramPT12LLFullJacobiZeroFluxClosedDecomposition4D
open P0EFTJanusProgramPT12LLCanonicalFriedrichsRealization4D

open P0EFTJanusProgramPT12LLFullReducedFriedrichsBridge4D
open P0EFTJanusProgramPT12IsometricPMapTransport4D

variable {configuration : GlobalFieldConfiguration period hPeriod}
variable (analysis : GlobalAnalysisData period hPeriod configuration)

/-- The canonical Friedrichs realization on the literal LL quotient Hilbert space. -/
def quotientLLFriedrichs : FullLLReducedHilbert period hPeriod →ₗ.[Real] FullLLReducedHilbert period hPeriod :=
  transportedPMap (fullLLReducedHilbertToCanonical period hPeriod analysis)
    (canonicalLLFriedrichsJacobi period hPeriod analysis)

theorem quotientLLFriedrichs_domain :
    (quotientLLFriedrichs period hPeriod analysis).domain =
      (canonicalLLFriedrichsJacobi period hPeriod analysis).domain.comap
        (fullLLReducedHilbertToCanonical period hPeriod analysis).toLinearEquiv.toLinearMap := rfl

theorem quotientLLFriedrichs_graph_iff (first second : FullLLReducedHilbert period hPeriod) :
    (first, second) ∈ (quotientLLFriedrichs period hPeriod analysis).graph ↔
      (fullLLReducedHilbertToCanonical period hPeriod analysis first,
        fullLLReducedHilbertToCanonical period hPeriod analysis second) ∈
          (canonicalLLFriedrichsJacobi period hPeriod analysis).graph :=
  transportedPMap_graph_iff _ _ first second

theorem quotientLLFriedrichs_denseDomain :
    Dense ((quotientLLFriedrichs period hPeriod analysis).domain : Set (FullLLReducedHilbert period hPeriod)) :=
  transportedPMap_denseDomain _ _ (canonicalLLFriedrichsJacobi_domain_dense period hPeriod analysis)

theorem quotientLLFriedrichs_isSelfAdjoint :
    IsSelfAdjoint (quotientLLFriedrichs period hPeriod analysis) :=
  transportedPMap_isSelfAdjoint _ _ (canonicalLLFriedrichsJacobi_domain_dense period hPeriod analysis)
    (canonicalLLFriedrichsJacobi_isFormalAdjoint_self period hPeriod analysis)
    (canonicalLLFriedrichsJacobi_surjective period hPeriod analysis)

theorem quotientLLFriedrichs_isClosed :
    (quotientLLFriedrichs period hPeriod analysis).IsClosed :=
  (quotientLLFriedrichs_isSelfAdjoint period hPeriod analysis).isClosed

theorem quotientLLFriedrichs_surjective : Function.Surjective (quotientLLFriedrichs period hPeriod analysis) :=
  transportedPMap_surjective _ _ (canonicalLLFriedrichsJacobi_surjective period hPeriod analysis)

theorem quotientLLFriedrichs_injective : Function.Injective (quotientLLFriedrichs period hPeriod analysis) :=
  transportedPMap_injective _ _ (canonicalLLFriedrichsJacobi_injective period hPeriod analysis)

/-- Transport of the existing weak L² inverse, not a new PDE solution assumption. -/
def quotientLLFriedrichsInverse : FullLLReducedHilbert period hPeriod →L[Real] FullLLReducedHilbert period hPeriod :=
  (fullLLReducedHilbertToCanonical period hPeriod analysis).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((canonicalLLWeakL2Inverse period hPeriod analysis).comp
      (fullLLReducedHilbertToCanonical period hPeriod analysis).toContinuousLinearEquiv.toContinuousLinearMap)

theorem quotientLLFriedrichsInverse_left_inverse
    (vector : (quotientLLFriedrichs period hPeriod analysis).domain) :
    quotientLLFriedrichsInverse period hPeriod analysis (quotientLLFriedrichs period hPeriod analysis vector) =
      (vector : FullLLReducedHilbert period hPeriod) := by
  let e := fullLLReducedHilbertToCanonical period hPeriod analysis
  apply e.injective
  calc
    e (quotientLLFriedrichsInverse period hPeriod analysis
      (quotientLLFriedrichs period hPeriod analysis vector)) =
        canonicalLLWeakL2Inverse period hPeriod analysis
          (e (quotientLLFriedrichs period hPeriod analysis vector)) := e.apply_symm_apply _
    _ = canonicalLLWeakL2Inverse period hPeriod analysis
        (canonicalLLFriedrichsJacobi period hPeriod analysis
          (transportedDomainEquiv e (canonicalLLFriedrichsJacobi period hPeriod analysis) vector)) :=
      congrArg (canonicalLLWeakL2Inverse period hPeriod analysis) (transportedPMap_action _ _ vector)
    _ = e (vector : FullLLReducedHilbert period hPeriod) :=
      canonicalLLWeakL2Inverse_friedrichsJacobi period hPeriod analysis _

theorem quotientLLFriedrichsInverse_right_inverse (source : FullLLReducedHilbert period hPeriod) :
    ∃ hDomain : quotientLLFriedrichsInverse period hPeriod analysis source ∈
        (quotientLLFriedrichs period hPeriod analysis).domain,
      quotientLLFriedrichs period hPeriod analysis
        ⟨quotientLLFriedrichsInverse period hPeriod analysis source, hDomain⟩ = source := by
  obtain ⟨vector, hVector⟩ := quotientLLFriedrichs_surjective period hPeriod analysis source
  have hValue : quotientLLFriedrichsInverse period hPeriod analysis source =
      (vector : FullLLReducedHilbert period hPeriod) := by
    rw [← hVector]
    exact quotientLLFriedrichsInverse_left_inverse period hPeriod analysis vector
  have hDomain : quotientLLFriedrichsInverse period hPeriod analysis source ∈
      (quotientLLFriedrichs period hPeriod analysis).domain := hValue ▸ vector.property
  refine ⟨hDomain, ?_⟩
  have hSubtype : (⟨quotientLLFriedrichsInverse period hPeriod analysis source, hDomain⟩ :
      (quotientLLFriedrichs period hPeriod analysis).domain) = vector := Subtype.ext hValue
  rw [hSubtype]
  exact hVector

theorem quotientLLFriedrichsInverse_compact :
    IsCompactOperator (quotientLLFriedrichsInverse period hPeriod analysis) := by
  exact ((canonicalLLWeakL2Inverse_isCompact period hPeriod analysis).comp_clm
    (fullLLReducedHilbertToCanonical period hPeriod analysis).toContinuousLinearEquiv.toContinuousLinearMap).clm_comp
      (fullLLReducedHilbertToCanonical period hPeriod analysis).symm.toContinuousLinearEquiv.toContinuousLinearMap

theorem quotientLLFriedrichs_norm_bound
    (vector : (quotientLLFriedrichs period hPeriod analysis).domain) :
    ‖(vector : FullLLReducedHilbert period hPeriod)‖ ≤
      ‖quotientLLFriedrichsInverse period hPeriod analysis‖ *
        ‖quotientLLFriedrichs period hPeriod analysis vector‖ := by
  calc
    _ = ‖quotientLLFriedrichsInverse period hPeriod analysis
        (quotientLLFriedrichs period hPeriod analysis vector)‖ :=
      congrArg norm (quotientLLFriedrichsInverse_left_inverse period hPeriod analysis vector).symm
    _ ≤ _ := (quotientLLFriedrichsInverse period hPeriod analysis).le_opNorm _

theorem quotientLLFriedrichs_kernel_eq_bot : (quotientLLFriedrichs period hPeriod analysis).toFun.ker = ⊥ :=
  LinearMap.ker_eq_bot.mpr (quotientLLFriedrichs_injective period hPeriod analysis)

theorem quotientLLFriedrichs_range_eq_top : (quotientLLFriedrichs period hPeriod analysis).toFun.range = ⊤ :=
  LinearMap.range_eq_top.mpr (quotientLLFriedrichs_surjective period hPeriod analysis)

theorem quotientLLFriedrichs_fredholm :
    IsClosed ((quotientLLFriedrichs period hPeriod analysis).toFun.range : Set (FullLLReducedHilbert period hPeriod)) ∧
      FiniteDimensional Real (quotientLLFriedrichs period hPeriod analysis).toFun.ker ∧
      FiniteDimensional Real ((FullLLReducedHilbert period hPeriod) ⧸
        (quotientLLFriedrichs period hPeriod analysis).toFun.range) := by
  rw [quotientLLFriedrichs_kernel_eq_bot, quotientLLFriedrichs_range_eq_top]
  refine ⟨isClosed_univ, inferInstance, ?_⟩
  exact FiniteDimensional.of_rank_eq_zero (by simp)

variable {couplings : GlobalCandidateAActionCouplings}
variable {NonNullFace NullFace : Type*} [Fintype NonNullFace] [Fintype NullFace]
variable (data : GlobalCandidateAActionData period hPeriod configuration couplings NonNullFace NullFace)
variable (hZero : (data.boundary.llFields period hPeriod).llField = 0)

include hZero in
/-- At zero flux this realization extends the actual closed quotient Jacobi. -/
theorem fullLLReducedJacobi_le_quotientFriedrichs :
    fullLLReducedJacobi period hPeriod data analysis ≤ quotientLLFriedrichs period hPeriod analysis := by
  apply LinearPMap.le_of_le_graph
  intro pair hPair
  exact (quotientLLFriedrichs_graph_iff period hPeriod analysis pair.1 pair.2).mpr
    (fullLLReducedJacobi_graph_mem_friedrichs period hPeriod data analysis hZero pair.1 pair.2 hPair)

end
end P0EFTJanusProgramPT12LLQuotientFriedrichsRealization4D
end JanusFormal
