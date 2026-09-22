import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LLFullReducedQuotientCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LLFullJacobiZeroFluxClosedDecomposition4D

/-! Concrete quotient-to-Friedrichs graph transport for the LL sector at
zero flux. The reduced closed Jacobi operator has trivial kernel. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12LLFullReducedFriedrichsBridge4D

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

variable {configuration : GlobalFieldConfiguration period hPeriod}
variable {couplings : GlobalCandidateAActionCouplings}
variable {NonNullFace NullFace : Type*} [Fintype NonNullFace] [Fintype NullFace]
variable (data : GlobalCandidateAActionData period hPeriod configuration couplings NonNullFace NullFace)
variable (analysis : GlobalAnalysisData period hPeriod configuration)
variable (hZero : (data.boundary.llFields period hPeriod).llField = 0)

private theorem quotientLift_eq_fieldSection (vector : FullLLReducedHilbert period hPeriod) :
    quotientLift (fullLLAuxMeasureNullSpace period hPeriod) vector =
      pureFieldHilbert period hPeriod (fullLLReducedHilbertToCanonical period hPeriod analysis vector) := by
  let field := fullLLReducedHilbertToCanonical period hPeriod analysis vector
  have hOrth : pureFieldHilbert period hPeriod field ∈ (fullLLAuxMeasureNullSpace period hPeriod)ᗮ := by
    rw [Submodule.mem_orthogonal']
    intro test hTest
    have hField : WithLp.snd test = 0 := hTest
    change inner Real 0 (WithLp.fst test) + inner Real field (WithLp.snd test) = 0
    rw [hField, inner_zero_left, inner_zero_right, add_zero]
  have hClass : (fullLLAuxMeasureNullSpace period hPeriod).mkQ
      (pureFieldHilbert period hPeriod field) = vector := by
    apply (fullLLReducedHilbertToCanonical period hPeriod analysis).injective
    rfl
  exact (congrArg (quotientLift (fullLLAuxMeasureNullSpace period hPeriod)) hClass).symm.trans
    (quotientLift_mk _ _ hOrth)

include hZero in
/-- Exact graph conjugacy with the existing closed field Jacobi realization. -/
theorem fullLLReducedJacobi_graph_iff_canonical
    (first second : FullLLReducedHilbert period hPeriod) :
    (first, second) ∈ (fullLLReducedJacobi period hPeriod data analysis).graph ↔
      (fullLLReducedHilbertToCanonical period hPeriod analysis first,
        fullLLReducedHilbertToCanonical period hPeriod analysis second) ∈
          (canonicalLLClosedJacobi period hPeriod analysis).graph := by
  rw [fullLLReducedJacobi, quotientPMap_graph]
  change (quotientLift (fullLLAuxMeasureNullSpace period hPeriod) first,
      quotientLift (fullLLAuxMeasureNullSpace period hPeriod) second) ∈
        (fullLLJacobiClosedPMap period hPeriod data analysis).graph ↔ _
  rw [quotientLift_eq_fieldSection, quotientLift_eq_fieldSection,
    fullLLJacobiClosedPMap_zeroFlux_graph_iff period hPeriod data analysis hZero]
  change (0 = (0 : WithLp 2
      (Lp LLMetricFiber (2 : ENNReal) (intrinsicCanonicalThroatVolumeMeasure period hPeriod) ×
        Lp Real (2 : ENNReal) (intrinsicCanonicalThroatVolumeMeasure period hPeriod))) ∧ _) ↔ _
  exact and_iff_right rfl

include hZero in
/-- The quotient's actual graph embeds into the canonical Friedrichs graph. -/
theorem fullLLReducedJacobi_graph_mem_friedrichs
    (first second : FullLLReducedHilbert period hPeriod)
    (hGraph : (first, second) ∈ (fullLLReducedJacobi period hPeriod data analysis).graph) :
    (fullLLReducedHilbertToCanonical period hPeriod analysis first,
      fullLLReducedHilbertToCanonical period hPeriod analysis second) ∈
        (canonicalLLFriedrichsJacobi period hPeriod analysis).graph :=
  (LinearPMap.le_graph_of_le (canonicalLLClosedJacobi_le_friedrichsJacobi period hPeriod analysis))
    ((fullLLReducedJacobi_graph_iff_canonical period hPeriod data analysis hZero first second).mp hGraph)

include hZero in
/-- No LL zero mode remains after quotienting the inactive slots. -/
theorem fullLLReducedJacobi_injective :
    Function.Injective (fullLLReducedJacobi period hPeriod data analysis) := by
  intro first second hEqual
  have hFirst := fullLLReducedJacobi_graph_mem_friedrichs period hPeriod data analysis hZero
    _ _ ((fullLLReducedJacobi period hPeriod data analysis).mem_graph first)
  have hSecond := fullLLReducedJacobi_graph_mem_friedrichs period hPeriod data analysis hZero
    _ _ ((fullLLReducedJacobi period hPeriod data analysis).mem_graph second)
  obtain ⟨x, hx, hAx⟩ := (canonicalLLFriedrichsJacobi period hPeriod analysis).mem_graph_iff.mp hFirst
  obtain ⟨y, hy, hAy⟩ := (canonicalLLFriedrichsJacobi period hPeriod analysis).mem_graph_iff.mp hSecond
  have hxy : x = y := canonicalLLFriedrichsJacobi_injective period hPeriod analysis (by
    exact hAx.trans ((congrArg (fullLLReducedHilbertToCanonical period hPeriod analysis) hEqual).trans hAy.symm))
  apply Subtype.ext
  apply (fullLLReducedHilbertToCanonical period hPeriod analysis).injective
  exact hx.symm.trans ((congrArg Subtype.val hxy).trans hy)

include hZero in
theorem fullLLReducedJacobi_kernel_eq_bot :
    (fullLLReducedJacobi period hPeriod data analysis).toFun.ker = ⊥ :=
  LinearMap.ker_eq_bot.mpr (fullLLReducedJacobi_injective period hPeriod data analysis hZero)

include hZero in
/-- The full zero-flux kernel consists exactly of the inactive input slots. -/
theorem fullLLJacobiClosed_zero_iff_auxMeasure
    (vector : (fullLLJacobiClosedPMap period hPeriod data analysis).domain) :
    fullLLJacobiClosedPMap period hPeriod data analysis vector = 0 ↔
      (vector : FullLLHilbert period hPeriod) ∈ fullLLAuxMeasureNullSpace period hPeriod := by
  constructor
  · intro hOutput
    have hGraph := fullLLReducedJacobi_graph_project period hPeriod data analysis hZero vector
    rw [hOutput, map_zero] at hGraph
    obtain ⟨source, hSource, hSourceOutput⟩ :=
      (fullLLReducedJacobi period hPeriod data analysis).mem_graph_iff.mp hGraph
    have hSourceZero : source = 0 := fullLLReducedJacobi_injective period hPeriod data analysis hZero
      (hSourceOutput.trans (map_zero (fullLLReducedJacobi period hPeriod data analysis).toFun).symm)
    apply (Submodule.Quotient.mk_eq_zero _).mp
    exact hSource.symm.trans (congrArg Subtype.val hSourceZero)
  · intro hVector
    exact (fullLLJacobiClosedPMap period hPeriod data analysis).mem_graph_snd_inj
      ((fullLLJacobiClosedPMap period hPeriod data analysis).mem_graph vector)
      (fullLLAuxMeasureNullSpace_graph_zero period hPeriod data analysis hZero _ hVector) rfl

end
end P0EFTJanusProgramPT12LLFullReducedFriedrichsBridge4D
end JanusFormal
