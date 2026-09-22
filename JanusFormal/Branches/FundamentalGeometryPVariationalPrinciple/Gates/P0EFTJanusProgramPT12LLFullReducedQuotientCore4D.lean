import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LLFullJacobiHilbertQuotient4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LLFullSmoothReducedQuotient4D

/-! The literal LL Hilbert quotient is canonically isometric to field L².
Its dense faithful smooth core is exactly the earlier algebraic quotient. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12LLFullReducedQuotientCore4D

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

private theorem fieldSection_orthogonal (field : ReducedLLFieldL2 period hPeriod) :
    (WithLp.toLp 2 (0, field) : FullLLHilbert period hPeriod) ∈
      (fullLLAuxMeasureNullSpace period hPeriod)ᗮ := by
  rw [Submodule.mem_orthogonal']
  intro vector hVector
  have hField : WithLp.snd vector = 0 := hVector
  change inner Real 0 (WithLp.fst vector) + inner Real field (WithLp.snd vector) = 0
  rw [hField, inner_zero_left, inner_zero_right, add_zero]

/-- The Hilbert quotient norm is precisely the canonical LL field L² norm. -/
def fullLLReducedHilbertIsometry :
    FullLLReducedHilbert period hPeriod ≃ₗᵢ[Real] ReducedLLFieldL2 period hPeriod where
  toLinearEquiv := fullLLReducedHilbertEquiv period hPeriod
  norm_map' vector := by
    let field := fullLLReducedHilbertEquiv period hPeriod vector
    let sectionValue : FullLLHilbert period hPeriod := WithLp.toLp 2 (0, field)
    have hClass : (fullLLAuxMeasureNullSpace period hPeriod).mkQ sectionValue = vector := by
      apply (fullLLReducedHilbertEquiv period hPeriod).injective
      rfl
    have hNorm := (fullLLAuxMeasureNullSpace period hPeriod).quotientEquivOrthogonal.norm_map
      ((fullLLAuxMeasureNullSpace period hPeriod).mkQ sectionValue)
    have hOrth : (fullLLAuxMeasureNullSpace period hPeriod).quotientEquivOrthogonal
        ((fullLLAuxMeasureNullSpace period hPeriod).mkQ sectionValue) =
        ⟨sectionValue, fieldSection_orthogonal period hPeriod field⟩ :=
      (fullLLAuxMeasureNullSpace period hPeriod).quotientEquivOrthogonal_mk
        sectionValue (fieldSection_orthogonal period hPeriod field)
    rw [hOrth] at hNorm
    change ‖sectionValue‖ = ‖(fullLLAuxMeasureNullSpace period hPeriod).mkQ sectionValue‖ at hNorm
    calc
      ‖field‖ = ‖sectionValue‖ := (WithLp.norm_toLp_snd 2 _ _ field).symm
      _ = _ := hNorm
      _ = ‖vector‖ := congrArg norm hClass

variable {configuration : GlobalFieldConfiguration period hPeriod}
variable (analysis : GlobalAnalysisData period hPeriod configuration)

/-- Canonical geometric L² identification, with no Fredholm hypothesis. -/
def fullLLReducedHilbertToCanonical :
    FullLLReducedHilbert period hPeriod ≃ₗᵢ[Real] CanonicalLLL2 period hPeriod analysis :=
  fullLLReducedHilbertIsometry period hPeriod

/-- Completion map for the existing algebraic auxiliary/measure quotient. -/
def fullLLReducedSmoothToHilbert :
    GlobalFullLLReducedSmoothQuotient period hPeriod analysis →ₗ[Real]
      FullLLReducedHilbert period hPeriod :=
  (fullLLReducedHilbertToCanonical period hPeriod analysis).symm.toLinearEquiv.toLinearMap.comp
    (globalFullLLReducedSmoothQuotientToCanonicalLLL2 period hPeriod analysis)

theorem fullLLReducedSmoothToHilbert_injective :
    Function.Injective (fullLLReducedSmoothToHilbert period hPeriod analysis) :=
  (fullLLReducedHilbertToCanonical period hPeriod analysis).symm.injective.comp
    (globalFullLLReducedSmoothQuotientToCanonicalLLL2_injective period hPeriod analysis)

theorem fullLLReducedSmoothToHilbert_denseRange :
    DenseRange (fullLLReducedSmoothToHilbert period hPeriod analysis) :=
  (fullLLReducedHilbertToCanonical period hPeriod analysis).symm.surjective.denseRange.comp
    (globalFullLLReducedSmoothQuotientToCanonicalLLL2_denseRange period hPeriod analysis)
    (fullLLReducedHilbertToCanonical period hPeriod analysis).symm.continuous

theorem fullLLReducedSmoothToHilbert_canonical
    (direction : GlobalFullLLReducedSmoothQuotient period hPeriod analysis) :
    fullLLReducedHilbertToCanonical period hPeriod analysis
      (fullLLReducedSmoothToHilbert period hPeriod analysis direction) =
      globalFullLLReducedSmoothQuotientToCanonicalLLL2 period hPeriod analysis direction :=
  (fullLLReducedHilbertToCanonical period hPeriod analysis).apply_symm_apply _

/-- The two reductions commute on every full smooth LL direction. -/
theorem fullLLReducedSmoothToHilbert_mk
    (direction : GlobalFullLLSmooth period hPeriod analysis) :
    fullLLReducedSmoothToHilbert period hPeriod analysis
      ((GlobalFullLLAuxMeasureSubmodule period hPeriod analysis).mkQ direction) =
      fullLLReducedHilbertCore period hPeriod analysis direction := by
  apply (fullLLReducedHilbertToCanonical period hPeriod analysis).injective
  rw [fullLLReducedSmoothToHilbert_canonical]
  rfl

end
end P0EFTJanusProgramPT12LLFullReducedQuotientCore4D
end JanusFormal
