import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LLStrongJacobiPositiveCoercivity4D
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Topology.MetricSpace.Antilipschitz

/-! Positive LL measure gives a closed range for the closed field Jacobi operator. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12LLStrongJacobiPositiveClosedRange4D

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

open scoped Manifold ContDiff ENNReal LinearPMap
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusProgramPT12LLStrongJacobiL2Core4D
open P0EFTJanusProgramPT12LLStrongJacobiClosure4D
open P0EFTJanusProgramPT12LLStrongJacobiPositiveCoercivity4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance :
    IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance : CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod

local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _

local instance : BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

local instance :
    IsFiniteMeasure (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod

/-- The positive closed field Jacobi operator has a uniform norm bound and closed range. -/
theorem llJacobiClosedPMap_positive_closed_range
    (fields : IndependentFields period hPeriod)
    (hMeasure : ∀ point, 0 < fields.llMeasure point) :
    ∃ K : Real, 0 < K ∧
      (∀ x : (llJacobiClosedPMap period hPeriod fields).domain,
        ‖(x : Lp LLFieldFiber (2 : ENNReal)
          (intrinsicCanonicalThroatVolumeMeasure period hPeriod))‖ ≤
          K * ‖llJacobiClosedPMap period hPeriod fields x‖) ∧
      IsClosed (Set.range (llJacobiClosedPMap period hPeriod fields).toFun) := by
  let E := Lp LLFieldFiber (2 : ENNReal)
    (intrinsicCanonicalThroatVolumeMeasure period hPeriod)
  let C := llJacobiClosedPMap period hPeriod fields
  obtain ⟨c, hc, hLower⟩ :=
    llJacobiClosedPMap_positive_l2_lower_bound period hPeriod fields hMeasure
  have hCoercive (x : C.domain) : c * ‖(x : E)‖ ≤ ‖C x‖ := by
    have h := hLower x
    change c * ‖(x : E)‖ ^ 2 ≤ inner Real (C x) (x : E) at h
    have hCS := real_inner_le_norm (C x) (x : E)
    by_cases hx : ‖(x : E)‖ = 0
    · simp [hx]
    · have hxpos : 0 < ‖(x : E)‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hx)
      apply le_of_mul_le_mul_right ?_ hxpos
      nlinarith
  let d : Real := min 1 c
  have hd : 0 < d := lt_min (by norm_num) hc
  have hd1 : d ≤ 1 := min_le_left _ _
  have hdc : d ≤ c := min_le_right _ _
  let projection : C.graph →ₗ[Real] E :=
    (LinearMap.snd Real E E).comp C.graph.subtype
  have hProjection (z : C.graph) : d * ‖z‖ ≤ ‖projection z‖ := by
    obtain ⟨x, hx, hy⟩ := C.mem_graph_iff.mp z.property
    have hInput : c * ‖z.1.1‖ ≤ ‖z.1.2‖ := by
      simpa only [hx, hy] using hCoercive x
    have hInput' : d * ‖z.1.1‖ ≤ ‖z.1.2‖ :=
      (mul_le_mul_of_nonneg_right hdc (norm_nonneg _)).trans hInput
    have hOutput : d * ‖z.1.2‖ ≤ ‖z.1.2‖ := by
      nlinarith [norm_nonneg z.1.2]
    change d * max ‖z.1.1‖ ‖z.1.2‖ ≤ ‖z.1.2‖
    rcases le_total ‖z.1.1‖ ‖z.1.2‖ with h | h
    · rw [max_eq_right h]
      exact hOutput
    · rw [max_eq_left h]
      exact hInput'
  have hAnti : ∃ K : NNReal, AntilipschitzWith K projection :=
    antilipschitzWith_iff_exists_mul_le_norm.mpr ⟨d, hd, hProjection⟩
  letI : CompleteSpace C.graph :=
    (llJacobiClosedPMap_isClosed period hPeriod fields).completeSpace_coe
  have hProjectionClosed : IsClosed (Set.range projection) :=
    hAnti.choose_spec.isClosed_range
      (uniformContinuous_snd.comp uniformContinuous_subtype_val)
  have hRange : Set.range projection = Set.range C.toFun := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      obtain ⟨x, _, hy⟩ := C.mem_graph_iff.mp z.property
      exact ⟨x, hy⟩
    · rintro ⟨x, rfl⟩
      exact ⟨⟨((x : E), C x), C.mem_graph x⟩, rfl⟩
  refine ⟨c⁻¹, inv_pos.mpr hc, ?_, ?_⟩
  · intro x
    calc
      ‖(x : E)‖ = c⁻¹ * (c * ‖(x : E)‖) := by
        rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
      _ ≤ c⁻¹ * ‖C x‖ :=
        mul_le_mul_of_nonneg_left (hCoercive x) (inv_pos.mpr hc).le
  · exact hRange ▸ hProjectionClosed

end
end P0EFTJanusProgramPT12LLStrongJacobiPositiveClosedRange4D
end JanusFormal
