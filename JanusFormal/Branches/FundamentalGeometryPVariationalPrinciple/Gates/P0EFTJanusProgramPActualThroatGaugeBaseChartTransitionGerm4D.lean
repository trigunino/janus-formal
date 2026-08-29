import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeChartwiseSecondOrderJetOverlap4D

/-!
# Base-chart transition germ for the actual throat gauge representative

This gate starts base-chart descent while keeping the tangent frame fixed.  It
proves the exact representative germ under a genuine extended-chart transition
and the transition's `C²` regularity at a common represented point.

No derivative law, jet descent, cocycle or global connection is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionGerm4D

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Manifold ContDiff RealInnerProductSpace Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusProgramPActualThroatAbelianPotentialChartwiseSecondOrderJetExtraction4D
open P0EFTJanusProgramPActualThroatGaugeChartwiseFirstOrderOverlap4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-- Genuine coordinate transition from the first extended chart to the
second. -/
def throatGaugeBaseChartTransition
    (firstCenter secondCenter : EffectiveThroat period hPeriod) :
    ThroatCoverCoordinates → ThroatCoverCoordinates :=
  (extChartAt throatCoverModelWithCorners secondCenter) ∘
    (extChartAt throatCoverModelWithCorners firstCenter).symm

@[simp]
theorem throatGaugeBaseChartTransition_apply_current
    (firstCenter secondCenter current : EffectiveThroat period hPeriod)
    (hFirst : current ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source) :
    throatGaugeBaseChartTransition period hPeriod firstCenter secondCenter
        (extChartAt throatCoverModelWithCorners firstCenter current) =
      extChartAt throatCoverModelWithCorners secondCenter current := by
  change
    extChartAt throatCoverModelWithCorners secondCenter
        ((extChartAt throatCoverModelWithCorners firstCenter).symm
          (extChartAt throatCoverModelWithCorners firstCenter current)) =
      extChartAt throatCoverModelWithCorners secondCenter current
  rw [(extChartAt throatCoverModelWithCorners firstCenter).left_inv hFirst]

/-- The genuine transition is `C²` at every coordinate representing a point
contained in both chart sources. -/
theorem throatGaugeBaseChartTransition_contDiffAt_two
    (firstCenter secondCenter current : EffectiveThroat period hPeriod)
    (hFirst : current ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : current ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source) :
    ContDiffAt Real 2
      (throatGaugeBaseChartTransition period hPeriod
        firstCenter secondCenter)
      (extChartAt throatCoverModelWithCorners firstCenter current) := by
  change ContDiffAt Real 2
    ((extChartAt throatCoverModelWithCorners secondCenter) ∘
      (extChartAt throatCoverModelWithCorners firstCenter).symm)
    (extChartAt throatCoverModelWithCorners firstCenter current)
  have hFirstTarget :
      extChartAt throatCoverModelWithCorners firstCenter current ∈
        (extChartAt throatCoverModelWithCorners firstCenter).target :=
    (extChartAt throatCoverModelWithCorners firstCenter).map_source hFirst
  have hFirstInverse :
      ContMDiffAt
        (modelWithCornersSelf Real ThroatCoverCoordinates)
        throatCoverModelWithCorners ∞
        (extChartAt throatCoverModelWithCorners firstCenter).symm
        (extChartAt throatCoverModelWithCorners firstCenter current) :=
    (contMDiffOn_extChartAt_symm
      (I := throatCoverModelWithCorners) (n := ∞) firstCenter).contMDiffAt
        (extChartAt_target_mem_nhds' hFirstTarget)
  have hSecondChart :
      ContMDiffAt throatCoverModelWithCorners
        (modelWithCornersSelf Real ThroatCoverCoordinates) ∞
        (extChartAt throatCoverModelWithCorners secondCenter) current := by
    apply contMDiffAt_extChartAt'
    simpa only [extChartAt_source] using hSecond
  have hTransition :
      ContMDiffAt
        (modelWithCornersSelf Real ThroatCoverCoordinates)
        (modelWithCornersSelf Real ThroatCoverCoordinates) ∞
        ((extChartAt throatCoverModelWithCorners secondCenter) ∘
          (extChartAt throatCoverModelWithCorners firstCenter).symm)
        (extChartAt throatCoverModelWithCorners firstCenter current) :=
    hSecondChart.comp_of_eq hFirstInverse
      ((extChartAt throatCoverModelWithCorners firstCenter).left_inv hFirst)
  exact hTransition.contDiffAt.of_le (by
    show (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω)
    exact WithTop.coe_le_coe.mpr le_top)

/-- With the tangent frame fixed, the first chart representative is locally
the second representative composed with the genuine base-chart transition. -/
theorem throatGaugeCovectorCenteredChart_baseChartTransition_eventuallyEq
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (frameAnchor firstCenter secondCenter current :
      EffectiveThroat period hPeriod)
    (hFirst : current ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : current ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source) :
    throatGaugeCovectorCenteredChart period hPeriod potential component
        frameAnchor firstCenter =ᶠ[
          𝓝 (extChartAt throatCoverModelWithCorners firstCenter current)]
      (throatGaugeCovectorCenteredChart period hPeriod potential component
          frameAnchor secondCenter) ∘
        throatGaugeBaseChartTransition period hPeriod
          firstCenter secondCenter := by
  have hFirstTarget :
      extChartAt throatCoverModelWithCorners firstCenter current ∈
        (extChartAt throatCoverModelWithCorners firstCenter).target :=
    (extChartAt throatCoverModelWithCorners firstCenter).map_source hFirst
  have hInverseContinuous :
      ContinuousAt
        (extChartAt throatCoverModelWithCorners firstCenter).symm
        (extChartAt throatCoverModelWithCorners firstCenter current) :=
    continuousAt_extChartAt_symm'' hFirstTarget
  have hSecondPreimage :
      (extChartAt throatCoverModelWithCorners firstCenter).symm ⁻¹'
          (extChartAt throatCoverModelWithCorners secondCenter).source ∈
        𝓝 (extChartAt throatCoverModelWithCorners firstCenter current) :=
    hInverseContinuous.preimage_mem_nhds (by
      rw [(extChartAt throatCoverModelWithCorners firstCenter).left_inv hFirst]
      exact extChartAt_source_mem_nhds' hSecond)
  filter_upwards [hSecondPreimage] with coordinate hCoordinate
  have hSecondAt :
      (extChartAt throatCoverModelWithCorners firstCenter).symm coordinate ∈
        (extChartAt throatCoverModelWithCorners secondCenter).source :=
    hCoordinate
  simp only [throatGaugeCovectorCenteredChart,
    throatGaugeBaseChartTransition, Function.comp_apply]
  rw [(extChartAt throatCoverModelWithCorners secondCenter).left_inv hSecondAt]

end
end P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionGerm4D
end JanusFormal
