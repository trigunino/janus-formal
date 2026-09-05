import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCanonicalHolonomicIntrinsicMetricVolume4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularFrameCanonicalDivergenceLocalFormula4D

/-! # Smooth compact tests transported through a holonomic chart

A test supported inside the domain of a holonomic local inverse defines a
global smooth scalar on the quotient by zero extension. Its support and its
directional derivatives are controlled by the original coordinate test.
-/

namespace JanusFormal
namespace P0EFTJanusHolonomicCompactTestPushforward4D

set_option autoImplicit false
noncomputable section
open Set Function
open scoped Manifold ContDiff Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusProgramPRegularFrameCanonicalDivergenceLocalFormula4D
open P0EFTJanusCanonicalHolonomicStereographicOverlap4D

private abbrev Vector4 := Fin 4 → Real
variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- The chart maps the whole target of its local inverse into its source. -/
theorem holonomicCoordinateMap_mapsTo_inverse_source
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : Vector4) :
    MapsTo patch.coordinateMap
      (holonomicCoordinateLocalInverse period hPeriod patch coordinate).target
      (holonomicCoordinateLocalInverse period hPeriod patch coordinate).source := by
  intro current hCurrent
  let hLocal := patch.coordinateMap_isLocalDiffeomorph coordinate
  change patch.coordinateMap current ∈ hLocal.choose.target
  rw [hLocal.choose_spec.2 hCurrent]
  exact hLocal.choose.map_source hCurrent

/-- The coordinate test transported to the quotient and set to zero outside
the source of the chosen local inverse. -/
def holonomicPushforwardTest
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : Vector4)
    (test : Vector4 → Real) : EffectiveQuotient period hPeriod → Real :=
  (holonomicCoordinateLocalInverse period hPeriod patch coordinate).source.indicator
    (fun point => test (holonomicCoordinateLocalInverse period hPeriod patch coordinate point))

theorem holonomicPushforwardTest_pullback
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : Vector4)
    (test : Vector4 → Real) :
    EqOn (holonomicPushforwardTest period hPeriod patch coordinate test ∘ patch.coordinateMap)
      test (holonomicCoordinateLocalInverse period hPeriod patch coordinate).target := by
  intro current hCurrent
  have hSource := holonomicCoordinateMap_mapsTo_inverse_source
    period hPeriod patch coordinate hCurrent
  change (holonomicCoordinateLocalInverse period hPeriod patch coordinate).source.indicator
    (fun point => test (holonomicCoordinateLocalInverse period hPeriod patch coordinate point))
    (patch.coordinateMap current) = test current
  rw [indicator_of_mem hSource]
  exact congrArg test
    ((patch.coordinateMap_isLocalDiffeomorph coordinate).localInverse_left_inv hCurrent)

theorem holonomicPushforwardTest_tsupport_subset
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : Vector4)
    (test : Vector4 → Real) (hCompact : HasCompactSupport test) :
    tsupport (holonomicPushforwardTest period hPeriod patch coordinate test) ⊆
      patch.coordinateMap '' tsupport test := by
  apply closure_minimal _ (hCompact.image patch.coordinateMap_contMDiff.continuous).isClosed
  intro point hPoint
  by_cases hSource : point ∈ (holonomicCoordinateLocalInverse period hPeriod patch coordinate).source
  · have hNonzero : test (holonomicCoordinateLocalInverse period hPeriod patch coordinate point) ≠ 0 := by
      simpa only [mem_support, holonomicPushforwardTest, indicator_of_mem hSource] using hPoint
    exact ⟨holonomicCoordinateLocalInverse period hPeriod patch coordinate point,
      subset_closure hNonzero,
      (patch.coordinateMap_isLocalDiffeomorph coordinate).localInverse_right_inv hSource⟩
  · simp only [mem_support, holonomicPushforwardTest, indicator_of_notMem hSource, ne_eq,
      not_true_eq_false] at hPoint

theorem holonomicPushforwardTest_contMDiff
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : Vector4)
    (test : Vector4 → Real) (hTest : ContDiff Real ∞ test)
    (hCompact : HasCompactSupport test)
    (hSupport : tsupport test ⊆
      (holonomicCoordinateLocalInverse period hPeriod patch coordinate).target) :
    ContMDiff coverModelWithCorners (modelWithCornersSelf Real Real) ∞
      (holonomicPushforwardTest period hPeriod patch coordinate test) := by
  refine contMDiff_of_tsupport (fun point hPoint => ?_)
  obtain ⟨current, hCurrent, rfl⟩ :=
    holonomicPushforwardTest_tsupport_subset period hPeriod patch coordinate test hCompact hPoint
  have hSource := holonomicCoordinateMap_mapsTo_inverse_source
    period hPeriod patch coordinate (hSupport hCurrent)
  have hNeighborhood := (holonomicCoordinateLocalInverse
    period hPeriod patch coordinate).open_source.mem_nhds hSource
  have hSmooth := hTest.contMDiff.contMDiffAt.comp (patch.coordinateMap current)
    ((holonomicCoordinateLocalInverse period hPeriod patch coordinate).contMDiffOn_toFun.contMDiffAt
      hNeighborhood)
  apply hSmooth.congr_of_eventuallyEq
  exact Filter.eventuallyEq_of_mem hNeighborhood (fun point hPoint =>
    indicator_of_mem hPoint _)

def holonomicPushforwardSmoothTest
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : Vector4)
    (test : Vector4 → Real) (hTest : ContDiff Real ∞ test)
    (hCompact : HasCompactSupport test)
    (hSupport : tsupport test ⊆
      (holonomicCoordinateLocalInverse period hPeriod patch coordinate).target) :
    SmoothQuotientField period hPeriod Real where
  toFun := holonomicPushforwardTest period hPeriod patch coordinate test
  contMDiff_toFun := holonomicPushforwardTest_contMDiff
    period hPeriod patch coordinate test hTest hCompact hSupport

/-- The differential of the global test pulls back to the ordinary
differential of the original test on the whole inverse domain. -/
theorem holonomicPushforwardTest_derivative_pullback
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : Vector4)
    (test : Vector4 → Real) (hTest : ContDiff Real ∞ test)
    (hCompact : HasCompactSupport test)
    (hSupport : tsupport test ⊆
      (holonomicCoordinateLocalInverse period hPeriod patch coordinate).target)
    (current vector : Vector4)
    (hCurrent : current ∈ (holonomicCoordinateLocalInverse period hPeriod patch coordinate).target) :
    mvfderiv coverModelWithCorners (holonomicPushforwardTest period hPeriod patch coordinate test)
        (patch.coordinateMap current)
        (mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners
          patch.coordinateMap current vector) = fderiv Real test current vector := by
  have hAgreement := (holonomicPushforwardTest_pullback period hPeriod patch coordinate test).eventuallyEq_of_mem
    ((holonomicCoordinateLocalInverse period hPeriod patch coordinate).open_target.mem_nhds hCurrent)
  have hDerivative : mfderiv (modelWithCornersSelf Real Vector4) (modelWithCornersSelf Real Real)
      (holonomicPushforwardTest period hPeriod patch coordinate test ∘ patch.coordinateMap) current =
      mfderiv (modelWithCornersSelf Real Vector4) (modelWithCornersSelf Real Real) test current :=
    hAgreement.mfderiv_eq
  rw [mfderiv_comp current
    ((holonomicPushforwardTest_contMDiff period hPeriod patch coordinate test hTest hCompact hSupport
      ).mdifferentiableAt (by simp))
    (patch.coordinateMap_contMDiff.mdifferentiableAt (by simp)), mfderiv_eq_fderiv] at hDerivative
  exact congrArg (fun derivative => derivative vector) hDerivative

/-- The directional derivative vanishes outside the compact image of the
original test support, including the boundary of the inverse chart. -/
theorem holonomicPushforwardTest_derivative_eq_zero_off_support
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : Vector4)
    (test : Vector4 → Real) (hCompact : HasCompactSupport test)
    (point : EffectiveQuotient period hPeriod)
    (hPoint : point ∉ patch.coordinateMap '' tsupport test)
    (vector : TangentSpace coverModelWithCorners point) :
    mvfderiv coverModelWithCorners (holonomicPushforwardTest period hPeriod patch coordinate test)
      point vector = 0 := by
  have hOutside : point ∉ tsupport (holonomicPushforwardTest period hPeriod patch coordinate test) :=
    fun hMem => hPoint (holonomicPushforwardTest_tsupport_subset
      period hPeriod patch coordinate test hCompact hMem)
  have hDerivative : mfderiv coverModelWithCorners (modelWithCornersSelf Real Real)
      (holonomicPushforwardTest period hPeriod patch coordinate test) point =
      mfderiv coverModelWithCorners (modelWithCornersSelf Real Real)
        (fun _ : EffectiveQuotient period hPeriod => (0 : Real)) point :=
    (notMem_tsupport_iff_eventuallyEq.mp hOutside).mfderiv_eq
  simp only [mfderiv_const] at hDerivative
  change (mfderiv coverModelWithCorners (modelWithCornersSelf Real Real)
    (holonomicPushforwardTest period hPeriod patch coordinate test) point) vector = 0
  rw [hDerivative]
  rfl

/-- Exact advection identity for the regular-frame coordinate expansion of
any smooth intrinsic field. -/
theorem holonomicPushforwardTest_regular_frame_advection
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : Vector4)
    (field : SmoothTangentField period hPeriod)
    (test : Vector4 → Real) (hTest : ContDiff Real ∞ test)
    (hCompact : HasCompactSupport test)
    (hSupport : tsupport test ⊆
      (holonomicCoordinateLocalInverse period hPeriod patch coordinate).target)
    (current : Vector4)
    (hCurrent : current ∈ (holonomicCoordinateLocalInverse period hPeriod patch coordinate).target) :
    mvfderiv coverModelWithCorners (holonomicPushforwardTest period hPeriod patch coordinate test)
      (patch.coordinateMap current) (field (patch.coordinateMap current)) =
      fderiv Real test current (pulledRegularFrameExpansion period hPeriod metric patch field current) := by
  rw [← coordinateMap_mfderiv_pulledRegularFrameExpansion period hPeriod metric patch field current]
  exact holonomicPushforwardTest_derivative_pullback period hPeriod patch coordinate test hTest
    hCompact hSupport current (pulledRegularFrameExpansion period hPeriod metric patch field current) hCurrent

end
end P0EFTJanusHolonomicCompactTestPushforward4D
end JanusFormal
