import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatSmoothFieldSecondOrderJetOverlap4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatBaseChartTransitionThirdOrderCocycle4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatConstantFiberThirdOrderJetBaseChange4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPhysicalThirdOrderJetChartwiseExtraction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFramedThirdOrderJetSemidirectTransportSmoothness4D

/-!
# Third-order chart overlap for smooth throat fields

A smooth field with a fixed normed fiber has a third jet in every valid
extended throat chart.  These jets obey the constant-fiber third-order
transition law on chart overlaps.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatSmoothFieldThirdOrderJetOverlap4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 600000

noncomputable section

open Function Module Set Filter
open scoped Manifold ContDiff RealInnerProductSpace Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPPhysicalThirdOrderJetChartwiseExtraction4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionGerm4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetTransitionSmoothRegularity4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionSecondOrderCocycle4D
open P0EFTJanusProgramPActualThroatBaseChartTransitionThirdOrderCocycle4D
open P0EFTJanusProgramPFramedThirdOrderJetConstantFiberBaseChange4D
open P0EFTJanusProgramPFramedThirdOrderJetSemidirectTransportSmoothness4D
open P0EFTJanusProgramPActualThroatConstantFiberSecondOrderJetSmoothVectorBundleCore4D
open P0EFTJanusProgramPActualThroatConstantFiberThirdOrderJetBaseChange4D
open P0EFTJanusProgramPActualThroatSmoothFieldSecondOrderJetOverlap4D

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

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

variable {Fiber : Type*}
  [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]

private abbrev FiberFirstDerivative :=
  ThroatCoverCoordinates →L[Real] Fiber

local instance fiberFirstDerivativeNormedAddCommGroup :
    NormedAddCommGroup (FiberFirstDerivative (Fiber := Fiber)) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance fiberFirstDerivativeNormedSpace :
    NormedSpace Real (FiberFirstDerivative (Fiber := Fiber)) :=
  ContinuousLinearMap.toNormedSpace

private abbrev FiberSecondDerivative :=
  ThroatCoverCoordinates →L[Real] FiberFirstDerivative (Fiber := Fiber)

local instance fiberSecondDerivativeNormedAddCommGroup :
    NormedAddCommGroup (FiberSecondDerivative (Fiber := Fiber)) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance fiberSecondDerivativeNormedSpace :
    NormedSpace Real (FiberSecondDerivative (Fiber := Fiber)) :=
  ContinuousLinearMap.toNormedSpace

private abbrev FiberThirdDerivative :=
  ThroatCoverCoordinates →L[Real] FiberSecondDerivative (Fiber := Fiber)

local instance fiberThirdDerivativeNormedAddCommGroup :
    NormedAddCommGroup (FiberThirdDerivative (Fiber := Fiber)) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance fiberThirdDerivativeNormedSpace :
    NormedSpace Real (FiberThirdDerivative (Fiber := Fiber)) :=
  ContinuousLinearMap.toNormedSpace

/-! ## Arbitrary-chart extraction -/

/-- `C³` specialization of the smooth coordinate representative. -/
theorem throatSmoothFieldChartRepresentative_contDiffAt_three_of_mem_source
    (field : SmoothThroatField period hPeriod Fiber)
    (chartAnchor current : EffectiveThroat period hPeriod)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source) :
    ContDiffAt Real 3
      (throatSmoothFieldChartRepresentative period hPeriod field chartAnchor)
      (extChartAt throatCoverModelWithCorners chartAnchor current) :=
  (throatSmoothFieldChartRepresentative_contDiffAt_infty_of_mem_source
    period hPeriod field chartAnchor current hChart).of_le (by
      show (3 : ℕ∞ω) ≤ (∞ : ℕ∞ω)
      exact WithTop.coe_le_coe.mpr le_top)

/-- The value and first three Frechet derivatives in an arbitrary valid
extended chart. -/
def throatSmoothFieldThirdOrderJetInChartAt
    (field : SmoothThroatField period hPeriod Fiber)
    (chartAnchor current : EffectiveThroat period hPeriod)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source) :
    FramedThirdOrderJet ThroatCoverCoordinates Fiber :=
  chartwiseThirdOrderJetAt
    (throatSmoothFieldChartRepresentative period hPeriod field chartAnchor)
    (extChartAt throatCoverModelWithCorners chartAnchor current)
    (throatSmoothFieldChartRepresentative_contDiffAt_three_of_mem_source
      period hPeriod field chartAnchor current hChart)

@[simp]
theorem throatSmoothFieldThirdOrderJetInChartAt_value
    (field : SmoothThroatField period hPeriod Fiber)
    (chartAnchor current : EffectiveThroat period hPeriod)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source) :
    (throatSmoothFieldThirdOrderJetInChartAt period hPeriod field
      chartAnchor current hChart).value = field current := by
  rw [throatSmoothFieldThirdOrderJetInChartAt,
    chartwiseThirdOrderJetAt_value]
  simp only [throatSmoothFieldChartRepresentative, Function.comp_apply]
  rw [(extChartAt throatCoverModelWithCorners chartAnchor).left_inv hChart]

@[simp]
theorem throatSmoothFieldThirdOrderJetInChartAt_firstDerivative
    (field : SmoothThroatField period hPeriod Fiber)
    (chartAnchor current : EffectiveThroat period hPeriod)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source) :
    (throatSmoothFieldThirdOrderJetInChartAt period hPeriod field
      chartAnchor current hChart).firstDerivative =
      fderiv Real
        (throatSmoothFieldChartRepresentative period hPeriod field chartAnchor)
        (extChartAt throatCoverModelWithCorners chartAnchor current) :=
  rfl

@[simp]
theorem throatSmoothFieldThirdOrderJetInChartAt_secondDerivative
    (field : SmoothThroatField period hPeriod Fiber)
    (chartAnchor current : EffectiveThroat period hPeriod)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source) :
    (throatSmoothFieldThirdOrderJetInChartAt period hPeriod field
      chartAnchor current hChart).secondDerivative =
      fderiv Real
        (fderiv Real
          (throatSmoothFieldChartRepresentative period hPeriod field
            chartAnchor))
        (extChartAt throatCoverModelWithCorners chartAnchor current) :=
  rfl

@[simp]
theorem throatSmoothFieldThirdOrderJetInChartAt_thirdDerivative
    (field : SmoothThroatField period hPeriod Fiber)
    (chartAnchor current : EffectiveThroat period hPeriod)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source) :
    (throatSmoothFieldThirdOrderJetInChartAt period hPeriod field
      chartAnchor current hChart).thirdDerivative =
      fderiv Real
        (fderiv Real
          (fderiv Real
            (throatSmoothFieldChartRepresentative period hPeriod field
              chartAnchor)))
        (extChartAt throatCoverModelWithCorners chartAnchor current) :=
  rfl

/-- Truncation recovers the existing arbitrary-chart second jet. -/
@[simp]
theorem throatSmoothFieldThirdOrderJetInChartAt_toFramedSecondOrderJet
    (field : SmoothThroatField period hPeriod Fiber)
    (chartAnchor current : EffectiveThroat period hPeriod)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source) :
    (throatSmoothFieldThirdOrderJetInChartAt period hPeriod field
      chartAnchor current hChart).toFramedSecondOrderJet =
      throatSmoothFieldSecondOrderJetInChartAt period hPeriod field
        chartAnchor current hChart := by
  apply FramedSecondOrderJet.ext_components
  · rfl
  · rfl
  · rfl

/-! ## Smooth totalized local representative -/

/-- The third derivative of a fixed-chart representative is smooth on the
chart source. -/
theorem throatSmoothFieldLocalThirdDerivative_contMDiffOn
    (field : SmoothThroatField period hPeriod Fiber)
    (chartAnchor : EffectiveThroat period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, FiberThirdDerivative (Fiber := Fiber)) ∞
      (fun current : EffectiveThroat period hPeriod ↦
        fderiv Real
          (fderiv Real
            (fderiv Real
              (throatSmoothFieldChartRepresentative period hPeriod field
                chartAnchor)))
          (extChartAt throatCoverModelWithCorners chartAnchor current))
      (extChartAt throatCoverModelWithCorners chartAnchor).source := by
  intro current hCurrent
  have hGerm :=
    throatSmoothFieldChartRepresentative_contDiffAt_infty_of_mem_source
      period hPeriod field chartAnchor current hCurrent
  have hThirdDerivative :=
    ((hGerm.fderiv_right (m := ∞) (by simp)).fderiv_right
      (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)
  have hChart : ContMDiffAt throatCoverModelWithCorners
      𝓘(Real, ThroatCoverCoordinates) ∞
      (extChartAt throatCoverModelWithCorners chartAnchor) current := by
    apply contMDiffAt_extChartAt'
    simpa only [extChartAt_source] using hCurrent
  exact (hThirdDerivative.contMDiffAt.comp current hChart).contMDiffWithinAt

/-- Totalized chartwise third jet. -/
def throatSmoothFieldThirdOrderJetLocalRepresentative
    (field : SmoothThroatField period hPeriod Fiber)
    (chartAnchor current : EffectiveThroat period hPeriod) :
    FramedThirdOrderJet ThroatCoverCoordinates Fiber := by
  classical
  exact if hCurrent : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source then
    throatSmoothFieldThirdOrderJetInChartAt period hPeriod field
      chartAnchor current hCurrent
  else 0

/-- On its chart source, the totalization is the arbitrary-chart extraction. -/
theorem throatSmoothFieldThirdOrderJetLocalRepresentative_eq_of_mem
    (field : SmoothThroatField period hPeriod Fiber)
    (chartAnchor current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source) :
    throatSmoothFieldThirdOrderJetLocalRepresentative period hPeriod field
        chartAnchor current =
      throatSmoothFieldThirdOrderJetInChartAt period hPeriod field
        chartAnchor current hCurrent := by
  simp only [throatSmoothFieldThirdOrderJetLocalRepresentative,
    dif_pos hCurrent]

/-- Totalized third jets truncate to the existing totalized second jets. -/
@[simp]
theorem throatSmoothFieldThirdOrderJetLocalRepresentative_truncate
    (field : SmoothThroatField period hPeriod Fiber)
    (chartAnchor current : EffectiveThroat period hPeriod) :
    (throatSmoothFieldThirdOrderJetLocalRepresentative period hPeriod field
      chartAnchor current).toFramedSecondOrderJet =
      throatSmoothFieldSecondOrderJetLocalRepresentative period hPeriod field
        chartAnchor current := by
  classical
  unfold throatSmoothFieldThirdOrderJetLocalRepresentative
    throatSmoothFieldSecondOrderJetLocalRepresentative
  split
  · apply FramedSecondOrderJet.ext_components <;> rfl
  · rfl

private theorem throatSmoothFieldThirdOrderJetLocalRepresentative_thirdDerivative_contMDiffOn
    (field : SmoothThroatField period hPeriod Fiber)
    (chartAnchor : EffectiveThroat period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, FiberThirdDerivative (Fiber := Fiber)) ∞
      (fun current : EffectiveThroat period hPeriod ↦
        (throatSmoothFieldThirdOrderJetLocalRepresentative period hPeriod
          field chartAnchor current).thirdDerivative)
      (extChartAt throatCoverModelWithCorners chartAnchor).source := by
  apply (throatSmoothFieldLocalThirdDerivative_contMDiffOn period hPeriod
    field chartAnchor).congr
  intro current hCurrent
  unfold throatSmoothFieldThirdOrderJetLocalRepresentative
  split
  · rw [throatSmoothFieldThirdOrderJetInChartAt_thirdDerivative]
  · contradiction

/-- The totalized chartwise third jet is smooth on its chart source. -/
theorem throatSmoothFieldThirdOrderJetLocalRepresentative_contMDiffOn
    [FiniteDimensional Real Fiber]
    (field : SmoothThroatField period hPeriod Fiber)
    (chartAnchor : EffectiveThroat period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, FramedThirdOrderJet ThroatCoverCoordinates Fiber) ∞
      (throatSmoothFieldThirdOrderJetLocalRepresentative period hPeriod
        field chartAnchor)
      (extChartAt throatCoverModelWithCorners chartAnchor).source := by
  have hLower : ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, FramedSecondOrderJet ThroatCoverCoordinates Fiber) ∞
      (fun current ↦
        (throatSmoothFieldThirdOrderJetLocalRepresentative period hPeriod
          field chartAnchor current).toFramedSecondOrderJet)
      (extChartAt throatCoverModelWithCorners chartAnchor).source := by
    apply (throatSmoothFieldSecondOrderJetLocalRepresentative_contMDiffOn
      period hPeriod field chartAnchor).congr
    intro current _
    exact throatSmoothFieldThirdOrderJetLocalRepresentative_truncate
      period hPeriod field chartAnchor current
  exact contMDiffOn_framedThirdOrderJet_of_truncate_and_thirdDerivative
    (throatSmoothFieldThirdOrderJetLocalRepresentative period hPeriod
      field chartAnchor) hLower
    (throatSmoothFieldThirdOrderJetLocalRepresentative_thirdDerivative_contMDiffOn
      period hPeriod field chartAnchor)

/-! ## Constant-fiber overlap transport -/

/-- On a double chart overlap, the target-chart third jet is the
constant-fiber transport of the source-chart third jet. -/
theorem throatSmoothFieldThirdOrderJetInChartAt_transition
    (field : SmoothThroatField period hPeriod Fiber)
    (sourceCenter targetCenter current : EffectiveThroat period hPeriod)
    (hSource : current ∈
      (extChartAt throatCoverModelWithCorners sourceCenter).source)
    (hTarget : current ∈
      (extChartAt throatCoverModelWithCorners targetCenter).source) :
    throatSmoothFieldThirdOrderJetInChartAt period hPeriod field
        targetCenter current hTarget =
      (actualThroatConstantFiberThirdOrderJetBaseChangeAt period hPeriod
        sourceCenter targetCenter current hSource hTarget).transport
        (throatSmoothFieldThirdOrderJetInChartAt period hPeriod field
          sourceCenter current hSource) := by
  let transition :=
    throatGaugeBaseChartTransition period hPeriod targetCenter sourceCenter
  let sourceRepresentative :=
    throatSmoothFieldChartRepresentative period hPeriod field sourceCenter
  let targetRepresentative :=
    throatSmoothFieldChartRepresentative period hPeriod field targetCenter
  let sourceCoordinate :=
    extChartAt throatCoverModelWithCorners sourceCenter current
  let targetCoordinate :=
    extChartAt throatCoverModelWithCorners targetCenter current
  have hTransition : ContDiffAt Real 3 transition targetCoordinate :=
    (throatGaugeBaseChartTransition_contDiffAt_infty period hPeriod
      targetCenter sourceCenter current hTarget hSource).of_le (by
        change ((3 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
        exact WithTop.coe_le_coe.mpr le_top)
  have hSourceRepresentative : ContDiffAt Real 3 sourceRepresentative
      sourceCoordinate := by
    simpa only [sourceRepresentative, sourceCoordinate] using
      throatSmoothFieldChartRepresentative_contDiffAt_three_of_mem_source
        period hPeriod field sourceCenter current hSource
  have hTransitionAt : transition targetCoordinate = sourceCoordinate := by
    simpa only [transition, targetCoordinate, sourceCoordinate] using
      throatGaugeBaseChartTransition_apply_current period hPeriod
        targetCenter sourceCenter current hTarget
  have hSourceRepresentativeAtTransition :
      ContDiffAt Real 3 sourceRepresentative
        (transition targetCoordinate) := by
    simpa only [hTransitionAt] using hSourceRepresentative
  have hGerm : targetRepresentative =ᶠ[𝓝 targetCoordinate]
      sourceRepresentative ∘ transition := by
    simpa only [targetRepresentative, sourceRepresentative, transition,
      targetCoordinate] using
      throatSmoothFieldChartRepresentative_baseChartTransition_eventuallyEq
        period hPeriod field targetCenter sourceCenter current hTarget hSource
  apply FramedThirdOrderJet.ext_components
  · rw [throatSmoothFieldThirdOrderJetInChartAt_toFramedSecondOrderJet,
      actualThroatConstantFiberThirdOrderJetBaseChangeAt_transport_truncate,
      throatSmoothFieldThirdOrderJetInChartAt_toFramedSecondOrderJet]
    simpa only [actualThroatConstantFiberSecondOrderJetBaseChangeAt,
      throatSmoothFieldConstantFiberBaseChangeAt] using
      throatSmoothFieldSecondOrderJetInChartAt_transition period hPeriod field
        sourceCenter targetCenter current hSource hTarget
  · apply ContinuousLinearMap.ext
    intro first
    apply ContinuousLinearMap.ext
    intro second
    apply ContinuousLinearMap.ext
    intro third
    simp only [
      throatSmoothFieldThirdOrderJetInChartAt_thirdDerivative,
      throatSmoothFieldThirdOrderJetInChartAt_secondDerivative,
      throatSmoothFieldThirdOrderJetInChartAt_firstDerivative,
      FramedThirdOrderJetConstantFiberBaseChange.transport_thirdDerivative_apply,
      actualThroatConstantFiberThirdOrderJetBaseChangeAt,
      actualThroatConstantFiberSecondOrderJetBaseChangeAt,
      throatGaugeBaseChartTransitionSecondOrderJetAt_firstDerivative,
      throatGaugeBaseChartTransitionSecondOrderJetAt_secondDerivative]
    have hThirdDerivative :
        fderiv Real (fderiv Real (fderiv Real targetRepresentative))
            targetCoordinate =
          fderiv Real
            (fderiv Real
              (fderiv Real (sourceRepresentative ∘ transition)))
            targetCoordinate :=
      ((hGerm.fderiv (𝕜 := Real)).fderiv (𝕜 := Real)).fderiv_eq
    rw [show
      fderiv Real (fderiv Real (fderiv Real targetRepresentative))
            targetCoordinate first second third =
        fderiv Real
          (fderiv Real
            (fderiv Real (sourceRepresentative ∘ transition)))
          targetCoordinate first second third by
      exact congrArg
        (fun derivative : ThroatCoverCoordinates →L[Real]
            ThroatCoverCoordinates →L[Real]
              ThroatCoverCoordinates →L[Real] Fiber ↦
          derivative first second third) hThirdDerivative]
    rw [third_fderiv_comp_apply transition sourceRepresentative
      targetCoordinate hTransition hSourceRepresentativeAtTransition,
      hTransitionAt]

end
end P0EFTJanusProgramPActualThroatSmoothFieldThirdOrderJetOverlap4D
end JanusFormal
