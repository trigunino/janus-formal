import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusSmoothThroatTrace4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionSecondOrderCocycle4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFramedSecondOrderJetConstantFiberBaseChange4D

/-!
# Second-order chart overlap for smooth throat fields

A smooth field with a fixed normed fiber has a second jet in every valid
extended throat chart.  On a double overlap, these jets are related by the
constant-fiber second-order transport of the reverse base-chart transition.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatSmoothFieldSecondOrderJetOverlap4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 300000

noncomputable section

open Function Module Set Filter
open scoped Manifold ContDiff RealInnerProductSpace Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPPhysicalSecondOrderJetChartwiseExtraction4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionGerm4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartSecondOrderJetOverlap4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionSecondOrderCocycle4D
open P0EFTJanusProgramPFramedSecondOrderJetConstantFiberBaseChange4D

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

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

/-! ## A smooth retraction from arbitrary jet components -/

private def symmetrizedThroatFieldJet
    (components : FramedSecondOrderJetAmbient
      ThroatCoverCoordinates Fiber) :
    FramedSecondOrderJet ThroatCoverCoordinates Fiber where
  value := components.1
  firstDerivative := components.2.1
  secondDerivative :=
    (2 : Real)⁻¹ • (components.2.2 + components.2.2.flip)
  secondDerivative_symmetric first second := by
    simp only [smul_apply, add_apply, ContinuousLinearMap.flip_apply]
    rw [add_comm]

private def symmetrizedThroatFieldJetLinearMap :
    FramedSecondOrderJetAmbient ThroatCoverCoordinates Fiber →ₗ[Real]
      FramedSecondOrderJet ThroatCoverCoordinates Fiber where
  toFun := symmetrizedThroatFieldJet
  map_add' first second := by
    apply FramedSecondOrderJet.ext_components ThroatCoverCoordinates Fiber
    · simp only [symmetrizedThroatFieldJet,
        FramedSecondOrderJet.add_value, Prod.fst_add]
    · simp only [symmetrizedThroatFieldJet,
        FramedSecondOrderJet.add_firstDerivative, Prod.snd_add,
        Prod.fst_add]
    · simp only [symmetrizedThroatFieldJet,
        FramedSecondOrderJet.add_secondDerivative, Prod.snd_add,
        ContinuousLinearMap.flip_add]
      module
  map_smul' scalar components := by
    apply FramedSecondOrderJet.ext_components ThroatCoverCoordinates Fiber
    · simp only [symmetrizedThroatFieldJet,
        FramedSecondOrderJet.smul_value, Prod.smul_fst,
        RingHom.id_apply]
    · simp only [symmetrizedThroatFieldJet,
        FramedSecondOrderJet.smul_firstDerivative, Prod.smul_snd,
        Prod.smul_fst, RingHom.id_apply]
    · simp only [symmetrizedThroatFieldJet,
        FramedSecondOrderJet.smul_secondDerivative, Prod.smul_snd,
        ContinuousLinearMap.flip_smul, RingHom.id_apply]
      module

private def symmetrizedThroatFieldJetContinuousLinearMap
    [FiniteDimensional Real Fiber] :
    FramedSecondOrderJetAmbient ThroatCoverCoordinates Fiber →L[Real]
      FramedSecondOrderJet ThroatCoverCoordinates Fiber :=
  LinearMap.toContinuousLinearMap symmetrizedThroatFieldJetLinearMap

private theorem symmetrizedThroatFieldJetContinuousLinearMap_components
    [FiniteDimensional Real Fiber]
    (jet : FramedSecondOrderJet ThroatCoverCoordinates Fiber) :
    symmetrizedThroatFieldJetContinuousLinearMap
        (jet.value, jet.firstDerivative, jet.secondDerivative) = jet := by
  change symmetrizedThroatFieldJet
    (jet.value, jet.firstDerivative, jet.secondDerivative) = jet
  apply FramedSecondOrderJet.ext_components ThroatCoverCoordinates Fiber
  · rfl
  · rfl
  · apply ContinuousLinearMap.ext
    intro first
    apply ContinuousLinearMap.ext
    intro second
    simp only [symmetrizedThroatFieldJet, smul_apply, add_apply,
      ContinuousLinearMap.flip_apply]
    rw [jet.secondDerivative_symmetric second first]
    module

/-! ## Representatives and jets in an arbitrary chart -/

/-- Coordinate representative of a globally fixed-fiber smooth throat
field in the extended chart centered at `chartAnchor`. -/
def throatSmoothFieldChartRepresentative
    (field : SmoothThroatField period hPeriod Fiber)
    (chartAnchor : EffectiveThroat period hPeriod) :
    ThroatCoverCoordinates → Fiber :=
  field.toFun ∘ (extChartAt throatCoverModelWithCorners chartAnchor).symm

/-- The representative is `C∞` at every coordinate whose represented point
belongs to the chart source. -/
theorem throatSmoothFieldChartRepresentative_contDiffAt_infty_of_mem_source
    (field : SmoothThroatField period hPeriod Fiber)
    (chartAnchor current : EffectiveThroat period hPeriod)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source) :
    ContDiffAt Real ∞
      (throatSmoothFieldChartRepresentative period hPeriod field chartAnchor)
      (extChartAt throatCoverModelWithCorners chartAnchor current) := by
  have hTarget :
      extChartAt throatCoverModelWithCorners chartAnchor current ∈
        (extChartAt throatCoverModelWithCorners chartAnchor).target :=
    (extChartAt throatCoverModelWithCorners chartAnchor).map_source hChart
  have hInverse : ContMDiffAt
      𝓘(Real, ThroatCoverCoordinates) throatCoverModelWithCorners ∞
      (extChartAt throatCoverModelWithCorners chartAnchor).symm
      (extChartAt throatCoverModelWithCorners chartAnchor current) :=
    (contMDiffOn_extChartAt_symm
      (I := throatCoverModelWithCorners) (n := ∞) chartAnchor).contMDiffAt
        (extChartAt_target_mem_nhds' hTarget)
  have hField : ContMDiffAt throatCoverModelWithCorners
      𝓘(Real, Fiber) ∞ field.toFun current :=
    field.contMDiff_toFun.contMDiffAt
  have hComposition := hField.comp_of_eq hInverse
    ((extChartAt throatCoverModelWithCorners chartAnchor).left_inv hChart)
  exact hComposition.contDiffAt

/-- `C²` specialization used to package the chartwise second jet. -/
theorem throatSmoothFieldChartRepresentative_contDiffAt_two_of_mem_source
    (field : SmoothThroatField period hPeriod Fiber)
    (chartAnchor current : EffectiveThroat period hPeriod)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source) :
    ContDiffAt Real 2
      (throatSmoothFieldChartRepresentative period hPeriod field chartAnchor)
      (extChartAt throatCoverModelWithCorners chartAnchor current) :=
  (throatSmoothFieldChartRepresentative_contDiffAt_infty_of_mem_source
    period hPeriod field chartAnchor current hChart).of_le (by
      show (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω)
      exact WithTop.coe_le_coe.mpr le_top)

/-- The value and first two Fréchet derivatives of a fixed-fiber smooth
field in an arbitrary valid extended chart. -/
def throatSmoothFieldSecondOrderJetInChartAt
    (field : SmoothThroatField period hPeriod Fiber)
    (chartAnchor current : EffectiveThroat period hPeriod)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source) :
    FramedSecondOrderJet ThroatCoverCoordinates Fiber :=
  chartwiseSecondOrderJetAt
    (throatSmoothFieldChartRepresentative period hPeriod field chartAnchor)
    (extChartAt throatCoverModelWithCorners chartAnchor current)
    (throatSmoothFieldChartRepresentative_contDiffAt_two_of_mem_source
      period hPeriod field chartAnchor current hChart)

@[simp]
theorem throatSmoothFieldSecondOrderJetInChartAt_value
    (field : SmoothThroatField period hPeriod Fiber)
    (chartAnchor current : EffectiveThroat period hPeriod)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source) :
    (throatSmoothFieldSecondOrderJetInChartAt period hPeriod field
      chartAnchor current hChart).value = field current := by
  rw [throatSmoothFieldSecondOrderJetInChartAt,
    chartwiseSecondOrderJetAt_value]
  simp only [throatSmoothFieldChartRepresentative, Function.comp_apply]
  rw [(extChartAt throatCoverModelWithCorners chartAnchor).left_inv hChart]

@[simp]
theorem throatSmoothFieldSecondOrderJetInChartAt_firstDerivative
    (field : SmoothThroatField period hPeriod Fiber)
    (chartAnchor current : EffectiveThroat period hPeriod)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source) :
    (throatSmoothFieldSecondOrderJetInChartAt period hPeriod field
      chartAnchor current hChart).firstDerivative =
      fderiv Real
        (throatSmoothFieldChartRepresentative period hPeriod field chartAnchor)
        (extChartAt throatCoverModelWithCorners chartAnchor current) :=
  rfl

@[simp]
theorem throatSmoothFieldSecondOrderJetInChartAt_secondDerivative
    (field : SmoothThroatField period hPeriod Fiber)
    (chartAnchor current : EffectiveThroat period hPeriod)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source) :
    (throatSmoothFieldSecondOrderJetInChartAt period hPeriod field
      chartAnchor current hChart).secondDerivative =
      fderiv Real
        (fderiv Real
          (throatSmoothFieldChartRepresentative period hPeriod field
            chartAnchor))
      (extChartAt throatCoverModelWithCorners chartAnchor current) :=
  rfl

/-! ## Smooth totalized local representative -/

/-- The chartwise Jacobian field is `C∞` on the chart source. -/
theorem throatSmoothFieldLocalFirstDerivative_contMDiffOn
    (field : SmoothThroatField period hPeriod Fiber)
    (chartAnchor : EffectiveThroat period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, ThroatCoverCoordinates →L[Real] Fiber) ∞
      (fun current : EffectiveThroat period hPeriod ↦
        fderiv Real
          (throatSmoothFieldChartRepresentative period hPeriod field
            chartAnchor)
          (extChartAt throatCoverModelWithCorners chartAnchor current))
      (extChartAt throatCoverModelWithCorners chartAnchor).source := by
  intro current hCurrent
  have hGerm :=
    throatSmoothFieldChartRepresentative_contDiffAt_infty_of_mem_source
      period hPeriod field chartAnchor current hCurrent
  have hDerivative := hGerm.fderiv_right (m := ∞) (by simp)
  have hChart : ContMDiffAt throatCoverModelWithCorners
      𝓘(Real, ThroatCoverCoordinates) ∞
      (extChartAt throatCoverModelWithCorners chartAnchor) current := by
    apply contMDiffAt_extChartAt'
    simpa only [extChartAt_source] using hCurrent
  exact (hDerivative.contMDiffAt.comp current hChart).contMDiffWithinAt

/-- The chartwise Hessian field is `C∞` on the chart source. -/
theorem throatSmoothFieldLocalSecondDerivative_contMDiffOn
    (field : SmoothThroatField period hPeriod Fiber)
    (chartAnchor : EffectiveThroat period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, ThroatCoverCoordinates →L[Real]
        ThroatCoverCoordinates →L[Real] Fiber) ∞
      (fun current : EffectiveThroat period hPeriod ↦
        fderiv Real
          (fderiv Real
            (throatSmoothFieldChartRepresentative period hPeriod field
              chartAnchor))
          (extChartAt throatCoverModelWithCorners chartAnchor current))
      (extChartAt throatCoverModelWithCorners chartAnchor).source := by
  intro current hCurrent
  have hGerm :=
    throatSmoothFieldChartRepresentative_contDiffAt_infty_of_mem_source
      period hPeriod field chartAnchor current hCurrent
  have hSecondDerivative :=
    (hGerm.fderiv_right (m := ∞) (by simp)).fderiv_right
      (m := ∞) (by simp)
  have hChart : ContMDiffAt throatCoverModelWithCorners
      𝓘(Real, ThroatCoverCoordinates) ∞
      (extChartAt throatCoverModelWithCorners chartAnchor) current := by
    apply contMDiffAt_extChartAt'
    simpa only [extChartAt_source] using hCurrent
  exact (hSecondDerivative.contMDiffAt.comp current hChart).contMDiffWithinAt

/-- Totalized chartwise second jet.  Its value away from the chart source is
irrelevant to all local smoothness and overlap statements. -/
def throatSmoothFieldSecondOrderJetLocalRepresentative
    (field : SmoothThroatField period hPeriod Fiber)
    (chartAnchor current : EffectiveThroat period hPeriod) :
    FramedSecondOrderJet ThroatCoverCoordinates Fiber := by
  classical
  exact if hCurrent : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source then
    throatSmoothFieldSecondOrderJetInChartAt period hPeriod field
      chartAnchor current hCurrent
  else 0

private theorem throatSmoothFieldSecondOrderJetLocalRepresentative_value_contMDiffOn
    (field : SmoothThroatField period hPeriod Fiber)
    (chartAnchor : EffectiveThroat period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners 𝓘(Real, Fiber) ∞
      (fun current : EffectiveThroat period hPeriod ↦
        (throatSmoothFieldSecondOrderJetLocalRepresentative period hPeriod
          field chartAnchor current).value)
      (extChartAt throatCoverModelWithCorners chartAnchor).source := by
  apply field.contMDiff_toFun.contMDiffOn.congr
  intro current hCurrent
  unfold throatSmoothFieldSecondOrderJetLocalRepresentative
  split
  · rw [throatSmoothFieldSecondOrderJetInChartAt_value]
  · contradiction

private theorem throatSmoothFieldSecondOrderJetLocalRepresentative_firstDerivative_contMDiffOn
    (field : SmoothThroatField period hPeriod Fiber)
    (chartAnchor : EffectiveThroat period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, ThroatCoverCoordinates →L[Real] Fiber) ∞
      (fun current : EffectiveThroat period hPeriod ↦
        (throatSmoothFieldSecondOrderJetLocalRepresentative period hPeriod
          field chartAnchor current).firstDerivative)
      (extChartAt throatCoverModelWithCorners chartAnchor).source := by
  apply (throatSmoothFieldLocalFirstDerivative_contMDiffOn period hPeriod
    field chartAnchor).congr
  intro current hCurrent
  unfold throatSmoothFieldSecondOrderJetLocalRepresentative
  split
  · rw [throatSmoothFieldSecondOrderJetInChartAt_firstDerivative]
  · contradiction

private theorem throatSmoothFieldSecondOrderJetLocalRepresentative_secondDerivative_contMDiffOn
    (field : SmoothThroatField period hPeriod Fiber)
    (chartAnchor : EffectiveThroat period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, ThroatCoverCoordinates →L[Real]
        ThroatCoverCoordinates →L[Real] Fiber) ∞
      (fun current : EffectiveThroat period hPeriod ↦
        (throatSmoothFieldSecondOrderJetLocalRepresentative period hPeriod
          field chartAnchor current).secondDerivative)
      (extChartAt throatCoverModelWithCorners chartAnchor).source := by
  apply (throatSmoothFieldLocalSecondDerivative_contMDiffOn period hPeriod
    field chartAnchor).congr
  intro current hCurrent
  unfold throatSmoothFieldSecondOrderJetLocalRepresentative
  split
  · rw [throatSmoothFieldSecondOrderJetInChartAt_secondDerivative]
  · contradiction

/-- The totalized chartwise second jet is `C∞` on its chart source. -/
theorem throatSmoothFieldSecondOrderJetLocalRepresentative_contMDiffOn
    [FiniteDimensional Real Fiber]
    (field : SmoothThroatField period hPeriod Fiber)
    (chartAnchor : EffectiveThroat period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, FramedSecondOrderJet ThroatCoverCoordinates Fiber) ∞
      (throatSmoothFieldSecondOrderJetLocalRepresentative period hPeriod
        field chartAnchor)
      (extChartAt throatCoverModelWithCorners chartAnchor).source := by
  have hValue :=
    throatSmoothFieldSecondOrderJetLocalRepresentative_value_contMDiffOn
      period hPeriod field chartAnchor
  have hFirstDerivative :=
    throatSmoothFieldSecondOrderJetLocalRepresentative_firstDerivative_contMDiffOn
      period hPeriod field chartAnchor
  have hSecondDerivative :=
    throatSmoothFieldSecondOrderJetLocalRepresentative_secondDerivative_contMDiffOn
      period hPeriod field chartAnchor
  have hComponents : ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, FramedSecondOrderJetAmbient ThroatCoverCoordinates Fiber) ∞
      (fun current : EffectiveThroat period hPeriod ↦
        ((throatSmoothFieldSecondOrderJetLocalRepresentative period hPeriod
            field chartAnchor current).value,
          (throatSmoothFieldSecondOrderJetLocalRepresentative period hPeriod
            field chartAnchor current).firstDerivative,
          (throatSmoothFieldSecondOrderJetLocalRepresentative period hPeriod
            field chartAnchor current).secondDerivative))
      (extChartAt throatCoverModelWithCorners chartAnchor).source := by
    rw [contMDiffOn_prod_module_iff]
    constructor
    · change ContMDiffOn throatCoverModelWithCorners _ ∞
        (fun current ↦
          (throatSmoothFieldSecondOrderJetLocalRepresentative period hPeriod
            field chartAnchor current).value) _
      exact hValue
    · rw [contMDiffOn_prod_module_iff]
      constructor
      · change ContMDiffOn throatCoverModelWithCorners _ ∞
          (fun current ↦
            (throatSmoothFieldSecondOrderJetLocalRepresentative period hPeriod
              field chartAnchor current).firstDerivative) _
        exact hFirstDerivative
      · change ContMDiffOn throatCoverModelWithCorners _ ∞
          (fun current ↦
            (throatSmoothFieldSecondOrderJetLocalRepresentative period hPeriod
              field chartAnchor current).secondDerivative) _
        exact hSecondDerivative
  have hBack :=
    symmetrizedThroatFieldJetContinuousLinearMap.contMDiff.comp_contMDiffOn
      hComponents
  apply hBack.congr
  intro current _
  exact
    (symmetrizedThroatFieldJetContinuousLinearMap_components
      (throatSmoothFieldSecondOrderJetLocalRepresentative period hPeriod
        field chartAnchor current)).symm

/-! ## Constant-fiber overlap transport -/

/-- Base two-jet which transports a jet written in `sourceCenter` coordinates
to the same field jet written in `targetCenter` coordinates.  Its underlying
coordinate transition therefore runs from `targetCenter` to `sourceCenter`. -/
def throatSmoothFieldConstantFiberBaseChangeAt
    (sourceCenter targetCenter current : EffectiveThroat period hPeriod)
    (hSource : current ∈
      (extChartAt throatCoverModelWithCorners sourceCenter).source)
    (hTarget : current ∈
      (extChartAt throatCoverModelWithCorners targetCenter).source) :
    FramedSecondOrderJetConstantFiberBaseChange ThroatCoverCoordinates where
  baseFirst :=
    (throatGaugeBaseChartTransitionSecondOrderJetAt period hPeriod
      targetCenter sourceCenter current hTarget hSource).firstDerivative
  baseSecond :=
    (throatGaugeBaseChartTransitionSecondOrderJetAt period hPeriod
      targetCenter sourceCenter current hTarget hSource).secondDerivative
  baseSecond_symmetric :=
    (throatGaugeBaseChartTransitionSecondOrderJetAt period hPeriod
      targetCenter sourceCenter current hTarget hSource).secondDerivative_symmetric

@[simp]
theorem throatSmoothFieldConstantFiberBaseChangeAt_baseFirst
    (sourceCenter targetCenter current : EffectiveThroat period hPeriod)
    (hSource : current ∈
      (extChartAt throatCoverModelWithCorners sourceCenter).source)
    (hTarget : current ∈
      (extChartAt throatCoverModelWithCorners targetCenter).source) :
    (throatSmoothFieldConstantFiberBaseChangeAt period hPeriod sourceCenter
      targetCenter current hSource hTarget).baseFirst =
      fderiv Real
        (throatGaugeBaseChartTransition period hPeriod
          targetCenter sourceCenter)
        (extChartAt throatCoverModelWithCorners targetCenter current) :=
  rfl

@[simp]
theorem throatSmoothFieldConstantFiberBaseChangeAt_baseSecond
    (sourceCenter targetCenter current : EffectiveThroat period hPeriod)
    (hSource : current ∈
      (extChartAt throatCoverModelWithCorners sourceCenter).source)
    (hTarget : current ∈
      (extChartAt throatCoverModelWithCorners targetCenter).source) :
    (throatSmoothFieldConstantFiberBaseChangeAt period hPeriod sourceCenter
      targetCenter current hSource hTarget).baseSecond =
      fderiv Real
        (fderiv Real
          (throatGaugeBaseChartTransition period hPeriod
            targetCenter sourceCenter))
        (extChartAt throatCoverModelWithCorners targetCenter current) :=
  rfl

/-- Local equality of fixed-fiber representatives under a genuine base-chart
transition. -/
theorem throatSmoothFieldChartRepresentative_baseChartTransition_eventuallyEq
    (field : SmoothThroatField period hPeriod Fiber)
    (firstCenter secondCenter current : EffectiveThroat period hPeriod)
    (hFirst : current ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : current ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source) :
    throatSmoothFieldChartRepresentative period hPeriod field firstCenter
        =ᶠ[𝓝 (extChartAt throatCoverModelWithCorners firstCenter current)]
      throatSmoothFieldChartRepresentative period hPeriod field secondCenter ∘
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
  simp only [throatSmoothFieldChartRepresentative,
    throatGaugeBaseChartTransition, Function.comp_apply]
  rw [(extChartAt throatCoverModelWithCorners secondCenter).left_inv hCoordinate]

/-- On a double chart overlap, the target-chart jet is the constant-fiber
transport of the source-chart jet along the reverse base transition. -/
theorem throatSmoothFieldSecondOrderJetInChartAt_transition
    (field : SmoothThroatField period hPeriod Fiber)
    (sourceCenter targetCenter current : EffectiveThroat period hPeriod)
    (hSource : current ∈
      (extChartAt throatCoverModelWithCorners sourceCenter).source)
    (hTarget : current ∈
      (extChartAt throatCoverModelWithCorners targetCenter).source) :
    throatSmoothFieldSecondOrderJetInChartAt period hPeriod field
        targetCenter current hTarget =
      (throatSmoothFieldConstantFiberBaseChangeAt period hPeriod sourceCenter
        targetCenter current hSource hTarget).transport
        (throatSmoothFieldSecondOrderJetInChartAt period hPeriod field
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
  have hTransition : ContDiffAt Real 2 transition targetCoordinate := by
    simpa only [transition, targetCoordinate] using
      throatGaugeBaseChartTransition_contDiffAt_two period hPeriod
        targetCenter sourceCenter current hTarget hSource
  have hSourceRepresentative : ContDiffAt Real 2 sourceRepresentative
      sourceCoordinate := by
    simpa only [sourceRepresentative, sourceCoordinate] using
      throatSmoothFieldChartRepresentative_contDiffAt_two_of_mem_source
        period hPeriod field sourceCenter current hSource
  have hTransitionAt : transition targetCoordinate = sourceCoordinate := by
    simpa only [transition, targetCoordinate, sourceCoordinate] using
      throatGaugeBaseChartTransition_apply_current period hPeriod
        targetCenter sourceCenter current hTarget
  have hSourceRepresentativeAtTransition :
      ContDiffAt Real 2 sourceRepresentative
        (transition targetCoordinate) := by
    simpa only [hTransitionAt] using hSourceRepresentative
  have hGerm : targetRepresentative =ᶠ[𝓝 targetCoordinate]
      sourceRepresentative ∘ transition := by
    simpa only [targetRepresentative, sourceRepresentative, transition,
      targetCoordinate] using
      throatSmoothFieldChartRepresentative_baseChartTransition_eventuallyEq
        period hPeriod field targetCenter sourceCenter current hTarget hSource
  apply FramedSecondOrderJet.ext_components
  · simp
  · apply ContinuousLinearMap.ext
    intro direction
    simp only [
      throatSmoothFieldSecondOrderJetInChartAt_firstDerivative,
      FramedSecondOrderJetConstantFiberBaseChange.transport_firstDerivative_apply,
      throatSmoothFieldConstantFiberBaseChangeAt_baseFirst]
    rw [show fderiv Real targetRepresentative targetCoordinate =
        fderiv Real (sourceRepresentative ∘ transition) targetCoordinate from
      hGerm.fderiv_eq]
    rw [fderiv_comp targetCoordinate
      (by simpa only [hTransitionAt] using
        hSourceRepresentative.differentiableAt (by norm_num))
      (hTransition.differentiableAt (by norm_num)), hTransitionAt]
    rfl
  · apply ContinuousLinearMap.ext
    intro first
    apply ContinuousLinearMap.ext
    intro second
    simp only [
      throatSmoothFieldSecondOrderJetInChartAt_secondDerivative,
      throatSmoothFieldSecondOrderJetInChartAt_firstDerivative,
      FramedSecondOrderJetConstantFiberBaseChange.transport_secondDerivative_apply,
      throatSmoothFieldConstantFiberBaseChangeAt_baseFirst,
      throatSmoothFieldConstantFiberBaseChangeAt_baseSecond]
    have hSecondDerivative :
        fderiv Real (fderiv Real targetRepresentative) targetCoordinate =
          fderiv Real
            (fderiv Real (sourceRepresentative ∘ transition))
            targetCoordinate :=
      (hGerm.fderiv).fderiv_eq
    rw [show fderiv Real (fderiv Real targetRepresentative) targetCoordinate
          first second =
        fderiv Real (fderiv Real (sourceRepresentative ∘ transition))
          targetCoordinate first second by
      exact congrArg
        (fun derivative : ThroatCoverCoordinates →L[Real]
            ThroatCoverCoordinates →L[Real] Fiber ↦
          derivative first second) hSecondDerivative]
    rw [second_fderiv_comp_apply transition sourceRepresentative
      targetCoordinate hTransition hSourceRepresentativeAtTransition,
      hTransitionAt]

end
end P0EFTJanusProgramPActualThroatSmoothFieldSecondOrderJetOverlap4D
end JanusFormal
