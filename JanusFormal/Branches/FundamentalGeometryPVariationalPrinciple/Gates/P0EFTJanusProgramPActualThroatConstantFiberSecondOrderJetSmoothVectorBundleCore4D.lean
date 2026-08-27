import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionSecondOrderGroupoid4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeSecondOrderJetTransitionSmoothRegularity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFramedSecondOrderJetConstantFiberBaseChange4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFramedSecondOrderJetSemidirectTransportSmoothness4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFrameChartPairSecondJetVectorBundleCore4D

/-!
# Smooth constant-fiber second-jet bundle on the actual throat

The atlas is indexed only by the center of an extended throat chart.  Its
transition operators transport second jets into a fixed finite-dimensional
real fiber through the reverse second-order base-chart transition.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatConstantFiberSecondOrderJetSmoothVectorBundleCore4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 600000

noncomputable section

open Set
open scoped Manifold ContDiff RealInnerProductSpace Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionGerm4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionSecondOrderCocycle4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionSecondOrderGroupoid4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetTransitionSmoothRegularity4D
open P0EFTJanusProgramPFramedSecondOrderJetSemidirectTransport4D
open P0EFTJanusProgramPFramedSecondOrderJetSemidirectTransportSmoothness4D
open P0EFTJanusProgramPFramedSecondOrderJetConstantFiberBaseChange4D
open P0EFTJanusProgramPFrameChartPairSecondJetVectorBundleCore4D

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

/-- Chart centers index the constant-fiber second-jet atlas. -/
abbrev ActualThroatConstantFiberSecondOrderJetBundleIndex :=
  EffectiveThroat period hPeriod

/-- The model fiber of constant-fiber second jets. -/
abbrev ActualThroatConstantFiberSecondOrderJet
    (Fiber : Type*) [NormedAddCommGroup Fiber] [NormedSpace Real Fiber] :=
  FramedSecondOrderJet ThroatCoverCoordinates Fiber

/-- Domain of the extended chart centered at `index`. -/
def actualThroatConstantFiberSecondOrderJetBundleBaseSet
    (index : ActualThroatConstantFiberSecondOrderJetBundleIndex period hPeriod) :
    Set (EffectiveThroat period hPeriod) :=
  (extChartAt throatCoverModelWithCorners index).source

theorem actualThroatConstantFiberSecondOrderJetBundleBaseSet_isOpen
    (index : ActualThroatConstantFiberSecondOrderJetBundleIndex period hPeriod) :
    IsOpen (actualThroatConstantFiberSecondOrderJetBundleBaseSet
      period hPeriod index) :=
  isOpen_extChartAt_source index

/-- The chart centered at the current point covers that point. -/
def actualThroatConstantFiberSecondOrderJetBundleIndexAt
    (current : EffectiveThroat period hPeriod) :
    ActualThroatConstantFiberSecondOrderJetBundleIndex period hPeriod :=
  current

theorem mem_actualThroatConstantFiberSecondOrderJetBundleBaseSet_indexAt
    (current : EffectiveThroat period hPeriod) :
    current ∈ actualThroatConstantFiberSecondOrderJetBundleBaseSet
      period hPeriod
        (actualThroatConstantFiberSecondOrderJetBundleIndexAt
          period hPeriod current) :=
  mem_extChartAt_source current

private def bundleOverlap
    (first second :
      ActualThroatConstantFiberSecondOrderJetBundleIndex period hPeriod) :
    Set (EffectiveThroat period hPeriod) :=
  actualThroatConstantFiberSecondOrderJetBundleBaseSet period hPeriod first ∩
    actualThroatConstantFiberSecondOrderJetBundleBaseSet period hPeriod second

/-- Reverse base-chart coefficients acting on jets from `first` to `second`. -/
def actualThroatConstantFiberSecondOrderJetBaseChangeAt
    (first second current : EffectiveThroat period hPeriod)
    (hFirst : current ∈
      actualThroatConstantFiberSecondOrderJetBundleBaseSet
        period hPeriod first)
    (hSecond : current ∈
      actualThroatConstantFiberSecondOrderJetBundleBaseSet
        period hPeriod second) :
    FramedSecondOrderJetConstantFiberBaseChange ThroatCoverCoordinates where
  baseFirst :=
    (throatGaugeBaseChartTransitionSecondOrderJetAt period hPeriod
      second first current hSecond hFirst).firstDerivative
  baseSecond :=
    (throatGaugeBaseChartTransitionSecondOrderJetAt period hPeriod
      second first current hSecond hFirst).secondDerivative
  baseSecond_symmetric :=
    (throatGaugeBaseChartTransitionSecondOrderJetAt period hPeriod
      second first current hSecond hFirst).secondDerivative_symmetric

/-- Totalized transition operator; only its overlap branch enters the core. -/
def actualThroatConstantFiberSecondOrderJetCoordChange
    {Fiber : Type*}
    [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
    [FiniteDimensional Real Fiber]
    (first second : EffectiveThroat period hPeriod)
    (current : EffectiveThroat period hPeriod) :
    ActualThroatConstantFiberSecondOrderJet Fiber →L[Real]
      ActualThroatConstantFiberSecondOrderJet Fiber := by
  classical
  exact if hCurrent : current ∈ bundleOverlap period hPeriod first second then
      (actualThroatConstantFiberSecondOrderJetBaseChangeAt period hPeriod
        first second current hCurrent.1 hCurrent.2).toContinuousLinearMap
    else
      ContinuousLinearMap.id Real
        (ActualThroatConstantFiberSecondOrderJet Fiber)

@[simp]
theorem actualThroatConstantFiberSecondOrderJetCoordChange_apply_of_mem
    {Fiber : Type*}
    [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
    [FiniteDimensional Real Fiber]
    (first second current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈ bundleOverlap period hPeriod first second)
    (jet : ActualThroatConstantFiberSecondOrderJet Fiber) :
    actualThroatConstantFiberSecondOrderJetCoordChange
        period hPeriod (Fiber := Fiber) first second current jet =
      (actualThroatConstantFiberSecondOrderJetBaseChangeAt period hPeriod
        first second current hCurrent.1 hCurrent.2).transport jet := by
  simp only [actualThroatConstantFiberSecondOrderJetCoordChange,
    dif_pos hCurrent,
    FramedSecondOrderJetConstantFiberBaseChange.toContinuousLinearMap_apply]

@[simp]
theorem actualThroatConstantFiberSecondOrderJetCoordChange_self
    {Fiber : Type*}
    [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
    [FiniteDimensional Real Fiber]
    (index current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      actualThroatConstantFiberSecondOrderJetBundleBaseSet
        period hPeriod index) :
    actualThroatConstantFiberSecondOrderJetCoordChange
        period hPeriod (Fiber := Fiber) index index current =
      ContinuousLinearMap.id Real
        (ActualThroatConstantFiberSecondOrderJet Fiber) := by
  apply ContinuousLinearMap.ext
  intro jet
  rw [actualThroatConstantFiberSecondOrderJetCoordChange_apply_of_mem
    period hPeriod index index current ⟨hCurrent, hCurrent⟩]
  have hChart : current ∈
      (extChartAt throatCoverModelWithCorners index).source := by
    simpa only [actualThroatConstantFiberSecondOrderJetBundleBaseSet] using
      hCurrent
  have hBaseFirst :
      (actualThroatConstantFiberSecondOrderJetBaseChangeAt period hPeriod
        index index current hCurrent hCurrent).baseFirst =
        ContinuousLinearMap.id Real ThroatCoverCoordinates :=
    throatGaugeBaseChartTransitionSecondOrderJetAt_self_firstDerivative
      period hPeriod index current hChart
  have hBaseSecond :
      (actualThroatConstantFiberSecondOrderJetBaseChangeAt period hPeriod
        index index current hCurrent hCurrent).baseSecond = 0 :=
    throatGaugeBaseChartTransitionSecondOrderJetAt_self_secondDerivative
      period hPeriod index current hChart
  apply FramedSecondOrderJet.ext_components
  · simp only [
      FramedSecondOrderJetConstantFiberBaseChange.transport_value,
      ContinuousLinearMap.id_apply]
  · apply ContinuousLinearMap.ext
    intro direction
    simp only [
      FramedSecondOrderJetConstantFiberBaseChange.transport_firstDerivative_apply,
      ContinuousLinearMap.id_apply]
    rw [hBaseFirst]
    rfl
  · apply ContinuousLinearMap.ext
    intro firstDirection
    apply ContinuousLinearMap.ext
    intro secondDirection
    simp only [
      FramedSecondOrderJetConstantFiberBaseChange.transport_secondDerivative_apply,
      ContinuousLinearMap.id_apply]
    rw [hBaseFirst, hBaseSecond]
    simp

theorem actualThroatConstantFiberSecondOrderJetCoordChange_comp
    {Fiber : Type*}
    [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
    [FiniteDimensional Real Fiber]
    (first middle last current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      actualThroatConstantFiberSecondOrderJetBundleBaseSet
          period hPeriod first ∩
        actualThroatConstantFiberSecondOrderJetBundleBaseSet
          period hPeriod middle ∩
        actualThroatConstantFiberSecondOrderJetBundleBaseSet
          period hPeriod last) :
    (actualThroatConstantFiberSecondOrderJetCoordChange
      period hPeriod (Fiber := Fiber) middle last current).comp
        (actualThroatConstantFiberSecondOrderJetCoordChange
          period hPeriod (Fiber := Fiber) first middle current) =
      actualThroatConstantFiberSecondOrderJetCoordChange
        period hPeriod (Fiber := Fiber) first last current := by
  apply ContinuousLinearMap.ext
  intro jet
  simp only [ContinuousLinearMap.comp_apply]
  rw [actualThroatConstantFiberSecondOrderJetCoordChange_apply_of_mem
    period hPeriod first middle current ⟨hCurrent.1.1, hCurrent.1.2⟩]
  rw [actualThroatConstantFiberSecondOrderJetCoordChange_apply_of_mem
    period hPeriod middle last current ⟨hCurrent.1.2, hCurrent.2⟩]
  rw [actualThroatConstantFiberSecondOrderJetCoordChange_apply_of_mem
    period hPeriod first last current ⟨hCurrent.1.1, hCurrent.2⟩]
  let firstChange :=
    actualThroatConstantFiberSecondOrderJetBaseChangeAt period hPeriod
      first middle current hCurrent.1.1 hCurrent.1.2
  let secondChange :=
    actualThroatConstantFiberSecondOrderJetBaseChangeAt period hPeriod
      middle last current hCurrent.1.2 hCurrent.2
  let compositeChange :=
    actualThroatConstantFiberSecondOrderJetBaseChangeAt period hPeriod
      first last current hCurrent.1.1 hCurrent.2
  have hFirst : compositeChange.baseFirst =
      firstChange.baseFirst.comp secondChange.baseFirst := by
    simpa only [compositeChange, firstChange, secondChange,
      actualThroatConstantFiberSecondOrderJetBaseChangeAt] using
      (throatGaugeBaseChartTransitionSecondOrderJetAt_firstDerivative_cocycle
        period hPeriod last middle first current hCurrent.2
          hCurrent.1.2 hCurrent.1.1)
  have hSecond : ∀ firstDirection secondDirection,
      compositeChange.baseSecond firstDirection secondDirection =
        firstChange.baseSecond
            (secondChange.baseFirst firstDirection)
            (secondChange.baseFirst secondDirection) +
          firstChange.baseFirst
            (secondChange.baseSecond firstDirection secondDirection) := by
    intro firstDirection secondDirection
    simpa only [compositeChange, firstChange, secondChange,
      actualThroatConstantFiberSecondOrderJetBaseChangeAt] using
      (throatGaugeBaseChartTransitionSecondOrderJetAt_secondDerivative_cocycle_apply
        period hPeriod last middle first current hCurrent.2
          hCurrent.1.2 hCurrent.1.1 firstDirection secondDirection)
  exact
    (FramedSecondOrderJetConstantFiberBaseChange.transport_comp_of_base_coefficients
      firstChange secondChange compositeChange hFirst hSecond jet).symm

section SmoothCore

variable
    {Fiber : Type*}
    [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
    [FiniteDimensional Real Fiber]

private abbrev FiberEnd := Fiber →L[Real] Fiber

local instance fiberEndNormedAddCommGroup :
    NormedAddCommGroup (FiberEnd (Fiber := Fiber)) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance fiberEndNormedSpace :
    NormedSpace Real (FiberEnd (Fiber := Fiber)) :=
  ContinuousLinearMap.toNormedSpace

private abbrev FiberFirst :=
  ThroatCoverCoordinates →L[Real] FiberEnd (Fiber := Fiber)

local instance fiberFirstNormedAddCommGroup :
    NormedAddCommGroup (FiberFirst (Fiber := Fiber)) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance fiberFirstNormedSpace :
    NormedSpace Real (FiberFirst (Fiber := Fiber)) :=
  ContinuousLinearMap.toNormedSpace

/-- Globally defined coefficients used to prove overlap smoothness. -/
def actualThroatConstantFiberSecondOrderJetTotalChange
    (first second current : EffectiveThroat period hPeriod) :
    FramedSecondOrderJetSemidirectChange ThroatCoverCoordinates Fiber := by
  classical
  exact if hCurrent : current ∈ bundleOverlap period hPeriod first second then
      (actualThroatConstantFiberSecondOrderJetBaseChangeAt period hPeriod
        first second current hCurrent.1 hCurrent.2).toSemidirectChange
    else
      (FramedSecondOrderJetConstantFiberBaseChange.identity
        (Base := ThroatCoverCoordinates)).toSemidirectChange

private theorem baseFirst_contMDiffOn
    (first second : EffectiveThroat period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, ThroatCoverCoordinates →L[Real] ThroatCoverCoordinates) ∞
      (fun current : EffectiveThroat period hPeriod ↦
        fderiv Real
          (throatGaugeBaseChartTransition period hPeriod second first)
          (extChartAt throatCoverModelWithCorners second current))
      (bundleOverlap period hPeriod first second) := by
  intro current hCurrent
  have hChart : current ∈ (chartAt ThroatCoverModel second).source := by
    simpa only [actualThroatConstantFiberSecondOrderJetBundleBaseSet,
      extChartAt_source] using hCurrent.2
  exact
    ((throatGaugeBaseChartTransition_fderiv_contDiffAt_infty period hPeriod
      second first current hCurrent.2 hCurrent.1).contMDiffAt.comp current
        (contMDiffAt_extChartAt' hChart)).contMDiffWithinAt

private theorem baseSecond_contMDiffOn
    (first second : EffectiveThroat period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, ThroatCoverCoordinates →L[Real]
        ThroatCoverCoordinates →L[Real] ThroatCoverCoordinates) ∞
      (fun current : EffectiveThroat period hPeriod ↦
        fderiv Real
          (fderiv Real
            (throatGaugeBaseChartTransition period hPeriod second first))
          (extChartAt throatCoverModelWithCorners second current))
      (bundleOverlap period hPeriod first second) := by
  intro current hCurrent
  have hChart : current ∈ (chartAt ThroatCoverModel second).source := by
    simpa only [actualThroatConstantFiberSecondOrderJetBundleBaseSet,
      extChartAt_source] using hCurrent.2
  exact
    ((throatGaugeBaseChartTransition_secondFDeriv_contDiffAt_infty
      period hPeriod second first current hCurrent.2 hCurrent.1).contMDiffAt.comp
        current (contMDiffAt_extChartAt' hChart)).contMDiffWithinAt

private theorem totalChange_baseFirst_contMDiffOn
    (first second : EffectiveThroat period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, ThroatCoverCoordinates →L[Real] ThroatCoverCoordinates) ∞
      (fun current ↦
        (actualThroatConstantFiberSecondOrderJetTotalChange
          period hPeriod (Fiber := Fiber) first second current).baseFirst)
      (bundleOverlap period hPeriod first second) := by
  apply (baseFirst_contMDiffOn period hPeriod first second).congr
  intro current hCurrent
  rw [actualThroatConstantFiberSecondOrderJetTotalChange, dif_pos hCurrent]
  rfl

private theorem totalChange_baseSecond_contMDiffOn
    (first second : EffectiveThroat period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, ThroatCoverCoordinates →L[Real]
        ThroatCoverCoordinates →L[Real] ThroatCoverCoordinates) ∞
      (fun current ↦
        (actualThroatConstantFiberSecondOrderJetTotalChange
          period hPeriod (Fiber := Fiber) first second current).baseSecond)
      (bundleOverlap period hPeriod first second) := by
  apply (baseSecond_contMDiffOn period hPeriod first second).congr
  intro current hCurrent
  rw [actualThroatConstantFiberSecondOrderJetTotalChange, dif_pos hCurrent]
  rfl

private theorem totalChange_fiberValue_contMDiffOn
    (first second : EffectiveThroat period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, FiberEnd (Fiber := Fiber)) ∞
      (fun current ↦
        (actualThroatConstantFiberSecondOrderJetTotalChange
          period hPeriod (Fiber := Fiber) first second current).fiberValue)
      (bundleOverlap period hPeriod first second) := by
  apply (contMDiffOn_const : ContMDiffOn throatCoverModelWithCorners
    𝓘(Real, FiberEnd (Fiber := Fiber)) ∞
      (fun _ : EffectiveThroat period hPeriod ↦
        ContinuousLinearMap.id Real Fiber)
      (bundleOverlap period hPeriod first second)).congr
  intro current hCurrent
  rw [actualThroatConstantFiberSecondOrderJetTotalChange, dif_pos hCurrent]
  rfl

private theorem totalChange_fiberFirst_contMDiffOn
    (first second : EffectiveThroat period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, FiberFirst (Fiber := Fiber)) ∞
      (fun current ↦
        (actualThroatConstantFiberSecondOrderJetTotalChange
          period hPeriod (Fiber := Fiber) first second current).fiberFirst)
      (bundleOverlap period hPeriod first second) := by
  apply (contMDiffOn_const : ContMDiffOn throatCoverModelWithCorners
    𝓘(Real, FiberFirst (Fiber := Fiber)) ∞
      (fun _ : EffectiveThroat period hPeriod ↦
        (0 : FiberFirst (Fiber := Fiber)))
      (bundleOverlap period hPeriod first second)).congr
  intro current hCurrent
  rw [actualThroatConstantFiberSecondOrderJetTotalChange, dif_pos hCurrent]
  rfl

private theorem totalChange_fiberSecond_contMDiffOn
    (first second : EffectiveThroat period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, ThroatCoverCoordinates →L[Real]
        FiberFirst (Fiber := Fiber)) ∞
      (fun current ↦
        (actualThroatConstantFiberSecondOrderJetTotalChange
          period hPeriod (Fiber := Fiber) first second current).fiberSecond)
      (bundleOverlap period hPeriod first second) := by
  apply (contMDiffOn_const : ContMDiffOn throatCoverModelWithCorners
    𝓘(Real, ThroatCoverCoordinates →L[Real]
      FiberFirst (Fiber := Fiber)) ∞
      (fun _ : EffectiveThroat period hPeriod ↦
        (0 : ThroatCoverCoordinates →L[Real]
          FiberFirst (Fiber := Fiber)))
      (bundleOverlap period hPeriod first second)).congr
  intro current hCurrent
  rw [actualThroatConstantFiberSecondOrderJetTotalChange, dif_pos hCurrent]
  rfl

/-- Constant-fiber transition operators are smooth on every chart overlap. -/
theorem actualThroatConstantFiberSecondOrderJetCoordChange_contMDiffOn
    (first second : EffectiveThroat period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, ActualThroatConstantFiberSecondOrderJet Fiber →L[Real]
        ActualThroatConstantFiberSecondOrderJet Fiber) ∞
      (actualThroatConstantFiberSecondOrderJetCoordChange
        period hPeriod (Fiber := Fiber) first second)
      (actualThroatConstantFiberSecondOrderJetBundleBaseSet
          period hPeriod first ∩
        actualThroatConstantFiberSecondOrderJetBundleBaseSet
          period hPeriod second) := by
  have hTransport := contMDiffOn_semidirectTransport
    (actualThroatConstantFiberSecondOrderJetTotalChange
      period hPeriod (Fiber := Fiber) first second)
    (totalChange_baseFirst_contMDiffOn
      period hPeriod (Fiber := Fiber) first second)
    (totalChange_baseSecond_contMDiffOn
      period hPeriod (Fiber := Fiber) first second)
    (totalChange_fiberValue_contMDiffOn
      period hPeriod (Fiber := Fiber) first second)
    (totalChange_fiberFirst_contMDiffOn
      period hPeriod (Fiber := Fiber) first second)
    (totalChange_fiberSecond_contMDiffOn
      period hPeriod (Fiber := Fiber) first second)
  apply hTransport.congr
  intro current hCurrent
  rw [actualThroatConstantFiberSecondOrderJetCoordChange, dif_pos hCurrent]
  rw [actualThroatConstantFiberSecondOrderJetTotalChange, dif_pos hCurrent]
  rfl

/-- The constant-fiber second-jet vector-bundle core. -/
def actualThroatConstantFiberSecondOrderJetSmoothVectorBundleCore :
    VectorBundleCore Real (EffectiveThroat period hPeriod)
      (ActualThroatConstantFiberSecondOrderJet Fiber)
      (ActualThroatConstantFiberSecondOrderJetBundleIndex period hPeriod) :=
  frameChartPairSecondJetVectorBundleCore
    (actualThroatConstantFiberSecondOrderJetBundleBaseSet period hPeriod)
    (actualThroatConstantFiberSecondOrderJetBundleBaseSet_isOpen
      period hPeriod)
    (actualThroatConstantFiberSecondOrderJetBundleIndexAt period hPeriod)
    (mem_actualThroatConstantFiberSecondOrderJetBundleBaseSet_indexAt
      period hPeriod)
    (actualThroatConstantFiberSecondOrderJetCoordChange
      period hPeriod (Fiber := Fiber))
    (actualThroatConstantFiberSecondOrderJetCoordChange_self
      period hPeriod (Fiber := Fiber))
    (fun first second ↦
      (actualThroatConstantFiberSecondOrderJetCoordChange_contMDiffOn
        period hPeriod (Fiber := Fiber) first second).continuousOn)
    (actualThroatConstantFiberSecondOrderJetCoordChange_comp
      period hPeriod (Fiber := Fiber))

/-- The constructed core has `C∞` coordinate changes. -/
theorem actualThroatConstantFiberSecondOrderJetSmoothVectorBundleCore_isContMDiff :
    (actualThroatConstantFiberSecondOrderJetSmoothVectorBundleCore
      period hPeriod (Fiber := Fiber)).IsContMDiff
        throatCoverModelWithCorners ∞ := by
  exact frameChartPairSecondJetVectorBundleCore_isContMDiff
    throatCoverModelWithCorners ∞
    (actualThroatConstantFiberSecondOrderJetBundleBaseSet period hPeriod)
    (actualThroatConstantFiberSecondOrderJetBundleBaseSet_isOpen
      period hPeriod)
    (actualThroatConstantFiberSecondOrderJetBundleIndexAt period hPeriod)
    (mem_actualThroatConstantFiberSecondOrderJetBundleBaseSet_indexAt
      period hPeriod)
    (actualThroatConstantFiberSecondOrderJetCoordChange
      period hPeriod (Fiber := Fiber))
    (actualThroatConstantFiberSecondOrderJetCoordChange_self
      period hPeriod (Fiber := Fiber))
    (fun first second ↦
      (actualThroatConstantFiberSecondOrderJetCoordChange_contMDiffOn
        period hPeriod (Fiber := Fiber) first second).continuousOn)
    (actualThroatConstantFiberSecondOrderJetCoordChange_comp
      period hPeriod (Fiber := Fiber))
    (actualThroatConstantFiberSecondOrderJetCoordChange_contMDiffOn
      period hPeriod (Fiber := Fiber))

end SmoothCore

end
end P0EFTJanusProgramPActualThroatConstantFiberSecondOrderJetSmoothVectorBundleCore4D
end JanusFormal
