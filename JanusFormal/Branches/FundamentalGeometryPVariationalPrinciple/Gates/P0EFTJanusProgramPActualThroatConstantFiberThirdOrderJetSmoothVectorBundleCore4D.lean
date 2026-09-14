import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatConstantFiberThirdOrderJetCoordChange4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeThirdOrderJetTransitionSmoothRegularity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFramedThirdOrderJetSemidirectTransportSmoothness4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFrameChartPairSecondJetVectorBundleCore4D

/-!
# Smooth constant-fiber third-jet bundle on the actual throat

The existing algebraic third-order coordinate changes are continuous linear
and smooth on every overlap, hence define a smooth vector-bundle core.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatConstantFiberThirdOrderJetSmoothVectorBundleCore4D

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
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetTransitionSmoothRegularity4D
open P0EFTJanusProgramPActualThroatConstantFiberSecondOrderJetSmoothVectorBundleCore4D
open P0EFTJanusProgramPFramedSecondOrderJetConstantFiberBaseChange4D
open P0EFTJanusProgramPFramedThirdOrderJetConstantFiberBaseChange4D
open P0EFTJanusProgramPFramedThirdOrderJetSemidirectTransport4D
open P0EFTJanusProgramPActualThroatConstantFiberThirdOrderJetBaseChange4D
open P0EFTJanusProgramPActualThroatConstantFiberThirdOrderJetCoordChange4D
open P0EFTJanusProgramPActualThroatGaugeThirdOrderJetTransitionSmoothRegularity4D
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

/-- The third-order atlas uses the same chart-center index as order two. -/
abbrev ActualThroatConstantFiberThirdOrderJetBundleIndex :=
  ActualThroatConstantFiberSecondOrderJetBundleIndex period hPeriod

/-- The third-order atlas uses the extended-chart domains from order two. -/
abbrev actualThroatConstantFiberThirdOrderJetBundleBaseSet :=
  actualThroatConstantFiberSecondOrderJetBundleBaseSet period hPeriod

private def bundleOverlap
    (first second : EffectiveThroat period hPeriod) :
    Set (EffectiveThroat period hPeriod) :=
  actualThroatConstantFiberThirdOrderJetBundleBaseSet period hPeriod first ∩
    actualThroatConstantFiberThirdOrderJetBundleBaseSet period hPeriod second

section SmoothCore

variable
    {Fiber : Type*}
    [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
    [FiniteDimensional Real Fiber]

private abbrev BaseFirst :=
  ThroatCoverCoordinates →L[Real] ThroatCoverCoordinates

local instance baseFirstNormedAddCommGroup : NormedAddCommGroup BaseFirst :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance baseFirstNormedSpace : NormedSpace Real BaseFirst :=
  ContinuousLinearMap.toNormedSpace

private abbrev BaseSecond :=
  ThroatCoverCoordinates →L[Real] BaseFirst

local instance baseSecondNormedAddCommGroup : NormedAddCommGroup BaseSecond :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance baseSecondNormedSpace : NormedSpace Real BaseSecond :=
  ContinuousLinearMap.toNormedSpace

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

private abbrev FiberSecond :=
  ThroatCoverCoordinates →L[Real] FiberFirst (Fiber := Fiber)

local instance fiberSecondNormedAddCommGroup :
    NormedAddCommGroup (FiberSecond (Fiber := Fiber)) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance fiberSecondNormedSpace :
    NormedSpace Real (FiberSecond (Fiber := Fiber)) :=
  ContinuousLinearMap.toNormedSpace

private def constantFiberSemidirectChange
    (change : FramedThirdOrderJetConstantFiberBaseChange
      ThroatCoverCoordinates) :
    FramedThirdOrderJetSemidirectChange ThroatCoverCoordinates Fiber where
  toFramedSecondOrderJetSemidirectChange :=
    change.toFramedSecondOrderJetConstantFiberBaseChange.toSemidirectChange
  baseThird := change.baseThird
  baseThird_swap_first_second := change.baseThird_swap_first_second
  baseThird_swap_second_third := change.baseThird_swap_second_third
  fiberThird := 0
  fiberThird_swap_first_second := by simp
  fiberThird_swap_second_third := by simp

omit [FiniteDimensional Real Fiber] in
private theorem constantFiberSemidirectChange_transport
    (change : FramedThirdOrderJetConstantFiberBaseChange
      ThroatCoverCoordinates)
    (jet : ActualThroatConstantFiberThirdOrderJet Fiber) :
    (constantFiberSemidirectChange (Fiber := Fiber) change).transport jet =
      change.transport jet := by
  apply FramedThirdOrderJet.ext_components
  · rfl
  · apply ContinuousLinearMap.ext
    intro first
    apply ContinuousLinearMap.ext
    intro second
    apply ContinuousLinearMap.ext
    intro third
    rw [FramedThirdOrderJetSemidirectChange.transport_thirdDerivative_apply_expanded]
    simp [constantFiberSemidirectChange,
      FramedThirdOrderJetConstantFiberBaseChange.transport_thirdDerivative_apply]

/-- Continuous-linear packaging of the existing algebraic coordinate map. -/
def actualThroatConstantFiberThirdOrderJetContinuousCoordChange
    (first second current : EffectiveThroat period hPeriod) :
    ActualThroatConstantFiberThirdOrderJet Fiber →L[Real]
      ActualThroatConstantFiberThirdOrderJet Fiber :=
  LinearMap.toContinuousLinearMap
    (actualThroatConstantFiberThirdOrderJetCoordChange period hPeriod
      (Fiber := Fiber) first second current)

@[simp]
theorem actualThroatConstantFiberThirdOrderJetContinuousCoordChange_apply
    (first second current : EffectiveThroat period hPeriod)
    (jet : ActualThroatConstantFiberThirdOrderJet Fiber) :
    actualThroatConstantFiberThirdOrderJetContinuousCoordChange period hPeriod
        (Fiber := Fiber) first second current jet =
      actualThroatConstantFiberThirdOrderJetCoordChange period hPeriod
        (Fiber := Fiber) first second current jet :=
  rfl

@[simp]
theorem actualThroatConstantFiberThirdOrderJetContinuousCoordChange_self
    (index current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      actualThroatConstantFiberThirdOrderJetBundleBaseSet
        period hPeriod index) :
    actualThroatConstantFiberThirdOrderJetContinuousCoordChange period hPeriod
        (Fiber := Fiber) index index current =
      ContinuousLinearMap.id Real
        (ActualThroatConstantFiberThirdOrderJet Fiber) := by
  apply ContinuousLinearMap.ext
  intro jet
  change
    actualThroatConstantFiberThirdOrderJetCoordChange period hPeriod
        (Fiber := Fiber) index index current jet = jet
  rw [actualThroatConstantFiberThirdOrderJetCoordChange_self
    period hPeriod index current hCurrent]
  rfl

theorem actualThroatConstantFiberThirdOrderJetContinuousCoordChange_comp
    (first middle last current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      actualThroatConstantFiberThirdOrderJetBundleBaseSet
          period hPeriod first ∩
        actualThroatConstantFiberThirdOrderJetBundleBaseSet
          period hPeriod middle ∩
        actualThroatConstantFiberThirdOrderJetBundleBaseSet
          period hPeriod last) :
    (actualThroatConstantFiberThirdOrderJetContinuousCoordChange period hPeriod
      (Fiber := Fiber) middle last current).comp
        (actualThroatConstantFiberThirdOrderJetContinuousCoordChange
          period hPeriod (Fiber := Fiber) first middle current) =
      actualThroatConstantFiberThirdOrderJetContinuousCoordChange period hPeriod
        (Fiber := Fiber) first last current := by
  apply ContinuousLinearMap.ext
  intro jet
  change
    actualThroatConstantFiberThirdOrderJetCoordChange period hPeriod
        (Fiber := Fiber) middle last current
          (actualThroatConstantFiberThirdOrderJetCoordChange period hPeriod
            (Fiber := Fiber) first middle current jet) =
      actualThroatConstantFiberThirdOrderJetCoordChange period hPeriod
        (Fiber := Fiber) first last current jet
  have hComp := congrArg (fun change ↦ change jet)
    (actualThroatConstantFiberThirdOrderJetCoordChange_comp period hPeriod
      (Fiber := Fiber) first middle last current hCurrent)
  simpa only [LinearMap.comp_apply] using hComp

/-- Totalized coefficients used only for overlap smoothness. -/
def actualThroatConstantFiberThirdOrderJetTotalChange
    (first second current : EffectiveThroat period hPeriod) :
    FramedThirdOrderJetSemidirectChange ThroatCoverCoordinates Fiber := by
  classical
  exact if hCurrent : current ∈ bundleOverlap period hPeriod first second then
      constantFiberSemidirectChange (Fiber := Fiber)
        (actualThroatConstantFiberThirdOrderJetBaseChangeAt period hPeriod
          first second current hCurrent.1 hCurrent.2)
    else
      constantFiberSemidirectChange (Fiber := Fiber)
        (FramedThirdOrderJetConstantFiberBaseChange.identity
          (Base := ThroatCoverCoordinates))

private theorem baseFirst_contMDiffOn
    (first second : EffectiveThroat period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners 𝓘(Real, BaseFirst) ∞
      (fun current : EffectiveThroat period hPeriod ↦
        fderiv Real
          (throatGaugeBaseChartTransition period hPeriod second first)
          (extChartAt throatCoverModelWithCorners second current))
      (bundleOverlap period hPeriod first second) := by
  intro current hCurrent
  have hChart : current ∈ (chartAt ThroatCoverModel second).source := by
    simpa only [actualThroatConstantFiberThirdOrderJetBundleBaseSet,
      actualThroatConstantFiberSecondOrderJetBundleBaseSet,
      extChartAt_source] using hCurrent.2
  exact
    ((throatGaugeBaseChartTransition_fderiv_contDiffAt_infty period hPeriod
      second first current hCurrent.2 hCurrent.1).contMDiffAt.comp current
        (contMDiffAt_extChartAt' hChart)).contMDiffWithinAt

private theorem baseSecond_contMDiffOn
    (first second : EffectiveThroat period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners 𝓘(Real, BaseSecond) ∞
      (fun current : EffectiveThroat period hPeriod ↦
        fderiv Real
          (fderiv Real
            (throatGaugeBaseChartTransition period hPeriod second first))
          (extChartAt throatCoverModelWithCorners second current))
      (bundleOverlap period hPeriod first second) := by
  intro current hCurrent
  have hChart : current ∈ (chartAt ThroatCoverModel second).source := by
    simpa only [actualThroatConstantFiberThirdOrderJetBundleBaseSet,
      actualThroatConstantFiberSecondOrderJetBundleBaseSet,
      extChartAt_source] using hCurrent.2
  exact
    ((throatGaugeBaseChartTransition_secondFDeriv_contDiffAt_infty
      period hPeriod second first current hCurrent.2 hCurrent.1).contMDiffAt.comp
        current (contMDiffAt_extChartAt' hChart)).contMDiffWithinAt

private theorem baseThird_contMDiffOn
    (first second : EffectiveThroat period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, ThroatCoverCoordinates →L[Real] BaseSecond) ∞
      (fun current : EffectiveThroat period hPeriod ↦
        fderiv Real
          (fderiv Real
            (fderiv Real
              (throatGaugeBaseChartTransition period hPeriod second first)))
          (extChartAt throatCoverModelWithCorners second current))
      (bundleOverlap period hPeriod first second) := by
  intro current hCurrent
  have hChart : current ∈ (chartAt ThroatCoverModel second).source := by
    simpa only [actualThroatConstantFiberThirdOrderJetBundleBaseSet,
      actualThroatConstantFiberSecondOrderJetBundleBaseSet,
      extChartAt_source] using hCurrent.2
  exact
    ((throatGaugeBaseChartTransition_thirdFDeriv_contDiffAt_infty
      period hPeriod second first current hCurrent.2 hCurrent.1).contMDiffAt.comp
        current (contMDiffAt_extChartAt' hChart)).contMDiffWithinAt

omit [FiniteDimensional Real Fiber] in
private theorem totalChange_baseFirst_contMDiffOn
    (first second : EffectiveThroat period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners 𝓘(Real, BaseFirst) ∞
      (fun current ↦ (actualThroatConstantFiberThirdOrderJetTotalChange
        period hPeriod (Fiber := Fiber) first second current).baseFirst)
      (bundleOverlap period hPeriod first second) := by
  apply (baseFirst_contMDiffOn period hPeriod first second).congr
  intro current hCurrent
  rw [actualThroatConstantFiberThirdOrderJetTotalChange, dif_pos hCurrent]
  rfl

omit [FiniteDimensional Real Fiber] in
private theorem totalChange_baseSecond_contMDiffOn
    (first second : EffectiveThroat period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners 𝓘(Real, BaseSecond) ∞
      (fun current ↦ (actualThroatConstantFiberThirdOrderJetTotalChange
        period hPeriod (Fiber := Fiber) first second current).baseSecond)
      (bundleOverlap period hPeriod first second) := by
  apply (baseSecond_contMDiffOn period hPeriod first second).congr
  intro current hCurrent
  rw [actualThroatConstantFiberThirdOrderJetTotalChange, dif_pos hCurrent]
  rfl

omit [FiniteDimensional Real Fiber] in
private theorem totalChange_baseThird_contMDiffOn
    (first second : EffectiveThroat period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, ThroatCoverCoordinates →L[Real] BaseSecond) ∞
      (fun current ↦ (actualThroatConstantFiberThirdOrderJetTotalChange
        period hPeriod (Fiber := Fiber) first second current).baseThird)
      (bundleOverlap period hPeriod first second) := by
  apply (baseThird_contMDiffOn period hPeriod first second).congr
  intro current hCurrent
  rw [actualThroatConstantFiberThirdOrderJetTotalChange, dif_pos hCurrent]
  rfl

omit [FiniteDimensional Real Fiber] in
private theorem totalChange_fiberValue_contMDiffOn
    (first second : EffectiveThroat period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners 𝓘(Real, FiberEnd (Fiber := Fiber)) ∞
      (fun current ↦ (actualThroatConstantFiberThirdOrderJetTotalChange
        period hPeriod (Fiber := Fiber) first second current).fiberValue)
      (bundleOverlap period hPeriod first second) := by
  apply (contMDiffOn_const : ContMDiffOn throatCoverModelWithCorners
    𝓘(Real, FiberEnd (Fiber := Fiber)) ∞
      (fun _ : EffectiveThroat period hPeriod ↦
        ContinuousLinearMap.id Real Fiber)
      (bundleOverlap period hPeriod first second)).congr
  intro current hCurrent
  rw [actualThroatConstantFiberThirdOrderJetTotalChange, dif_pos hCurrent]
  rfl

omit [FiniteDimensional Real Fiber] in
private theorem totalChange_fiberFirst_contMDiffOn
    (first second : EffectiveThroat period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners 𝓘(Real, FiberFirst (Fiber := Fiber)) ∞
      (fun current ↦ (actualThroatConstantFiberThirdOrderJetTotalChange
        period hPeriod (Fiber := Fiber) first second current).fiberFirst)
      (bundleOverlap period hPeriod first second) := by
  apply (contMDiffOn_const : ContMDiffOn throatCoverModelWithCorners
    𝓘(Real, FiberFirst (Fiber := Fiber)) ∞
      (fun _ : EffectiveThroat period hPeriod ↦ (0 : FiberFirst (Fiber := Fiber)))
      (bundleOverlap period hPeriod first second)).congr
  intro current hCurrent
  rw [actualThroatConstantFiberThirdOrderJetTotalChange, dif_pos hCurrent]
  rfl

omit [FiniteDimensional Real Fiber] in
private theorem totalChange_fiberSecond_contMDiffOn
    (first second : EffectiveThroat period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners 𝓘(Real, FiberSecond (Fiber := Fiber)) ∞
      (fun current ↦ (actualThroatConstantFiberThirdOrderJetTotalChange
        period hPeriod (Fiber := Fiber) first second current).fiberSecond)
      (bundleOverlap period hPeriod first second) := by
  apply (contMDiffOn_const : ContMDiffOn throatCoverModelWithCorners
    𝓘(Real, FiberSecond (Fiber := Fiber)) ∞
      (fun _ : EffectiveThroat period hPeriod ↦ (0 : FiberSecond (Fiber := Fiber)))
      (bundleOverlap period hPeriod first second)).congr
  intro current hCurrent
  rw [actualThroatConstantFiberThirdOrderJetTotalChange, dif_pos hCurrent]
  rfl

omit [FiniteDimensional Real Fiber] in
private theorem totalChange_fiberThird_contMDiffOn
    (first second : EffectiveThroat period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, ThroatCoverCoordinates →L[Real] FiberSecond (Fiber := Fiber)) ∞
      (fun current ↦ (actualThroatConstantFiberThirdOrderJetTotalChange
        period hPeriod (Fiber := Fiber) first second current).fiberThird)
      (bundleOverlap period hPeriod first second) := by
  apply (contMDiffOn_const : ContMDiffOn throatCoverModelWithCorners
    𝓘(Real, ThroatCoverCoordinates →L[Real] FiberSecond (Fiber := Fiber)) ∞
      (fun _ : EffectiveThroat period hPeriod ↦
        (0 : ThroatCoverCoordinates →L[Real] FiberSecond (Fiber := Fiber)))
      (bundleOverlap period hPeriod first second)).congr
  intro current hCurrent
  rw [actualThroatConstantFiberThirdOrderJetTotalChange, dif_pos hCurrent]
  rfl

/-- Constant-fiber third-order coordinate changes are smooth on overlaps. -/
theorem actualThroatConstantFiberThirdOrderJetContinuousCoordChange_contMDiffOn
    (first second : EffectiveThroat period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, ActualThroatConstantFiberThirdOrderJet Fiber →L[Real]
        ActualThroatConstantFiberThirdOrderJet Fiber) ∞
      (actualThroatConstantFiberThirdOrderJetContinuousCoordChange
        period hPeriod (Fiber := Fiber) first second)
      (bundleOverlap period hPeriod first second) := by
  have hTransport :=
    P0EFTJanusProgramPFramedThirdOrderJetSemidirectTransportSmoothness4D.contMDiffOn_semidirectTransport
      (actualThroatConstantFiberThirdOrderJetTotalChange
        period hPeriod (Fiber := Fiber) first second)
      (totalChange_baseFirst_contMDiffOn
        period hPeriod (Fiber := Fiber) first second)
      (totalChange_baseSecond_contMDiffOn
        period hPeriod (Fiber := Fiber) first second)
      (totalChange_baseThird_contMDiffOn
        period hPeriod (Fiber := Fiber) first second)
      (totalChange_fiberValue_contMDiffOn
        period hPeriod (Fiber := Fiber) first second)
      (totalChange_fiberFirst_contMDiffOn
        period hPeriod (Fiber := Fiber) first second)
      (totalChange_fiberSecond_contMDiffOn
        period hPeriod (Fiber := Fiber) first second)
      (totalChange_fiberThird_contMDiffOn
        period hPeriod (Fiber := Fiber) first second)
  apply hTransport.congr
  intro current hCurrent
  apply ContinuousLinearMap.ext
  intro jet
  rw [actualThroatConstantFiberThirdOrderJetTotalChange, dif_pos hCurrent]
  rw [actualThroatConstantFiberThirdOrderJetContinuousCoordChange_apply]
  rw [actualThroatConstantFiberThirdOrderJetCoordChange_apply_of_mem
    period hPeriod first second current hCurrent]
  simpa only [FramedThirdOrderJetSemidirectChange.toContinuousLinearMap_apply]
    using (constantFiberSemidirectChange_transport (Fiber := Fiber)
      (actualThroatConstantFiberThirdOrderJetBaseChangeAt period hPeriod
        first second current hCurrent.1 hCurrent.2) jet).symm

/-- Smooth vector-bundle core of actual constant-fiber third jets. -/
def actualThroatConstantFiberThirdOrderJetSmoothVectorBundleCore :
    VectorBundleCore Real (EffectiveThroat period hPeriod)
      (ActualThroatConstantFiberThirdOrderJet Fiber)
      (ActualThroatConstantFiberThirdOrderJetBundleIndex period hPeriod) :=
  frameChartPairSecondJetVectorBundleCore
    (actualThroatConstantFiberThirdOrderJetBundleBaseSet period hPeriod)
    (actualThroatConstantFiberSecondOrderJetBundleBaseSet_isOpen
      period hPeriod)
    (actualThroatConstantFiberSecondOrderJetBundleIndexAt period hPeriod)
    (mem_actualThroatConstantFiberSecondOrderJetBundleBaseSet_indexAt
      period hPeriod)
    (actualThroatConstantFiberThirdOrderJetContinuousCoordChange
      period hPeriod (Fiber := Fiber))
    (actualThroatConstantFiberThirdOrderJetContinuousCoordChange_self
      period hPeriod (Fiber := Fiber))
    (fun first second ↦
      (actualThroatConstantFiberThirdOrderJetContinuousCoordChange_contMDiffOn
        period hPeriod (Fiber := Fiber) first second).continuousOn)
    (actualThroatConstantFiberThirdOrderJetContinuousCoordChange_comp
      period hPeriod (Fiber := Fiber))

/-- The constructed third-jet core has smooth coordinate changes. -/
theorem actualThroatConstantFiberThirdOrderJetSmoothVectorBundleCore_isContMDiff :
    (actualThroatConstantFiberThirdOrderJetSmoothVectorBundleCore
      period hPeriod (Fiber := Fiber)).IsContMDiff
        throatCoverModelWithCorners ∞ := by
  exact frameChartPairSecondJetVectorBundleCore_isContMDiff
    throatCoverModelWithCorners ∞
    (actualThroatConstantFiberThirdOrderJetBundleBaseSet period hPeriod)
    (actualThroatConstantFiberSecondOrderJetBundleBaseSet_isOpen
      period hPeriod)
    (actualThroatConstantFiberSecondOrderJetBundleIndexAt period hPeriod)
    (mem_actualThroatConstantFiberSecondOrderJetBundleBaseSet_indexAt
      period hPeriod)
    (actualThroatConstantFiberThirdOrderJetContinuousCoordChange
      period hPeriod (Fiber := Fiber))
    (actualThroatConstantFiberThirdOrderJetContinuousCoordChange_self
      period hPeriod (Fiber := Fiber))
    (fun first second ↦
      (actualThroatConstantFiberThirdOrderJetContinuousCoordChange_contMDiffOn
        period hPeriod (Fiber := Fiber) first second).continuousOn)
    (actualThroatConstantFiberThirdOrderJetContinuousCoordChange_comp
      period hPeriod (Fiber := Fiber))
    (actualThroatConstantFiberThirdOrderJetContinuousCoordChange_contMDiffOn
      period hPeriod (Fiber := Fiber))

end SmoothCore

end
end P0EFTJanusProgramPActualThroatConstantFiberThirdOrderJetSmoothVectorBundleCore4D
end JanusFormal
