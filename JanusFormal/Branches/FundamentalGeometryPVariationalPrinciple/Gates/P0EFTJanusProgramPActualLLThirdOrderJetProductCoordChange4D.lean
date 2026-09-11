import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualLLSecondOrderJetProductVectorBundleCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatConstantFiberThirdOrderJetBaseChange4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatBaseChartTransitionThirdOrderCocycle4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFramedThirdOrderJetLinearStructure4D

/-!
# Actual LL third-order jet product coordinate changes

The three LL slots have globally fixed fibers.  The actual reverse throat
base-chart transition therefore acts through the constant-fiber third-order
chain rule, with no nonzero fiber-transition derivative.  These transports
are assembled componentwise for the auxiliary metric, measure and LL field,
and truncate exactly to the existing LL second-jet product core.

This gate supplies an algebraic `LinearMap` groupoid on the existing overlap
domains.  It does not assert continuity, a normed third-jet model fiber, a
third-order `VectorBundleCore`, or third-jet extraction of the LL sections.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualLLThirdOrderJetProductCoordChange4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 600000

noncomputable section

open Set
open scoped Manifold ContDiff RealInnerProductSpace Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPFramedSecondOrderJetConstantFiberBaseChange4D
open P0EFTJanusProgramPFramedThirdOrderJetConstantFiberBaseChange4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionSecondOrderCocycle4D
open P0EFTJanusProgramPActualThroatConstantFiberSecondOrderJetSmoothVectorBundleCore4D
open P0EFTJanusProgramPActualThroatConstantFiberThirdOrderJetBaseChange4D
open P0EFTJanusProgramPActualThroatBaseChartTransitionThirdOrderCocycle4D
open P0EFTJanusProgramPActualLLSecondOrderJetProductVectorBundleCore4D
open P0EFTJanusPhysicalSecondJetProductVectorBundleCore

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

section ConstantFiberLinearMap

variable
    {Base Fiber : Type*}
    [NormedAddCommGroup Base] [NormedSpace Real Base]
    [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]

/-- Constant-fiber third-order transport as a real-linear map of jets. -/
def framedThirdOrderJetConstantFiberBaseChangeLinearMap
    [FiniteDimensional Real Base]
    (change : FramedThirdOrderJetConstantFiberBaseChange Base) :
    FramedThirdOrderJet Base Fiber →ₗ[Real]
      FramedThirdOrderJet Base Fiber where
  toFun := change.transport
  map_add' left right := by
    apply FramedThirdOrderJet.ext_components
    · simpa only [
        FramedThirdOrderJetConstantFiberBaseChange.transport_toFramedSecondOrderJet,
        FramedThirdOrderJet.add_toFramedSecondOrderJet,
        FramedSecondOrderJetConstantFiberBaseChange.toLinearMap_apply] using
        change.toFramedSecondOrderJetConstantFiberBaseChange.toLinearMap.map_add
          left.toFramedSecondOrderJet right.toFramedSecondOrderJet
    · ext first second third
      simp only [
        FramedThirdOrderJetConstantFiberBaseChange.transport_thirdDerivative_apply,
        FramedThirdOrderJet.add_firstDerivative,
        FramedThirdOrderJet.add_secondDerivative,
        FramedThirdOrderJet.add_thirdDerivative,
        add_apply]
      abel
  map_smul' scalar jet := by
    apply FramedThirdOrderJet.ext_components
    · simpa only [
        FramedThirdOrderJetConstantFiberBaseChange.transport_toFramedSecondOrderJet,
        FramedThirdOrderJet.smul_toFramedSecondOrderJet,
        FramedSecondOrderJetConstantFiberBaseChange.toLinearMap_apply,
        RingHom.id_apply] using
        change.toFramedSecondOrderJetConstantFiberBaseChange.toLinearMap.map_smul
          scalar jet.toFramedSecondOrderJet
    · ext first second third
      simp only [
        FramedThirdOrderJetConstantFiberBaseChange.transport_thirdDerivative_apply,
        FramedThirdOrderJet.smul_firstDerivative,
        FramedThirdOrderJet.smul_secondDerivative,
        FramedThirdOrderJet.smul_thirdDerivative,
        smul_apply, RingHom.id_apply]
      module

@[simp]
theorem framedThirdOrderJetConstantFiberBaseChangeLinearMap_apply
    [FiniteDimensional Real Base]
    (change : FramedThirdOrderJetConstantFiberBaseChange Base)
    (jet : FramedThirdOrderJet Base Fiber) :
    framedThirdOrderJetConstantFiberBaseChangeLinearMap change jet =
      change.transport jet :=
  rfl

end ConstantFiberLinearMap

/-- Linear truncation from a framed third jet to its framed second jet. -/
def framedThirdOrderJetTruncateLinearMap
    {Base Fiber : Type*}
    [NormedAddCommGroup Base] [NormedSpace Real Base]
    [NormedAddCommGroup Fiber] [NormedSpace Real Fiber] :
    FramedThirdOrderJet Base Fiber →ₗ[Real]
      FramedSecondOrderJet Base Fiber where
  toFun := FramedThirdOrderJet.toFramedSecondOrderJet
  map_add' first second :=
    FramedThirdOrderJet.add_toFramedSecondOrderJet Base Fiber first second
  map_smul' scalar jet := by
    simpa only [RingHom.id_apply] using
      FramedThirdOrderJet.smul_toFramedSecondOrderJet Base Fiber scalar jet

/-- The model fiber of actual constant-fiber third jets. -/
abbrev ActualThroatConstantFiberThirdOrderJet
    (Fiber : Type*) [NormedAddCommGroup Fiber] [NormedSpace Real Fiber] :=
  FramedThirdOrderJet ThroatCoverCoordinates Fiber

/-- The actual third-order reverse-base transport on a double overlap. -/
def actualThroatConstantFiberThirdOrderJetTransportLinearMapAt
    {Fiber : Type*}
    [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
    (first second current : EffectiveThroat period hPeriod)
    (hFirst : current ∈
      actualThroatConstantFiberSecondOrderJetBundleBaseSet
        period hPeriod first)
    (hSecond : current ∈
      actualThroatConstantFiberSecondOrderJetBundleBaseSet
        period hPeriod second) :
    ActualThroatConstantFiberThirdOrderJet Fiber →ₗ[Real]
      ActualThroatConstantFiberThirdOrderJet Fiber :=
  framedThirdOrderJetConstantFiberBaseChangeLinearMap
    (actualThroatConstantFiberThirdOrderJetBaseChangeAt period hPeriod
      first second current hFirst hSecond)

@[simp]
theorem actualThroatConstantFiberThirdOrderJetTransportLinearMapAt_apply
    {Fiber : Type*}
    [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
    (first second current : EffectiveThroat period hPeriod)
    (hFirst : current ∈
      actualThroatConstantFiberSecondOrderJetBundleBaseSet
        period hPeriod first)
    (hSecond : current ∈
      actualThroatConstantFiberSecondOrderJetBundleBaseSet
        period hPeriod second)
    (jet : ActualThroatConstantFiberThirdOrderJet Fiber) :
    actualThroatConstantFiberThirdOrderJetTransportLinearMapAt
        period hPeriod first second current hFirst hSecond jet =
      (actualThroatConstantFiberThirdOrderJetBaseChangeAt period hPeriod
        first second current hFirst hSecond).transport jet :=
  rfl

/-- The actual constant-fiber third-order transports compose on a triple
overlap. -/
theorem actualThroatConstantFiberThirdOrderJetBaseChangeAt_transport_comp
    {Fiber : Type*}
    [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
    (first middle last current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      actualThroatConstantFiberSecondOrderJetBundleBaseSet
          period hPeriod first ∩
        actualThroatConstantFiberSecondOrderJetBundleBaseSet
          period hPeriod middle ∩
        actualThroatConstantFiberSecondOrderJetBundleBaseSet
          period hPeriod last)
    (jet : ActualThroatConstantFiberThirdOrderJet Fiber) :
    (actualThroatConstantFiberThirdOrderJetBaseChangeAt period hPeriod
      middle last current hCurrent.1.2 hCurrent.2).transport
        ((actualThroatConstantFiberThirdOrderJetBaseChangeAt period hPeriod
          first middle current hCurrent.1.1 hCurrent.1.2).transport jet) =
      (actualThroatConstantFiberThirdOrderJetBaseChangeAt period hPeriod
        first last current hCurrent.1.1 hCurrent.2).transport jet := by
  let firstChange :=
    actualThroatConstantFiberThirdOrderJetBaseChangeAt period hPeriod
      first middle current hCurrent.1.1 hCurrent.1.2
  let secondChange :=
    actualThroatConstantFiberThirdOrderJetBaseChangeAt period hPeriod
      middle last current hCurrent.1.2 hCurrent.2
  let compositeChange :=
    actualThroatConstantFiberThirdOrderJetBaseChangeAt period hPeriod
      first last current hCurrent.1.1 hCurrent.2
  have hFirst : compositeChange.baseFirst =
      firstChange.baseFirst.comp secondChange.baseFirst := by
    simpa only [compositeChange, firstChange, secondChange,
      actualThroatConstantFiberThirdOrderJetBaseChangeAt,
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
      actualThroatConstantFiberThirdOrderJetBaseChangeAt,
      actualThroatConstantFiberSecondOrderJetBaseChangeAt] using
      (throatGaugeBaseChartTransitionSecondOrderJetAt_secondDerivative_cocycle_apply
        period hPeriod last middle first current hCurrent.2
          hCurrent.1.2 hCurrent.1.1 firstDirection secondDirection)
  have hFirstChart : current ∈
      (extChartAt throatCoverModelWithCorners first).source := by
    simpa only [actualThroatConstantFiberSecondOrderJetBundleBaseSet] using
      hCurrent.1.1
  have hMiddleChart : current ∈
      (extChartAt throatCoverModelWithCorners middle).source := by
    simpa only [actualThroatConstantFiberSecondOrderJetBundleBaseSet] using
      hCurrent.1.2
  have hLastChart : current ∈
      (extChartAt throatCoverModelWithCorners last).source := by
    simpa only [actualThroatConstantFiberSecondOrderJetBundleBaseSet] using
      hCurrent.2
  have hThird : ∀ firstDirection secondDirection thirdDirection,
      compositeChange.baseThird
          firstDirection secondDirection thirdDirection =
        firstChange.baseThird
            (secondChange.baseFirst firstDirection)
            (secondChange.baseFirst secondDirection)
            (secondChange.baseFirst thirdDirection) +
          firstChange.baseSecond
            (secondChange.baseSecond firstDirection secondDirection)
            (secondChange.baseFirst thirdDirection) +
          firstChange.baseSecond
            (secondChange.baseSecond firstDirection thirdDirection)
            (secondChange.baseFirst secondDirection) +
          firstChange.baseSecond
            (secondChange.baseSecond secondDirection thirdDirection)
            (secondChange.baseFirst firstDirection) +
          firstChange.baseFirst
            (secondChange.baseThird
              firstDirection secondDirection thirdDirection) := by
    intro firstDirection secondDirection thirdDirection
    dsimp only [compositeChange, firstChange, secondChange]
    simp only [
      actualThroatConstantFiberThirdOrderJetBaseChangeAt_baseThird_apply]
    simpa only [
      actualThroatConstantFiberThirdOrderJetBaseChangeAt,
      actualThroatConstantFiberSecondOrderJetBaseChangeAt,
      throatGaugeBaseChartTransitionSecondOrderJetAt_firstDerivative,
      throatGaugeBaseChartTransitionSecondOrderJetAt_secondDerivative] using
      (throatGaugeBaseChartTransitionThirdDerivativeAt_cocycle period hPeriod
        last middle first current hLastChart hMiddleChart hFirstChart
          firstDirection secondDirection thirdDirection)
  exact
    (FramedThirdOrderJetConstantFiberBaseChange.transport_comp_of_base_coefficients
      firstChange secondChange compositeChange hFirst hSecond hThird jet).symm

/-- Totalized algebraic coordinate change.  Only its overlap branch is used
by the groupoid laws. -/
def actualThroatConstantFiberThirdOrderJetCoordChange
    {Fiber : Type*}
    [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
    (first second current : EffectiveThroat period hPeriod) :
    ActualThroatConstantFiberThirdOrderJet Fiber →ₗ[Real]
      ActualThroatConstantFiberThirdOrderJet Fiber := by
  classical
  exact if hCurrent : current ∈
        actualThroatConstantFiberSecondOrderJetBundleBaseSet
            period hPeriod first ∩
          actualThroatConstantFiberSecondOrderJetBundleBaseSet
            period hPeriod second then
      actualThroatConstantFiberThirdOrderJetTransportLinearMapAt
        period hPeriod first second current hCurrent.1 hCurrent.2
    else
      LinearMap.id

@[simp]
theorem actualThroatConstantFiberThirdOrderJetCoordChange_apply_of_mem
    {Fiber : Type*}
    [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
    (first second current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      actualThroatConstantFiberSecondOrderJetBundleBaseSet
          period hPeriod first ∩
        actualThroatConstantFiberSecondOrderJetBundleBaseSet
          period hPeriod second)
    (jet : ActualThroatConstantFiberThirdOrderJet Fiber) :
    actualThroatConstantFiberThirdOrderJetCoordChange period hPeriod
        first second current jet =
      (actualThroatConstantFiberThirdOrderJetBaseChangeAt period hPeriod
        first second current hCurrent.1 hCurrent.2).transport jet := by
  simp only [actualThroatConstantFiberThirdOrderJetCoordChange,
    dif_pos hCurrent,
    actualThroatConstantFiberThirdOrderJetTransportLinearMapAt_apply]

@[simp]
theorem actualThroatConstantFiberThirdOrderJetCoordChange_self
    {Fiber : Type*}
    [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
    (index current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      actualThroatConstantFiberSecondOrderJetBundleBaseSet
        period hPeriod index) :
    actualThroatConstantFiberThirdOrderJetCoordChange period hPeriod
        (Fiber := Fiber) index index current =
      LinearMap.id := by
  apply LinearMap.ext
  intro jet
  rw [actualThroatConstantFiberThirdOrderJetCoordChange_apply_of_mem
    period hPeriod index index current ⟨hCurrent, hCurrent⟩]
  simpa only [LinearMap.id_apply] using
    actualThroatConstantFiberThirdOrderJetBaseChangeAt_self_transport
      period hPeriod (Fiber := Fiber) index current hCurrent jet

theorem actualThroatConstantFiberThirdOrderJetCoordChange_comp
    {Fiber : Type*}
    [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
    (first middle last current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      actualThroatConstantFiberSecondOrderJetBundleBaseSet
          period hPeriod first ∩
        actualThroatConstantFiberSecondOrderJetBundleBaseSet
          period hPeriod middle ∩
        actualThroatConstantFiberSecondOrderJetBundleBaseSet
          period hPeriod last) :
    (actualThroatConstantFiberThirdOrderJetCoordChange period hPeriod
      (Fiber := Fiber) middle last current).comp
        (actualThroatConstantFiberThirdOrderJetCoordChange period hPeriod
          (Fiber := Fiber) first middle current) =
      actualThroatConstantFiberThirdOrderJetCoordChange period hPeriod
        (Fiber := Fiber) first last current := by
  apply LinearMap.ext
  intro jet
  simp only [LinearMap.comp_apply]
  rw [actualThroatConstantFiberThirdOrderJetCoordChange_apply_of_mem
    period hPeriod first middle current ⟨hCurrent.1.1, hCurrent.1.2⟩]
  rw [actualThroatConstantFiberThirdOrderJetCoordChange_apply_of_mem
    period hPeriod middle last current ⟨hCurrent.1.2, hCurrent.2⟩]
  rw [actualThroatConstantFiberThirdOrderJetCoordChange_apply_of_mem
    period hPeriod first last current ⟨hCurrent.1.1, hCurrent.2⟩]
  exact actualThroatConstantFiberThirdOrderJetBaseChangeAt_transport_comp
    period hPeriod first middle last current hCurrent jet

/-- Exact truncation of the actual constant-fiber third-order coordinate
change to the existing second-order coordinate change. -/
@[simp]
theorem actualThroatConstantFiberThirdOrderJetCoordChange_truncate_apply_of_mem
    {Fiber : Type*}
    [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
    [FiniteDimensional Real Fiber]
    (first second current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      actualThroatConstantFiberSecondOrderJetBundleBaseSet
          period hPeriod first ∩
        actualThroatConstantFiberSecondOrderJetBundleBaseSet
          period hPeriod second)
    (jet : ActualThroatConstantFiberThirdOrderJet Fiber) :
    (actualThroatConstantFiberThirdOrderJetCoordChange period hPeriod
      first second current jet).toFramedSecondOrderJet =
      actualThroatConstantFiberSecondOrderJetCoordChange period hPeriod
        (Fiber := Fiber) first second current jet.toFramedSecondOrderJet := by
  rw [actualThroatConstantFiberThirdOrderJetCoordChange_apply_of_mem
    period hPeriod first second current hCurrent]
  rw [actualThroatConstantFiberSecondOrderJetCoordChange_apply_of_mem
    period hPeriod first second current hCurrent]
  exact
    actualThroatConstantFiberThirdOrderJetBaseChangeAt_transport_truncate
      period hPeriod first second current hCurrent.1 hCurrent.2 jet

/-! ## The three-component LL product -/

/-- Third jets of the auxiliary LL metric, measure and LL field. -/
abbrev ActualLLThirdOrderJetFiber :=
  (ActualThroatConstantFiberThirdOrderJet LLMetricFiber ×
      ActualThroatConstantFiberThirdOrderJet Real) ×
    ActualThroatConstantFiberThirdOrderJet LLFieldFiber

/-- The LL third-order transport uses the same three chart centers as the
existing second-order product core. -/
abbrev ActualLLThirdOrderJetBundleIndex :=
  ActualLLSecondOrderJetBundleIndex period hPeriod

/-- Componentwise actual LL third-order coordinate change. -/
def actualLLThirdOrderJetProductCoordChange
    (first second : ActualLLThirdOrderJetBundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod) :
    ActualLLThirdOrderJetFiber →ₗ[Real] ActualLLThirdOrderJetFiber :=
  ((actualThroatConstantFiberThirdOrderJetCoordChange period hPeriod
      (Fiber := LLMetricFiber) first.1.1 second.1.1 current).prodMap
    (actualThroatConstantFiberThirdOrderJetCoordChange period hPeriod
      (Fiber := Real) first.1.2 second.1.2 current)).prodMap
    (actualThroatConstantFiberThirdOrderJetCoordChange period hPeriod
      (Fiber := LLFieldFiber) first.2 second.2 current)

/-- Componentwise truncation to the existing LL second-order product fiber. -/
def actualLLThirdOrderJetProductTruncate :
    ActualLLThirdOrderJetFiber →ₗ[Real] ActualLLSecondOrderJetFiber :=
  ((framedThirdOrderJetTruncateLinearMap
      (Base := ThroatCoverCoordinates) (Fiber := LLMetricFiber)).prodMap
    (framedThirdOrderJetTruncateLinearMap
      (Base := ThroatCoverCoordinates) (Fiber := Real))).prodMap
    (framedThirdOrderJetTruncateLinearMap
      (Base := ThroatCoverCoordinates) (Fiber := LLFieldFiber))

@[simp]
theorem actualLLThirdOrderJetProductCoordChange_self
    (index : ActualLLThirdOrderJetBundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      (actualLLSecondOrderJetProductVectorBundleCore
        period hPeriod).baseSet index) :
    actualLLThirdOrderJetProductCoordChange period hPeriod
        index index current =
      LinearMap.id := by
  change current ∈
    (actualThroatConstantFiberSecondOrderJetBundleBaseSet period hPeriod
        index.1.1 ∩
      actualThroatConstantFiberSecondOrderJetBundleBaseSet period hPeriod
        index.1.2) ∩
      actualThroatConstantFiberSecondOrderJetBundleBaseSet period hPeriod
        index.2 at hCurrent
  unfold actualLLThirdOrderJetProductCoordChange
  rw [actualThroatConstantFiberThirdOrderJetCoordChange_self
    period hPeriod (Fiber := LLMetricFiber) index.1.1 current hCurrent.1.1]
  rw [actualThroatConstantFiberThirdOrderJetCoordChange_self
    period hPeriod (Fiber := Real) index.1.2 current hCurrent.1.2]
  rw [actualThroatConstantFiberThirdOrderJetCoordChange_self
    period hPeriod (Fiber := LLFieldFiber) index.2 current hCurrent.2]
  rfl

theorem actualLLThirdOrderJetProductCoordChange_comp
    (first middle last : ActualLLThirdOrderJetBundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      (actualLLSecondOrderJetProductVectorBundleCore
          period hPeriod).baseSet first ∩
        (actualLLSecondOrderJetProductVectorBundleCore
          period hPeriod).baseSet middle ∩
        (actualLLSecondOrderJetProductVectorBundleCore
          period hPeriod).baseSet last) :
    (actualLLThirdOrderJetProductCoordChange period hPeriod
      middle last current).comp
        (actualLLThirdOrderJetProductCoordChange period hPeriod
          first middle current) =
      actualLLThirdOrderJetProductCoordChange period hPeriod
        first last current := by
  change current ∈
    (((actualThroatConstantFiberSecondOrderJetBundleBaseSet period hPeriod
          first.1.1 ∩
        actualThroatConstantFiberSecondOrderJetBundleBaseSet period hPeriod
          first.1.2) ∩
      actualThroatConstantFiberSecondOrderJetBundleBaseSet period hPeriod
        first.2) ∩
    ((actualThroatConstantFiberSecondOrderJetBundleBaseSet period hPeriod
          middle.1.1 ∩
        actualThroatConstantFiberSecondOrderJetBundleBaseSet period hPeriod
          middle.1.2) ∩
      actualThroatConstantFiberSecondOrderJetBundleBaseSet period hPeriod
        middle.2)) ∩
    ((actualThroatConstantFiberSecondOrderJetBundleBaseSet period hPeriod
          last.1.1 ∩
        actualThroatConstantFiberSecondOrderJetBundleBaseSet period hPeriod
          last.1.2) ∩
      actualThroatConstantFiberSecondOrderJetBundleBaseSet period hPeriod
        last.2) at hCurrent
  have hMetric : current ∈
      actualThroatConstantFiberSecondOrderJetBundleBaseSet period hPeriod
          first.1.1 ∩
        actualThroatConstantFiberSecondOrderJetBundleBaseSet period hPeriod
          middle.1.1 ∩
        actualThroatConstantFiberSecondOrderJetBundleBaseSet period hPeriod
          last.1.1 :=
    ⟨⟨hCurrent.1.1.1.1, hCurrent.1.2.1.1⟩, hCurrent.2.1.1⟩
  have hMeasure : current ∈
      actualThroatConstantFiberSecondOrderJetBundleBaseSet period hPeriod
          first.1.2 ∩
        actualThroatConstantFiberSecondOrderJetBundleBaseSet period hPeriod
          middle.1.2 ∩
        actualThroatConstantFiberSecondOrderJetBundleBaseSet period hPeriod
          last.1.2 :=
    ⟨⟨hCurrent.1.1.1.2, hCurrent.1.2.1.2⟩, hCurrent.2.1.2⟩
  have hField : current ∈
      actualThroatConstantFiberSecondOrderJetBundleBaseSet period hPeriod
          first.2 ∩
        actualThroatConstantFiberSecondOrderJetBundleBaseSet period hPeriod
          middle.2 ∩
        actualThroatConstantFiberSecondOrderJetBundleBaseSet period hPeriod
          last.2 :=
    ⟨⟨hCurrent.1.1.2, hCurrent.1.2.2⟩, hCurrent.2.2⟩
  unfold actualLLThirdOrderJetProductCoordChange
  rw [LinearMap.prodMap_comp, LinearMap.prodMap_comp]
  rw [actualThroatConstantFiberThirdOrderJetCoordChange_comp
    period hPeriod (Fiber := LLMetricFiber)
      first.1.1 middle.1.1 last.1.1 current hMetric]
  rw [actualThroatConstantFiberThirdOrderJetCoordChange_comp
    period hPeriod (Fiber := Real)
      first.1.2 middle.1.2 last.1.2 current hMeasure]
  rw [actualThroatConstantFiberThirdOrderJetCoordChange_comp
    period hPeriod (Fiber := LLFieldFiber)
      first.2 middle.2 last.2 current hField]

/-- On a common LL double overlap, componentwise third-order transport
truncates exactly to the coordinate change of the existing LL second-jet
product core. -/
@[simp]
theorem actualLLThirdOrderJetProductCoordChange_truncate_apply_of_mem
    (first second : ActualLLThirdOrderJetBundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      (actualLLSecondOrderJetProductVectorBundleCore
          period hPeriod).baseSet first ∩
        (actualLLSecondOrderJetProductVectorBundleCore
          period hPeriod).baseSet second)
    (jet : ActualLLThirdOrderJetFiber) :
    actualLLThirdOrderJetProductTruncate
        (actualLLThirdOrderJetProductCoordChange period hPeriod
          first second current jet) =
      (actualLLSecondOrderJetProductVectorBundleCore period hPeriod).coordChange
        first second current (actualLLThirdOrderJetProductTruncate jet) := by
  change current ∈
    ((actualThroatConstantFiberSecondOrderJetBundleBaseSet period hPeriod
          first.1.1 ∩
        actualThroatConstantFiberSecondOrderJetBundleBaseSet period hPeriod
          first.1.2) ∩
      actualThroatConstantFiberSecondOrderJetBundleBaseSet period hPeriod
        first.2) ∩
    ((actualThroatConstantFiberSecondOrderJetBundleBaseSet period hPeriod
          second.1.1 ∩
        actualThroatConstantFiberSecondOrderJetBundleBaseSet period hPeriod
          second.1.2) ∩
      actualThroatConstantFiberSecondOrderJetBundleBaseSet period hPeriod
        second.2) at hCurrent
  rcases jet with ⟨⟨metricJet, measureJet⟩, fieldJet⟩
  change
    (((actualThroatConstantFiberThirdOrderJetCoordChange period hPeriod
          first.1.1 second.1.1 current metricJet).toFramedSecondOrderJet,
      (actualThroatConstantFiberThirdOrderJetCoordChange period hPeriod
          first.1.2 second.1.2 current measureJet).toFramedSecondOrderJet),
      (actualThroatConstantFiberThirdOrderJetCoordChange period hPeriod
          first.2 second.2 current fieldJet).toFramedSecondOrderJet) =
    ((actualThroatConstantFiberSecondOrderJetCoordChange period hPeriod
        first.1.1 second.1.1 current metricJet.toFramedSecondOrderJet,
      actualThroatConstantFiberSecondOrderJetCoordChange period hPeriod
        first.1.2 second.1.2 current measureJet.toFramedSecondOrderJet),
      actualThroatConstantFiberSecondOrderJetCoordChange period hPeriod
        first.2 second.2 current fieldJet.toFramedSecondOrderJet)
  apply Prod.ext
  · apply Prod.ext
    · exact
        actualThroatConstantFiberThirdOrderJetCoordChange_truncate_apply_of_mem
          period hPeriod first.1.1 second.1.1 current
            ⟨hCurrent.1.1.1, hCurrent.2.1.1⟩ metricJet
    · exact
        actualThroatConstantFiberThirdOrderJetCoordChange_truncate_apply_of_mem
          period hPeriod first.1.2 second.1.2 current
            ⟨hCurrent.1.1.2, hCurrent.2.1.2⟩ measureJet
  · exact
      actualThroatConstantFiberThirdOrderJetCoordChange_truncate_apply_of_mem
        period hPeriod first.2 second.2 current
          ⟨hCurrent.1.2, hCurrent.2.2⟩ fieldJet

end
end P0EFTJanusProgramPActualLLThirdOrderJetProductCoordChange4D
end JanusFormal
