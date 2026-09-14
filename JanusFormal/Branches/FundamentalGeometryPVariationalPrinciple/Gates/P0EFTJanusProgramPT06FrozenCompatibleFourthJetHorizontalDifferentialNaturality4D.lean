import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06ActualPhysicalThirdJetVectorDensityHorizontalDifferential4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06T02CompatibleThirdJetCurrentTransport4D

/-!
# Frozen-compatible J4 naturality of the horizontal differential

A continuous-linear transition on formal J3 jets intertwines horizontal
differentials whenever it admits a J4 lift commuting with truncation and the
three formal total derivatives.  Gate945's spatially frozen moving-frame
transport has such a coefficientwise lift at order four, so its current
pullback satisfies this naturality law.

This is the frozen compatible transport selected by Gate945.  It is not the
derivative-corrected physical J4 atlas transition, and no base-Jacobian or
Piola identity is asserted here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06FrozenCompatibleFourthJetHorizontalDifferentialNaturality4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000

noncomputable section

open Set
open scoped BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusProgramPActualPhysicalSecondOrderJetProductVectorBundleCore4D
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPT06ActualPhysicalValueProductSecondJetBridge4D
open P0EFTJanusProgramPT06ActualPhysicalDeckJetProlongation4D
open P0EFTJanusProgramPT06CanonicalFixedFrameDeckData4D
open P0EFTJanusProgramPT06ThroatSpatialFinsuppJetTower4D
open P0EFTJanusProgramPT06LocalFunctionTotalDerivative4D
open P0EFTJanusProgramPT06SecondOrderRadialCartanHomotopy4D
open P0EFTJanusProgramPT06MovingFrameDeckConjugation4D
open P0EFTJanusProgramPT06T02MovingFrameRankOneCompatibility4D
open P0EFTJanusProgramPT06T02CompatibleThirdJetCurrentTransport4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

/-! ## Generic J3/J4 naturality -/

universe u

variable {Fiber : Type u} [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]

private abbrev GenericThirdJet := ThroatSpatialMultiindexJet3 Fiber
private abbrev GenericFourthJet := ThroatSpatialMultiindexJet4 Fiber
private abbrev GenericCurrent :=
  ProgramPT06SecondOrderHorizontalCurrent4D (Fiber := Fiber)

/-- Horizontal differentiation is natural under any continuous-linear J3
transition with a J4 lift intertwining truncation and all total derivatives. -/
theorem programPT06SecondOrderHorizontalCurrentDH_precompose_of_intertwines
    (transition3 : GenericThirdJet (Fiber := Fiber) →L[Real]
      GenericThirdJet (Fiber := Fiber))
    (transition4 : GenericFourthJet (Fiber := Fiber) →
      GenericFourthJet (Fiber := Fiber))
    (hTruncate : ∀ jet,
      transition3
          (truncateThroatSpatialMultiindexJet (by omega : 3 ≤ 4) jet) =
        truncateThroatSpatialMultiindexJet (by omega : 3 ≤ 4)
          (transition4 jet))
    (hTotalDerivative : ∀ direction jet,
      transition3 (throatSpatialTotalDerivative direction jet) =
        throatSpatialTotalDerivative direction (transition4 jet))
    (current : GenericCurrent (Fiber := Fiber))
    (hCurrent : ∀ direction, Differentiable Real (current direction))
    (jet : GenericFourthJet (Fiber := Fiber)) :
    programPT06SecondOrderHorizontalCurrentDH
        (fun direction => current direction ∘ transition3) jet =
      programPT06SecondOrderHorizontalCurrentDH current
        (transition4 jet) := by
  unfold programPT06SecondOrderHorizontalCurrentDH
  apply Finset.sum_congr rfl
  intro direction _
  let base :=
    truncateThroatSpatialMultiindexJet (by omega : 3 ≤ 4) jet
  have hDerivative :
      HasFDerivAt (current direction ∘ transition3)
        ((fderiv Real (current direction) (transition3 base)).comp
          transition3) base :=
    ((hCurrent direction (transition3 base)).hasFDerivAt).comp base
      transition3.hasFDerivAt
  unfold programPT06ThroatSpatialLocalFunctionTotalDerivative
  rw [show
    fderiv Real (current direction ∘ transition3) base =
        (fderiv Real (current direction) (transition3 base)).comp
          transition3 from hDerivative.fderiv]
  simp only [ContinuousLinearMap.comp_apply]
  rw [hTruncate jet, hTotalDerivative direction jet]

/-! ## Gate945's frozen compatible fourth-jet lift -/

private abbrev PhysicalFiber := ActualPhysicalValueProductFiber
private abbrev PhysicalThirdJet :=
  ThroatSpatialMultiindexJet3 PhysicalFiber
private abbrev PhysicalFourthJet :=
  ThroatSpatialMultiindexJet4 PhysicalFiber
private abbrev PhysicalCurrent :=
  ProgramPT06SecondOrderHorizontalCurrent4D (Fiber := PhysicalFiber)

attribute [local instance]
  P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D.actualPhysicalValueProductNormedAddCommGroup
  P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D.actualPhysicalValueProductNormedSpace

local instance frozenActualMetricValueNormedAddCommGroup :
    NormedAddCommGroup ActualMetricValueFiber :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance frozenActualMetricValueNormedSpace :
    NormedSpace Real ActualMetricValueFiber :=
  ContinuousLinearMap.toNormedSpace

local instance frozenActualMetricValueFiniteDimensional :
    FiniteDimensional Real ActualMetricValueFiber :=
  ContinuousLinearMap.finiteDimensional

private abbrev RawPhysicalFiber :=
  ((ActualGaugeValueProductFiber × ActualLLValueProductFiber) ×
      ActualMetricValueProductFiber) × ActualSpinCValueProductFiber

local instance frozenPhysicalFiberFiniteDimensional :
    FiniteDimensional Real PhysicalFiber :=
  inferInstanceAs (FiniteDimensional Real RawPhysicalFiber)

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev Base := MappingTorus (fixedEquatorData period hPeriod)
private abbrev Chart :=
  ActualPhysicalSecondOrderJetProductBundleIndex period hPeriod

/-- Gate945's coefficientwise moving-frame transition, prolonged to J4. -/
def programPT06T02FrozenCompatibleFinsuppFourthJetCoordChange
    (compatibility :
      ProgramPT06T02MovingFrameJetCompatibility4D period hPeriod)
    (first second : Chart period hPeriod) (base : Base period hPeriod)
    (jet : PhysicalFourthJet) : PhysicalFourthJet :=
  programPT06ActualPhysicalMovingFrameJetDeckAction
    compatibility.trivialization .positiveQuarter
    (compatibility.transitionWinding first second base)
    (compatibility.chartLift first base) 4 jet

/-- Identity overlaps act trivially on the frozen compatible J4 lift. -/
@[simp]
theorem programPT06T02FrozenCompatibleFinsuppFourthJetCoordChange_self
    (compatibility :
      ProgramPT06T02MovingFrameJetCompatibility4D period hPeriod)
    (chart : Chart period hPeriod) (base : Base period hPeriod)
    (hBase : base ∈
      (actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
        .positiveQuarter).baseSet chart)
    (jet : PhysicalFourthJet) :
    programPT06T02FrozenCompatibleFinsuppFourthJetCoordChange period hPeriod
        compatibility chart chart base jet = jet := by
  rw [programPT06T02FrozenCompatibleFinsuppFourthJetCoordChange,
    programPT06T02CompatibleTransitionWinding_self
      period hPeriod compatibility chart base hBase]
  exact programPT06ActualPhysicalMovingFrameJetDeckAction_zero
    compatibility.trivialization .positiveQuarter
      (compatibility.chartLift chart base) 4 jet

/-- The frozen compatible J4 lifts obey the same overlap cocycle as Gate945. -/
theorem programPT06T02FrozenCompatibleFinsuppFourthJetCoordChange_comp
    (compatibility :
      ProgramPT06T02MovingFrameJetCompatibility4D period hPeriod)
    (first second third : Chart period hPeriod)
    (base : Base period hPeriod)
    (hBase : base ∈
      (actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
          .positiveQuarter).baseSet first ∩
        (actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
          .positiveQuarter).baseSet second ∩
        (actualPhysicalSecondOrderJetProductVectorBundleCore period hPeriod
          .positiveQuarter).baseSet third)
    (jet : PhysicalFourthJet) :
    programPT06T02FrozenCompatibleFinsuppFourthJetCoordChange period hPeriod
        compatibility second third base
        (programPT06T02FrozenCompatibleFinsuppFourthJetCoordChange
          period hPeriod compatibility first second base jet) =
      programPT06T02FrozenCompatibleFinsuppFourthJetCoordChange period hPeriod
        compatibility first third base jet := by
  unfold programPT06T02FrozenCompatibleFinsuppFourthJetCoordChange
  rw [← compatibility.target_point first second base
    ⟨hBase.1.1, hBase.1.2⟩]
  rw [← programPT06ActualPhysicalMovingFrameJetDeckAction_add]
  rw [programPT06T02CompatibleTransitionWinding_comp
    period hPeriod compatibility first second third base hBase]

/-- Truncating the frozen J4 lift gives exactly Gate945's frozen J3 lift. -/
theorem programPT06T02FrozenCompatibleFinsuppFourthJetCoordChange_truncate
    (compatibility :
      ProgramPT06T02MovingFrameJetCompatibility4D period hPeriod)
    (first second : Chart period hPeriod) (base : Base period hPeriod)
    (jet : PhysicalFourthJet) :
    truncateThroatSpatialMultiindexJet (by omega : 3 ≤ 4)
        (programPT06T02FrozenCompatibleFinsuppFourthJetCoordChange
          period hPeriod compatibility first second base jet) =
      programPT06T02CompatibleFinsuppThirdJetCoordChange period hPeriod
        compatibility first second base
        (truncateThroatSpatialMultiindexJet (by omega : 3 ≤ 4) jet) := by
  exact
    programPT06ActualPhysicalMovingFrameJetDeckAction_commutes_truncation
      compatibility.trivialization .positiveQuarter
      (compatibility.transitionWinding first second base)
      (compatibility.chartLift first base) (by omega) jet

/-- The frozen J4 lift intertwines each formal total derivative with Gate945's
J3 lift. -/
theorem
    programPT06T02FrozenCompatibleFinsuppFourthJetCoordChange_commutes_totalDerivative
    (compatibility :
      ProgramPT06T02MovingFrameJetCompatibility4D period hPeriod)
    (first second : Chart period hPeriod) (base : Base period hPeriod)
    (direction : Fin 3) (jet : PhysicalFourthJet) :
    throatSpatialTotalDerivative direction
        (programPT06T02FrozenCompatibleFinsuppFourthJetCoordChange
          period hPeriod compatibility first second base jet) =
      programPT06T02CompatibleFinsuppThirdJetCoordChange period hPeriod
        compatibility first second base
        (throatSpatialTotalDerivative direction jet) := by
  exact
    programPT06ActualPhysicalMovingFrameJetDeckAction_commutes_totalDerivative
      compatibility.trivialization .positiveQuarter
      (compatibility.transitionWinding first second base)
      (compatibility.chartLift first base) direction jet

/-! ## Continuous-linear realization and dH specialization -/

private theorem programPT06ActualPhysicalCanonicalValueDeckAction_additive
    (choice : NormalRootChoice) (winding : Int)
    (first second : PhysicalFiber) :
    programPT06ActualPhysicalCanonicalValueDeckAction choice winding
        (first + second) =
      programPT06ActualPhysicalCanonicalValueDeckAction choice winding first +
        programPT06ActualPhysicalCanonicalValueDeckAction choice winding
          second := by
  rcases first with ⟨⟨⟨firstGauge, firstLL⟩, firstMetric⟩, firstSpinC⟩
  rcases second with
    ⟨⟨⟨secondGauge, secondLL⟩, secondMetric⟩, secondSpinC⟩
  simp [programPT06ActualPhysicalCanonicalValueDeckAction,
    programPT06ActualPhysicalValueProductDeckAction,
    programPT06ActualGaugeValueProductDeckAction,
    programPT06ActualLLValueProductDeckAction,
    programPT06ActualMetricValueProductDeckAction,
    programPT06ActualSpinCValueProductDeckAction,
    d9DoubledMatterSpinorMonodromy_additive]

private theorem programPT06ActualPhysicalCanonicalValueDeckAction_smul
    (choice : NormalRootChoice) (winding : Int) (scalar : Real)
    (value : PhysicalFiber) :
    programPT06ActualPhysicalCanonicalValueDeckAction choice winding
        (scalar • value) =
      scalar • programPT06ActualPhysicalCanonicalValueDeckAction choice
        winding value := by
  rcases value with ⟨⟨⟨gauge, ll⟩, metric⟩, spinC⟩
  simp [programPT06ActualPhysicalCanonicalValueDeckAction,
    programPT06ActualPhysicalValueProductDeckAction,
    programPT06ActualGaugeValueProductDeckAction,
    programPT06ActualLLValueProductDeckAction,
    programPT06ActualMetricValueProductDeckAction,
    programPT06ActualSpinCValueProductDeckAction,
    d9DoubledMatterSpinorMonodromy_real_smul]

private def programPT06ActualPhysicalCanonicalValueDeckLinearMap
    (choice : NormalRootChoice) (winding : Int) :
    PhysicalFiber →ₗ[Real] PhysicalFiber where
  toFun := programPT06ActualPhysicalCanonicalValueDeckAction choice winding
  map_add' :=
    programPT06ActualPhysicalCanonicalValueDeckAction_additive choice winding
  map_smul' :=
    programPT06ActualPhysicalCanonicalValueDeckAction_smul choice winding

private def programPT06ActualPhysicalMovingFrameValueDeckLinearMap
    (compatibility :
      ProgramPT06T02MovingFrameJetCompatibility4D period hPeriod)
    (first second : Chart period hPeriod) (base : Base period hPeriod) :
    PhysicalFiber →ₗ[Real] PhysicalFiber :=
  (compatibility.trivialization.toFixed
      (programPT06MovingFrameDeckPoint
        (compatibility.transitionWinding first second base)
        (compatibility.chartLift first base))).symm.toLinearMap.comp
    ((programPT06ActualPhysicalCanonicalValueDeckLinearMap .positiveQuarter
        (compatibility.transitionWinding first second base)).comp
      (compatibility.trivialization.toFixed
        (compatibility.chartLift first base)).toLinearMap)

@[simp]
private theorem programPT06ActualPhysicalMovingFrameValueDeckLinearMap_apply
    (compatibility :
      ProgramPT06T02MovingFrameJetCompatibility4D period hPeriod)
    (first second : Chart period hPeriod) (base : Base period hPeriod)
    (value : PhysicalFiber) :
    programPT06ActualPhysicalMovingFrameValueDeckLinearMap period hPeriod
        compatibility first second base value =
      programPT06ActualPhysicalMovingFrameValueDeckAction
        compatibility.trivialization .positiveQuarter
        (compatibility.transitionWinding first second base)
        (compatibility.chartLift first base) value :=
  rfl

/-- Continuous-linear realization of Gate945's frozen J3 transition. -/
def programPT06T02FrozenCompatibleFinsuppThirdJetCoordChangeCLM
    (compatibility :
      ProgramPT06T02MovingFrameJetCompatibility4D period hPeriod)
    (first second : Chart period hPeriod) (base : Base period hPeriod) :
    PhysicalThirdJet →L[Real] PhysicalThirdJet :=
  ContinuousLinearMap.pi fun index =>
    (programPT06ActualPhysicalMovingFrameValueDeckLinearMap period hPeriod
      compatibility first second base).toContinuousLinearMap.comp
        (ContinuousLinearMap.proj index)

@[simp]
theorem programPT06T02FrozenCompatibleFinsuppThirdJetCoordChangeCLM_apply
    (compatibility :
      ProgramPT06T02MovingFrameJetCompatibility4D period hPeriod)
    (first second : Chart period hPeriod) (base : Base period hPeriod)
    (jet : PhysicalThirdJet) :
    programPT06T02FrozenCompatibleFinsuppThirdJetCoordChangeCLM
        period hPeriod compatibility first second base jet =
      programPT06T02CompatibleFinsuppThirdJetCoordChange period hPeriod
        compatibility first second base jet := by
  funext index
  rfl

/-- Gate945's frozen current pullback commutes exactly with the horizontal
differential through its coefficientwise J4 lift. -/
theorem programPT06T02CompatibleThirdJetCurrentPullback_DH
    (compatibility :
      ProgramPT06T02MovingFrameJetCompatibility4D period hPeriod)
    (first second : Chart period hPeriod) (base : Base period hPeriod)
    (current : PhysicalCurrent)
    (hCurrent : ∀ direction, Differentiable Real (current direction))
    (jet : PhysicalFourthJet) :
    programPT06SecondOrderHorizontalCurrentDH
        (programPT06T02CompatibleThirdJetCurrentPullback period hPeriod
          compatibility first second base current) jet =
      programPT06SecondOrderHorizontalCurrentDH current
        (programPT06T02FrozenCompatibleFinsuppFourthJetCoordChange
          period hPeriod compatibility first second base jet) := by
  change
    programPT06SecondOrderHorizontalCurrentDH
        (fun direction candidate =>
          current direction
            (programPT06T02CompatibleFinsuppThirdJetCoordChange period hPeriod
              compatibility first second base candidate)) jet = _
  have hNaturality :=
    programPT06SecondOrderHorizontalCurrentDH_precompose_of_intertwines
      (transition3 :=
        programPT06T02FrozenCompatibleFinsuppThirdJetCoordChangeCLM
          period hPeriod compatibility first second base)
      (transition4 :=
        programPT06T02FrozenCompatibleFinsuppFourthJetCoordChange
          period hPeriod compatibility first second base)
      (fun candidate => by
        simpa using
          (programPT06T02FrozenCompatibleFinsuppFourthJetCoordChange_truncate
            period hPeriod compatibility first second base candidate).symm)
      (fun direction candidate => by
        simpa using
          (programPT06T02FrozenCompatibleFinsuppFourthJetCoordChange_commutes_totalDerivative
            period hPeriod compatibility first second base direction
            candidate).symm)
      current hCurrent jet
  have hPullback :
      (fun direction => current direction ∘
        programPT06T02FrozenCompatibleFinsuppThirdJetCoordChangeCLM
          period hPeriod compatibility first second base) =
        (fun direction candidate =>
          current direction
            (programPT06T02CompatibleFinsuppThirdJetCoordChange period hPeriod
              compatibility first second base candidate)) := by
    funext direction candidate
    rw [Function.comp_apply,
      programPT06T02FrozenCompatibleFinsuppThirdJetCoordChangeCLM_apply]
  rw [hPullback] at hNaturality
  exact hNaturality

end
end P0EFTJanusProgramPT06FrozenCompatibleFourthJetHorizontalDifferentialNaturality4D
end JanusFormal
