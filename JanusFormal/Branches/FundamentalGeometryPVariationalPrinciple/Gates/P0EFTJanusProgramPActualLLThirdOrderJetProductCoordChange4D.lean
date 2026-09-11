import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualLLSecondOrderJetProductVectorBundleCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatConstantFiberThirdOrderJetCoordChange4D

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
open P0EFTJanusProgramPActualThroatConstantFiberSecondOrderJetSmoothVectorBundleCore4D
open P0EFTJanusProgramPActualThroatConstantFiberThirdOrderJetCoordChange4D
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
