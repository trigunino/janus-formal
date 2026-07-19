import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMatterRobinFullLLActualHessian4D

/-! Exact active projection and quotient for the matter--Robin--full-LL action. -/

namespace JanusFormal
namespace P0EFTJanusMatterRobinFullLLActiveQuotientHessian4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff Topology
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusScalarDiffeomorphismNoetherOperator4D
open P0EFTJanusGlobalMatterMultipletActualEulerHessian4D
open P0EFTJanusCommonMatterActionVariation4D
open P0EFTJanusFullMatterRobinLLDirections4D
open P0EFTJanusIntegratedPTFullLLHessianAssembly4D
open P0EFTJanusIntegratedPTFullLLHessianVariation4D
open P0EFTJanusMatterRobinFullLLActualHessian4D
open P0EFTJanusFullMatterRobinTrueLLActionVariation4D
open P0EFTJanusCommonCompleteSectorD9Variation4D
open P0EFTJanusMappingTorusCandidateAFunctionalVariation4D
open P0EFTJanusProgramPCommonLLActionVariation4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where measurable_eq := rfl

/-- Exactly the five direction slots seen by the existing true action. -/
structure ActiveDirection where
  matter : SmoothQuotientField period hPeriod MatterFiber ×
    SmoothQuotientField period hPeriod MatterFiber
  robin : SmoothThroatField period hPeriod Real
  llField : SmoothThroatField period hPeriod LLFieldFiber
  llAuxMetric : SmoothThroatField period hPeriod LLMetricFiber
  llMeasure : SmoothThroatField period hPeriod Real

def activeProjection (d : FullMatterRobinLLDirections period hPeriod) :
    ActiveDirection period hPeriod where
  matter := d.common.matter
  robin := d.robin
  llField := d.common.ll
  llAuxMetric := d.llAuxMetric
  llMeasure := d.llMeasure

def activeRepresentative (a : ActiveDirection period hPeriod) :
    FullMatterRobinLLDirections period hPeriod where
  common :=
    { metric := zeroSmoothDiagonalMetricVariation period hPeriod
      matter := a.matter
      gauge := 0
      ghost := 0
      auxiliary := 0
      ll := a.llField }
  robin := a.robin
  llAuxMetric := a.llAuxMetric
  llMeasure := a.llMeasure

theorem activeProjection_eq_iff
    (first second : FullMatterRobinLLDirections period hPeriod) :
    activeProjection period hPeriod first = activeProjection period hPeriod second ↔
      first.common.matter = second.common.matter ∧
      first.robin = second.robin ∧
      first.common.ll = second.common.ll ∧
      first.llAuxMetric = second.llAuxMetric ∧
      first.llMeasure = second.llMeasure := by
  simp [activeProjection]

@[simp] theorem activeProjection_representative (a : ActiveDirection period hPeriod) :
    activeProjection period hPeriod (activeRepresentative period hPeriod a) = a := by
  cases a
  rfl

theorem activeProjection_surjective :
    Function.Surjective (activeProjection period hPeriod) := by
  intro a
  exact ⟨activeRepresentative period hPeriod a, activeProjection_representative period hPeriod a⟩

/-- Euler functional written only on the five active slots. -/
def activeEuler
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod)
    (junction : SmoothThroatField period hPeriod Real)
    (a : ActiveDirection period hPeriod) : Real :=
  fullMatterRobinTrueLLEuler period hPeriod matterData kPlus kMinus bulkPlus
    bulkMinus robinMeasure frame llMeasure fields junction
    (activeRepresentative period hPeriod a)

theorem trueEuler_factors_active
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod)
    (junction : SmoothThroatField period hPeriod Real)
    (d : FullMatterRobinLLDirections period hPeriod) :
    fullMatterRobinTrueLLEuler period hPeriod matterData kPlus kMinus bulkPlus
        bulkMinus robinMeasure frame llMeasure fields junction d =
      activeEuler period hPeriod matterData kPlus kMinus bulkPlus bulkMinus
        robinMeasure frame llMeasure fields junction (activeProjection period hPeriod d) := by
  rfl

/-- Hessian written only on active representatives. -/
def activeHessian
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod)
    (a b : ActiveDirection period hPeriod) : Real :=
  globalMatterRobinFullLLHessian period hPeriod matterData kPlus kMinus
    robinMeasure frame llMeasure fields (activeRepresentative period hPeriod a)
      (activeRepresentative period hPeriod b)

theorem fullHessian_factors_active
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod)
    (first second : FullMatterRobinLLDirections period hPeriod) :
    globalMatterRobinFullLLHessian period hPeriod matterData kPlus kMinus
        robinMeasure frame llMeasure fields first second =
      activeHessian period hPeriod matterData kPlus kMinus robinMeasure frame
        llMeasure fields (activeProjection period hPeriod first)
          (activeProjection period hPeriod second) := by
  rfl

theorem activeHessian_symmetric
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real) (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod) (a b : ActiveDirection period hPeriod) :
    activeHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields a b =
      activeHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields b a := by
  exact globalMatterRobinFullLLHessian_symmetric period hPeriod matterData kPlus
    kMinus robinMeasure frame llMeasure fields _ _

/-- Metric, gauge, ghost, and bulk-auxiliary directions are the exact inactive kernel. -/
def inactiveDirection
    (metric : SmoothDiagonalMetricVariation period hPeriod)
    (gauge : SmoothQuotientField period hPeriod GaugeFiber ×
      SmoothQuotientField period hPeriod GaugeFiber)
    (ghost : SmoothQuotientField period hPeriod GhostFiber ×
      SmoothQuotientField period hPeriod GhostFiber)
    (auxiliary : SmoothQuotientField period hPeriod AuxiliaryFiber ×
      SmoothQuotientField period hPeriod AuxiliaryFiber) :
    FullMatterRobinLLDirections period hPeriod where
  common :=
    { metric := metric
      matter := 0
      gauge := gauge
      ghost := ghost
      auxiliary := auxiliary
      ll := 0 }
  robin := 0
  llAuxMetric := 0
  llMeasure := 0

theorem activeProjection_inactiveDirection
    (metric : SmoothDiagonalMetricVariation period hPeriod)
    (gauge : SmoothQuotientField period hPeriod GaugeFiber × SmoothQuotientField period hPeriod GaugeFiber)
    (ghost : SmoothQuotientField period hPeriod GhostFiber × SmoothQuotientField period hPeriod GhostFiber)
    (auxiliary : SmoothQuotientField period hPeriod AuxiliaryFiber × SmoothQuotientField period hPeriod AuxiliaryFiber) :
    activeProjection period hPeriod (inactiveDirection period hPeriod metric gauge ghost auxiliary) =
      activeProjection period hPeriod
        (inactiveDirection period hPeriod (zeroSmoothDiagonalMetricVariation period hPeriod) 0 0 0) := by
  rfl

/-- Quotient identifying precisely directions with equal active projection. -/
def activeSetoid : Setoid (FullMatterRobinLLDirections period hPeriod) where
  r first second := activeProjection period hPeriod first = activeProjection period hPeriod second
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

abbrev ActiveQuotient := Quotient (activeSetoid period hPeriod)

def quotientHessian
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real) (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod) :
    ActiveQuotient period hPeriod → ActiveQuotient period hPeriod → Real :=
  Quotient.lift₂
    (globalMatterRobinFullLLHessian period hPeriod matterData kPlus kMinus
      robinMeasure frame llMeasure fields)
    (by
      intro a a' b b' ha hb
      rw [fullHessian_factors_active, fullHessian_factors_active, ha, hb])

theorem quotientHessian_mk
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real) (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod)
    (first second : FullMatterRobinLLDirections period hPeriod) :
    quotientHessian period hPeriod matterData kPlus kMinus robinMeasure frame llMeasure fields
        ⟦first⟧ ⟦second⟧ =
      globalMatterRobinFullLLHessian period hPeriod matterData kPlus kMinus
        robinMeasure frame llMeasure fields first second := by
  rfl

end
end P0EFTJanusMatterRobinFullLLActiveQuotientHessian4D
end JanusFormal
