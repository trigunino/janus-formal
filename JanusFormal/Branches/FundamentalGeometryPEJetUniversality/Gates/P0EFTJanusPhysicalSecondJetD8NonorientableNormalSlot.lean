import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusPhysicalSecondJetBackgroundNormalCore
import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusSmoothNormalZ4RootBundle

namespace JanusFormal
namespace P0EFTJanusPhysicalSecondJetD8NonorientableNormalSlot

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusNormalBundleOrientationCover
open P0EFTJanusMappingTorusSmoothNormalVectorBundle
open P0EFTJanusMappingTorusSmoothNormalZ4RootBundle
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusPhysicalSecondJetCommonRefinedAtlas
open P0EFTJanusPhysicalSecondJetProductVectorBundleCore
open P0EFTJanusPhysicalSecondJetBackgroundNormalCore

universe uGaugeFiber uLLFiber uMetricFiber uSpinCFiber uBackgroundFiber
universe uGaugeChart uLLChart uMetricChart uSpinCChart uBackgroundChart

variable (period : ℝ) (hPeriod : period ≠ 0)

private abbrev ThroatCover :=
  MappingTorusCover (fixedEquatorData period hPeriod)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

variable {GaugeFiber : Type uGaugeFiber}
variable {LLFiber : Type uLLFiber}
variable {MetricFiber : Type uMetricFiber}
variable {SpinCFiber : Type uSpinCFiber}
variable {BackgroundFiber : Type uBackgroundFiber}
variable [NormedAddCommGroup GaugeFiber] [NormedSpace ℝ GaugeFiber]
variable [NormedAddCommGroup LLFiber] [NormedSpace ℝ LLFiber]
variable [NormedAddCommGroup MetricFiber] [NormedSpace ℝ MetricFiber]
variable [NormedAddCommGroup SpinCFiber] [NormedSpace ℝ SpinCFiber]
variable [NormedAddCommGroup BackgroundFiber] [NormedSpace ℝ BackgroundFiber]

variable {GaugeChart : Type uGaugeChart}
variable {LLChart : Type uLLChart}
variable {MetricChart : Type uMetricChart}
variable {SpinCChart : Type uSpinCChart}
variable {BackgroundChart : Type uBackgroundChart}

/-- Install the actual sign-clutched D8 normal line as the normal slot of the
complete physical second-jet core.  No oriented scalar trivialization is used. -/
def physicalSecondJetD8NormalCore
    (gaugeCore : VectorBundleCore ℝ (EffectiveThroat period hPeriod)
      GaugeFiber GaugeChart)
    (llCore : VectorBundleCore ℝ (EffectiveThroat period hPeriod)
      LLFiber LLChart)
    (metricCore : VectorBundleCore ℝ (EffectiveThroat period hPeriod)
      MetricFiber MetricChart)
    (spinCCore : VectorBundleCore ℝ (EffectiveThroat period hPeriod)
      SpinCFiber SpinCChart)
    (backgroundCore : VectorBundleCore ℝ (EffectiveThroat period hPeriod)
      BackgroundFiber BackgroundChart) :
    VectorBundleCore ℝ (EffectiveThroat period hPeriod)
      (PhysicalSecondJetBackgroundNormalFiber
        (GaugeFiber := GaugeFiber) (LLFiber := LLFiber)
        (MetricFiber := MetricFiber) (SpinCFiber := SpinCFiber)
        (BackgroundFiber := BackgroundFiber) (NormalFiber := ℝ))
      (PhysicalSecondJetBackgroundNormalChart
        (GaugeChart := GaugeChart) (LLChart := LLChart)
        (MetricChart := MetricChart) (SpinCChart := SpinCChart)
        (BackgroundChart := BackgroundChart)
        (NormalChart := ThroatCover period hPeriod)) :=
  physicalSecondJetBackgroundNormalCore gaugeCore llCore metricCore spinCCore
    backgroundCore (fixedThroatNormalVectorBundleCore period hPeriod)

/-- The normal projection of every complete coordinate change is exactly the
D8 sign representation. -/
@[simp]
theorem physicalSecondJetD8NormalCore_coordChange_normal
    (gaugeCore : VectorBundleCore ℝ (EffectiveThroat period hPeriod)
      GaugeFiber GaugeChart)
    (llCore : VectorBundleCore ℝ (EffectiveThroat period hPeriod)
      LLFiber LLChart)
    (metricCore : VectorBundleCore ℝ (EffectiveThroat period hPeriod)
      MetricFiber MetricChart)
    (spinCCore : VectorBundleCore ℝ (EffectiveThroat period hPeriod)
      SpinCFiber SpinCChart)
    (backgroundCore : VectorBundleCore ℝ (EffectiveThroat period hPeriod)
      BackgroundFiber BackgroundChart)
    (first second : PhysicalSecondJetBackgroundNormalChart
      (GaugeChart := GaugeChart) (LLChart := LLChart)
      (MetricChart := MetricChart) (SpinCChart := SpinCChart)
      (BackgroundChart := BackgroundChart)
      (NormalChart := ThroatCover period hPeriod))
    (base : EffectiveThroat period hPeriod)
    (vector : PhysicalSecondJetBackgroundNormalFiber
      (GaugeFiber := GaugeFiber) (LLFiber := LLFiber)
      (MetricFiber := MetricFiber) (SpinCFiber := SpinCFiber)
      (BackgroundFiber := BackgroundFiber) (NormalFiber := ℝ)) :
    ((physicalSecondJetD8NormalCore period hPeriod gaugeCore llCore metricCore
      spinCCore backgroundCore).coordChange first second base vector).2 =
      (fixedThroatNormalVectorBundleCore period hPeriod).coordChange
        first.normal second.normal base vector.2 :=
  rfl

/-- One throat circuit negates the normal component of the complete physical
coordinate change, while making no claim of a global oriented normal scalar. -/
theorem physicalSecondJetD8NormalCore_oneLoop_normal
    (gaugeCore : VectorBundleCore ℝ (EffectiveThroat period hPeriod)
      GaugeFiber GaugeChart)
    (llCore : VectorBundleCore ℝ (EffectiveThroat period hPeriod)
      LLFiber LLChart)
    (metricCore : VectorBundleCore ℝ (EffectiveThroat period hPeriod)
      MetricFiber MetricChart)
    (spinCCore : VectorBundleCore ℝ (EffectiveThroat period hPeriod)
      SpinCFiber SpinCChart)
    (backgroundCore : VectorBundleCore ℝ (EffectiveThroat period hPeriod)
      BackgroundFiber BackgroundChart)
    (physicalChart : PhysicalCommonChart GaugeChart LLChart MetricChart SpinCChart)
    (backgroundChart : BackgroundChart)
    (anchor : ThroatCover period hPeriod)
    (vector : PhysicalSecondJetBackgroundNormalFiber
      (GaugeFiber := GaugeFiber) (LLFiber := LLFiber)
      (MetricFiber := MetricFiber) (SpinCFiber := SpinCFiber)
      (BackgroundFiber := BackgroundFiber) (NormalFiber := ℝ)) :
    ((physicalSecondJetD8NormalCore period hPeriod gaugeCore llCore metricCore
      spinCCore backgroundCore).coordChange
        { physical := physicalChart
          background := backgroundChart
          normal := anchor }
        { physical := physicalChart
          background := backgroundChart
          normal := (1 : ℤ) +ᵥ anchor }
        (mappingTorusMk (fixedEquatorData period hPeriod) anchor) vector).2 =
      -vector.2 := by
  change
    (fixedThroatNormalVectorBundleCore period hPeriod).coordChange anchor
        ((1 : ℤ) +ᵥ anchor)
        (mappingTorusMk (fixedEquatorData period hPeriod) anchor) vector.2 =
      -vector.2
  exact one_loop_coordChange_eq_neg_id period hPeriod anchor vector.2

/-- The selected `Z4` root transition squares to the normal projection of the
same complete one-loop coordinate change. -/
theorem physicalSecondJetD8NormalCore_z4_square
    (gaugeCore : VectorBundleCore ℝ (EffectiveThroat period hPeriod)
      GaugeFiber GaugeChart)
    (llCore : VectorBundleCore ℝ (EffectiveThroat period hPeriod)
      LLFiber LLChart)
    (metricCore : VectorBundleCore ℝ (EffectiveThroat period hPeriod)
      MetricFiber MetricChart)
    (spinCCore : VectorBundleCore ℝ (EffectiveThroat period hPeriod)
      SpinCFiber SpinCChart)
    (backgroundCore : VectorBundleCore ℝ (EffectiveThroat period hPeriod)
      BackgroundFiber BackgroundChart)
    (physicalChart : PhysicalCommonChart GaugeChart LLChart MetricChart SpinCChart)
    (backgroundChart : BackgroundChart)
    (choice : NormalRootChoice)
    (anchor : ThroatCover period hPeriod)
    (vector : PhysicalSecondJetBackgroundNormalFiber
      (GaugeFiber := GaugeFiber) (LLFiber := LLFiber)
      (MetricFiber := MetricFiber) (SpinCFiber := SpinCFiber)
      (BackgroundFiber := BackgroundFiber) (NormalFiber := ℝ)) :
    quarterRootCLM choice 1
        (quarterRootCLM choice 1 (vector.2 : ℂ)) =
      (((physicalSecondJetD8NormalCore period hPeriod gaugeCore llCore metricCore
        spinCCore backgroundCore).coordChange
          { physical := physicalChart
            background := backgroundChart
            normal := anchor }
          { physical := physicalChart
            background := backgroundChart
            normal := (1 : ℤ) +ᵥ anchor }
          (mappingTorusMk (fixedEquatorData period hPeriod) anchor) vector).2 : ℂ) := by
  rw [one_loop_root_transition_square]
  rw [physicalSecondJetD8NormalCore_oneLoop_normal period hPeriod gaugeCore llCore
    metricCore spinCCore backgroundCore physicalChart backgroundChart anchor vector]
  norm_num

end

end P0EFTJanusPhysicalSecondJetD8NonorientableNormalSlot
end JanusFormal
