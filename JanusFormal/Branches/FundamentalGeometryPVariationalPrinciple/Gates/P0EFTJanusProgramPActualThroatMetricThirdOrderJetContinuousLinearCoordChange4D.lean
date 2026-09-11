import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatMetricThirdOrderJetBundleCoordChange4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFramedThirdOrderJetNormedSpace4D

/-!
# Continuous-linear coordinate maps for actual throat metric third jets

Finite dimensionality of the normed framed third-jet carrier turns each
algebraic overlap map into a continuous linear map.  This gate records the
groupoid and truncation laws in that packaging.  Continuity with respect to
the base point is left to the next stage.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatMetricThirdOrderJetContinuousLinearCoordChange4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 600000
noncomputable section

open Set
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPFramedThirdOrderJetConstantFiberBaseChange4D
open P0EFTJanusProgramPActualThroatCovariantTwoTensorSecondOrderFrameOverlap4D
open P0EFTJanusProgramPActualThroatMetricSecondOrderJetBundleAtlasData4D
open P0EFTJanusProgramPActualThroatMetricSecondOrderJetBundleCoordChange4D
open P0EFTJanusProgramPActualThroatMetricThirdOrderJetBundleCoordChange4D

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev TensorModel :=
  FramedCovariantTwoTensor ThroatCoverCoordinates

attribute [local instance]
  P0EFTJanusProgramPActualThroatCovariantTwoTensorSecondOrderFrameOverlap4D.tensorModelNormedAddCommGroup
  P0EFTJanusProgramPActualThroatCovariantTwoTensorSecondOrderFrameOverlap4D.tensorModelNormedSpace

private abbrev MetricThirdJet :=
  FramedThirdOrderJet ThroatCoverCoordinates TensorModel

private abbrev BundleIndex :=
  ThroatMetricSecondOrderJetBundleIndex period hPeriod

/-- Continuous-linear packaging of the actual algebraic J3 coordinate map. -/
def throatMetricThirdOrderJetBundleContinuousCoordChange
    (first second : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod) :
    MetricThirdJet →L[Real] MetricThirdJet :=
  LinearMap.toContinuousLinearMap
    (throatMetricThirdOrderJetBundleCoordChange period hPeriod
      first second current)

@[simp]
theorem throatMetricThirdOrderJetBundleContinuousCoordChange_apply
    (first second : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod)
    (jet : MetricThirdJet) :
    throatMetricThirdOrderJetBundleContinuousCoordChange period hPeriod
        first second current jet =
      throatMetricThirdOrderJetBundleCoordChange period hPeriod
        first second current jet :=
  rfl

@[simp]
theorem throatMetricThirdOrderJetBundleContinuousCoordChange_self
    (index : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatMetricSecondOrderJetBundleBaseSet period hPeriod index) :
    throatMetricThirdOrderJetBundleContinuousCoordChange period hPeriod
        index index current =
      ContinuousLinearMap.id Real MetricThirdJet := by
  apply ContinuousLinearMap.ext
  intro jet
  simp only [throatMetricThirdOrderJetBundleContinuousCoordChange_apply,
    ContinuousLinearMap.id_apply]
  rw [throatMetricThirdOrderJetBundleCoordChange_self period hPeriod
    index current hCurrent]
  rfl

theorem throatMetricThirdOrderJetBundleContinuousCoordChange_comp
    (first middle last : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatMetricSecondOrderJetBundleBaseSet period hPeriod first ∩
        throatMetricSecondOrderJetBundleBaseSet period hPeriod middle ∩
        throatMetricSecondOrderJetBundleBaseSet period hPeriod last) :
    (throatMetricThirdOrderJetBundleContinuousCoordChange period hPeriod
        middle last current).comp
        (throatMetricThirdOrderJetBundleContinuousCoordChange period hPeriod
          first middle current) =
      throatMetricThirdOrderJetBundleContinuousCoordChange period hPeriod
        first last current := by
  apply ContinuousLinearMap.ext
  intro jet
  simpa only [ContinuousLinearMap.comp_apply,
    throatMetricThirdOrderJetBundleContinuousCoordChange_apply,
    LinearMap.comp_apply] using
    congrArg
      (fun change : MetricThirdJet →ₗ[Real] MetricThirdJet => change jet)
      (throatMetricThirdOrderJetBundleCoordChange_comp period hPeriod
        first middle last current hCurrent)

theorem throatMetricThirdOrderJetBundleContinuousCoordChange_inverse_comp
    (first second : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatMetricSecondOrderJetBundleBaseSet period hPeriod first ∩
        throatMetricSecondOrderJetBundleBaseSet period hPeriod second) :
    (throatMetricThirdOrderJetBundleContinuousCoordChange period hPeriod
        second first current).comp
        (throatMetricThirdOrderJetBundleContinuousCoordChange period hPeriod
          first second current) =
      ContinuousLinearMap.id Real MetricThirdJet := by
  apply ContinuousLinearMap.ext
  intro jet
  simpa only [ContinuousLinearMap.comp_apply,
    throatMetricThirdOrderJetBundleContinuousCoordChange_apply,
    ContinuousLinearMap.id_apply, LinearMap.comp_apply,
    LinearMap.id_apply] using
    congrArg
      (fun change : MetricThirdJet →ₗ[Real] MetricThirdJet => change jet)
      (throatMetricThirdOrderJetBundleCoordChange_inverse_comp period hPeriod
        first second current hCurrent)

theorem throatMetricThirdOrderJetBundleContinuousCoordChange_comp_inverse
    (first second : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatMetricSecondOrderJetBundleBaseSet period hPeriod first ∩
        throatMetricSecondOrderJetBundleBaseSet period hPeriod second) :
    (throatMetricThirdOrderJetBundleContinuousCoordChange period hPeriod
        first second current).comp
        (throatMetricThirdOrderJetBundleContinuousCoordChange period hPeriod
          second first current) =
      ContinuousLinearMap.id Real MetricThirdJet := by
  apply ContinuousLinearMap.ext
  intro jet
  simpa only [ContinuousLinearMap.comp_apply,
    throatMetricThirdOrderJetBundleContinuousCoordChange_apply,
    ContinuousLinearMap.id_apply, LinearMap.comp_apply,
    LinearMap.id_apply] using
    congrArg
      (fun change : MetricThirdJet →ₗ[Real] MetricThirdJet => change jet)
      (throatMetricThirdOrderJetBundleCoordChange_comp_inverse period hPeriod
        first second current hCurrent)

/-- Continuous-linear packaging preserves the exact J3-to-J2 truncation law. -/
@[simp]
theorem throatMetricThirdOrderJetBundleContinuousCoordChange_truncate_apply_of_mem
    (first second : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatMetricSecondOrderJetBundleBaseSet period hPeriod first ∩
        throatMetricSecondOrderJetBundleBaseSet period hPeriod second)
    (jet : MetricThirdJet) :
    (throatMetricThirdOrderJetBundleContinuousCoordChange period hPeriod
      first second current jet).toFramedSecondOrderJet =
      throatMetricSecondOrderJetBundleCoordChange period hPeriod
        first second current jet.toFramedSecondOrderJet := by
  rw [throatMetricThirdOrderJetBundleContinuousCoordChange_apply]
  exact throatMetricThirdOrderJetBundleCoordChange_truncate_apply_of_mem
    period hPeriod first second current hCurrent jet

end
end P0EFTJanusProgramPActualThroatMetricThirdOrderJetContinuousLinearCoordChange4D
end JanusFormal
