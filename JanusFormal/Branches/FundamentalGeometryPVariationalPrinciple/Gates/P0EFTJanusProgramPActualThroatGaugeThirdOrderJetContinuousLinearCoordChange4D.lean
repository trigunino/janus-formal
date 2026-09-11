import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeThirdOrderJetBundleCoordChange4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFramedThirdOrderJetNormedSpace4D

/-!
# Continuous-linear coordinate maps for actual throat gauge third jets

Finite dimensionality of the normed framed third-jet carrier turns each
algebraic overlap map into a continuous linear map.  This gate records the
groupoid and truncation laws in that packaging.  Continuity with respect to
the base point is left to the next stage.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatGaugeThirdOrderJetContinuousLinearCoordChange4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 600000
noncomputable section

open Set
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPFramedThirdOrderJetConstantFiberBaseChange4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetBundleAtlasData4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetBundleCoordChange4D
open P0EFTJanusProgramPActualThroatGaugeThirdOrderJetBundleCoordChange4D

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev GaugeThirdJet :=
  FramedThirdOrderJet ThroatCoverCoordinates
    (FramedCovector ThroatCoverCoordinates)

private abbrev BundleIndex :=
  ThroatGaugeSecondOrderJetBundleIndex period hPeriod

/-- Continuous-linear packaging of the actual algebraic J3 coordinate map. -/
def throatGaugeThirdOrderJetBundleContinuousCoordChange
    (first second : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod) :
    GaugeThirdJet →L[Real] GaugeThirdJet :=
  LinearMap.toContinuousLinearMap
    (throatGaugeThirdOrderJetBundleCoordChange period hPeriod
      first second current)

@[simp]
theorem throatGaugeThirdOrderJetBundleContinuousCoordChange_apply
    (first second : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod)
    (jet : GaugeThirdJet) :
    throatGaugeThirdOrderJetBundleContinuousCoordChange period hPeriod
        first second current jet =
      throatGaugeThirdOrderJetBundleCoordChange period hPeriod
        first second current jet :=
  rfl

@[simp]
theorem throatGaugeThirdOrderJetBundleContinuousCoordChange_self
    (index : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatGaugeSecondOrderJetBundleBaseSet period hPeriod index) :
    throatGaugeThirdOrderJetBundleContinuousCoordChange period hPeriod
        index index current =
      ContinuousLinearMap.id Real GaugeThirdJet := by
  apply ContinuousLinearMap.ext
  intro jet
  simp only [throatGaugeThirdOrderJetBundleContinuousCoordChange_apply,
    ContinuousLinearMap.id_apply]
  rw [throatGaugeThirdOrderJetBundleCoordChange_self period hPeriod
    index current hCurrent]
  rfl

theorem throatGaugeThirdOrderJetBundleContinuousCoordChange_comp
    (first middle last : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatGaugeSecondOrderJetBundleBaseSet period hPeriod first ∩
        throatGaugeSecondOrderJetBundleBaseSet period hPeriod middle ∩
        throatGaugeSecondOrderJetBundleBaseSet period hPeriod last) :
    (throatGaugeThirdOrderJetBundleContinuousCoordChange period hPeriod
        middle last current).comp
        (throatGaugeThirdOrderJetBundleContinuousCoordChange period hPeriod
          first middle current) =
      throatGaugeThirdOrderJetBundleContinuousCoordChange period hPeriod
        first last current := by
  apply ContinuousLinearMap.ext
  intro jet
  simpa only [ContinuousLinearMap.comp_apply,
    throatGaugeThirdOrderJetBundleContinuousCoordChange_apply,
    LinearMap.comp_apply] using
    congrArg
      (fun change : GaugeThirdJet →ₗ[Real] GaugeThirdJet => change jet)
      (throatGaugeThirdOrderJetBundleCoordChange_comp period hPeriod
        first middle last current hCurrent)

theorem throatGaugeThirdOrderJetBundleContinuousCoordChange_inverse_comp
    (first second : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatGaugeSecondOrderJetBundleBaseSet period hPeriod first ∩
        throatGaugeSecondOrderJetBundleBaseSet period hPeriod second) :
    (throatGaugeThirdOrderJetBundleContinuousCoordChange period hPeriod
        second first current).comp
        (throatGaugeThirdOrderJetBundleContinuousCoordChange period hPeriod
          first second current) =
      ContinuousLinearMap.id Real GaugeThirdJet := by
  apply ContinuousLinearMap.ext
  intro jet
  simpa only [ContinuousLinearMap.comp_apply,
    throatGaugeThirdOrderJetBundleContinuousCoordChange_apply,
    ContinuousLinearMap.id_apply, LinearMap.comp_apply,
    LinearMap.id_apply] using
    congrArg
      (fun change : GaugeThirdJet →ₗ[Real] GaugeThirdJet => change jet)
      (throatGaugeThirdOrderJetBundleCoordChange_inverse_comp period hPeriod
        first second current hCurrent)

theorem throatGaugeThirdOrderJetBundleContinuousCoordChange_comp_inverse
    (first second : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatGaugeSecondOrderJetBundleBaseSet period hPeriod first ∩
        throatGaugeSecondOrderJetBundleBaseSet period hPeriod second) :
    (throatGaugeThirdOrderJetBundleContinuousCoordChange period hPeriod
        first second current).comp
        (throatGaugeThirdOrderJetBundleContinuousCoordChange period hPeriod
          second first current) =
      ContinuousLinearMap.id Real GaugeThirdJet := by
  apply ContinuousLinearMap.ext
  intro jet
  simpa only [ContinuousLinearMap.comp_apply,
    throatGaugeThirdOrderJetBundleContinuousCoordChange_apply,
    ContinuousLinearMap.id_apply, LinearMap.comp_apply,
    LinearMap.id_apply] using
    congrArg
      (fun change : GaugeThirdJet →ₗ[Real] GaugeThirdJet => change jet)
      (throatGaugeThirdOrderJetBundleCoordChange_comp_inverse period hPeriod
        first second current hCurrent)

/-- Continuous-linear packaging preserves the exact J3-to-J2 truncation law. -/
@[simp]
theorem throatGaugeThirdOrderJetBundleContinuousCoordChange_truncate_apply_of_mem
    (first second : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatGaugeSecondOrderJetBundleBaseSet period hPeriod first ∩
        throatGaugeSecondOrderJetBundleBaseSet period hPeriod second)
    (jet : GaugeThirdJet) :
    (throatGaugeThirdOrderJetBundleContinuousCoordChange period hPeriod
      first second current jet).toFramedSecondOrderJet =
      throatGaugeSecondOrderJetBundleCoordChange period hPeriod
        first second current jet.toFramedSecondOrderJet := by
  rw [throatGaugeThirdOrderJetBundleContinuousCoordChange_apply]
  exact throatGaugeThirdOrderJetBundleCoordChange_truncate_apply_of_mem
    period hPeriod first second current hCurrent jet

end
end P0EFTJanusProgramPActualThroatGaugeThirdOrderJetContinuousLinearCoordChange4D
end JanusFormal
