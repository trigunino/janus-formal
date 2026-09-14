import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatSpinCThirdOrderJetBundleCoordChange4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFramedThirdOrderJetNormedSpace4D

/-!
# Continuous-linear coordinate maps for actual throat SpinC third jets

Finite dimensionality of the normed framed third-jet carrier turns each
algebraic overlap map into a continuous linear map.  This gate records the
groupoid and truncation laws in that packaging.  Continuity with respect to
the base point is left to the next stage.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatSpinCThirdOrderJetContinuousLinearCoordChange4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 600000
noncomputable section

open Set
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPFramedThirdOrderJetConstantFiberBaseChange4D
open P0EFTJanusProgramPActualThroatSpinCSecondOrderJetBundleAtlasData4D
open P0EFTJanusProgramPActualThroatSpinCSecondOrderJetBundleCoordChange4D
open P0EFTJanusProgramPActualThroatSpinCThirdOrderJetBundleCoordChange4D

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

variable (period : Real) (hPeriod : period ≠ 0)
variable (choice : NormalRootChoice)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev SpinCThirdJet :=
  FramedThirdOrderJet ThroatCoverCoordinates D9DoubledMatterFiber

private abbrev BundleIndex :=
  ThroatSpinCSecondOrderJetBundleIndex period hPeriod

/-- Continuous-linear packaging of the actual algebraic SpinC J3 coordinate
map. -/
def throatSpinCThirdOrderJetBundleContinuousCoordChange
    (first second : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod) :
    SpinCThirdJet →L[Real] SpinCThirdJet :=
  LinearMap.toContinuousLinearMap
    (throatSpinCThirdOrderJetBundleCoordChange period hPeriod choice
      first second current)

@[simp]
theorem throatSpinCThirdOrderJetBundleContinuousCoordChange_apply
    (first second : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod)
    (jet : SpinCThirdJet) :
    throatSpinCThirdOrderJetBundleContinuousCoordChange period hPeriod choice
        first second current jet =
      throatSpinCThirdOrderJetBundleCoordChange period hPeriod choice
        first second current jet :=
  rfl

@[simp]
theorem throatSpinCThirdOrderJetBundleContinuousCoordChange_self
    (index : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatSpinCSecondOrderJetBundleBaseSet period hPeriod index) :
    throatSpinCThirdOrderJetBundleContinuousCoordChange period hPeriod choice
        index index current =
      ContinuousLinearMap.id Real SpinCThirdJet := by
  apply ContinuousLinearMap.ext
  intro jet
  simp only [throatSpinCThirdOrderJetBundleContinuousCoordChange_apply,
    ContinuousLinearMap.id_apply]
  rw [throatSpinCThirdOrderJetBundleCoordChange_self period hPeriod choice
    index current hCurrent]
  rfl

theorem throatSpinCThirdOrderJetBundleContinuousCoordChange_comp
    (first middle last : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatSpinCSecondOrderJetBundleBaseSet period hPeriod first ∩
        throatSpinCSecondOrderJetBundleBaseSet period hPeriod middle ∩
        throatSpinCSecondOrderJetBundleBaseSet period hPeriod last) :
    (throatSpinCThirdOrderJetBundleContinuousCoordChange period hPeriod choice
        middle last current).comp
        (throatSpinCThirdOrderJetBundleContinuousCoordChange period hPeriod choice
          first middle current) =
      throatSpinCThirdOrderJetBundleContinuousCoordChange period hPeriod choice
        first last current := by
  apply ContinuousLinearMap.ext
  intro jet
  simpa only [ContinuousLinearMap.comp_apply,
    throatSpinCThirdOrderJetBundleContinuousCoordChange_apply,
    LinearMap.comp_apply] using
    congrArg
      (fun change : SpinCThirdJet →ₗ[Real] SpinCThirdJet => change jet)
      (throatSpinCThirdOrderJetBundleCoordChange_comp period hPeriod choice
        first middle last current hCurrent)

theorem throatSpinCThirdOrderJetBundleContinuousCoordChange_inverse_comp
    (first second : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatSpinCSecondOrderJetBundleBaseSet period hPeriod first ∩
        throatSpinCSecondOrderJetBundleBaseSet period hPeriod second) :
    (throatSpinCThirdOrderJetBundleContinuousCoordChange period hPeriod choice
        second first current).comp
        (throatSpinCThirdOrderJetBundleContinuousCoordChange period hPeriod choice
          first second current) =
      ContinuousLinearMap.id Real SpinCThirdJet := by
  apply ContinuousLinearMap.ext
  intro jet
  simpa only [ContinuousLinearMap.comp_apply,
    throatSpinCThirdOrderJetBundleContinuousCoordChange_apply,
    ContinuousLinearMap.id_apply, LinearMap.comp_apply,
    LinearMap.id_apply] using
    congrArg
      (fun change : SpinCThirdJet →ₗ[Real] SpinCThirdJet => change jet)
      (throatSpinCThirdOrderJetBundleCoordChange_inverse_comp period hPeriod
        choice first second current hCurrent)

theorem throatSpinCThirdOrderJetBundleContinuousCoordChange_comp_inverse
    (first second : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatSpinCSecondOrderJetBundleBaseSet period hPeriod first ∩
        throatSpinCSecondOrderJetBundleBaseSet period hPeriod second) :
    (throatSpinCThirdOrderJetBundleContinuousCoordChange period hPeriod choice
        first second current).comp
        (throatSpinCThirdOrderJetBundleContinuousCoordChange period hPeriod choice
          second first current) =
      ContinuousLinearMap.id Real SpinCThirdJet := by
  apply ContinuousLinearMap.ext
  intro jet
  simpa only [ContinuousLinearMap.comp_apply,
    throatSpinCThirdOrderJetBundleContinuousCoordChange_apply,
    ContinuousLinearMap.id_apply, LinearMap.comp_apply,
    LinearMap.id_apply] using
    congrArg
      (fun change : SpinCThirdJet →ₗ[Real] SpinCThirdJet => change jet)
      (throatSpinCThirdOrderJetBundleCoordChange_comp_inverse period hPeriod
        choice first second current hCurrent)

/-- Continuous-linear packaging preserves the exact SpinC J3-to-J2
truncation law. -/
@[simp]
theorem throatSpinCThirdOrderJetBundleContinuousCoordChange_truncate_apply_of_mem
    (first second : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatSpinCSecondOrderJetBundleBaseSet period hPeriod first ∩
        throatSpinCSecondOrderJetBundleBaseSet period hPeriod second)
    (jet : SpinCThirdJet) :
    (throatSpinCThirdOrderJetBundleContinuousCoordChange period hPeriod choice
      first second current jet).toFramedSecondOrderJet =
      throatSpinCSecondOrderJetBundleCoordChange period hPeriod choice
        first second current jet.toFramedSecondOrderJet := by
  rw [throatSpinCThirdOrderJetBundleContinuousCoordChange_apply]
  exact throatSpinCThirdOrderJetBundleCoordChange_truncate_apply_of_mem
    period hPeriod choice first second current hCurrent jet

end
end P0EFTJanusProgramPActualThroatSpinCThirdOrderJetContinuousLinearCoordChange4D
end JanusFormal
