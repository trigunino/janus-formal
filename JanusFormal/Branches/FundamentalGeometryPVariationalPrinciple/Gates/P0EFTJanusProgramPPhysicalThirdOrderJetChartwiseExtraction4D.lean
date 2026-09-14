import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPhysicalSecondOrderJetChartwiseExtraction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFramedThirdOrderJetConstantFiberBaseChange4D

/-!
# Chartwise extraction of physical third-order jets

This gate extends the chartwise second-jet extractor by the genuine third
Frechet derivative of a `C^3` coordinate representative.  The two adjacent
symmetries follow from Schwarz symmetry.

The throat wrapper remains local to one fixed base chart and one fixed SpinC
fiber trivialization.  No overlap law or global jet-bundle section is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPPhysicalThirdOrderJetChartwiseExtraction4D

set_option autoImplicit false
noncomputable section

open scoped Topology
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPPhysicalSecondOrderJetChartwiseExtraction4D
open P0EFTJanusProgramPFramedThirdOrderJetConstantFiberBaseChange4D

variable {Domain Fiber : Type*}
  [NormedAddCommGroup Domain] [NormedSpace Real Domain]
  [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]

private theorem fderiv_continuousLinearMap_apply_const
    {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E]
    [NormedAddCommGroup F] [NormedSpace Real F]
    [NormedAddCommGroup G] [NormedSpace Real G]
    (maps : E → F →L[Real] G) (point direction : E) (vector : F)
    (hMaps : DifferentiableAt Real maps point) :
    fderiv Real (fun current => maps current vector) point direction =
      fderiv Real maps point direction vector := by
  let evaluation : (F →L[Real] G) →L[Real] G :=
    ContinuousLinearMap.apply Real G vector
  have hDerivative :
      fderiv Real (evaluation ∘ maps) point =
        evaluation.comp (fderiv Real maps point) :=
    (evaluation.hasFDerivAt.comp point hMaps.hasFDerivAt).fderiv
  have hFunction :
      evaluation ∘ maps = fun current => maps current vector := by
    funext current
    rfl
  rw [hFunction] at hDerivative
  have hApply := congrArg
    (fun derivative : E →L[Real] G => derivative direction) hDerivative
  simpa only [evaluation, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply] using hApply

private theorem thirdFDeriv_swap_first_second
    (field : Domain → Fiber) (point first second third : Domain)
    (regularity : ContDiffAt Real 3 field point) :
    fderiv Real (fderiv Real (fderiv Real field)) point first second third =
      fderiv Real (fderiv Real (fderiv Real field))
        point second first third := by
  have hFirstDerivative :
      ContDiffAt Real 2 (fderiv Real field) point :=
    regularity.fderiv_right (m := 2) (by norm_num)
  have hSymmetric :=
    (hFirstDerivative.isSymmSndFDerivAt (by norm_num)).eq first second
  exact congrArg
    (fun derivative : Domain →L[Real] Fiber => derivative third) hSymmetric

private theorem thirdFDeriv_swap_second_third
    (field : Domain → Fiber) (point first second third : Domain)
    (regularity : ContDiffAt Real 3 field point) :
    fderiv Real (fderiv Real (fderiv Real field)) point first second third =
      fderiv Real (fderiv Real (fderiv Real field))
        point first third second := by
  have hHessian :
      DifferentiableAt Real (fderiv Real (fderiv Real field)) point :=
    ((regularity.fderiv_right (m := 2) (by norm_num)).fderiv_right
      (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hHessianAtSecond :
      DifferentiableAt Real
        (fun nearby => fderiv Real (fderiv Real field) nearby second) point :=
    hHessian.clm_apply (differentiableAt_const (c := second))
  have hHessianAtThird :
      DifferentiableAt Real
        (fun nearby => fderiv Real (fderiv Real field) nearby third) point :=
    hHessian.clm_apply (differentiableAt_const (c := third))
  have hNearbySymmetry :
      Filter.EventuallyEq (𝓝 point)
        (fun nearby => fderiv Real (fderiv Real field) nearby second third)
        (fun nearby => fderiv Real (fderiv Real field) nearby third second) := by
    filter_upwards [regularity.eventually (by norm_num)] with nearby hNearby
    exact (hNearby.isSymmSndFDerivAt (𝕜 := Real) (by norm_num)).eq second third
  have hDerivativeEquality := hNearbySymmetry.fderiv_eq (𝕜 := Real)
  have hApplied := congrArg
    (fun derivative : Domain →L[Real] Fiber => derivative first)
      hDerivativeEquality
  have hOuterSecond :
      fderiv Real
          (fun nearby => fderiv Real (fderiv Real field) nearby second)
          point first =
        fderiv Real (fderiv Real (fderiv Real field)) point first second :=
    fderiv_continuousLinearMap_apply_const _ point first second hHessian
  have hOuterThird :
      fderiv Real
          (fun nearby => fderiv Real (fderiv Real field) nearby third)
          point first =
        fderiv Real (fderiv Real (fderiv Real field)) point first third :=
    fderiv_continuousLinearMap_apply_const _ point first third hHessian
  have hSecondThird :
      fderiv Real
          (fun nearby => fderiv Real (fderiv Real field) nearby second third)
          point first =
        fderiv Real (fderiv Real (fderiv Real field))
          point first second third := by
    calc
      _ = fderiv Real
          (fun nearby => fderiv Real (fderiv Real field) nearby second)
          point first third :=
        fderiv_continuousLinearMap_apply_const _ point first third
          hHessianAtSecond
      _ = _ := congrArg (fun derivative : Domain →L[Real] Fiber =>
        derivative third) hOuterSecond
  have hThirdSecond :
      fderiv Real
          (fun nearby => fderiv Real (fderiv Real field) nearby third second)
          point first =
        fderiv Real (fderiv Real (fderiv Real field))
          point first third second := by
    calc
      _ = fderiv Real
          (fun nearby => fderiv Real (fderiv Real field) nearby third)
          point first second :=
        fderiv_continuousLinearMap_apply_const _ point first second
          hHessianAtThird
      _ = _ := congrArg (fun derivative : Domain →L[Real] Fiber =>
        derivative second) hOuterThird
  rw [hSecondThird, hThirdSecond] at hApplied
  exact hApplied

/-- The actual value and first three Frechet derivatives of a `C^3`
coordinate representative at one chart point. -/
def chartwiseThirdOrderJetAt
    (field : Domain → Fiber) (point : Domain)
    (regularity : ContDiffAt Real 3 field point) :
    FramedThirdOrderJet Domain Fiber where
  toFramedSecondOrderJet :=
    chartwiseSecondOrderJetAt field point
      (regularity.of_le (by norm_num))
  thirdDerivative := fderiv Real (fderiv Real (fderiv Real field)) point
  thirdDerivative_swap_first_second := fun first second third =>
    thirdFDeriv_swap_first_second field point first second third regularity
  thirdDerivative_swap_second_third := fun first second third =>
    thirdFDeriv_swap_second_third field point first second third regularity

@[simp]
theorem chartwiseThirdOrderJetAt_value
    (field : Domain → Fiber) (point : Domain)
    (regularity : ContDiffAt Real 3 field point) :
    (chartwiseThirdOrderJetAt field point regularity).value = field point :=
  rfl

@[simp]
theorem chartwiseThirdOrderJetAt_firstDerivative
    (field : Domain → Fiber) (point : Domain)
    (regularity : ContDiffAt Real 3 field point) :
    (chartwiseThirdOrderJetAt field point regularity).firstDerivative =
      fderiv Real field point :=
  rfl

@[simp]
theorem chartwiseThirdOrderJetAt_secondDerivative
    (field : Domain → Fiber) (point : Domain)
    (regularity : ContDiffAt Real 3 field point) :
    (chartwiseThirdOrderJetAt field point regularity).secondDerivative =
      fderiv Real (fderiv Real field) point :=
  rfl

@[simp]
theorem chartwiseThirdOrderJetAt_thirdDerivative
    (field : Domain → Fiber) (point : Domain)
    (regularity : ContDiffAt Real 3 field point) :
    (chartwiseThirdOrderJetAt field point regularity).thirdDerivative =
      fderiv Real (fderiv Real (fderiv Real field)) point :=
  rfl

@[simp]
theorem chartwiseThirdOrderJetAt_toFramedSecondOrderJet
    (field : Domain → Fiber) (point : Domain)
    (regularity : ContDiffAt Real 3 field point) :
    (chartwiseThirdOrderJetAt field point regularity).toFramedSecondOrderJet =
      chartwiseSecondOrderJetAt field point
        (regularity.of_le (by norm_num)) :=
  rfl

/-- Global `C^3` regularity supplies the pointwise chartwise constructor. -/
def chartwiseThirdOrderJet
    (field : Domain → Fiber) (regularity : ContDiff Real 3 field)
    (point : Domain) :
    FramedThirdOrderJet Domain Fiber :=
  chartwiseThirdOrderJetAt field point regularity.contDiffAt

@[simp]
theorem chartwiseThirdOrderJet_value
    (field : Domain → Fiber) (regularity : ContDiff Real 3 field)
    (point : Domain) :
    (chartwiseThirdOrderJet field regularity point).value = field point :=
  rfl

@[simp]
theorem chartwiseThirdOrderJet_firstDerivative
    (field : Domain → Fiber) (regularity : ContDiff Real 3 field)
    (point : Domain) :
    (chartwiseThirdOrderJet field regularity point).firstDerivative =
      fderiv Real field point :=
  rfl

@[simp]
theorem chartwiseThirdOrderJet_secondDerivative
    (field : Domain → Fiber) (regularity : ContDiff Real 3 field)
    (point : Domain) :
    (chartwiseThirdOrderJet field regularity point).secondDerivative =
      fderiv Real (fderiv Real field) point :=
  rfl

@[simp]
theorem chartwiseThirdOrderJet_thirdDerivative
    (field : Domain → Fiber) (regularity : ContDiff Real 3 field)
    (point : Domain) :
    (chartwiseThirdOrderJet field regularity point).thirdDerivative =
      fderiv Real (fderiv Real (fderiv Real field)) point :=
  rfl

@[simp]
theorem chartwiseThirdOrderJet_toFramedSecondOrderJet
    (field : Domain → Fiber) (regularity : ContDiff Real 3 field)
    (point : Domain) :
    (chartwiseThirdOrderJet field regularity point).toFramedSecondOrderJet =
      chartwiseSecondOrderJet field (regularity.of_le (by norm_num)) point :=
  rfl

/-- SpinC matter third jet in a selected throat chart and selected bundle
trivialization. -/
def fixedTrivializationSpinCMatterThirdOrderJetAt
    (field : ThroatCoverCoordinates → D9DoubledMatterFiber)
    (point : ThroatCoverCoordinates)
    (regularity : ContDiffAt Real 3 field point) :
    FramedThirdOrderJet ThroatCoverCoordinates D9DoubledMatterFiber :=
  chartwiseThirdOrderJetAt field point regularity

@[simp]
theorem fixedTrivializationSpinCMatterThirdOrderJetAt_toFramedSecondOrderJet
    (field : ThroatCoverCoordinates → D9DoubledMatterFiber)
    (point : ThroatCoverCoordinates)
    (regularity : ContDiffAt Real 3 field point) :
    (fixedTrivializationSpinCMatterThirdOrderJetAt
      field point regularity).toFramedSecondOrderJet =
      fixedTrivializationSpinCMatterJetAt field point
        (regularity.of_le (by norm_num)) :=
  rfl

end
end P0EFTJanusProgramPPhysicalThirdOrderJetChartwiseExtraction4D
end JanusFormal
