import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06SecondOrderHorizontalDivergenceEulerSoundness4D

/-!
# Higher Frechet derivatives of a second-order horizontal divergence

This file expands the first three derivatives of a summand
`fderiv current_i (A z) (B_i z)`.  Here `A` is fourth-to-third jet
truncation and `B_i` is the fourth-to-third formal total-derivative shift.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06HorizontalCurrentDivergenceHigherFrechet4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000
set_option maxRecDepth 100000
noncomputable section

open scoped BigOperators ContDiff
open P0EFTJanusProgramPT06ThroatSpatialFinsuppJetTower4D
open P0EFTJanusProgramPT06LocalFunctionTotalDerivative4D
open P0EFTJanusProgramPT06SecondOrderRadialCartanHomotopy4D
open P0EFTJanusProgramPT06SecondOrderHorizontalDivergenceEulerSoundness4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

universe u

variable {Fiber : Type u} [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]

private abbrev ThirdJet := ThroatSpatialMultiindexJet3 Fiber
private abbrev FourthJet := ThroatSpatialMultiindexJet4 Fiber

/-- One directional summand of the fourth-jet horizontal divergence. -/
def programPT06SecondOrderHorizontalCurrentDHSummand
    (current : ProgramPT06SecondOrderHorizontalCurrent4D (Fiber := Fiber))
    (direction : Fin 3) : FourthJet (Fiber := Fiber) → Real :=
  fun jet =>
    fderiv Real (current direction)
      (programPT06FourthJetToThirdJetContinuousLinearMap
        (Fiber := Fiber) jet)
      (programPT06FourthJetTotalDerivativeContinuousLinearMap
        (Fiber := Fiber) direction jet)

@[simp] theorem programPT06SecondOrderHorizontalCurrentDHSummand_eq
    (current : ProgramPT06SecondOrderHorizontalCurrent4D (Fiber := Fiber))
    (direction : Fin 3) (jet : FourthJet (Fiber := Fiber)) :
    programPT06SecondOrderHorizontalCurrentDHSummand current direction jet =
      programPT06ThroatSpatialLocalFunctionTotalDerivative
        direction (current direction) jet := by
  rfl

theorem programPT06SecondOrderHorizontalCurrentDH_eq_sum_summand
    (current : ProgramPT06SecondOrderHorizontalCurrent4D (Fiber := Fiber)) :
    programPT06SecondOrderHorizontalCurrentDH current =
      fun jet => ∑ direction : Fin 3,
        programPT06SecondOrderHorizontalCurrentDHSummand
          current direction jet := by
  rfl

section LinearContraction

variable {X Y : Type*}
  [NormedAddCommGroup X] [NormedSpace Real X]
  [NormedAddCommGroup Y] [NormedSpace Real Y]

private def linearDerivativeContraction
    (field : X → Y →L[Real] Real) (tangent : X →L[Real] Y) : X → Real :=
  fun point => field point (tangent point)

private theorem linearDerivativeContraction_contDiff_three
    (field : X → Y →L[Real] Real) (tangent : X →L[Real] Y)
    (hField : ContDiff Real 3 field) :
    ContDiff Real 3 (linearDerivativeContraction field tangent) := by
  exact hField.clm_apply tangent.contDiff

private theorem linearDerivativeContraction_fderiv_iterated
    (field : X → Y →L[Real] Real) (tangent : X →L[Real] Y)
    (hField : ContDiff Real 3 field)
    (order : Nat) (hOrder : order < 3)
    (point variation : X) (arguments : Fin order → X) :
    fderiv Real
        (fun candidate =>
          iteratedFDeriv Real order field candidate arguments
            (tangent candidate))
        point variation =
      iteratedFDeriv Real (order + 1) field point
          (Matrix.vecCons variation arguments) (tangent point) +
        iteratedFDeriv Real order field point arguments
          (tangent variation) := by
  have hIterated : Differentiable Real
      (fun candidate => iteratedFDeriv Real order field candidate) :=
    hField.differentiable_iteratedFDeriv (by exact_mod_cast hOrder)
  have hEvaluated : DifferentiableAt Real
      (fun candidate => iteratedFDeriv Real order field candidate arguments)
      point :=
    (hIterated point).continuousMultilinear_apply_const arguments
  have hProduct := fderiv_clm_apply hEvaluated tangent.differentiableAt
  have hApplied := congrArg
    (fun derivative : X →L[Real] Real => derivative variation) hProduct
  have hHigher :
      fderiv Real
          (fun candidate =>
            iteratedFDeriv Real order field candidate arguments)
          point variation =
        iteratedFDeriv Real (order + 1) field point
          (Matrix.vecCons variation arguments) := by
    rw [fderiv_continuousMultilinear_apply_const_apply
      (hIterated point) arguments variation]
    symm
    simpa using
      (iteratedFDeriv_succ_apply_left
        (f := field) (x := point)
        (Matrix.vecCons variation arguments))
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.fderiv] at hApplied
  rw [hHigher] at hApplied
  exact hApplied.trans (add_comm _ _)

private theorem linearDerivativeContraction_fderiv_fixed
    (field : X → Y →L[Real] Real)
    (hField : ContDiff Real 3 field)
    (order : Nat) (hOrder : order < 3)
    (point variation : X) (arguments : Fin order → X) (fixed : Y) :
    fderiv Real
        (fun candidate =>
          iteratedFDeriv Real order field candidate arguments fixed)
        point variation =
      iteratedFDeriv Real (order + 1) field point
        (Matrix.vecCons variation arguments) fixed := by
  have hIterated : Differentiable Real
      (fun candidate => iteratedFDeriv Real order field candidate) :=
    hField.differentiable_iteratedFDeriv (by exact_mod_cast hOrder)
  have hEvaluated : DifferentiableAt Real
      (fun candidate => iteratedFDeriv Real order field candidate arguments)
      point :=
    (hIterated point).continuousMultilinear_apply_const arguments
  have hApply := fderiv_clm_apply hEvaluated
    (differentiableAt_const (c := fixed))
  have hApplied := congrArg
    (fun derivative : X →L[Real] Real => derivative variation) hApply
  have hHigher :
      fderiv Real
          (fun candidate =>
            iteratedFDeriv Real order field candidate arguments)
          point variation =
        iteratedFDeriv Real (order + 1) field point
          (Matrix.vecCons variation arguments) := by
    rw [fderiv_continuousMultilinear_apply_const_apply
      (hIterated point) arguments variation]
    symm
    simpa using
      (iteratedFDeriv_succ_apply_left
        (f := field) (x := point)
        (Matrix.vecCons variation arguments))
  have hFixed :
      fderiv Real (fun _ : X => fixed) point = 0 :=
    fderiv_const_apply (𝕜 := Real) (x := point) fixed
  rw [hFixed] at hApplied
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, zero_apply, map_zero, zero_add] at hApplied
  rw [hHigher] at hApplied
  exact hApplied

private theorem linearDerivativeContraction_iteratedFDeriv_one
    (field : X → Y →L[Real] Real) (tangent : X →L[Real] Y)
    (hField : ContDiff Real 3 field)
    (point first : X) :
    iteratedFDeriv Real 1 (linearDerivativeContraction field tangent)
        point ![first] =
      iteratedFDeriv Real 1 field point ![first] (tangent point) +
        field point (tangent first) := by
  have hRaw := linearDerivativeContraction_fderiv_iterated
    field tangent hField 0 (by norm_num) point first
      (fun slot : Fin 0 => Fin.elim0 slot)
  have hOne :
      iteratedFDeriv Real (0 + 1) field point
          (Matrix.vecCons first (fun slot : Fin 0 => Fin.elim0 slot)) =
        fderiv Real field point first := by
    simp
  rw [hOne] at hRaw
  simp only [iteratedFDeriv_one_apply, iteratedFDeriv_zero_apply] at hRaw ⊢
  change
    fderiv Real (fun candidate => field candidate (tangent candidate))
      point first = _
  exact hRaw

private theorem linearDerivativeContraction_iteratedFDeriv_two
    (field : X → Y →L[Real] Real) (tangent : X →L[Real] Y)
    (hField : ContDiff Real 3 field)
    (point first second : X) :
    iteratedFDeriv Real 2 (linearDerivativeContraction field tangent)
        point ![first, second] =
      iteratedFDeriv Real 2 field point ![first, second]
          (tangent point) +
        iteratedFDeriv Real 1 field point ![first] (tangent second) +
        iteratedFDeriv Real 1 field point ![second] (tangent first) := by
  have hContraction : ContDiff Real 3
      (linearDerivativeContraction field tangent) :=
    linearDerivativeContraction_contDiff_three field tangent hField
  have hFunctions :
      (fun candidate =>
        iteratedFDeriv Real 1 (linearDerivativeContraction field tangent)
          candidate ![second]) =
      (fun candidate =>
        iteratedFDeriv Real 1 field candidate ![second]
            (tangent candidate) +
          field candidate (tangent second)) := by
    funext candidate
    exact linearDerivativeContraction_iteratedFDeriv_one
      field tangent hField candidate second
  have hLeft :
      iteratedFDeriv Real 2 (linearDerivativeContraction field tangent)
          point ![first, second] =
        fderiv Real
          (fun candidate =>
            iteratedFDeriv Real 1
              (linearDerivativeContraction field tangent)
              candidate ![second]) point first := by
    rw [iteratedFDeriv_succ_apply_left]
    symm
    simpa using
      (fderiv_continuousMultilinear_apply_const_apply
        (hContraction.differentiable_iteratedFDeriv (by norm_num) point)
        ![second] first)
  have hFirstTerm : DifferentiableAt Real
      (fun candidate =>
        iteratedFDeriv Real 1 field candidate ![second]
          (tangent candidate)) point := by
    exact ((hField.differentiable_iteratedFDeriv (by norm_num) point)
      |>.continuousMultilinear_apply_const ![second]).clm_apply
        tangent.differentiableAt
  have hSecondTerm : DifferentiableAt Real
      (fun candidate => field candidate (tangent second)) point := by
    exact (hField.differentiable (by norm_num) point).clm_apply
      (differentiableAt_const (c := tangent second))
  have hFirstDerivative := linearDerivativeContraction_fderiv_iterated
    field tangent hField 1 (by norm_num) point first ![second]
  have hSecondDerivative :
      fderiv Real (fun candidate => field candidate (tangent second))
          point first =
        iteratedFDeriv Real 1 field point ![first] (tangent second) := by
    simpa using
      (linearDerivativeContraction_fderiv_fixed
        field hField 0 (by norm_num) point first
          (fun slot : Fin 0 => Fin.elim0 slot) (tangent second))
  rw [hLeft, hFunctions]
  change
    fderiv Real
      ((fun candidate =>
          iteratedFDeriv Real 1 field candidate ![second]
            (tangent candidate)) +
        fun candidate => field candidate (tangent second))
      point first = _
  rw [fderiv_add hFirstTerm hSecondTerm]
  simp only [add_apply]
  rw [hFirstDerivative, hSecondDerivative]
  abel

private theorem linearDerivativeContraction_iteratedFDeriv_three
    (field : X → Y →L[Real] Real) (tangent : X →L[Real] Y)
    (hField : ContDiff Real 3 field)
    (point first second third : X) :
    iteratedFDeriv Real 3 (linearDerivativeContraction field tangent)
        point ![first, second, third] =
      iteratedFDeriv Real 3 field point ![first, second, third]
          (tangent point) +
        iteratedFDeriv Real 2 field point ![first, second]
          (tangent third) +
        iteratedFDeriv Real 2 field point ![first, third]
          (tangent second) +
        iteratedFDeriv Real 2 field point ![second, third]
          (tangent first) := by
  have hContraction : ContDiff Real 3
      (linearDerivativeContraction field tangent) :=
    linearDerivativeContraction_contDiff_three field tangent hField
  have hFunctions :
      (fun candidate =>
        iteratedFDeriv Real 2 (linearDerivativeContraction field tangent)
          candidate ![second, third]) =
      (fun candidate =>
        iteratedFDeriv Real 2 field candidate ![second, third]
            (tangent candidate) +
          iteratedFDeriv Real 1 field candidate ![second]
              (tangent third) +
          iteratedFDeriv Real 1 field candidate ![third]
              (tangent second)) := by
    funext candidate
    exact linearDerivativeContraction_iteratedFDeriv_two
      field tangent hField candidate second third
  have hLeft :
      iteratedFDeriv Real 3 (linearDerivativeContraction field tangent)
          point ![first, second, third] =
        fderiv Real
          (fun candidate =>
            iteratedFDeriv Real 2
              (linearDerivativeContraction field tangent)
              candidate ![second, third]) point first := by
    rw [iteratedFDeriv_succ_apply_left]
    symm
    simpa using
      (fderiv_continuousMultilinear_apply_const_apply
        (hContraction.differentiable_iteratedFDeriv (by norm_num) point)
        ![second, third] first)
  have hFirstTerm : DifferentiableAt Real
      (fun candidate =>
        iteratedFDeriv Real 2 field candidate ![second, third]
          (tangent candidate)) point := by
    exact ((hField.differentiable_iteratedFDeriv (by norm_num) point)
      |>.continuousMultilinear_apply_const ![second, third]).clm_apply
        tangent.differentiableAt
  have hSecondTerm : DifferentiableAt Real
      (fun candidate =>
        iteratedFDeriv Real 1 field candidate ![second]
          (tangent third)) point := by
    exact ((hField.differentiable_iteratedFDeriv (by norm_num) point)
      |>.continuousMultilinear_apply_const ![second]).clm_apply
        (differentiableAt_const (c := tangent third))
  have hThirdTerm : DifferentiableAt Real
      (fun candidate =>
        iteratedFDeriv Real 1 field candidate ![third]
          (tangent second)) point := by
    exact ((hField.differentiable_iteratedFDeriv (by norm_num) point)
      |>.continuousMultilinear_apply_const ![third]).clm_apply
        (differentiableAt_const (c := tangent second))
  have hFirstDerivative := linearDerivativeContraction_fderiv_iterated
    field tangent hField 2 (by norm_num) point first ![second, third]
  have hSecondDerivative := linearDerivativeContraction_fderiv_fixed
    field hField 1 (by norm_num) point first ![second] (tangent third)
  have hThirdDerivative := linearDerivativeContraction_fderiv_fixed
    field hField 1 (by norm_num) point first ![third] (tangent second)
  rw [hLeft, hFunctions]
  change
    fderiv Real
      (((fun candidate =>
          iteratedFDeriv Real 2 field candidate ![second, third]
            (tangent candidate)) +
        fun candidate =>
          iteratedFDeriv Real 1 field candidate ![second]
            (tangent third)) +
        fun candidate =>
          iteratedFDeriv Real 1 field candidate ![third]
            (tangent second))
      point first = _
  rw [fderiv_add (hFirstTerm.add hSecondTerm) hThirdTerm,
    fderiv_add hFirstTerm hSecondTerm]
  simp only [add_apply]
  rw [hFirstDerivative, hSecondDerivative, hThirdDerivative]
  abel

private theorem derivativeField_contDiff_three
    (localFunction : Y → Real) (base : X →L[Real] Y)
    (hFunction : ContDiff Real 4 localFunction) :
    ContDiff Real 3 (fun point => fderiv Real localFunction (base point)) := by
  exact (hFunction.fderiv_right (m := 3) (by norm_num)).comp base.contDiff

private theorem derivativeField_iteratedFDeriv_apply
    (localFunction : Y → Real) (base : X →L[Real] Y)
    (hFunction : ContDiff Real 4 localFunction)
    (order : Nat) (hOrder : order ≤ 3)
    (point : X) (arguments : Fin order → X) (value : Y) :
    iteratedFDeriv Real order
        (fun candidate => fderiv Real localFunction (base candidate))
        point arguments value =
      iteratedFDeriv Real (order + 1) localFunction (base point)
        (Fin.snoc (fun slot => base (arguments slot)) value) := by
  have hGradient : ContDiff Real 3 (fderiv Real localFunction) :=
    hFunction.fderiv_right (m := 3) (by norm_num)
  have hComp := ContinuousLinearMap.iteratedFDeriv_comp_right
    (i := order) base hGradient point (by exact_mod_cast hOrder)
  have hApplied := congrArg
    (fun derivative => derivative arguments value) hComp
  calc
    iteratedFDeriv Real order
        (fun candidate => fderiv Real localFunction (base candidate))
        point arguments value =
      iteratedFDeriv Real order (fderiv Real localFunction) (base point)
          (fun slot => base (arguments slot)) value := by
        simpa [Function.comp_def,
          ContinuousMultilinearMap.compContinuousLinearMap_apply] using hApplied
    _ = iteratedFDeriv Real (order + 1) localFunction (base point)
        (Fin.snoc (fun slot => base (arguments slot)) value) := by
      symm
      rw [iteratedFDeriv_succ_apply_right]
      simp

end LinearContraction

theorem programPT06SecondOrderHorizontalCurrentDHSummand_contDiff_three
    (current : ProgramPT06SecondOrderHorizontalCurrent4D (Fiber := Fiber))
    (hCurrent : ∀ direction, ContDiff Real 4 (current direction))
    (direction : Fin 3) :
    ContDiff Real 3
      (programPT06SecondOrderHorizontalCurrentDHSummand current direction) := by
  exact linearDerivativeContraction_contDiff_three
    (fun jet => fderiv Real (current direction)
      (programPT06FourthJetToThirdJetContinuousLinearMap
        (Fiber := Fiber) jet))
    (programPT06FourthJetTotalDerivativeContinuousLinearMap
      (Fiber := Fiber) direction)
    (derivativeField_contDiff_three
      (current direction)
      (programPT06FourthJetToThirdJetContinuousLinearMap
        (Fiber := Fiber))
      (hCurrent direction))

/-- First Frechet derivative of one horizontal-divergence summand. -/
theorem programPT06SecondOrderHorizontalCurrentDHSummand_iteratedFDeriv_one
    (current : ProgramPT06SecondOrderHorizontalCurrent4D (Fiber := Fiber))
    (hCurrent : ∀ direction, ContDiff Real 4 (current direction))
    (direction : Fin 3) (jet variation : FourthJet (Fiber := Fiber)) :
    iteratedFDeriv Real 1
        (programPT06SecondOrderHorizontalCurrentDHSummand current direction)
        jet ![variation] =
      iteratedFDeriv Real 2 (current direction)
          (programPT06FourthJetToThirdJetContinuousLinearMap
            (Fiber := Fiber) jet)
          ![programPT06FourthJetToThirdJetContinuousLinearMap
              (Fiber := Fiber) variation,
            programPT06FourthJetTotalDerivativeContinuousLinearMap
              (Fiber := Fiber) direction jet] +
        iteratedFDeriv Real 1 (current direction)
          (programPT06FourthJetToThirdJetContinuousLinearMap
            (Fiber := Fiber) jet)
          ![programPT06FourthJetTotalDerivativeContinuousLinearMap
            (Fiber := Fiber) direction variation] := by
  let base := programPT06FourthJetToThirdJetContinuousLinearMap
    (Fiber := Fiber)
  let tangent := programPT06FourthJetTotalDerivativeContinuousLinearMap
    (Fiber := Fiber) direction
  let field := fun candidate => fderiv Real (current direction) (base candidate)
  have hField : ContDiff Real 3 field :=
    derivativeField_contDiff_three (current direction) base (hCurrent direction)
  have hRaw := linearDerivativeContraction_iteratedFDeriv_one
    field tangent hField jet variation
  rw [derivativeField_iteratedFDeriv_apply
    (current direction) base (hCurrent direction) 1 (by norm_num)] at hRaw
  have hContractionEq :
      linearDerivativeContraction field tangent =
        programPT06SecondOrderHorizontalCurrentDHSummand
          current direction := by
    rfl
  rw [hContractionEq] at hRaw
  have hSnoc :
      Fin.snoc (fun slot : Fin 1 => base (![variation] slot))
          (tangent jet) =
        ![base variation, tangent jet] := by
    funext slot
    fin_cases slot <;> rfl
  rw [hSnoc] at hRaw
  simpa [programPT06SecondOrderHorizontalCurrentDHSummand,
    field, base, tangent, iteratedFDeriv_one_apply] using hRaw

/-- Second Frechet derivative of one horizontal-divergence summand. -/
theorem programPT06SecondOrderHorizontalCurrentDHSummand_iteratedFDeriv_two
    (current : ProgramPT06SecondOrderHorizontalCurrent4D (Fiber := Fiber))
    (hCurrent : ∀ direction, ContDiff Real 4 (current direction))
    (direction : Fin 3) (jet first second : FourthJet (Fiber := Fiber)) :
    iteratedFDeriv Real 2
        (programPT06SecondOrderHorizontalCurrentDHSummand current direction)
        jet ![first, second] =
      iteratedFDeriv Real 3 (current direction)
          (programPT06FourthJetToThirdJetContinuousLinearMap
            (Fiber := Fiber) jet)
          ![programPT06FourthJetToThirdJetContinuousLinearMap
              (Fiber := Fiber) first,
            programPT06FourthJetToThirdJetContinuousLinearMap
              (Fiber := Fiber) second,
            programPT06FourthJetTotalDerivativeContinuousLinearMap
              (Fiber := Fiber) direction jet] +
        iteratedFDeriv Real 2 (current direction)
          (programPT06FourthJetToThirdJetContinuousLinearMap
            (Fiber := Fiber) jet)
          ![programPT06FourthJetToThirdJetContinuousLinearMap
              (Fiber := Fiber) first,
            programPT06FourthJetTotalDerivativeContinuousLinearMap
              (Fiber := Fiber) direction second] +
        iteratedFDeriv Real 2 (current direction)
          (programPT06FourthJetToThirdJetContinuousLinearMap
            (Fiber := Fiber) jet)
          ![programPT06FourthJetToThirdJetContinuousLinearMap
              (Fiber := Fiber) second,
            programPT06FourthJetTotalDerivativeContinuousLinearMap
              (Fiber := Fiber) direction first] := by
  let base := programPT06FourthJetToThirdJetContinuousLinearMap
    (Fiber := Fiber)
  let tangent := programPT06FourthJetTotalDerivativeContinuousLinearMap
    (Fiber := Fiber) direction
  let field := fun candidate => fderiv Real (current direction) (base candidate)
  have hField : ContDiff Real 3 field :=
    derivativeField_contDiff_three (current direction) base (hCurrent direction)
  have hRaw := linearDerivativeContraction_iteratedFDeriv_two
    field tangent hField jet first second
  rw [derivativeField_iteratedFDeriv_apply
      (current direction) base (hCurrent direction) 2 (by norm_num),
    derivativeField_iteratedFDeriv_apply
      (current direction) base (hCurrent direction) 1 (by norm_num),
    derivativeField_iteratedFDeriv_apply
      (current direction) base (hCurrent direction) 1 (by norm_num)] at hRaw
  have hContractionEq :
      linearDerivativeContraction field tangent =
        programPT06SecondOrderHorizontalCurrentDHSummand
          current direction := by
    rfl
  rw [hContractionEq] at hRaw
  have hSnocOne (variation : FourthJet (Fiber := Fiber))
      (value : ThirdJet (Fiber := Fiber)) :
      Fin.snoc (fun slot : Fin 1 => base (![variation] slot)) value =
        ![base variation, value] := by
    funext slot
    fin_cases slot <;> rfl
  have hSnocTwo (first second : FourthJet (Fiber := Fiber))
      (value : ThirdJet (Fiber := Fiber)) :
      Fin.snoc (fun slot : Fin 2 => base (![first, second] slot)) value =
        ![base first, base second, value] := by
    funext slot
    fin_cases slot <;> rfl
  rw [hSnocTwo first second (tangent jet),
    hSnocOne first (tangent second),
    hSnocOne second (tangent first)] at hRaw
  simpa [programPT06SecondOrderHorizontalCurrentDHSummand,
    field, base, tangent] using hRaw

/-- Third Frechet derivative of one horizontal-divergence summand. -/
theorem programPT06SecondOrderHorizontalCurrentDHSummand_iteratedFDeriv_three
    (current : ProgramPT06SecondOrderHorizontalCurrent4D (Fiber := Fiber))
    (hCurrent : ∀ direction, ContDiff Real 4 (current direction))
    (direction : Fin 3) (jet first second third : FourthJet (Fiber := Fiber)) :
    iteratedFDeriv Real 3
        (programPT06SecondOrderHorizontalCurrentDHSummand current direction)
        jet ![first, second, third] =
      iteratedFDeriv Real 4 (current direction)
          (programPT06FourthJetToThirdJetContinuousLinearMap
            (Fiber := Fiber) jet)
          ![programPT06FourthJetToThirdJetContinuousLinearMap
              (Fiber := Fiber) first,
            programPT06FourthJetToThirdJetContinuousLinearMap
              (Fiber := Fiber) second,
            programPT06FourthJetToThirdJetContinuousLinearMap
              (Fiber := Fiber) third,
            programPT06FourthJetTotalDerivativeContinuousLinearMap
              (Fiber := Fiber) direction jet] +
        iteratedFDeriv Real 3 (current direction)
          (programPT06FourthJetToThirdJetContinuousLinearMap
            (Fiber := Fiber) jet)
          ![programPT06FourthJetToThirdJetContinuousLinearMap
              (Fiber := Fiber) first,
            programPT06FourthJetToThirdJetContinuousLinearMap
              (Fiber := Fiber) second,
            programPT06FourthJetTotalDerivativeContinuousLinearMap
              (Fiber := Fiber) direction third] +
        iteratedFDeriv Real 3 (current direction)
          (programPT06FourthJetToThirdJetContinuousLinearMap
            (Fiber := Fiber) jet)
          ![programPT06FourthJetToThirdJetContinuousLinearMap
              (Fiber := Fiber) first,
            programPT06FourthJetToThirdJetContinuousLinearMap
              (Fiber := Fiber) third,
            programPT06FourthJetTotalDerivativeContinuousLinearMap
              (Fiber := Fiber) direction second] +
        iteratedFDeriv Real 3 (current direction)
          (programPT06FourthJetToThirdJetContinuousLinearMap
            (Fiber := Fiber) jet)
          ![programPT06FourthJetToThirdJetContinuousLinearMap
              (Fiber := Fiber) second,
            programPT06FourthJetToThirdJetContinuousLinearMap
              (Fiber := Fiber) third,
            programPT06FourthJetTotalDerivativeContinuousLinearMap
              (Fiber := Fiber) direction first] := by
  let base := programPT06FourthJetToThirdJetContinuousLinearMap
    (Fiber := Fiber)
  let tangent := programPT06FourthJetTotalDerivativeContinuousLinearMap
    (Fiber := Fiber) direction
  let field := fun candidate => fderiv Real (current direction) (base candidate)
  have hField : ContDiff Real 3 field :=
    derivativeField_contDiff_three (current direction) base (hCurrent direction)
  have hRaw := linearDerivativeContraction_iteratedFDeriv_three
    field tangent hField jet first second third
  rw [derivativeField_iteratedFDeriv_apply
      (current direction) base (hCurrent direction) 3 (by norm_num),
    derivativeField_iteratedFDeriv_apply
      (current direction) base (hCurrent direction) 2 (by norm_num),
    derivativeField_iteratedFDeriv_apply
      (current direction) base (hCurrent direction) 2 (by norm_num),
    derivativeField_iteratedFDeriv_apply
      (current direction) base (hCurrent direction) 2 (by norm_num)] at hRaw
  have hContractionEq :
      linearDerivativeContraction field tangent =
        programPT06SecondOrderHorizontalCurrentDHSummand
          current direction := by
    rfl
  rw [hContractionEq] at hRaw
  have hSnocTwo (first second : FourthJet (Fiber := Fiber))
      (value : ThirdJet (Fiber := Fiber)) :
      Fin.snoc (fun slot : Fin 2 => base (![first, second] slot)) value =
        ![base first, base second, value] := by
    funext slot
    fin_cases slot <;> rfl
  have hSnocThree (first second third : FourthJet (Fiber := Fiber))
      (value : ThirdJet (Fiber := Fiber)) :
      Fin.snoc
          (fun slot : Fin 3 => base (![first, second, third] slot)) value =
        ![base first, base second, base third, value] := by
    funext slot
    fin_cases slot <;> rfl
  rw [hSnocThree first second third (tangent jet),
    hSnocTwo first second (tangent third),
    hSnocTwo first third (tangent second),
    hSnocTwo second third (tangent first)] at hRaw
  simpa [programPT06SecondOrderHorizontalCurrentDHSummand,
    field, base, tangent] using hRaw

/-- Complete first derivative of the horizontal divergence. -/
theorem programPT06SecondOrderHorizontalCurrentDH_iteratedFDeriv_one
    (current : ProgramPT06SecondOrderHorizontalCurrent4D (Fiber := Fiber))
    (hCurrent : ∀ direction, ContDiff Real 4 (current direction))
    (jet variation : FourthJet (Fiber := Fiber)) :
    iteratedFDeriv Real 1
        (programPT06SecondOrderHorizontalCurrentDH current) jet ![variation] =
      ∑ direction : Fin 3,
        (iteratedFDeriv Real 2 (current direction)
            (programPT06FourthJetToThirdJetContinuousLinearMap
              (Fiber := Fiber) jet)
            ![programPT06FourthJetToThirdJetContinuousLinearMap
                (Fiber := Fiber) variation,
              programPT06FourthJetTotalDerivativeContinuousLinearMap
                (Fiber := Fiber) direction jet] +
          iteratedFDeriv Real 1 (current direction)
            (programPT06FourthJetToThirdJetContinuousLinearMap
              (Fiber := Fiber) jet)
            ![programPT06FourthJetTotalDerivativeContinuousLinearMap
              (Fiber := Fiber) direction variation]) := by
  rw [programPT06SecondOrderHorizontalCurrentDH_eq_sum_summand]
  rw [iteratedFDeriv_fun_sum_apply]
  · rw [ContinuousMultilinearMap.sum_apply]
    apply Finset.sum_congr rfl
    intro direction _
    exact programPT06SecondOrderHorizontalCurrentDHSummand_iteratedFDeriv_one
      current hCurrent direction jet variation
  · intro direction _
    exact (programPT06SecondOrderHorizontalCurrentDHSummand_contDiff_three
      current hCurrent direction).of_le (by norm_num) |>.contDiffAt

/-- Complete second derivative of the horizontal divergence. -/
theorem programPT06SecondOrderHorizontalCurrentDH_iteratedFDeriv_two
    (current : ProgramPT06SecondOrderHorizontalCurrent4D (Fiber := Fiber))
    (hCurrent : ∀ direction, ContDiff Real 4 (current direction))
    (jet first second : FourthJet (Fiber := Fiber)) :
    iteratedFDeriv Real 2
        (programPT06SecondOrderHorizontalCurrentDH current)
        jet ![first, second] =
      ∑ direction : Fin 3,
        (iteratedFDeriv Real 3 (current direction)
            (programPT06FourthJetToThirdJetContinuousLinearMap
              (Fiber := Fiber) jet)
            ![programPT06FourthJetToThirdJetContinuousLinearMap
                (Fiber := Fiber) first,
              programPT06FourthJetToThirdJetContinuousLinearMap
                (Fiber := Fiber) second,
              programPT06FourthJetTotalDerivativeContinuousLinearMap
                (Fiber := Fiber) direction jet] +
          iteratedFDeriv Real 2 (current direction)
            (programPT06FourthJetToThirdJetContinuousLinearMap
              (Fiber := Fiber) jet)
            ![programPT06FourthJetToThirdJetContinuousLinearMap
                (Fiber := Fiber) first,
              programPT06FourthJetTotalDerivativeContinuousLinearMap
                (Fiber := Fiber) direction second] +
          iteratedFDeriv Real 2 (current direction)
            (programPT06FourthJetToThirdJetContinuousLinearMap
              (Fiber := Fiber) jet)
            ![programPT06FourthJetToThirdJetContinuousLinearMap
                (Fiber := Fiber) second,
              programPT06FourthJetTotalDerivativeContinuousLinearMap
                (Fiber := Fiber) direction first]) := by
  rw [programPT06SecondOrderHorizontalCurrentDH_eq_sum_summand]
  rw [iteratedFDeriv_fun_sum_apply]
  · rw [ContinuousMultilinearMap.sum_apply]
    apply Finset.sum_congr rfl
    intro direction _
    exact programPT06SecondOrderHorizontalCurrentDHSummand_iteratedFDeriv_two
      current hCurrent direction jet first second
  · intro direction _
    exact (programPT06SecondOrderHorizontalCurrentDHSummand_contDiff_three
      current hCurrent direction).of_le (by norm_num) |>.contDiffAt

/-- Complete third derivative of the horizontal divergence. -/
theorem programPT06SecondOrderHorizontalCurrentDH_iteratedFDeriv_three
    (current : ProgramPT06SecondOrderHorizontalCurrent4D (Fiber := Fiber))
    (hCurrent : ∀ direction, ContDiff Real 4 (current direction))
    (jet first second third : FourthJet (Fiber := Fiber)) :
    iteratedFDeriv Real 3
        (programPT06SecondOrderHorizontalCurrentDH current)
        jet ![first, second, third] =
      ∑ direction : Fin 3,
        (iteratedFDeriv Real 4 (current direction)
            (programPT06FourthJetToThirdJetContinuousLinearMap
              (Fiber := Fiber) jet)
            ![programPT06FourthJetToThirdJetContinuousLinearMap
                (Fiber := Fiber) first,
              programPT06FourthJetToThirdJetContinuousLinearMap
                (Fiber := Fiber) second,
              programPT06FourthJetToThirdJetContinuousLinearMap
                (Fiber := Fiber) third,
              programPT06FourthJetTotalDerivativeContinuousLinearMap
                (Fiber := Fiber) direction jet] +
          iteratedFDeriv Real 3 (current direction)
            (programPT06FourthJetToThirdJetContinuousLinearMap
              (Fiber := Fiber) jet)
            ![programPT06FourthJetToThirdJetContinuousLinearMap
                (Fiber := Fiber) first,
              programPT06FourthJetToThirdJetContinuousLinearMap
                (Fiber := Fiber) second,
              programPT06FourthJetTotalDerivativeContinuousLinearMap
                (Fiber := Fiber) direction third] +
          iteratedFDeriv Real 3 (current direction)
            (programPT06FourthJetToThirdJetContinuousLinearMap
              (Fiber := Fiber) jet)
            ![programPT06FourthJetToThirdJetContinuousLinearMap
                (Fiber := Fiber) first,
              programPT06FourthJetToThirdJetContinuousLinearMap
                (Fiber := Fiber) third,
              programPT06FourthJetTotalDerivativeContinuousLinearMap
                (Fiber := Fiber) direction second] +
          iteratedFDeriv Real 3 (current direction)
            (programPT06FourthJetToThirdJetContinuousLinearMap
              (Fiber := Fiber) jet)
            ![programPT06FourthJetToThirdJetContinuousLinearMap
                (Fiber := Fiber) second,
              programPT06FourthJetToThirdJetContinuousLinearMap
                (Fiber := Fiber) third,
              programPT06FourthJetTotalDerivativeContinuousLinearMap
                (Fiber := Fiber) direction first]) := by
  rw [programPT06SecondOrderHorizontalCurrentDH_eq_sum_summand]
  rw [iteratedFDeriv_fun_sum_apply]
  · rw [ContinuousMultilinearMap.sum_apply]
    apply Finset.sum_congr rfl
    intro direction _
    exact programPT06SecondOrderHorizontalCurrentDHSummand_iteratedFDeriv_three
      current hCurrent direction jet first second third
  · intro direction _
    exact (programPT06SecondOrderHorizontalCurrentDHSummand_contDiff_three
      current hCurrent direction).contDiffAt

end
end P0EFTJanusProgramPT06HorizontalCurrentDivergenceHigherFrechet4D
end JanusFormal
