import Mathlib.Analysis.Calculus.FDeriv.Analytic
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06SecondOrderLocalEuler4D

/-!
# Higher Frechet formula for the second-order Euler operator

This support gate expands Gate880's vertical and formal total derivatives for
a `C3` local function in terms of its first three iterated Frechet
derivatives.  The second total derivative contains both the third-derivative
chain-rule term and the derivative of the formal jet translation.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06SecondOrderEulerHigherFrechetFormula4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000
set_option maxRecDepth 100000
noncomputable section

open scoped BigOperators
open P0EFTJanusProgramPT06ThroatSpatialFinsuppJetTower4D
open P0EFTJanusProgramPT06LocalFunctionTotalDerivative4D
open P0EFTJanusProgramPT06SecondOrderLocalEuler4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

universe u

variable {Fiber : Type u} [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]

private abbrev SecondJet := ThroatSpatialMultiindexJet2 Fiber
private abbrev ThirdJet := ThroatSpatialMultiindexJet3 Fiber
private abbrev FourthJet := ThroatSpatialMultiindexJet4 Fiber

/-- The iterated Frechet derivative used in the expanded Euler formula. -/
def programPT06SecondOrderEulerHigherFrechetDerivative
    (order : Nat) (localLagrangian : SecondJet (Fiber := Fiber) -> Real)
    (jet : SecondJet (Fiber := Fiber)) :
    SecondJet (Fiber := Fiber) [×order]→L[Real] Real :=
  iteratedFDeriv Real order localLagrangian jet

omit [NormedAddCommGroup Fiber] [NormedSpace Real Fiber] in
/-- Truncation commutes with a formal total derivative. -/
@[simp] theorem programPT06TruncateThroatSpatialTotalDerivative
    {lower higher : Nat} (hOrder : lower <= higher)
    (direction : Fin 3)
    (jet : TruncatedThroatSpatialMultiindexJet Fiber (higher + 1)) :
    truncateThroatSpatialMultiindexJet hOrder
        (throatSpatialTotalDerivative direction jet) =
      throatSpatialTotalDerivative direction
        (truncateThroatSpatialMultiindexJet
          (Nat.add_le_add_right hOrder 1) jet) := by
  funext index
  change jet _ = jet _
  apply congrArg jet
  apply Subtype.ext
  rfl

omit [NormedAddCommGroup Fiber] [NormedSpace Real Fiber] in
/-- Successive truncations equal direct truncation. -/
@[simp] theorem programPT06TruncateThroatSpatialMultiindexJet_trans
    {lower middle higher : Nat} (hLower : lower <= middle)
    (hHigher : middle <= higher)
    (jet : TruncatedThroatSpatialMultiindexJet Fiber higher) :
    truncateThroatSpatialMultiindexJet hLower
        (truncateThroatSpatialMultiindexJet hHigher jet) =
      truncateThroatSpatialMultiindexJet (hLower.trans hHigher) jet := by
  rfl

private def programPT06TruncateThirdJetContinuousLinearMap :
    ThirdJet (Fiber := Fiber) →L[Real] SecondJet (Fiber := Fiber) :=
  ContinuousLinearMap.pi fun index : ThroatSpatialTruncatedIndex 2 =>
    ContinuousLinearMap.proj
      ⟨index.1, index.2.trans (by omega : 2 <= 3)⟩

@[simp] private theorem
    programPT06TruncateThirdJetContinuousLinearMap_apply
    (jet : ThirdJet (Fiber := Fiber)) :
    programPT06TruncateThirdJetContinuousLinearMap (Fiber := Fiber) jet =
      truncateThroatSpatialMultiindexJet (by omega : 2 <= 3) jet := by
  rfl

private def programPT06ThirdJetTotalDerivativeContinuousLinearMap
    (direction : Fin 3) :
    ThirdJet (Fiber := Fiber) →L[Real] SecondJet (Fiber := Fiber) :=
  ContinuousLinearMap.pi fun index : ThroatSpatialTruncatedIndex 2 =>
    ContinuousLinearMap.proj
      ⟨index.1 + throatSpatialCoordinateMultiIndex direction, by
        rw [throatSpatialMultiIndexOrder_add_coordinateMultiIndex]
        omega⟩

@[simp] private theorem
    programPT06ThirdJetTotalDerivativeContinuousLinearMap_apply
    (direction : Fin 3) (jet : ThirdJet (Fiber := Fiber)) :
    programPT06ThirdJetTotalDerivativeContinuousLinearMap
        (Fiber := Fiber) direction jet =
      throatSpatialTotalDerivative direction jet := by
  rfl

private def programPT06SecondOrderEulerRestriction
    (index : ThroatSpatialTruncatedIndex 2) :
    (SecondJet (Fiber := Fiber) →L[Real] Real) →L[Real]
      (Fiber →L[Real] Real) :=
  (ContinuousLinearMap.compL Real Fiber
    (SecondJet (Fiber := Fiber)) Real).flip
      (programPT06ThroatSpatialJetCoordinateInjection index)

private def programPT06SecondOrderEulerRestrictedGradientDerivative
    (localLagrangian : SecondJet (Fiber := Fiber) -> Real)
    (index : ThroatSpatialTruncatedIndex 2)
    (jet : SecondJet (Fiber := Fiber)) :
    SecondJet (Fiber := Fiber) →L[Real] (Fiber →L[Real] Real) :=
  (programPT06SecondOrderEulerRestriction (Fiber := Fiber) index).comp
    (fderiv Real (fderiv Real localLagrangian) jet)

private theorem
    programPT06SecondOrderEulerRestrictedGradient_hasFDerivAt
    (localLagrangian : SecondJet (Fiber := Fiber) -> Real)
    (hLagrangian : ContDiff Real 2 localLagrangian)
    (index : ThroatSpatialTruncatedIndex 2)
    (jet : SecondJet (Fiber := Fiber)) :
    HasFDerivAt
      (fun candidate =>
        programPT06ThroatSpatialVerticalPartialDerivative
          localLagrangian candidate index)
      (programPT06SecondOrderEulerRestrictedGradientDerivative
        localLagrangian index jet) jet := by
  have hGradient :
      HasFDerivAt (fderiv Real localLagrangian)
        (fderiv Real (fderiv Real localLagrangian) jet) jet :=
    (((hLagrangian.fderiv_right (m := 1) (by norm_num)).differentiable
      (by norm_num) jet).hasFDerivAt)
  have hRestricted :=
    (programPT06SecondOrderEulerRestriction
      (Fiber := Fiber) index).hasFDerivAt.comp jet hGradient
  simpa [programPT06SecondOrderEulerRestriction,
    programPT06SecondOrderEulerRestrictedGradientDerivative,
    programPT06ThroatSpatialVerticalPartialDerivative,
    Function.comp_def] using hRestricted

/-- A vertical partial is the first iterated Frechet derivative evaluated on
the corresponding coordinate injection. -/
@[simp] theorem programPT06ThroatSpatialVerticalPartialDerivative_eq_higherFrechet
    (localLagrangian : SecondJet (Fiber := Fiber) -> Real)
    (jet : SecondJet (Fiber := Fiber))
    (index : ThroatSpatialTruncatedIndex 2) (variation : Fiber) :
    programPT06ThroatSpatialVerticalPartialDerivative
        localLagrangian jet index variation =
      programPT06SecondOrderEulerHigherFrechetDerivative
        1 localLagrangian jet
        ![programPT06ThroatSpatialJetCoordinateInjection index variation] := by
  simp [programPT06SecondOrderEulerHigherFrechetDerivative]

private theorem
    programPT06ThroatSpatialTotalDerivative_verticalPartial_apply
    (localLagrangian : SecondJet (Fiber := Fiber) -> Real)
    (hLagrangian : ContDiff Real 2 localLagrangian)
    (index : ThroatSpatialTruncatedIndex 2) (direction : Fin 3)
    (jet : ThirdJet (Fiber := Fiber)) (variation : Fiber) :
    programPT06ThroatSpatialLocalFunctionTotalDerivative direction
        (fun candidate =>
          programPT06ThroatSpatialVerticalPartialDerivative
            localLagrangian candidate index) jet variation =
      programPT06SecondOrderEulerHigherFrechetDerivative
        2 localLagrangian
        (truncateThroatSpatialMultiindexJet (by omega : 2 <= 3) jet)
        ![throatSpatialTotalDerivative direction jet,
          programPT06ThroatSpatialJetCoordinateInjection index variation] := by
  rw [programPT06ThroatSpatialLocalFunctionTotalDerivative_eq_of_hasFDerivAt
    direction
    (fun candidate =>
      programPT06ThroatSpatialVerticalPartialDerivative
        localLagrangian candidate index)
    jet
    (programPT06SecondOrderEulerRestrictedGradientDerivative
      localLagrangian index
      (truncateThroatSpatialMultiindexJet (by omega : 2 <= 3) jet))
    (programPT06SecondOrderEulerRestrictedGradient_hasFDerivAt
      localLagrangian hLagrangian index
      (truncateThroatSpatialMultiindexJet (by omega : 2 <= 3) jet))]
  simp [programPT06SecondOrderEulerHigherFrechetDerivative,
    programPT06SecondOrderEulerRestrictedGradientDerivative,
    programPT06SecondOrderEulerRestriction, iteratedFDeriv_two_apply]

/-- The first total-derivative term in Gate880 is the Hessian contracted with
the formal jet translation and the selected vertical variation. -/
@[simp] theorem programPT06SecondOrderLocalEulerFirstTotalTerm_eq_higherFrechet
    (localLagrangian : SecondJet (Fiber := Fiber) -> Real)
    (hLagrangian : ContDiff Real 2 localLagrangian)
    (direction : Fin 3) (jet : ThirdJet (Fiber := Fiber))
    (variation : Fiber) :
    programPT06SecondOrderLocalEulerFirstTotalTerm
        localLagrangian direction jet variation =
      programPT06SecondOrderEulerHigherFrechetDerivative
        2 localLagrangian
        (truncateThroatSpatialMultiindexJet (by omega : 2 <= 3) jet)
        ![throatSpatialTotalDerivative direction jet,
          programPT06ThroatSpatialJetCoordinateInjection
            (programPT06SecondOrderFirstMultiIndex direction) variation] := by
  exact programPT06ThroatSpatialTotalDerivative_verticalPartial_apply
    localLagrangian hLagrangian
    (programPT06SecondOrderFirstMultiIndex direction) direction jet variation

private def programPT06SecondOrderEulerFirstProlongedPartial
    (localLagrangian : SecondJet (Fiber := Fiber) -> Real)
    (index : ThroatSpatialTruncatedIndex 2) (direction : Fin 3) :
    ThirdJet (Fiber := Fiber) -> (Fiber →L[Real] Real) :=
  fun jet =>
    ((fderiv Real (fderiv Real localLagrangian)
      (truncateThroatSpatialMultiindexJet (by omega : 2 <= 3) jet))
      (throatSpatialTotalDerivative direction jet)).comp
        (programPT06ThroatSpatialJetCoordinateInjection index)

private theorem programPT06SecondOrderEulerFirstProlongedPartial_eq
    (localLagrangian : SecondJet (Fiber := Fiber) -> Real)
    (hLagrangian : ContDiff Real 2 localLagrangian)
    (index : ThroatSpatialTruncatedIndex 2) (direction : Fin 3) :
    programPT06ThroatSpatialLocalFunctionTotalDerivative direction
        (fun candidate =>
          programPT06ThroatSpatialVerticalPartialDerivative
            localLagrangian candidate index) =
      programPT06SecondOrderEulerFirstProlongedPartial
        localLagrangian index direction := by
  funext jet
  apply ContinuousLinearMap.ext
  intro variation
  rw [programPT06ThroatSpatialTotalDerivative_verticalPartial_apply
    localLagrangian hLagrangian index direction jet variation]
  simp [programPT06SecondOrderEulerFirstProlongedPartial,
    programPT06SecondOrderEulerHigherFrechetDerivative,
    iteratedFDeriv_two_apply]

private theorem
    programPT06SecondOrderEulerFirstProlongedPartial_differentiableAt
    (localLagrangian : SecondJet (Fiber := Fiber) -> Real)
    (hLagrangian : ContDiff Real 3 localLagrangian)
    (index : ThroatSpatialTruncatedIndex 2) (direction : Fin 3)
    (jet : ThirdJet (Fiber := Fiber)) :
    DifferentiableAt Real
      (programPT06SecondOrderEulerFirstProlongedPartial
        localLagrangian index direction) jet := by
  let truncate : ThirdJet (Fiber := Fiber) →L[Real]
      SecondJet (Fiber := Fiber) :=
    programPT06TruncateThirdJetContinuousLinearMap (Fiber := Fiber)
  let total : ThirdJet (Fiber := Fiber) →L[Real]
      SecondJet (Fiber := Fiber) :=
    programPT06ThirdJetTotalDerivativeContinuousLinearMap
      (Fiber := Fiber) direction
  let hessian := fderiv Real (fderiv Real localLagrangian)
  have hGradient : ContDiff Real 2 (fderiv Real localLagrangian) :=
    hLagrangian.fderiv_right (m := 2) (by norm_num)
  have hHessian : Differentiable Real hessian :=
    (hGradient.fderiv_right (m := 1) (by norm_num)).differentiable
      (by norm_num)
  have hComposed : DifferentiableAt Real
      (fun candidate : ThirdJet (Fiber := Fiber) =>
        hessian (truncate candidate)) jet :=
    (hHessian (truncate jet)).comp jet truncate.differentiableAt
  have hApplied : DifferentiableAt Real
      (fun candidate : ThirdJet (Fiber := Fiber) =>
        hessian (truncate candidate) (total candidate)) jet :=
    hComposed.clm_apply total.differentiableAt
  have hRestricted :=
    (programPT06SecondOrderEulerRestriction
      (Fiber := Fiber) index).differentiableAt.comp jet hApplied
  change DifferentiableAt Real
    (fun candidate : ThirdJet (Fiber := Fiber) =>
      ((fderiv Real (fderiv Real localLagrangian)
        (truncateThroatSpatialMultiindexJet (by omega : 2 <= 3) candidate))
        (throatSpatialTotalDerivative direction candidate)).comp
          (programPT06ThroatSpatialJetCoordinateInjection index)) jet
  simpa [programPT06SecondOrderEulerFirstProlongedPartial,
    programPT06SecondOrderEulerRestriction, truncate, total, hessian,
    Function.comp_def] using hRestricted

private def programPT06SecondOrderEulerProlongedScalar
    (localLagrangian : SecondJet (Fiber := Fiber) -> Real)
    (index : ThroatSpatialTruncatedIndex 2) (direction : Fin 3)
    (variation : Fiber) : ThirdJet (Fiber := Fiber) -> Real :=
  fun jet =>
    programPT06SecondOrderEulerHigherFrechetDerivative
      2 localLagrangian
      (truncateThroatSpatialMultiindexJet (by omega : 2 <= 3) jet)
      ![throatSpatialTotalDerivative direction jet,
        programPT06ThroatSpatialJetCoordinateInjection index variation]

private theorem programPT06SecondOrderEulerProlongedScalar_fderiv
    (localLagrangian : SecondJet (Fiber := Fiber) -> Real)
    (hLagrangian : ContDiff Real 3 localLagrangian)
    (index : ThroatSpatialTruncatedIndex 2) (direction : Fin 3)
    (variation : Fiber) (jet directionJet : ThirdJet (Fiber := Fiber)) :
    fderiv Real
        (programPT06SecondOrderEulerProlongedScalar
          localLagrangian index direction variation) jet directionJet =
      programPT06SecondOrderEulerHigherFrechetDerivative
        3 localLagrangian
        (truncateThroatSpatialMultiindexJet (by omega : 2 <= 3) jet)
        ![truncateThroatSpatialMultiindexJet
            (by omega : 2 <= 3) directionJet,
          throatSpatialTotalDerivative direction jet,
          programPT06ThroatSpatialJetCoordinateInjection index variation] +
      programPT06SecondOrderEulerHigherFrechetDerivative
        2 localLagrangian
        (truncateThroatSpatialMultiindexJet (by omega : 2 <= 3) jet)
        ![throatSpatialTotalDerivative direction directionJet,
          programPT06ThroatSpatialJetCoordinateInjection index variation] := by
  let truncate : ThirdJet (Fiber := Fiber) →L[Real]
      SecondJet (Fiber := Fiber) :=
    programPT06TruncateThirdJetContinuousLinearMap (Fiber := Fiber)
  let total : ThirdJet (Fiber := Fiber) →L[Real]
      SecondJet (Fiber := Fiber) :=
    programPT06ThirdJetTotalDerivativeContinuousLinearMap
      (Fiber := Fiber) direction
  let fixed : SecondJet (Fiber := Fiber) :=
    programPT06ThroatSpatialJetCoordinateInjection index variation
  let derivativeTwo := iteratedFDeriv Real 2 localLagrangian
  let arguments : Fin 2 -> ThirdJet (Fiber := Fiber) ->
      SecondJet (Fiber := Fiber) :=
    ![fun candidate => total candidate, fun _ => fixed]
  let argumentDerivatives : Fin 2 ->
      ThirdJet (Fiber := Fiber) →L[Real] SecondJet (Fiber := Fiber) :=
    ![total, 0]
  have hDerivativeTwo : Differentiable Real derivativeTwo :=
    hLagrangian.differentiable_iteratedFDeriv (by norm_num)
  have hBase : HasFDerivAt
      (fun candidate : ThirdJet (Fiber := Fiber) =>
        derivativeTwo (truncate candidate))
      ((fderiv Real derivativeTwo (truncate jet)).comp truncate) jet :=
    (hDerivativeTwo (truncate jet)).hasFDerivAt.comp jet truncate.hasFDerivAt
  have hArguments : forall slot,
      HasFDerivAt (arguments slot) (argumentDerivatives slot) jet := by
    intro slot
    fin_cases slot
    · exact total.hasFDerivAt
    · change HasFDerivAt
        (fun _ : ThirdJet (Fiber := Fiber) => fixed)
        (0 : ThirdJet (Fiber := Fiber) →L[Real]
          SecondJet (Fiber := Fiber)) jet
      exact hasFDerivAt_const (x := jet) (c := fixed)
  have hApplied := hBase.continuousMultilinearMap_apply hArguments
  have hRaw :
      fderiv Real
          (programPT06SecondOrderEulerProlongedScalar
            localLagrangian index direction variation) jet directionJet =
        fderiv Real derivativeTwo (truncate jet) (truncate directionJet)
            ![total jet, fixed] +
          derivativeTwo (truncate jet) ![total directionJet, fixed] := by
    change
      fderiv Real
          (fun candidate =>
            derivativeTwo (truncate candidate) ![total candidate, fixed])
          jet directionJet =
        fderiv Real derivativeTwo (truncate jet) (truncate directionJet)
            ![total jet, fixed] +
          derivativeTwo (truncate jet) ![total directionJet, fixed]
    have hUpdate :
        Function.update (![total jet, fixed] :
          Fin 2 -> SecondJet (Fiber := Fiber)) (0 : Fin 2)
            (total directionJet) =
          ![total directionJet, fixed] := by
      funext slot
      fin_cases slot <;> simp
    have hFderiv := congrArg
      (fun derivative => derivative directionJet) hApplied.fderiv
    have hVec (first second : SecondJet (Fiber := Fiber)) :
        (fun slot : Fin 2 =>
          Matrix.vecCons first (fun _ => second) slot) =
          ![first, second] := by
      funext slot
      fin_cases slot <;> rfl
    have hFderivUpdated :
        fderiv Real
            (fun candidate =>
              derivativeTwo (truncate candidate) ![total candidate, fixed])
            jet directionJet =
          fderiv Real derivativeTwo (truncate jet) (truncate directionJet)
              ![total jet, fixed] +
            derivativeTwo (truncate jet)
              (Function.update (![total jet, fixed] :
                Fin 2 -> SecondJet (Fiber := Fiber)) (0 : Fin 2)
                  (total directionJet)) := by
      simpa [arguments, argumentDerivatives, Fin.sum_univ_two, hVec] using
        hFderiv
    rw [hUpdate] at hFderivUpdated
    exact hFderivUpdated
  have hThird :
      fderiv Real derivativeTwo (truncate jet) (truncate directionJet)
          ![total jet, fixed] =
        iteratedFDeriv Real 3 localLagrangian (truncate jet)
          ![truncate directionJet, total jet, fixed] := by
    symm
    simpa [derivativeTwo] using
      (iteratedFDeriv_succ_apply_left
        (x := truncate jet)
        (![truncate directionJet, total jet, fixed] :
          Fin 3 -> SecondJet (Fiber := Fiber)))
  rw [hRaw, hThird]
  rfl

private theorem
    programPT06SecondOrderEulerFirstProlongedPartial_fderiv_apply
    (localLagrangian : SecondJet (Fiber := Fiber) -> Real)
    (hLagrangian : ContDiff Real 3 localLagrangian)
    (index : ThroatSpatialTruncatedIndex 2) (direction : Fin 3)
    (variation : Fiber) (jet directionJet : ThirdJet (Fiber := Fiber)) :
    fderiv Real
        (programPT06SecondOrderEulerFirstProlongedPartial
          localLagrangian index direction) jet directionJet variation =
      programPT06SecondOrderEulerHigherFrechetDerivative
        3 localLagrangian
        (truncateThroatSpatialMultiindexJet (by omega : 2 <= 3) jet)
        ![truncateThroatSpatialMultiindexJet
            (by omega : 2 <= 3) directionJet,
          throatSpatialTotalDerivative direction jet,
          programPT06ThroatSpatialJetCoordinateInjection index variation] +
      programPT06SecondOrderEulerHigherFrechetDerivative
        2 localLagrangian
        (truncateThroatSpatialMultiindexJet (by omega : 2 <= 3) jet)
        ![throatSpatialTotalDerivative direction directionJet,
          programPT06ThroatSpatialJetCoordinateInjection index variation] := by
  have hDifferentiable :=
    programPT06SecondOrderEulerFirstProlongedPartial_differentiableAt
      localLagrangian hLagrangian index direction jet
  have hEvaluation :
      fderiv Real
          (fun candidate =>
            programPT06SecondOrderEulerFirstProlongedPartial
              localLagrangian index direction candidate variation)
          jet directionJet =
        fderiv Real
          (programPT06SecondOrderEulerFirstProlongedPartial
            localLagrangian index direction) jet directionJet variation := by
    have hApply := fderiv_clm_apply hDifferentiable
      (differentiableAt_const (c := variation))
    have hPoint := congrArg (fun derivative => derivative directionJet) hApply
    simpa using hPoint
  have hFunctions :
      (fun candidate =>
        programPT06SecondOrderEulerFirstProlongedPartial
          localLagrangian index direction candidate variation) =
        programPT06SecondOrderEulerProlongedScalar
          localLagrangian index direction variation := by
    funext candidate
    simp [programPT06SecondOrderEulerFirstProlongedPartial,
      programPT06SecondOrderEulerProlongedScalar,
      programPT06SecondOrderEulerHigherFrechetDerivative,
      iteratedFDeriv_two_apply]
  rw [← hEvaluation, hFunctions]
  exact programPT06SecondOrderEulerProlongedScalar_fderiv
    localLagrangian hLagrangian index direction variation jet directionJet

/-- The iterated total derivative in Gate880 has the complete chain-rule
expansion, including the derivative of the formal jet translation. -/
@[simp] theorem programPT06SecondOrderLocalEulerSecondTotalTerm_eq_higherFrechet
    (localLagrangian : SecondJet (Fiber := Fiber) -> Real)
    (hLagrangian : ContDiff Real 3 localLagrangian)
    (first second : Fin 3) (jet : FourthJet (Fiber := Fiber))
    (variation : Fiber) :
    programPT06SecondOrderLocalEulerSecondTotalTerm
        localLagrangian first second jet variation =
      programPT06SecondOrderEulerHigherFrechetDerivative
        3 localLagrangian
        (truncateThroatSpatialMultiindexJet (by omega : 2 <= 4) jet)
        ![throatSpatialTotalDerivative first
            (truncateThroatSpatialMultiindexJet (by omega : 3 <= 4) jet),
          throatSpatialTotalDerivative second
            (truncateThroatSpatialMultiindexJet (by omega : 3 <= 4) jet),
          programPT06ThroatSpatialJetCoordinateInjection
            (programPT06SecondOrderSecondMultiIndex first second) variation] +
      programPT06SecondOrderEulerHigherFrechetDerivative
        2 localLagrangian
        (truncateThroatSpatialMultiindexJet (by omega : 2 <= 4) jet)
        ![throatSpatialTotalDerivative second
            (throatSpatialTotalDerivative first jet),
          programPT06ThroatSpatialJetCoordinateInjection
            (programPT06SecondOrderSecondMultiIndex first second) variation] := by
  rw [programPT06SecondOrderLocalEulerSecondTotalTerm]
  change
    (programPT06ThroatSpatialLocalFunctionTotalDerivative first
      (programPT06ThroatSpatialLocalFunctionTotalDerivative second
        (fun candidate =>
          programPT06ThroatSpatialVerticalPartialDerivative
            localLagrangian candidate
              (programPT06SecondOrderSecondMultiIndex first second))) jet)
        variation = _
  rw [
    programPT06SecondOrderEulerFirstProlongedPartial_eq
      localLagrangian (hLagrangian.of_le (by norm_num))
      (programPT06SecondOrderSecondMultiIndex first second) second,
    programPT06ThroatSpatialLocalFunctionTotalDerivative_apply]
  simpa using
    (programPT06SecondOrderEulerFirstProlongedPartial_fderiv_apply
      localLagrangian hLagrangian
      (programPT06SecondOrderSecondMultiIndex first second) second variation
      (truncateThroatSpatialMultiindexJet (by omega : 3 <= 4) jet)
      (throatSpatialTotalDerivative first jet))

/-- Complete higher-Frechet expansion of Gate880 on a fourth jet. -/
theorem programPT06SecondOrderLocalEuler_eq_higherFrechet
    (localLagrangian : SecondJet (Fiber := Fiber) -> Real)
    (hLagrangian : ContDiff Real 3 localLagrangian)
    (jet : FourthJet (Fiber := Fiber)) (variation : Fiber) :
    programPT06SecondOrderLocalEuler localLagrangian jet variation =
      programPT06SecondOrderEulerHigherFrechetDerivative
          1 localLagrangian
          (truncateThroatSpatialMultiindexJet (by omega : 2 <= 4) jet)
          ![programPT06ThroatSpatialJetCoordinateInjection
            programPT06SecondOrderZeroMultiIndex variation] -
        (∑ direction : Fin 3,
          programPT06SecondOrderEulerHigherFrechetDerivative
            2 localLagrangian
            (truncateThroatSpatialMultiindexJet (by omega : 2 <= 4) jet)
            ![throatSpatialTotalDerivative direction
                (truncateThroatSpatialMultiindexJet (by omega : 3 <= 4) jet),
              programPT06ThroatSpatialJetCoordinateInjection
                (programPT06SecondOrderFirstMultiIndex direction) variation]) +
        ∑ first : Fin 3, ∑ second : Fin 3,
          programPT06SecondOrderEulerSymmetryWeight first second •
            (programPT06SecondOrderEulerHigherFrechetDerivative
                3 localLagrangian
                (truncateThroatSpatialMultiindexJet (by omega : 2 <= 4) jet)
                ![throatSpatialTotalDerivative first
                    (truncateThroatSpatialMultiindexJet
                      (by omega : 3 <= 4) jet),
                  throatSpatialTotalDerivative second
                    (truncateThroatSpatialMultiindexJet
                      (by omega : 3 <= 4) jet),
                  programPT06ThroatSpatialJetCoordinateInjection
                    (programPT06SecondOrderSecondMultiIndex first second)
                    variation] +
              programPT06SecondOrderEulerHigherFrechetDerivative
                2 localLagrangian
                (truncateThroatSpatialMultiindexJet (by omega : 2 <= 4) jet)
                ![throatSpatialTotalDerivative second
                    (throatSpatialTotalDerivative first jet),
                  programPT06ThroatSpatialJetCoordinateInjection
                    (programPT06SecondOrderSecondMultiIndex first second)
                    variation]) := by
  rw [programPT06SecondOrderLocalEuler_apply,
    programPT06SecondOrderLocalVerticalPartialZero_apply]
  simp_rw [programPT06SecondOrderLocalEulerFirstTotalTerm_eq_higherFrechet
    localLagrangian (hLagrangian.of_le (by norm_num))]
  simp_rw [programPT06SecondOrderLocalEulerSecondTotalTerm_eq_higherFrechet
    localLagrangian hLagrangian]
  simp [programPT06SecondOrderEulerHigherFrechetDerivative]

end
end P0EFTJanusProgramPT06SecondOrderEulerHigherFrechetFormula4D
end JanusFormal
