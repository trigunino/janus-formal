import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06SecondOrderRadialCartanHomotopy4D

/-!
# Factorization support for second-order horizontal-divergence soundness

This gate records the exact non-circular interface needed to compare a
second-order density with the horizontal divergence of a third-jet current.
It supplies continuous-linear truncation and zero-extension maps, proves that
the factorization reconstructs the density on every second jet, and transfers
the first three Frechet derivatives of the factorization.

The final cancellation `Euler (dH current) = 0` requires the fourth-order
Euler telescoping identity on eighth jets.  That higher-order variational
identity is deliberately not replaced here by an assumption equivalent to
the desired conclusion.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06SecondOrderHorizontalDivergenceEulerSoundness4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000
set_option maxRecDepth 100000
noncomputable section

open scoped BigOperators ContDiff
open P0EFTJanusProgramPT06ThroatSpatialFinsuppJetTower4D
open P0EFTJanusProgramPT06LocalFunctionTotalDerivative4D
open P0EFTJanusProgramPT06SecondOrderLocalEuler4D
open P0EFTJanusProgramPT06SecondOrderRadialCartanHomotopy4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

universe u

variable {Fiber : Type u} [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]

private abbrev SecondJet := ThroatSpatialMultiindexJet2 Fiber
private abbrev ThirdJet := ThroatSpatialMultiindexJet3 Fiber
private abbrev FourthJet := ThroatSpatialMultiindexJet4 Fiber

/-- Continuous-linear truncation from fourth to second spatial jets. -/
def programPT06FourthJetToSecondJetContinuousLinearMap :
    FourthJet (Fiber := Fiber) →L[Real] SecondJet (Fiber := Fiber) :=
  ContinuousLinearMap.pi fun index : ThroatSpatialTruncatedIndex 2 =>
    ContinuousLinearMap.proj
      ⟨index.1, index.2.trans (by omega : 2 ≤ 4)⟩

@[simp] theorem programPT06FourthJetToSecondJetContinuousLinearMap_apply
    (jet : FourthJet (Fiber := Fiber)) :
    programPT06FourthJetToSecondJetContinuousLinearMap (Fiber := Fiber) jet =
      truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 4) jet := by
  rfl

/-- Continuous-linear truncation from fourth to third spatial jets. -/
def programPT06FourthJetToThirdJetContinuousLinearMap :
    FourthJet (Fiber := Fiber) →L[Real] ThirdJet (Fiber := Fiber) :=
  ContinuousLinearMap.pi fun index : ThroatSpatialTruncatedIndex 3 =>
    ContinuousLinearMap.proj
      ⟨index.1, index.2.trans (by omega : 3 ≤ 4)⟩

@[simp] theorem programPT06FourthJetToThirdJetContinuousLinearMap_apply
    (jet : FourthJet (Fiber := Fiber)) :
    programPT06FourthJetToThirdJetContinuousLinearMap (Fiber := Fiber) jet =
      truncateThroatSpatialMultiindexJet (by omega : 3 ≤ 4) jet := by
  rfl

/-- Continuous-linear fourth-to-third formal total-derivative shift. -/
def programPT06FourthJetTotalDerivativeContinuousLinearMap
    (direction : Fin 3) :
    FourthJet (Fiber := Fiber) →L[Real] ThirdJet (Fiber := Fiber) :=
  ContinuousLinearMap.pi fun index : ThroatSpatialTruncatedIndex 3 =>
    ContinuousLinearMap.proj
      ⟨index.1 + throatSpatialCoordinateMultiIndex direction, by
        rw [throatSpatialMultiIndexOrder_add_coordinateMultiIndex]
        omega⟩

@[simp] theorem programPT06FourthJetTotalDerivativeContinuousLinearMap_apply
    (direction : Fin 3) (jet : FourthJet (Fiber := Fiber)) :
    programPT06FourthJetTotalDerivativeContinuousLinearMap
        (Fiber := Fiber) direction jet =
      throatSpatialTotalDerivative direction jet := by
  rfl

/-- Extend a second jet by zero in all coordinates of orders three and four. -/
def programPT06SecondJetZeroExtension
    (jet : SecondJet (Fiber := Fiber)) : FourthJet (Fiber := Fiber) :=
  fun index =>
    if hIndex : throatSpatialMultiIndexOrder index.1 ≤ 2 then
      jet ⟨index.1, hIndex⟩
    else
      0

omit [NormedSpace Real Fiber] in
@[simp] theorem programPT06SecondJetZeroExtension_apply_of_order_le
    (jet : SecondJet (Fiber := Fiber))
    (index : ThroatSpatialTruncatedIndex 4)
    (hIndex : throatSpatialMultiIndexOrder index.1 ≤ 2) :
    programPT06SecondJetZeroExtension jet index =
      jet ⟨index.1, hIndex⟩ := by
  simp [programPT06SecondJetZeroExtension, hIndex]

omit [NormedSpace Real Fiber] in
@[simp] theorem programPT06SecondJetZeroExtension_apply_of_order_gt
    (jet : SecondJet (Fiber := Fiber))
    (index : ThroatSpatialTruncatedIndex 4)
    (hIndex : ¬ throatSpatialMultiIndexOrder index.1 ≤ 2) :
    programPT06SecondJetZeroExtension jet index = 0 := by
  simp [programPT06SecondJetZeroExtension, hIndex]

@[simp] theorem programPT06FourthJetToSecondJet_zeroExtension
    (jet : SecondJet (Fiber := Fiber)) :
    programPT06FourthJetToSecondJetContinuousLinearMap (Fiber := Fiber)
        (programPT06SecondJetZeroExtension jet) = jet := by
  funext index
  change
    (if hIndex : throatSpatialMultiIndexOrder index.1 ≤ 2 then
      jet ⟨index.1, hIndex⟩
    else
      0) = jet index
  split_ifs with hIndex
  · apply congrArg jet
    apply Subtype.ext
    rfl
  · exact (hIndex index.2).elim

/-- A third-jet horizontal current represents a second-order density when its
fourth-jet divergence is exactly the pullback of that density by truncation. -/
def ProgramPT06SecondOrderHorizontalCurrentFactorsDensity4D
    (density : SecondJet (Fiber := Fiber) → Real)
    (current : ProgramPT06SecondOrderHorizontalCurrent4D
      (Fiber := Fiber)) : Prop :=
  ∀ jet : FourthJet (Fiber := Fiber),
    density
        (programPT06FourthJetToSecondJetContinuousLinearMap
          (Fiber := Fiber) jet) =
      programPT06SecondOrderHorizontalCurrentDH current jet

/-- The analytic, non-circular input for the pending fourth-order Euler
telescoping calculation. -/
structure ProgramPT06SecondOrderHorizontalDivergenceSoundnessData4D
    (density : SecondJet (Fiber := Fiber) → Real)
    (current : ProgramPT06SecondOrderHorizontalCurrent4D
      (Fiber := Fiber)) : Prop where
  density_contDiff : ContDiff Real 3 density
  current_contDiff : ∀ direction, ContDiff Real 4 (current direction)
  factors : ProgramPT06SecondOrderHorizontalCurrentFactorsDensity4D
    density current

/-- Function-level form of the factorization. -/
theorem programPT06SecondOrderHorizontalCurrentFactorsDensity_function_eq
    (density : SecondJet (Fiber := Fiber) → Real)
    (current : ProgramPT06SecondOrderHorizontalCurrent4D
      (Fiber := Fiber))
    (hFactor : ProgramPT06SecondOrderHorizontalCurrentFactorsDensity4D
      density current) :
    density ∘
        programPT06FourthJetToSecondJetContinuousLinearMap
          (Fiber := Fiber) =
      programPT06SecondOrderHorizontalCurrentDH current := by
  funext jet
  exact hFactor jet

/-- A factorization on fourth jets reconstructs the original density on every
second jet by the canonical zero extension. -/
theorem programPT06SecondOrderHorizontalCurrentFactorsDensity_reconstruct
    (density : SecondJet (Fiber := Fiber) → Real)
    (current : ProgramPT06SecondOrderHorizontalCurrent4D
      (Fiber := Fiber))
    (hFactor : ProgramPT06SecondOrderHorizontalCurrentFactorsDensity4D
      density current)
    (jet : SecondJet (Fiber := Fiber)) :
    density jet =
      programPT06SecondOrderHorizontalCurrentDH current
        (programPT06SecondJetZeroExtension jet) := by
  rw [← hFactor (programPT06SecondJetZeroExtension jet)]
  exact congrArg density
    (programPT06FourthJetToSecondJet_zeroExtension jet).symm

/-- `C4` current components have a `C3` fourth-jet horizontal divergence. -/
theorem programPT06SecondOrderHorizontalCurrentDH_contDiff_three
    (current : ProgramPT06SecondOrderHorizontalCurrent4D
      (Fiber := Fiber))
    (hCurrent : ∀ direction, ContDiff Real 4 (current direction)) :
    ContDiff Real 3
      (programPT06SecondOrderHorizontalCurrentDH current) := by
  apply ContDiff.sum
  intro direction _
  have hGradient : ContDiff Real 3 (fderiv Real (current direction)) :=
    (hCurrent direction).fderiv_right (m := 3) (by norm_num)
  have hRestricted : ContDiff Real 3
      (fun jet : FourthJet (Fiber := Fiber) =>
        fderiv Real (current direction)
          (programPT06FourthJetToThirdJetContinuousLinearMap
            (Fiber := Fiber) jet)) :=
    hGradient.comp
      (programPT06FourthJetToThirdJetContinuousLinearMap
        (Fiber := Fiber)).contDiff
  have hApplied : ContDiff Real 3
      (fun jet : FourthJet (Fiber := Fiber) =>
        fderiv Real (current direction)
            (programPT06FourthJetToThirdJetContinuousLinearMap
              (Fiber := Fiber) jet)
          (programPT06FourthJetTotalDerivativeContinuousLinearMap
            (Fiber := Fiber) direction jet)) :=
    hRestricted.clm_apply
      (programPT06FourthJetTotalDerivativeContinuousLinearMap
        (Fiber := Fiber) direction).contDiff
  simpa [programPT06SecondOrderHorizontalCurrentDH,
    programPT06ThroatSpatialLocalFunctionTotalDerivative] using hApplied

/-- Every soundness datum identifies the first iterated derivative of the
pulled-back density with that of the represented divergence. -/
theorem programPT06SecondOrderHorizontalCurrentFactorsDensity_iteratedFDeriv_one
    (density : SecondJet (Fiber := Fiber) → Real)
    (current : ProgramPT06SecondOrderHorizontalCurrent4D
      (Fiber := Fiber))
    (data : ProgramPT06SecondOrderHorizontalDivergenceSoundnessData4D
      density current)
    (jet : FourthJet (Fiber := Fiber)) :
    (iteratedFDeriv Real 1 density
        (programPT06FourthJetToSecondJetContinuousLinearMap
          (Fiber := Fiber) jet)).compContinuousLinearMap
          (fun _ : Fin 1 =>
            programPT06FourthJetToSecondJetContinuousLinearMap
              (Fiber := Fiber)) =
      iteratedFDeriv Real 1
        (programPT06SecondOrderHorizontalCurrentDH current) jet := by
  rw [← ContinuousLinearMap.iteratedFDeriv_comp_right
    (programPT06FourthJetToSecondJetContinuousLinearMap (Fiber := Fiber))
    data.density_contDiff jet (by norm_num)]
  rw [programPT06SecondOrderHorizontalCurrentFactorsDensity_function_eq
    density current data.factors]

/-- Second-derivative transfer forced by the same factorization. -/
theorem programPT06SecondOrderHorizontalCurrentFactorsDensity_iteratedFDeriv_two
    (density : SecondJet (Fiber := Fiber) → Real)
    (current : ProgramPT06SecondOrderHorizontalCurrent4D
      (Fiber := Fiber))
    (data : ProgramPT06SecondOrderHorizontalDivergenceSoundnessData4D
      density current)
    (jet : FourthJet (Fiber := Fiber)) :
    (iteratedFDeriv Real 2 density
        (programPT06FourthJetToSecondJetContinuousLinearMap
          (Fiber := Fiber) jet)).compContinuousLinearMap
          (fun _ : Fin 2 =>
            programPT06FourthJetToSecondJetContinuousLinearMap
              (Fiber := Fiber)) =
      iteratedFDeriv Real 2
        (programPT06SecondOrderHorizontalCurrentDH current) jet := by
  rw [← ContinuousLinearMap.iteratedFDeriv_comp_right
    (programPT06FourthJetToSecondJetContinuousLinearMap (Fiber := Fiber))
    data.density_contDiff jet (by norm_num)]
  rw [programPT06SecondOrderHorizontalCurrentFactorsDensity_function_eq
    density current data.factors]

/-- Third-derivative transfer forced by the same factorization.  This is the
highest derivative of the density appearing in Gate922's Euler formula. -/
theorem programPT06SecondOrderHorizontalCurrentFactorsDensity_iteratedFDeriv_three
    (density : SecondJet (Fiber := Fiber) → Real)
    (current : ProgramPT06SecondOrderHorizontalCurrent4D
      (Fiber := Fiber))
    (data : ProgramPT06SecondOrderHorizontalDivergenceSoundnessData4D
      density current)
    (jet : FourthJet (Fiber := Fiber)) :
    (iteratedFDeriv Real 3 density
        (programPT06FourthJetToSecondJetContinuousLinearMap
          (Fiber := Fiber) jet)).compContinuousLinearMap
          (fun _ : Fin 3 =>
            programPT06FourthJetToSecondJetContinuousLinearMap
              (Fiber := Fiber)) =
      iteratedFDeriv Real 3
        (programPT06SecondOrderHorizontalCurrentDH current) jet := by
  rw [← ContinuousLinearMap.iteratedFDeriv_comp_right
    (programPT06FourthJetToSecondJetContinuousLinearMap (Fiber := Fiber))
    data.density_contDiff jet (by norm_num)]
  rw [programPT06SecondOrderHorizontalCurrentFactorsDensity_function_eq
    density current data.factors]

end
end P0EFTJanusProgramPT06SecondOrderHorizontalDivergenceEulerSoundness4D
end JanusFormal
