import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06ThroatSpatialFinsuppJetTower4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFramedThirdOrderJetLinearStructure4D

/-!
# Exact spatial multi-index bridge for framed third jets

The genuine degree-at-most-three `Fin 3 →₀ Nat` carrier is identified with
the symmetric framed third jet over the fixed throat basis.  All constructions
are generic in the value fiber and use no physical atlas data.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06ThroatSpatialFinsuppThirdJetBridge4D

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 400000
noncomputable section

open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPFramedThirdOrderJetConstantFiberBaseChange4D
open P0EFTJanusProgramPT06ThroatSpatialMultiindexSecondJetBridge4D
open P0EFTJanusProgramPT06ThroatSpatialFinsuppJetTower4D

universe v

variable {Fiber : Type v}
variable [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]

private abbrev SpatialThirdJet (F : Type v) :=
  ThroatSpatialMultiindexJet3 F
private abbrev SpatialSecondJet (F : Type v) :=
  ThroatSpatialMultiindexJet2 F
private abbrev FramedThirdJet (F : Type v)
    [NormedAddCommGroup F] [NormedSpace Real F] :=
  FramedThirdOrderJet ThroatCoverCoordinates F

private theorem throatContinuousLinearMap_ext
    {Target : Type*} [NormedAddCommGroup Target] [NormedSpace Real Target]
    {first second : ThroatCoverCoordinates →L[Real] Target}
    (hBasis : ∀ direction : Fin 3,
      first (programPT06ThroatSpatialBasis direction) =
        second (programPT06ThroatSpatialBasis direction)) :
    first = second := by
  apply ContinuousLinearMap.ext
  intro vector
  rw [← programPT06ThroatSpatialBasis.sum_repr vector]
  simp only [map_sum, map_smul, hBasis]

/-! ## Canonical multi-indices -/

def throatSpatialThirdJetZeroIndex : ThroatSpatialTruncatedIndex 3 :=
  ⟨0, by simp⟩

def throatSpatialThirdJetFirstIndex
    (direction : Fin 3) : ThroatSpatialTruncatedIndex 3 :=
  ⟨throatSpatialCoordinateMultiIndex direction, by simp⟩

def throatSpatialThirdJetSecondIndex
    (first second : Fin 3) : ThroatSpatialTruncatedIndex 3 :=
  ⟨throatSpatialCoordinateMultiIndex first +
      throatSpatialCoordinateMultiIndex second, by
    rw [throatSpatialMultiIndexOrder_add]
    simp⟩

def throatSpatialThirdJetThirdIndex
    (first second third : Fin 3) : ThroatSpatialTruncatedIndex 3 :=
  ⟨throatSpatialCoordinateMultiIndex first +
      throatSpatialCoordinateMultiIndex second +
      throatSpatialCoordinateMultiIndex third, by
    rw [throatSpatialMultiIndexOrder_add,
      throatSpatialMultiIndexOrder_add]
    simp⟩

private theorem throatSpatialThirdJetSecondIndex_swap
    (first second : Fin 3) :
    throatSpatialThirdJetSecondIndex first second =
      throatSpatialThirdJetSecondIndex second first := by
  apply Subtype.ext
  change
    throatSpatialCoordinateMultiIndex first +
        throatSpatialCoordinateMultiIndex second =
      throatSpatialCoordinateMultiIndex second +
        throatSpatialCoordinateMultiIndex first
  ac_rfl

private theorem throatSpatialThirdJetThirdIndex_swap_first_second
    (first second third : Fin 3) :
    throatSpatialThirdJetThirdIndex first second third =
      throatSpatialThirdJetThirdIndex second first third := by
  apply Subtype.ext
  change
    throatSpatialCoordinateMultiIndex first +
          throatSpatialCoordinateMultiIndex second +
        throatSpatialCoordinateMultiIndex third =
      throatSpatialCoordinateMultiIndex second +
          throatSpatialCoordinateMultiIndex first +
        throatSpatialCoordinateMultiIndex third
  ac_rfl

private theorem throatSpatialThirdJetThirdIndex_swap_second_third
    (first second third : Fin 3) :
    throatSpatialThirdJetThirdIndex first second third =
      throatSpatialThirdJetThirdIndex first third second := by
  apply Subtype.ext
  change
    throatSpatialCoordinateMultiIndex first +
          throatSpatialCoordinateMultiIndex second +
        throatSpatialCoordinateMultiIndex third =
      throatSpatialCoordinateMultiIndex first +
          throatSpatialCoordinateMultiIndex third +
        throatSpatialCoordinateMultiIndex second
  ac_rfl

/-! ## Reconstruction of continuous derivatives -/

def programPT06ThroatFirstDerivativeFromFinsuppThirdJet
    (jet : SpatialThirdJet Fiber) :
    ThroatCoverCoordinates →L[Real] Fiber :=
  LinearMap.toContinuousLinearMap
    (programPT06ThroatSpatialBasis.constr Real fun direction =>
      jet (throatSpatialThirdJetFirstIndex direction))

@[simp] theorem programPT06ThroatFirstDerivativeFromFinsuppThirdJet_basis
    (jet : SpatialThirdJet Fiber) (direction : Fin 3) :
    programPT06ThroatFirstDerivativeFromFinsuppThirdJet jet
        (programPT06ThroatSpatialBasis direction) =
      jet (throatSpatialThirdJetFirstIndex direction) := by
  simp [programPT06ThroatFirstDerivativeFromFinsuppThirdJet]

def programPT06ThroatSecondDerivativeFromFinsuppThirdJet
    (jet : SpatialThirdJet Fiber) :
    ThroatCoverCoordinates →L[Real]
      ThroatCoverCoordinates →L[Real] Fiber :=
  LinearMap.toContinuousLinearMap
    (programPT06ThroatSpatialBasis.constr Real fun first =>
      LinearMap.toContinuousLinearMap
        (programPT06ThroatSpatialBasis.constr Real fun second =>
          jet (throatSpatialThirdJetSecondIndex first second)))

@[simp] theorem programPT06ThroatSecondDerivativeFromFinsuppThirdJet_basis
    (jet : SpatialThirdJet Fiber) (first second : Fin 3) :
    programPT06ThroatSecondDerivativeFromFinsuppThirdJet jet
        (programPT06ThroatSpatialBasis first)
        (programPT06ThroatSpatialBasis second) =
      jet (throatSpatialThirdJetSecondIndex first second) := by
  simp [programPT06ThroatSecondDerivativeFromFinsuppThirdJet]

private theorem
    programPT06ThroatSecondDerivativeFromFinsuppThirdJet_symmetric
    (jet : SpatialThirdJet Fiber) (first second : ThroatCoverCoordinates) :
    programPT06ThroatSecondDerivativeFromFinsuppThirdJet jet first second =
      programPT06ThroatSecondDerivativeFromFinsuppThirdJet jet second first := by
  let derivative := programPT06ThroatSecondDerivativeFromFinsuppThirdJet jet
  have hFlip : derivative = derivative.flip := by
    apply throatContinuousLinearMap_ext
    intro firstDirection
    apply throatContinuousLinearMap_ext
    intro secondDirection
    simpa [derivative] using congrArg jet
      (throatSpatialThirdJetSecondIndex_swap
        firstDirection secondDirection)
  have hAt := congrArg (fun map => map first second) hFlip
  simpa [derivative] using hAt

def programPT06ThroatThirdDerivativeFromFinsuppThirdJet
    (jet : SpatialThirdJet Fiber) :
    ThroatCoverCoordinates →L[Real]
      ThroatCoverCoordinates →L[Real]
        ThroatCoverCoordinates →L[Real] Fiber :=
  LinearMap.toContinuousLinearMap
    (programPT06ThroatSpatialBasis.constr Real fun first =>
      LinearMap.toContinuousLinearMap
        (programPT06ThroatSpatialBasis.constr Real fun second =>
          LinearMap.toContinuousLinearMap
            (programPT06ThroatSpatialBasis.constr Real fun third =>
              jet (throatSpatialThirdJetThirdIndex first second third))))

@[simp] theorem programPT06ThroatThirdDerivativeFromFinsuppThirdJet_basis
    (jet : SpatialThirdJet Fiber) (first second third : Fin 3) :
    programPT06ThroatThirdDerivativeFromFinsuppThirdJet jet
        (programPT06ThroatSpatialBasis first)
        (programPT06ThroatSpatialBasis second)
        (programPT06ThroatSpatialBasis third) =
      jet (throatSpatialThirdJetThirdIndex first second third) := by
  simp [programPT06ThroatThirdDerivativeFromFinsuppThirdJet]

private theorem
    programPT06ThroatThirdDerivativeFromFinsuppThirdJet_swap_first_second
    (jet : SpatialThirdJet Fiber)
    (first second third : ThroatCoverCoordinates) :
    programPT06ThroatThirdDerivativeFromFinsuppThirdJet jet
        first second third =
      programPT06ThroatThirdDerivativeFromFinsuppThirdJet jet
        second first third := by
  let derivative := programPT06ThroatThirdDerivativeFromFinsuppThirdJet jet
  have hFlip : derivative = derivative.flip := by
    apply throatContinuousLinearMap_ext
      (Target := ThroatCoverCoordinates →L[Real]
        ThroatCoverCoordinates →L[Real] Fiber)
    intro firstDirection
    apply throatContinuousLinearMap_ext
      (Target := ThroatCoverCoordinates →L[Real] Fiber)
    intro secondDirection
    apply throatContinuousLinearMap_ext (Target := Fiber)
    intro thirdDirection
    simpa [derivative] using congrArg jet
      (throatSpatialThirdJetThirdIndex_swap_first_second
        firstDirection secondDirection thirdDirection)
  have hAt := congrArg (fun map => map first second third) hFlip
  simpa [derivative] using hAt

private theorem
    programPT06ThroatThirdDerivativeFromFinsuppThirdJet_swap_second_third
    (jet : SpatialThirdJet Fiber)
    (first second third : ThroatCoverCoordinates) :
    programPT06ThroatThirdDerivativeFromFinsuppThirdJet jet
        first second third =
      programPT06ThroatThirdDerivativeFromFinsuppThirdJet jet
        first third second := by
  let derivative := programPT06ThroatThirdDerivativeFromFinsuppThirdJet jet
  have hAtBasis (firstDirection secondDirection thirdDirection : Fin 3) :
      derivative (programPT06ThroatSpatialBasis firstDirection)
          (programPT06ThroatSpatialBasis secondDirection)
          (programPT06ThroatSpatialBasis thirdDirection) =
        derivative (programPT06ThroatSpatialBasis firstDirection)
          (programPT06ThroatSpatialBasis thirdDirection)
          (programPT06ThroatSpatialBasis secondDirection) := by
    simpa [derivative] using congrArg jet
      (throatSpatialThirdJetThirdIndex_swap_second_third
        firstDirection secondDirection thirdDirection)
  have hAtFirst : derivative first = (derivative first).flip := by
    apply throatContinuousLinearMap_ext
      (Target := ThroatCoverCoordinates →L[Real] Fiber)
    intro secondDirection
    apply throatContinuousLinearMap_ext (Target := Fiber)
    intro thirdDirection
    change derivative first
        (programPT06ThroatSpatialBasis secondDirection)
        (programPT06ThroatSpatialBasis thirdDirection) =
      derivative first
        (programPT06ThroatSpatialBasis thirdDirection)
        (programPT06ThroatSpatialBasis secondDirection)
    rw [← programPT06ThroatSpatialBasis.sum_repr first]
    simp only [map_sum, map_smul, sum_apply, smul_apply]
    apply Finset.sum_congr rfl
    intro firstDirection _
    rw [hAtBasis firstDirection secondDirection thirdDirection]
  have hAt := congrArg (fun map => map second third) hAtFirst
  simpa [derivative] using hAt

/-! ## The two directions of the bridge -/

def programPT06ThroatSpatialThirdJetToFramed
    (jet : SpatialThirdJet Fiber) : FramedThirdJet Fiber where
  value := jet throatSpatialThirdJetZeroIndex
  firstDerivative := programPT06ThroatFirstDerivativeFromFinsuppThirdJet jet
  secondDerivative := programPT06ThroatSecondDerivativeFromFinsuppThirdJet jet
  secondDerivative_symmetric :=
    programPT06ThroatSecondDerivativeFromFinsuppThirdJet_symmetric jet
  thirdDerivative := programPT06ThroatThirdDerivativeFromFinsuppThirdJet jet
  thirdDerivative_swap_first_second :=
    programPT06ThroatThirdDerivativeFromFinsuppThirdJet_swap_first_second jet
  thirdDerivative_swap_second_third :=
    programPT06ThroatThirdDerivativeFromFinsuppThirdJet_swap_second_third jet

@[simp] theorem programPT06ThroatSpatialThirdJetToFramed_value
    (jet : SpatialThirdJet Fiber) :
    (programPT06ThroatSpatialThirdJetToFramed jet).value =
      jet throatSpatialThirdJetZeroIndex :=
  rfl

@[simp] theorem programPT06ThroatSpatialThirdJetToFramed_firstDerivative_basis
    (jet : SpatialThirdJet Fiber) (direction : Fin 3) :
    (programPT06ThroatSpatialThirdJetToFramed jet).firstDerivative
        (programPT06ThroatSpatialBasis direction) =
      jet (throatSpatialThirdJetFirstIndex direction) := by
  exact programPT06ThroatFirstDerivativeFromFinsuppThirdJet_basis jet direction

@[simp] theorem programPT06ThroatSpatialThirdJetToFramed_secondDerivative_basis
    (jet : SpatialThirdJet Fiber) (first second : Fin 3) :
    (programPT06ThroatSpatialThirdJetToFramed jet).secondDerivative
        (programPT06ThroatSpatialBasis first)
        (programPT06ThroatSpatialBasis second) =
      jet (throatSpatialThirdJetSecondIndex first second) := by
  exact programPT06ThroatSecondDerivativeFromFinsuppThirdJet_basis
    jet first second

@[simp] theorem programPT06ThroatSpatialThirdJetToFramed_thirdDerivative_basis
    (jet : SpatialThirdJet Fiber) (first second third : Fin 3) :
    (programPT06ThroatSpatialThirdJetToFramed jet).thirdDerivative
        (programPT06ThroatSpatialBasis first)
        (programPT06ThroatSpatialBasis second)
        (programPT06ThroatSpatialBasis third) =
      jet (throatSpatialThirdJetThirdIndex first second third) := by
  exact programPT06ThroatThirdDerivativeFromFinsuppThirdJet_basis
    jet first second third

private def framedThirdJetCoefficient
    (jet : FramedThirdJet Fiber) (index : ThroatSpatialMultiIndex) : Fiber :=
  match index 0, index 1, index 2 with
  | 0, 0, 0 => jet.value
  | 1, 0, 0 => jet.firstDerivative (programPT06ThroatSpatialBasis 0)
  | 0, 1, 0 => jet.firstDerivative (programPT06ThroatSpatialBasis 1)
  | 0, 0, 1 => jet.firstDerivative (programPT06ThroatSpatialBasis 2)
  | 2, 0, 0 => jet.secondDerivative
      (programPT06ThroatSpatialBasis 0) (programPT06ThroatSpatialBasis 0)
  | 1, 1, 0 => jet.secondDerivative
      (programPT06ThroatSpatialBasis 0) (programPT06ThroatSpatialBasis 1)
  | 1, 0, 1 => jet.secondDerivative
      (programPT06ThroatSpatialBasis 0) (programPT06ThroatSpatialBasis 2)
  | 0, 2, 0 => jet.secondDerivative
      (programPT06ThroatSpatialBasis 1) (programPT06ThroatSpatialBasis 1)
  | 0, 1, 1 => jet.secondDerivative
      (programPT06ThroatSpatialBasis 1) (programPT06ThroatSpatialBasis 2)
  | 0, 0, 2 => jet.secondDerivative
      (programPT06ThroatSpatialBasis 2) (programPT06ThroatSpatialBasis 2)
  | 3, 0, 0 => jet.thirdDerivative
      (programPT06ThroatSpatialBasis 0) (programPT06ThroatSpatialBasis 0)
      (programPT06ThroatSpatialBasis 0)
  | 2, 1, 0 => jet.thirdDerivative
      (programPT06ThroatSpatialBasis 0) (programPT06ThroatSpatialBasis 0)
      (programPT06ThroatSpatialBasis 1)
  | 2, 0, 1 => jet.thirdDerivative
      (programPT06ThroatSpatialBasis 0) (programPT06ThroatSpatialBasis 0)
      (programPT06ThroatSpatialBasis 2)
  | 1, 2, 0 => jet.thirdDerivative
      (programPT06ThroatSpatialBasis 0) (programPT06ThroatSpatialBasis 1)
      (programPT06ThroatSpatialBasis 1)
  | 1, 1, 1 => jet.thirdDerivative
      (programPT06ThroatSpatialBasis 0) (programPT06ThroatSpatialBasis 1)
      (programPT06ThroatSpatialBasis 2)
  | 1, 0, 2 => jet.thirdDerivative
      (programPT06ThroatSpatialBasis 0) (programPT06ThroatSpatialBasis 2)
      (programPT06ThroatSpatialBasis 2)
  | 0, 3, 0 => jet.thirdDerivative
      (programPT06ThroatSpatialBasis 1) (programPT06ThroatSpatialBasis 1)
      (programPT06ThroatSpatialBasis 1)
  | 0, 2, 1 => jet.thirdDerivative
      (programPT06ThroatSpatialBasis 1) (programPT06ThroatSpatialBasis 1)
      (programPT06ThroatSpatialBasis 2)
  | 0, 1, 2 => jet.thirdDerivative
      (programPT06ThroatSpatialBasis 1) (programPT06ThroatSpatialBasis 2)
      (programPT06ThroatSpatialBasis 2)
  | 0, 0, 3 => jet.thirdDerivative
      (programPT06ThroatSpatialBasis 2) (programPT06ThroatSpatialBasis 2)
      (programPT06ThroatSpatialBasis 2)
  | _, _, _ => 0

def programPT06FramedThirdJetToThroatSpatial
    (jet : FramedThirdJet Fiber) : SpatialThirdJet Fiber :=
  fun index => framedThirdJetCoefficient jet index.1

/-! ## Inverses, linearity and truncation -/

private theorem programPT06FramedThirdJetToThroatSpatial_toFramed
    (jet : SpatialThirdJet Fiber) :
    programPT06FramedThirdJetToThroatSpatial
        (programPT06ThroatSpatialThirdJetToFramed jet) = jet := by
  funext index
  have hOrder :
      index.1 0 + index.1 1 + index.1 2 ≤ 3 := by
    have h := index.2
    simp only [throatSpatialMultiIndexOrder, Finsupp.degree_eq_sum,
      Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
    norm_num at h ⊢
    omega
  have hZero : index.1 0 ≤ 3 := by omega
  have hOne : index.1 1 ≤ 3 := by omega
  have hTwo : index.1 2 ≤ 3 := by omega
  interval_cases h0 : index.1 0 <;>
    interval_cases h1 : index.1 1 <;>
      interval_cases h2 : index.1 2 <;>
        simp_all [programPT06FramedThirdJetToThroatSpatial,
          framedThirdJetCoefficient,
          programPT06ThroatSpatialThirdJetToFramed,
          throatSpatialThirdJetZeroIndex,
          throatSpatialThirdJetFirstIndex,
          throatSpatialThirdJetSecondIndex,
          throatSpatialThirdJetThirdIndex,
          throatSpatialCoordinateMultiIndex]
  all_goals
    congr 1
    apply Subtype.ext
    ext direction
    fin_cases direction <;> simp_all

private theorem programPT06ThroatSpatialThirdJetToFramed_toSpatial
    (jet : FramedThirdJet Fiber) :
    programPT06ThroatSpatialThirdJetToFramed
        (programPT06FramedThirdJetToThroatSpatial jet) = jet := by
  apply FramedThirdOrderJet.ext_components
  · apply FramedSecondOrderJet.ext_components
    · simp [programPT06ThroatSpatialThirdJetToFramed,
        programPT06FramedThirdJetToThroatSpatial,
        framedThirdJetCoefficient, throatSpatialThirdJetZeroIndex]
    · apply throatContinuousLinearMap_ext
      intro direction
      fin_cases direction <;>
        simp [programPT06FramedThirdJetToThroatSpatial,
          framedThirdJetCoefficient, throatSpatialThirdJetFirstIndex,
          throatSpatialCoordinateMultiIndex]
    · apply throatContinuousLinearMap_ext
      intro first
      apply throatContinuousLinearMap_ext
      intro second
      fin_cases first <;> fin_cases second <;>
        simp [programPT06FramedThirdJetToThroatSpatial,
          framedThirdJetCoefficient, throatSpatialThirdJetSecondIndex,
          throatSpatialCoordinateMultiIndex,
          jet.secondDerivative_symmetric]
      all_goals exact jet.secondDerivative_symmetric _ _
  · apply throatContinuousLinearMap_ext
      (Target := ThroatCoverCoordinates →L[Real]
        ThroatCoverCoordinates →L[Real] Fiber)
    intro first
    apply throatContinuousLinearMap_ext
      (Target := ThroatCoverCoordinates →L[Real] Fiber)
    intro second
    apply throatContinuousLinearMap_ext (Target := Fiber)
    intro third
    have hSwapFirstThird (a b c : ThroatCoverCoordinates) :
        jet.thirdDerivative a b c = jet.thirdDerivative c b a := by
      calc
        jet.thirdDerivative a b c = jet.thirdDerivative b a c :=
          jet.thirdDerivative_swap_first_second _ _ _
        _ = jet.thirdDerivative b c a :=
          jet.thirdDerivative_swap_second_third _ _ _
        _ = jet.thirdDerivative c b a :=
          jet.thirdDerivative_swap_first_second _ _ _
    have hCycleLeft (a b c : ThroatCoverCoordinates) :
        jet.thirdDerivative a b c = jet.thirdDerivative b c a := by
      calc
        jet.thirdDerivative a b c = jet.thirdDerivative b a c :=
          jet.thirdDerivative_swap_first_second _ _ _
        _ = jet.thirdDerivative b c a :=
          jet.thirdDerivative_swap_second_third _ _ _
    have hCycleRight (a b c : ThroatCoverCoordinates) :
        jet.thirdDerivative a b c = jet.thirdDerivative c a b := by
      calc
        jet.thirdDerivative a b c = jet.thirdDerivative a c b :=
          jet.thirdDerivative_swap_second_third _ _ _
        _ = jet.thirdDerivative c a b :=
          jet.thirdDerivative_swap_first_second _ _ _
    rw [programPT06ThroatSpatialThirdJetToFramed_thirdDerivative_basis]
    fin_cases first <;> fin_cases second <;> fin_cases third <;>
      simp [programPT06FramedThirdJetToThroatSpatial,
        framedThirdJetCoefficient, throatSpatialThirdJetThirdIndex,
        throatSpatialCoordinateMultiIndex]
    all_goals first
      | rfl
      | exact jet.thirdDerivative_swap_first_second _ _ _
      | exact jet.thirdDerivative_swap_second_third _ _ _
      | exact hSwapFirstThird _ _ _
      | exact hCycleLeft _ _ _
      | exact hCycleRight _ _ _

private theorem programPT06ThroatSpatialThirdJetToFramed_add
    (first second : SpatialThirdJet Fiber) :
    programPT06ThroatSpatialThirdJetToFramed (first + second) =
      programPT06ThroatSpatialThirdJetToFramed first +
        programPT06ThroatSpatialThirdJetToFramed second := by
  apply FramedThirdOrderJet.ext_components
  · apply FramedSecondOrderJet.ext_components
    · rfl
    · apply throatContinuousLinearMap_ext
      intro direction
      simp
    · apply throatContinuousLinearMap_ext
      intro firstDirection
      apply throatContinuousLinearMap_ext
      intro secondDirection
      simp
  · apply throatContinuousLinearMap_ext
      (Target := ThroatCoverCoordinates →L[Real]
        ThroatCoverCoordinates →L[Real] Fiber)
    intro firstDirection
    apply throatContinuousLinearMap_ext
      (Target := ThroatCoverCoordinates →L[Real] Fiber)
    intro secondDirection
    apply throatContinuousLinearMap_ext (Target := Fiber)
    intro thirdDirection
    simp

private theorem programPT06ThroatSpatialThirdJetToFramed_smul
    (scalar : Real) (jet : SpatialThirdJet Fiber) :
    programPT06ThroatSpatialThirdJetToFramed (scalar • jet) =
      scalar • programPT06ThroatSpatialThirdJetToFramed jet := by
  apply FramedThirdOrderJet.ext_components
  · apply FramedSecondOrderJet.ext_components
    · rfl
    · apply throatContinuousLinearMap_ext
      intro direction
      simp
    · apply throatContinuousLinearMap_ext
      intro firstDirection
      apply throatContinuousLinearMap_ext
      intro secondDirection
      simp
  · apply throatContinuousLinearMap_ext
      (Target := ThroatCoverCoordinates →L[Real]
        ThroatCoverCoordinates →L[Real] Fiber)
    intro firstDirection
    apply throatContinuousLinearMap_ext
      (Target := ThroatCoverCoordinates →L[Real] Fiber)
    intro secondDirection
    apply throatContinuousLinearMap_ext (Target := Fiber)
    intro thirdDirection
    simp

/-- Exact generic linear equivalence between genuine spatial coefficients
through order three and the symmetric framed third jet. -/
def programPT06ThroatSpatialFinsuppThirdJetFramedLinearEquiv :
    SpatialThirdJet Fiber ≃ₗ[Real] FramedThirdJet Fiber where
  toFun := programPT06ThroatSpatialThirdJetToFramed
  invFun := programPT06FramedThirdJetToThroatSpatial
  left_inv := programPT06FramedThirdJetToThroatSpatial_toFramed
  right_inv := programPT06ThroatSpatialThirdJetToFramed_toSpatial
  map_add' := programPT06ThroatSpatialThirdJetToFramed_add
  map_smul' := programPT06ThroatSpatialThirdJetToFramed_smul

@[simp] theorem programPT06ThroatSpatialFinsuppThirdJetFramedLinearEquiv_apply
    (jet : SpatialThirdJet Fiber) :
    programPT06ThroatSpatialFinsuppThirdJetFramedLinearEquiv jet =
      programPT06ThroatSpatialThirdJetToFramed jet :=
  rfl

@[simp] theorem programPT06ThroatSpatialFinsuppThirdJetFramedLinearEquiv_symm_apply
    (jet : FramedThirdJet Fiber) :
    programPT06ThroatSpatialFinsuppThirdJetFramedLinearEquiv.symm jet =
      programPT06FramedThirdJetToThroatSpatial jet :=
  rfl

/-- Extend a spatial second jet by zero on the homogeneous cubic indices. -/
private def spatialSecondJetZeroExtend
    (jet : SpatialSecondJet Fiber) : SpatialThirdJet Fiber :=
  fun index =>
    if hOrder : throatSpatialMultiIndexOrder index.1 ≤ 2 then
      jet ⟨index.1, hOrder⟩
    else
      0

/-- Generic framed second jet reconstructed from genuine bounded spatial
multi-indices.  This definition is kept here so the J3 truncation theorem has
no dependency on a physical product bridge. -/
def programPT06ThroatSpatialFinsuppSecondJetToFramed
    (jet : SpatialSecondJet Fiber) :
    FramedSecondOrderJet ThroatCoverCoordinates Fiber :=
  (programPT06ThroatSpatialThirdJetToFramed
    (spatialSecondJetZeroExtend jet)).toFramedSecondOrderJet

/-- Forgetting the cubic coefficient agrees exactly with Gate875 spatial
truncation followed by the generic framed second-jet reconstruction. -/
theorem programPT06ThroatSpatialFinsuppThirdJetFramedLinearEquiv_truncate
    (jet : SpatialThirdJet Fiber) :
    (programPT06ThroatSpatialFinsuppThirdJetFramedLinearEquiv jet
      ).toFramedSecondOrderJet =
      programPT06ThroatSpatialFinsuppSecondJetToFramed
        (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 3) jet) := by
  apply FramedSecondOrderJet.ext_components
  · simp [programPT06ThroatSpatialFinsuppThirdJetFramedLinearEquiv,
      programPT06ThroatSpatialFinsuppSecondJetToFramed,
      spatialSecondJetZeroExtend, programPT06ThroatSpatialThirdJetToFramed,
      throatSpatialThirdJetZeroIndex,
      truncateThroatSpatialMultiindexJet]
  · apply throatContinuousLinearMap_ext
    intro direction
    simp [programPT06ThroatSpatialFinsuppThirdJetFramedLinearEquiv,
      programPT06ThroatSpatialFinsuppSecondJetToFramed,
      spatialSecondJetZeroExtend, programPT06ThroatSpatialThirdJetToFramed,
      throatSpatialThirdJetFirstIndex,
      truncateThroatSpatialMultiindexJet]
  · apply throatContinuousLinearMap_ext
    intro first
    apply throatContinuousLinearMap_ext
    intro second
    simp [programPT06ThroatSpatialFinsuppThirdJetFramedLinearEquiv,
      programPT06ThroatSpatialFinsuppSecondJetToFramed,
      spatialSecondJetZeroExtend, programPT06ThroatSpatialThirdJetToFramed,
      throatSpatialThirdJetSecondIndex,
      truncateThroatSpatialMultiindexJet,
      throatSpatialMultiIndexOrder_add]

end
end P0EFTJanusProgramPT06ThroatSpatialFinsuppThirdJetBridge4D
end JanusFormal
