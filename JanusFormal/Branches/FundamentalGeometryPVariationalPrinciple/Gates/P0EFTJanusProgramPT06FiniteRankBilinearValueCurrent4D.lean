import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06DirectedQuadraticValueCurrent4D

/-!
# Finite-rank bilinear value currents in all throat directions

This gate closes the directed rank-one construction under finite linear
combinations, independently in each of the three throat directions.  Thus a
current component is the diagonal of a finite-rank continuous bilinear form
`sum_r c_r * left_r (u) * right_r (u)`.  Its genuine total divergence is the
corresponding homogeneous quadratic density, and Gate880's Euler operator
annihilates the whole finite span.

No representation theorem for arbitrary continuous bilinear forms and no
classification of all polynomial null densities is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06FiniteRankBilinearValueCurrent4D

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open P0EFTJanusProgramPT06ThroatSpatialFinsuppJetTower4D
open P0EFTJanusProgramPT06LocalFunctionTotalDerivative4D
open P0EFTJanusProgramPT06SecondOrderLocalEuler4D
open P0EFTJanusProgramPT06DirectedQuadraticValueCurrent4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

universe u v w z

variable {Fiber : Type u} [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
variable {Rank : Type v} [Fintype Rank]

private abbrev FirstJet := ThroatSpatialMultiindexJet1 Fiber
private abbrev SecondJet := ThroatSpatialMultiindexJet2 Fiber
private abbrev ThirdJet := ThroatSpatialMultiindexJet3 Fiber
private abbrev FourthJet := ThroatSpatialMultiindexJet4 Fiber

/-- A finite-rank bilinear current in each of the three throat directions. -/
structure ProgramPT06FiniteRankBilinearValueCurrent4D
    (Fiber : Type u) [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
    (Rank : Type v) [Fintype Rank] where
  coefficient : Fin 3 → Rank → Real
  left : Fin 3 → Rank → Fiber →L[Real] Real
  right : Fin 3 → Rank → Fiber →L[Real] Real

/-- The directed rank-one atom indexed by one direction and rank label. -/
def programPT06FiniteRankBilinearValueAtom
    (current : ProgramPT06FiniteRankBilinearValueCurrent4D Fiber Rank)
    (index : Fin 3 × Rank) :
    ProgramPT06DirectedQuadraticValueCurrent4D Fiber where
  direction := index.1
  left := current.left index.1 index.2
  right := current.right index.1 index.2

/-- One current component, expressed as a finite-rank bilinear diagonal. -/
def programPT06FiniteRankBilinearValueCurrentComponent
    (current : ProgramPT06FiniteRankBilinearValueCurrent4D Fiber Rank)
    (direction : Fin 3) : FirstJet (Fiber := Fiber) → Real :=
  fun jet => ∑ term : Rank,
    current.coefficient direction term •
      programPT06DirectedQuadraticValueCurrentComponent
        (programPT06FiniteRankBilinearValueAtom current (direction, term)) jet

/-- The actual `dH` divergence of all three finite-rank components. -/
def programPT06FiniteRankBilinearValueCurrentDivergence
    (current : ProgramPT06FiniteRankBilinearValueCurrent4D Fiber Rank) :
    SecondJet (Fiber := Fiber) → Real :=
  fun jet => ∑ direction : Fin 3,
    programPT06ThroatSpatialLocalFunctionTotalDerivative direction
      (programPT06FiniteRankBilinearValueCurrentComponent current direction) jet

/-- Explicit quadratic density assembled from every directed atom. -/
def programPT06FiniteRankBilinearValueDensityEvaluation
    (current : ProgramPT06FiniteRankBilinearValueCurrent4D Fiber Rank) :
    SecondJet (Fiber := Fiber) → Real :=
  fun jet => ∑ index : Fin 3 × Rank,
    current.coefficient index.1 index.2 •
      programPT06DirectedQuadraticValueDensityEvaluation
        (programPT06FiniteRankBilinearValueAtom current index) jet

private theorem programPT06LocalFunctionTotalDerivative_fin_sum
    {Index : Type z} [Fintype Index]
    {Target : Type w} [NormedAddCommGroup Target] [NormedSpace Real Target]
    {order : Nat} (coefficient : Index → Real)
    (family : Index →
      TruncatedThroatSpatialMultiindexJet Fiber order → Target)
    (hDifferentiable : ∀ index, Differentiable Real (family index))
    (direction : Fin 3) :
    programPT06ThroatSpatialLocalFunctionTotalDerivative direction
        (fun jet => ∑ index : Index, coefficient index • family index jet) =
      fun jet => ∑ index : Index, coefficient index •
        programPT06ThroatSpatialLocalFunctionTotalDerivative direction
          (family index) jet := by
  funext jet
  let truncated :=
    truncateThroatSpatialMultiindexJet (Nat.le_succ order) jet
  have hDerivative :
      HasFDerivAt
        (fun candidate =>
          ∑ index : Index, coefficient index • family index candidate)
        (∑ index : Index,
          coefficient index • fderiv Real (family index) truncated)
        truncated := by
    apply HasFDerivAt.fun_sum
    intro index _
    exact ((hDifferentiable index).differentiableAt.hasFDerivAt).const_smul
      (coefficient index)
  rw [programPT06ThroatSpatialLocalFunctionTotalDerivative_eq_of_hasFDerivAt
    direction _ jet _ hDerivative]
  simp [programPT06ThroatSpatialLocalFunctionTotalDerivative, truncated]

private theorem programPT06VerticalPartialDerivative_fin_sum
    {Index : Type z} [Fintype Index]
    {Target : Type w} [NormedAddCommGroup Target] [NormedSpace Real Target]
    {order : Nat} (coefficient : Index → Real)
    (family : Index →
      TruncatedThroatSpatialMultiindexJet Fiber order → Target)
    (hDifferentiable : ∀ index, Differentiable Real (family index))
    (jet : TruncatedThroatSpatialMultiindexJet Fiber order)
    (multiIndex : ThroatSpatialTruncatedIndex order) :
    programPT06ThroatSpatialVerticalPartialDerivative
        (fun candidate =>
          ∑ index : Index, coefficient index • family index candidate)
        jet multiIndex =
      ∑ index : Index, coefficient index •
        programPT06ThroatSpatialVerticalPartialDerivative
          (family index) jet multiIndex := by
  have hDerivative :
      HasFDerivAt
        (fun candidate =>
          ∑ index : Index, coefficient index • family index candidate)
        (∑ index : Index,
          coefficient index • fderiv Real (family index) jet) jet := by
    apply HasFDerivAt.fun_sum
    intro index _
    exact ((hDifferentiable index).differentiableAt.hasFDerivAt).const_smul
      (coefficient index)
  rw [programPT06ThroatSpatialVerticalPartialDerivative_eq_of_hasFDerivAt
    _ jet multiIndex _ hDerivative]
  ext variation
  simp [programPT06ThroatSpatialVerticalPartialDerivative]

private theorem programPT06DirectedAtomComponent_differentiable
    (current : ProgramPT06FiniteRankBilinearValueCurrent4D Fiber Rank)
    (index : Fin 3 × Rank) :
    Differentiable Real
      (programPT06DirectedQuadraticValueCurrentComponent
        (programPT06FiniteRankBilinearValueAtom current index)) := by
  intro jet
  exact
    (programPT06DirectedQuadraticValueCurrentComponent_hasFDerivAt
      (programPT06FiniteRankBilinearValueAtom current index) jet).differentiableAt

private theorem programPT06DirectedAtomDensity_differentiable
    (current : ProgramPT06FiniteRankBilinearValueCurrent4D Fiber Rank)
    (index : Fin 3 × Rank) :
    Differentiable Real
      (programPT06DirectedQuadraticValueDensityEvaluation
        (programPT06FiniteRankBilinearValueAtom current index)) := by
  intro jet
  exact
    (programPT06DirectedQuadraticValueDensityEvaluation_hasFDerivAt
      (programPT06FiniteRankBilinearValueAtom current index) jet).differentiableAt

theorem programPT06FiniteRankBilinearValueCurrentComponent_totalDerivative
    (current : ProgramPT06FiniteRankBilinearValueCurrent4D Fiber Rank)
    (direction : Fin 3) :
    programPT06ThroatSpatialLocalFunctionTotalDerivative direction
        (programPT06FiniteRankBilinearValueCurrentComponent current direction) =
      fun jet => ∑ term : Rank,
        current.coefficient direction term •
          programPT06DirectedQuadraticValueCurrentDivergence
            (programPT06FiniteRankBilinearValueAtom current
              (direction, term)) jet := by
  unfold programPT06FiniteRankBilinearValueCurrentComponent
  simpa only [programPT06DirectedQuadraticValueCurrentDivergence,
    programPT06FiniteRankBilinearValueAtom] using
    (programPT06LocalFunctionTotalDerivative_fin_sum
      (Fiber := Fiber)
      (coefficient := current.coefficient direction)
      (family := fun term =>
        programPT06DirectedQuadraticValueCurrentComponent
          (programPT06FiniteRankBilinearValueAtom current
            (direction, term)))
      (fun term => programPT06DirectedAtomComponent_differentiable
        current (direction, term)) direction)

/-- The assembled density is exactly the genuine three-direction `dH`. -/
theorem programPT06FiniteRankBilinearValueCurrentDivergence_eq_density
    (current : ProgramPT06FiniteRankBilinearValueCurrent4D Fiber Rank) :
    programPT06FiniteRankBilinearValueCurrentDivergence current =
      programPT06FiniteRankBilinearValueDensityEvaluation current := by
  funext jet
  calc
    programPT06FiniteRankBilinearValueCurrentDivergence current jet =
        ∑ direction : Fin 3, ∑ term : Rank,
          current.coefficient direction term •
            programPT06DirectedQuadraticValueCurrentDivergence
              (programPT06FiniteRankBilinearValueAtom current
                (direction, term)) jet := by
      unfold programPT06FiniteRankBilinearValueCurrentDivergence
      apply Finset.sum_congr rfl
      intro direction _
      exact congrFun
        (programPT06FiniteRankBilinearValueCurrentComponent_totalDerivative
          current direction) jet
    _ = ∑ direction : Fin 3, ∑ term : Rank,
          current.coefficient direction term •
            programPT06DirectedQuadraticValueDensityEvaluation
              (programPT06FiniteRankBilinearValueAtom current
                (direction, term)) jet := by
      apply Finset.sum_congr rfl
      intro direction _
      apply Finset.sum_congr rfl
      intro term _
      rw [programPT06DirectedQuadraticValueCurrentDivergence_eq_density]
    _ = ∑ index : Fin 3 × Rank,
          current.coefficient index.1 index.2 •
            programPT06DirectedQuadraticValueDensityEvaluation
              (programPT06FiniteRankBilinearValueAtom current index) jet := by
      exact (Fintype.sum_prod_type
        (fun index : Fin 3 × Rank =>
          current.coefficient index.1 index.2 •
            programPT06DirectedQuadraticValueDensityEvaluation
              (programPT06FiniteRankBilinearValueAtom current index) jet)).symm
    _ = programPT06FiniteRankBilinearValueDensityEvaluation current jet := rfl

@[simp] theorem programPT06FiniteRankBilinearValueDensityEvaluation_smul
    (current : ProgramPT06FiniteRankBilinearValueCurrent4D Fiber Rank)
    (scalar : Real) (jet : SecondJet (Fiber := Fiber)) :
    programPT06FiniteRankBilinearValueDensityEvaluation current (scalar • jet) =
      scalar ^ 2 *
        programPT06FiniteRankBilinearValueDensityEvaluation current jet := by
  simp only [programPT06FiniteRankBilinearValueDensityEvaluation,
    programPT06DirectedQuadraticValueDensityEvaluation_smul,
    Finset.mul_sum, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro index _
  ring

private theorem programPT06FiniteRankBilinearValueVerticalPartial
    (current : ProgramPT06FiniteRankBilinearValueCurrent4D Fiber Rank)
    (jet : SecondJet (Fiber := Fiber))
    (multiIndex : ThroatSpatialTruncatedIndex 2) :
    programPT06ThroatSpatialVerticalPartialDerivative
        (programPT06FiniteRankBilinearValueDensityEvaluation current)
        jet multiIndex =
      ∑ index : Fin 3 × Rank,
        current.coefficient index.1 index.2 •
          programPT06ThroatSpatialVerticalPartialDerivative
            (programPT06DirectedQuadraticValueDensityEvaluation
              (programPT06FiniteRankBilinearValueAtom current index))
            jet multiIndex := by
  exact programPT06VerticalPartialDerivative_fin_sum
    (Fiber := Fiber)
    (coefficient := fun index : Fin 3 × Rank =>
      current.coefficient index.1 index.2)
    (family := fun index =>
      programPT06DirectedQuadraticValueDensityEvaluation
        (programPT06FiniteRankBilinearValueAtom current index))
    (programPT06DirectedAtomDensity_differentiable current) jet multiIndex

private theorem programPT06FiniteRankBilinearValueVerticalPartialZero
    (current : ProgramPT06FiniteRankBilinearValueCurrent4D Fiber Rank) :
    programPT06SecondOrderLocalVerticalPartialZero
        (programPT06FiniteRankBilinearValueDensityEvaluation current) =
      fun jet => ∑ index : Fin 3 × Rank,
        current.coefficient index.1 index.2 •
          programPT06SecondOrderLocalVerticalPartialZero
            (programPT06DirectedQuadraticValueDensityEvaluation
              (programPT06FiniteRankBilinearValueAtom current index)) jet := by
  funext jet
  exact programPT06FiniteRankBilinearValueVerticalPartial current jet
    programPT06SecondOrderZeroMultiIndex

private theorem programPT06FiniteRankBilinearValueVerticalPartialOne
    (current : ProgramPT06FiniteRankBilinearValueCurrent4D Fiber Rank)
    (direction : Fin 3) :
    programPT06SecondOrderLocalVerticalPartialOne
        (programPT06FiniteRankBilinearValueDensityEvaluation current)
        direction =
      fun jet => ∑ index : Fin 3 × Rank,
        current.coefficient index.1 index.2 •
          programPT06SecondOrderLocalVerticalPartialOne
            (programPT06DirectedQuadraticValueDensityEvaluation
              (programPT06FiniteRankBilinearValueAtom current index))
            direction jet := by
  funext jet
  exact programPT06FiniteRankBilinearValueVerticalPartial current jet
    (programPT06SecondOrderFirstMultiIndex direction)

private theorem programPT06FiniteRankBilinearValueVerticalPartialTwo
    (current : ProgramPT06FiniteRankBilinearValueCurrent4D Fiber Rank)
    (first second : Fin 3) :
    programPT06SecondOrderLocalVerticalPartialTwo
        (programPT06FiniteRankBilinearValueDensityEvaluation current)
        first second =
      fun jet => ∑ index : Fin 3 × Rank,
        current.coefficient index.1 index.2 •
          programPT06SecondOrderLocalVerticalPartialTwo
            (programPT06DirectedQuadraticValueDensityEvaluation
              (programPT06FiniteRankBilinearValueAtom current index))
            first second jet := by
  funext jet
  exact programPT06FiniteRankBilinearValueVerticalPartial current jet
    (programPT06SecondOrderSecondMultiIndex first second)

private theorem programPT06DirectedAtomVerticalPartialOne_differentiable
    (current : ProgramPT06FiniteRankBilinearValueCurrent4D Fiber Rank)
    (index : Fin 3 × Rank) (direction : Fin 3) :
    Differentiable Real
      (programPT06SecondOrderLocalVerticalPartialOne
        (programPT06DirectedQuadraticValueDensityEvaluation
          (programPT06FiniteRankBilinearValueAtom current index)) direction) := by
  by_cases hDirection : direction = index.1
  · subst direction
    change Differentiable Real
      (programPT06SecondOrderLocalVerticalPartialOne
        (programPT06DirectedQuadraticValueDensityEvaluation
          (programPT06FiniteRankBilinearValueAtom current index))
        (programPT06FiniteRankBilinearValueAtom current index).direction)
    rw [programPT06DirectedQuadraticValueDensityVerticalPartialOne_self]
    exact ContinuousLinearMap.differentiable _
  · have hAtomDirection :
        direction ≠
          (programPT06FiniteRankBilinearValueAtom current index).direction := by
      simpa [programPT06FiniteRankBilinearValueAtom] using hDirection
    rw [programPT06DirectedQuadraticValueDensityVerticalPartialOne_of_ne
      _ direction hAtomDirection]
    exact differentiable_zero

private theorem programPT06FiniteRankBilinearValueEulerFirstTotalTerm
    (current : ProgramPT06FiniteRankBilinearValueCurrent4D Fiber Rank)
    (direction : Fin 3) (jet : ThirdJet (Fiber := Fiber)) :
    programPT06SecondOrderLocalEulerFirstTotalTerm
        (programPT06FiniteRankBilinearValueDensityEvaluation current)
        direction jet =
      ∑ index : Fin 3 × Rank,
        current.coefficient index.1 index.2 •
          programPT06SecondOrderLocalEulerFirstTotalTerm
            (programPT06DirectedQuadraticValueDensityEvaluation
              (programPT06FiniteRankBilinearValueAtom current index))
            direction jet := by
  rw [programPT06SecondOrderLocalEulerFirstTotalTerm,
    programPT06FiniteRankBilinearValueVerticalPartialOne]
  exact congrFun
    (programPT06LocalFunctionTotalDerivative_fin_sum
      (Fiber := Fiber)
      (coefficient := fun index : Fin 3 × Rank =>
        current.coefficient index.1 index.2)
      (family := fun index =>
        programPT06SecondOrderLocalVerticalPartialOne
          (programPT06DirectedQuadraticValueDensityEvaluation
            (programPT06FiniteRankBilinearValueAtom current index)) direction)
      (fun index =>
        programPT06DirectedAtomVerticalPartialOne_differentiable
          current index direction) direction) jet

private theorem programPT06FiniteRankBilinearValueVerticalPartialTwo_eq_zero
    (current : ProgramPT06FiniteRankBilinearValueCurrent4D Fiber Rank)
    (first second : Fin 3) :
    programPT06SecondOrderLocalVerticalPartialTwo
        (programPT06FiniteRankBilinearValueDensityEvaluation current)
        first second = 0 := by
  rw [programPT06FiniteRankBilinearValueVerticalPartialTwo]
  funext jet
  simp_rw [programPT06DirectedQuadraticValueDensityVerticalPartialTwo]
  simp

private theorem programPT06FiniteRankBilinearValueEulerSecondTotalTerm_eq_zero
    (current : ProgramPT06FiniteRankBilinearValueCurrent4D Fiber Rank)
    (first second : Fin 3) (jet : FourthJet (Fiber := Fiber)) :
    programPT06SecondOrderLocalEulerSecondTotalTerm
        (programPT06FiniteRankBilinearValueDensityEvaluation current)
        first second jet = 0 := by
  rw [programPT06SecondOrderLocalEulerSecondTotalTerm,
    programPT06FiniteRankBilinearValueVerticalPartialTwo_eq_zero]
  simp

private theorem programPT06DirectedAtomEulerFirstCancellation
    (current : ProgramPT06FiniteRankBilinearValueCurrent4D Fiber Rank)
    (index : Fin 3 × Rank) (jet : FourthJet (Fiber := Fiber)) :
    programPT06SecondOrderLocalVerticalPartialZero
        (programPT06DirectedQuadraticValueDensityEvaluation
          (programPT06FiniteRankBilinearValueAtom current index))
        (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 4) jet) -
      (∑ direction : Fin 3,
        programPT06SecondOrderLocalEulerFirstTotalTerm
          (programPT06DirectedQuadraticValueDensityEvaluation
            (programPT06FiniteRankBilinearValueAtom current index))
          direction
          (truncateThroatSpatialMultiindexJet (by omega : 3 ≤ 4) jet)) = 0 := by
  have hEuler :=
    programPT06SecondOrderLocalEuler_directedQuadraticValueDensity_eq_zero
      (programPT06FiniteRankBilinearValueAtom current index) jet
  rw [programPT06SecondOrderLocalEuler_formula] at hEuler
  simpa [programPT06SecondOrderLocalEulerSecondTotalTerm,
    programPT06DirectedQuadraticValueDensityVerticalPartialTwo,
    programPT06ThroatSpatialLocalFunctionTotalDerivative] using hEuler

/-- Gate880 annihilates every finite-rank bilinear boundary density assembled
over the three throat directions. -/
theorem programPT06SecondOrderLocalEuler_finiteRankBilinearValueDensity_eq_zero
    (current : ProgramPT06FiniteRankBilinearValueCurrent4D Fiber Rank)
    (jet : FourthJet (Fiber := Fiber)) :
    programPT06SecondOrderLocalEuler
        (programPT06FiniteRankBilinearValueDensityEvaluation current) jet = 0 := by
  rw [programPT06SecondOrderLocalEuler_formula,
    programPT06FiniteRankBilinearValueVerticalPartialZero]
  have hFirst :
      (∑ direction : Fin 3,
        programPT06SecondOrderLocalEulerFirstTotalTerm
          (programPT06FiniteRankBilinearValueDensityEvaluation current)
          direction
          (truncateThroatSpatialMultiindexJet (by omega : 3 ≤ 4) jet)) =
        ∑ index : Fin 3 × Rank,
          current.coefficient index.1 index.2 •
            (∑ direction : Fin 3,
              programPT06SecondOrderLocalEulerFirstTotalTerm
                (programPT06DirectedQuadraticValueDensityEvaluation
                  (programPT06FiniteRankBilinearValueAtom current index))
                direction
                (truncateThroatSpatialMultiindexJet
                  (by omega : 3 ≤ 4) jet)) := by
    simp_rw [programPT06FiniteRankBilinearValueEulerFirstTotalTerm]
    rw [Finset.sum_comm]
    simp [Finset.smul_sum]
  rw [hFirst]
  simp_rw [programPT06FiniteRankBilinearValueEulerSecondTotalTerm_eq_zero]
  simp only [smul_zero, Finset.sum_const_zero, add_zero]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_eq_zero
  intro index _
  have hScaled := congrArg
    (fun value : Fiber →L[Real] Real =>
      current.coefficient index.1 index.2 • value)
    (programPT06DirectedAtomEulerFirstCancellation current index jet)
  simpa only [smul_sub, smul_zero] using hScaled

/-- Euler-nullity stated directly for the actual assembled `dH`. -/
theorem programPT06SecondOrderLocalEuler_finiteRankBilinearValueDivergence_eq_zero
    (current : ProgramPT06FiniteRankBilinearValueCurrent4D Fiber Rank)
    (jet : FourthJet (Fiber := Fiber)) :
    programPT06SecondOrderLocalEuler
        (programPT06FiniteRankBilinearValueCurrentDivergence current) jet = 0 := by
  rw [programPT06FiniteRankBilinearValueCurrentDivergence_eq_density]
  exact
    programPT06SecondOrderLocalEuler_finiteRankBilinearValueDensity_eq_zero
      current jet

end
end P0EFTJanusProgramPT06FiniteRankBilinearValueCurrent4D
end JanusFormal
