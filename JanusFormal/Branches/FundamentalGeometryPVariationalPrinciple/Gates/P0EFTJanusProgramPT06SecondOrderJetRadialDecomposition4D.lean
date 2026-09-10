import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06SecondOrderLocalEuler4D

namespace JanusFormal
namespace P0EFTJanusProgramPT06SecondOrderJetRadialDecomposition4D

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open P0EFTJanusProgramPT06ThroatSpatialMultiindexSecondJetBridge4D
open P0EFTJanusProgramPT06ThroatSpatialFinsuppJetTower4D
open P0EFTJanusProgramPT06ThroatSpatialFinsuppSecondJetBridge4D
open P0EFTJanusProgramPT06LocalFunctionTotalDerivative4D
open P0EFTJanusProgramPT06SecondOrderLocalEuler4D

universe u

variable {Fiber : Type u} [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]

/-- The ordered-pair weight used for symmetric second-order coordinates is
symmetric. -/
theorem programPT06SecondOrderEulerSymmetryWeight_comm
    (first second : Fin 3) :
    programPT06SecondOrderEulerSymmetryWeight first second =
      programPT06SecondOrderEulerSymmetryWeight second first := by
  by_cases hDirections : first = second
  · subst second
    rfl
  · have hReverse : second ≠ first := Ne.symm hDirections
    simp [programPT06SecondOrderEulerSymmetryWeight,
      hDirections, hReverse]

/-- The vertical partial in a symmetric second-order coordinate is unchanged
when its two direction labels are exchanged. -/
theorem programPT06SecondOrderLocalVerticalPartialTwo_comm
    (localLagrangian : ThroatSpatialMultiindexJet2 Fiber → Real)
    (first second : Fin 3) :
    programPT06SecondOrderLocalVerticalPartialTwo
        localLagrangian first second =
      programPT06SecondOrderLocalVerticalPartialTwo
        localLagrangian second first := by
  unfold programPT06SecondOrderLocalVerticalPartialTwo
  rw [programPT06SecondOrderSecondMultiIndex_comm first second]

private theorem indexUpToTwoToTruncated_orderZero :
    throatSpatialIndexUpToTwoToTruncated
        (.orderZero : ThroatSpatialMultiIndexUpToTwo) =
      programPT06SecondOrderZeroMultiIndex := by
  apply Subtype.ext
  rfl

private theorem indexUpToTwoToTruncated_orderOne
    (direction : Fin 3) :
    throatSpatialIndexUpToTwoToTruncated (.orderOne direction) =
      programPT06SecondOrderFirstMultiIndex direction := by
  apply Subtype.ext
  ext coordinate
  change
    (((Sym.equivNatSum (Fin 3) 1) (Sym.oneEquiv direction) :
      Fin 3 →₀ Nat) coordinate) =
      (Finsupp.single direction 1) coordinate
  rw [Sym.coe_equivNatSum_apply_apply]
  classical
  by_cases hCoordinate : coordinate = direction <;>
    simp [hCoordinate]

private theorem indexUpToTwoToTruncated_orderTwo
    (first second : Fin 3) :
    throatSpatialIndexUpToTwoToTruncated (.orderTwo s(first, second)) =
      programPT06SecondOrderSecondMultiIndex first second := by
  apply Subtype.ext
  ext coordinate
  change
    (((Sym.equivNatSum (Fin 3) 2)
      ((Sym2.equivSym (Fin 3)) s(first, second)) :
        Fin 3 →₀ Nat) coordinate) =
      ((Finsupp.single first 1 + Finsupp.single second 1 :
        Fin 3 →₀ Nat) coordinate)
  rw [Sym.coe_equivNatSum_apply_apply]
  change
    ({first, second} : Multiset (Fin 3)).count coordinate =
      ((Finsupp.single first 1 + Finsupp.single second 1 :
        Fin 3 →₀ Nat) coordinate)
  classical
  by_cases hFirst : first = coordinate <;>
    by_cases hSecond : second = coordinate <;>
      simp [hFirst, hSecond, eq_comm]

private theorem indexUpToTwoToTruncated_injective :
    Function.Injective throatSpatialIndexUpToTwoToTruncated :=
  throatSpatialIndexUpToTwo_leftInverse.injective

@[simp] private theorem secondOrderZero_ne_first
    (direction : Fin 3) :
    programPT06SecondOrderZeroMultiIndex ≠
      programPT06SecondOrderFirstMultiIndex direction := by
  rw [← indexUpToTwoToTruncated_orderZero,
    ← indexUpToTwoToTruncated_orderOne direction]
  intro h
  have hConstructors := indexUpToTwoToTruncated_injective h
  cases hConstructors

@[simp] private theorem secondOrderZero_ne_second
    (first second : Fin 3) :
    programPT06SecondOrderZeroMultiIndex ≠
      programPT06SecondOrderSecondMultiIndex first second := by
  rw [← indexUpToTwoToTruncated_orderZero,
    ← indexUpToTwoToTruncated_orderTwo first second]
  intro h
  have hConstructors := indexUpToTwoToTruncated_injective h
  cases hConstructors

@[simp] private theorem secondOrderFirst_ne_zero
    (direction : Fin 3) :
    programPT06SecondOrderFirstMultiIndex direction ≠
      programPT06SecondOrderZeroMultiIndex :=
  Ne.symm (secondOrderZero_ne_first direction)

@[simp] private theorem secondOrderSecond_ne_zero
    (first second : Fin 3) :
    programPT06SecondOrderSecondMultiIndex first second ≠
      programPT06SecondOrderZeroMultiIndex :=
  Ne.symm (secondOrderZero_ne_second first second)

@[simp] private theorem secondOrderFirst_ne_second
    (direction first second : Fin 3) :
    programPT06SecondOrderFirstMultiIndex direction ≠
      programPT06SecondOrderSecondMultiIndex first second := by
  rw [← indexUpToTwoToTruncated_orderOne direction,
    ← indexUpToTwoToTruncated_orderTwo first second]
  intro h
  have hConstructors := indexUpToTwoToTruncated_injective h
  cases hConstructors

@[simp] private theorem secondOrderFirstMultiIndex_eq_iff
    (first second : Fin 3) :
    programPT06SecondOrderFirstMultiIndex first =
        programPT06SecondOrderFirstMultiIndex second ↔
      first = second := by
  constructor
  · intro h
    rw [← indexUpToTwoToTruncated_orderOne first,
      ← indexUpToTwoToTruncated_orderOne second] at h
    have hConstructors := indexUpToTwoToTruncated_injective h
    simpa using hConstructors
  · intro h
    subst second
    rfl

@[simp] private theorem secondOrderSecond_ne_first
    (first second direction : Fin 3) :
    programPT06SecondOrderSecondMultiIndex first second ≠
      programPT06SecondOrderFirstMultiIndex direction :=
  Ne.symm (secondOrderFirst_ne_second direction first second)

@[simp] private theorem secondOrderSecondMultiIndex_eq_iff
    (first second third fourth : Fin 3) :
    programPT06SecondOrderSecondMultiIndex first second =
        programPT06SecondOrderSecondMultiIndex third fourth ↔
      s(first, second) = s(third, fourth) := by
  constructor
  · intro h
    rw [← indexUpToTwoToTruncated_orderTwo first second,
      ← indexUpToTwoToTruncated_orderTwo third fourth] at h
    have hConstructors := indexUpToTwoToTruncated_injective h
    simpa using hConstructors
  · intro h
    rw [← indexUpToTwoToTruncated_orderTwo first second,
      ← indexUpToTwoToTruncated_orderTwo third fourth]
    exact congrArg
      (fun directions : Sym2 (Fin 3) =>
        throatSpatialIndexUpToTwoToTruncated (.orderTwo directions)) h

@[simp] private theorem second10_eq_second01 :
    programPT06SecondOrderSecondMultiIndex 1 0 =
      programPT06SecondOrderSecondMultiIndex 0 1 :=
  programPT06SecondOrderSecondMultiIndex_comm 1 0

@[simp] private theorem second20_eq_second02 :
    programPT06SecondOrderSecondMultiIndex 2 0 =
      programPT06SecondOrderSecondMultiIndex 0 2 :=
  programPT06SecondOrderSecondMultiIndex_comm 2 0

@[simp] private theorem second21_eq_second12 :
    programPT06SecondOrderSecondMultiIndex 2 1 =
      programPT06SecondOrderSecondMultiIndex 1 2 :=
  programPT06SecondOrderSecondMultiIndex_comm 2 1

private theorem weightedSecondCoordinateSum_apply
    (jet : ThroatSpatialMultiindexJet2 Fiber)
    (targetFirst targetSecond : Fin 3) :
    (∑ first : Fin 3, ∑ second : Fin 3,
      programPT06SecondOrderEulerSymmetryWeight first second •
        programPT06ThroatSpatialJetCoordinateInjection
          (programPT06SecondOrderSecondMultiIndex first second)
          (jet (programPT06SecondOrderSecondMultiIndex first second)))
        (programPT06SecondOrderSecondMultiIndex targetFirst targetSecond) =
      jet (programPT06SecondOrderSecondMultiIndex targetFirst targetSecond) := by
  fin_cases targetFirst <;> fin_cases targetSecond <;>
    simp [Fin.sum_univ_three,
      programPT06SecondOrderEulerSymmetryWeight,
      programPT06ThroatSpatialJetCoordinateInjection,
      secondOrderSecondMultiIndex_eq_iff] <;>
    module

/-- Every genuine order-two throat jet is the weighted sum of its value,
first-order, and symmetric second-order coordinate injections.  The last sum
runs over ordered pairs; the Gate880 weight removes the duplicate mixed
coordinates. -/
theorem programPT06SecondOrderJet_weightedCoordinateDecomposition
    (jet : ThroatSpatialMultiindexJet2 Fiber) :
    jet =
      programPT06ThroatSpatialJetCoordinateInjection
          programPT06SecondOrderZeroMultiIndex
          (jet programPT06SecondOrderZeroMultiIndex) +
        (∑ direction : Fin 3,
          programPT06ThroatSpatialJetCoordinateInjection
            (programPT06SecondOrderFirstMultiIndex direction)
            (jet (programPT06SecondOrderFirstMultiIndex direction))) +
        ∑ first : Fin 3, ∑ second : Fin 3,
          programPT06SecondOrderEulerSymmetryWeight first second •
            programPT06ThroatSpatialJetCoordinateInjection
              (programPT06SecondOrderSecondMultiIndex first second)
              (jet (programPT06SecondOrderSecondMultiIndex first second)) := by
  classical
  funext index
  let classified := throatSpatialTruncatedIndexTwoEquiv index
  have hIndex :
      throatSpatialIndexUpToTwoToTruncated classified = index := by
    dsimp [classified]
    exact throatSpatialIndexUpToTwo_rightInverse index
  cases hClassified : classified with
  | orderZero =>
      have hCoordinate : index = programPT06SecondOrderZeroMultiIndex := by
        rw [← hIndex, hClassified, indexUpToTwoToTruncated_orderZero]
      rw [hCoordinate]
      simp [Fin.sum_univ_three,
        programPT06ThroatSpatialJetCoordinateInjection]
  | orderOne direction =>
      have hCoordinate :
          index = programPT06SecondOrderFirstMultiIndex direction := by
        rw [← hIndex, hClassified,
          indexUpToTwoToTruncated_orderOne direction]
      rw [hCoordinate]
      fin_cases direction <;>
        simp [Fin.sum_univ_three,
          programPT06ThroatSpatialJetCoordinateInjection]
  | orderTwo directions =>
      have hCoordinate :
          index = throatSpatialIndexUpToTwoToTruncated
            (.orderTwo directions) := by
        rw [← hIndex, hClassified]
      rw [hCoordinate]
      refine Sym2.inductionOn directions ?_
      intro first second
      rw [indexUpToTwoToTruncated_orderTwo first second]
      simp only [Pi.add_apply]
      rw [weightedSecondCoordinateSum_apply jet first second]
      fin_cases first <;> fin_cases second <;>
        simp [programPT06ThroatSpatialJetCoordinateInjection]

end
end P0EFTJanusProgramPT06SecondOrderJetRadialDecomposition4D
end JanusFormal
