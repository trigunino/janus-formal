import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06ThroatSpatialFinsuppJetTower4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06ActualPhysicalValueProductSecondJetBridge4D

/-!
# Exact order-two bridge for genuine throat spatial multi-indices

This gate classifies genuine Fin 3 spatial multi-indices of total degree at
most two as the zero index, a degree-one direction, or an unordered degree-two
pair. Reindexing along that equivalence identifies the genuine order-two jet
from Gate875 with the finite symmetric carrier from Gate870. Composition with
Gate874 then reaches the exact eleven-component physical second-jet product
used by T02.

No Euler operator, horizontal complex or terminal T06 classification is
asserted here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06ThroatSpatialFinsuppSecondJetBridge4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPT06ThroatSpatialMultiindexSecondJetBridge4D
open P0EFTJanusProgramPT06ThroatSpatialFinsuppJetTower4D
open P0EFTJanusProgramPT06ActualPhysicalValueProductSecondJetBridge4D
open P0EFTJanusProgramPActualPhysicalSecondOrderJetProductVectorBundleCore4D

universe v

/-- Genuine spatial multi-indices of one fixed total degree. -/
abbrev ThroatSpatialHomogeneousIndex (degree : Nat) :=
  {index : ThroatSpatialMultiIndex //
    throatSpatialMultiIndexOrder index = degree}

/-- A degree-one genuine multi-index is exactly one throat direction. -/
noncomputable def throatSpatialDegreeOneIndexEquiv :
    ThroatSpatialHomogeneousIndex 1 ≃ Fin 3 :=
  (Sym.equivNatSum (Fin 3) 1).symm.trans Sym.oneEquiv.symm

/-- A degree-two genuine multi-index is exactly an unordered pair of throat
directions. -/
noncomputable def throatSpatialDegreeTwoIndexEquiv :
    ThroatSpatialHomogeneousIndex 2 ≃ Sym2 (Fin 3) :=
  (Sym.equivNatSum (Fin 3) 2).symm.trans (Sym2.equivSym (Fin 3)).symm

/-- Embed the finite symmetric order-two presentation into genuine bounded
multi-indices. -/
noncomputable def throatSpatialIndexUpToTwoToTruncated :
    ThroatSpatialMultiIndexUpToTwo → ThroatSpatialTruncatedIndex 2
  | .orderZero => ⟨0, by simp⟩
  | .orderOne direction =>
      ⟨(throatSpatialDegreeOneIndexEquiv.symm direction).1, by
        rw [(throatSpatialDegreeOneIndexEquiv.symm direction).2]
        omega⟩
  | .orderTwo directions =>
      ⟨(throatSpatialDegreeTwoIndexEquiv.symm directions).1, by
        rw [(throatSpatialDegreeTwoIndexEquiv.symm directions).2]⟩

/-- Classify a genuine bounded multi-index by its total degree zero, one or
two. -/
noncomputable def throatSpatialTruncatedToIndexUpToTwo
    (index : ThroatSpatialTruncatedIndex 2) :
    ThroatSpatialMultiIndexUpToTwo :=
  if hZero : throatSpatialMultiIndexOrder index.1 = 0 then
    .orderZero
  else if hOne : throatSpatialMultiIndexOrder index.1 = 1 then
    .orderOne (throatSpatialDegreeOneIndexEquiv ⟨index.1, hOne⟩)
  else
    .orderTwo
      (throatSpatialDegreeTwoIndexEquiv ⟨index.1, by omega⟩)

theorem throatSpatialIndexUpToTwo_leftInverse :
    Function.LeftInverse throatSpatialTruncatedToIndexUpToTwo
      throatSpatialIndexUpToTwoToTruncated := by
  intro index
  cases index with
  | orderZero =>
      simp [throatSpatialIndexUpToTwoToTruncated,
        throatSpatialTruncatedToIndexUpToTwo]
  | orderOne direction =>
      simp [throatSpatialIndexUpToTwoToTruncated,
        throatSpatialTruncatedToIndexUpToTwo,
        (throatSpatialDegreeOneIndexEquiv.symm direction).2]
  | orderTwo directions =>
      simp [throatSpatialIndexUpToTwoToTruncated,
        throatSpatialTruncatedToIndexUpToTwo,
        (throatSpatialDegreeTwoIndexEquiv.symm directions).2]

theorem throatSpatialIndexUpToTwo_rightInverse :
    Function.RightInverse throatSpatialTruncatedToIndexUpToTwo
      throatSpatialIndexUpToTwoToTruncated := by
  intro index
  by_cases hZero : throatSpatialMultiIndexOrder index.1 = 0
  · have hIndex : index.1 = 0 := by
      apply (Finsupp.degree_eq_zero_iff index.1).mp
      exact hZero
    apply Subtype.ext
    simp [throatSpatialTruncatedToIndexUpToTwo,
      throatSpatialIndexUpToTwoToTruncated, hZero, hIndex]
  · by_cases hOne : throatSpatialMultiIndexOrder index.1 = 1
    · apply Subtype.ext
      simp [throatSpatialTruncatedToIndexUpToTwo,
        throatSpatialIndexUpToTwoToTruncated, hZero, hOne]
    · have hTwo : throatSpatialMultiIndexOrder index.1 = 2 := by
        omega
      apply Subtype.ext
      simp [throatSpatialTruncatedToIndexUpToTwo,
        throatSpatialIndexUpToTwoToTruncated, hZero, hOne, hTwo]

/-- Exact equivalence between genuine bounded degree-two multi-indices and the
zero/one/unordered-pair presentation of Gate870. -/
noncomputable def throatSpatialTruncatedIndexTwoEquiv :
    ThroatSpatialTruncatedIndex 2 ≃ ThroatSpatialMultiIndexUpToTwo where
  toFun := throatSpatialTruncatedToIndexUpToTwo
  invFun := throatSpatialIndexUpToTwoToTruncated
  left_inv := throatSpatialIndexUpToTwo_rightInverse
  right_inv := throatSpatialIndexUpToTwo_leftInverse

/-- Reindex genuine order-two spatial jets into the symmetric Gate870
carrier. -/
noncomputable def throatSpatialFinsuppSecondJetEquiv (Fiber : Type v) :
    ThroatSpatialMultiindexJet2 Fiber ≃
      ThroatSpatialMultiindexSecondJet Fiber where
  toFun jet index := jet (throatSpatialTruncatedIndexTwoEquiv.symm index)
  invFun jet index := jet (throatSpatialTruncatedIndexTwoEquiv index)
  left_inv jet := by
    funext index
    simp
  right_inv jet := by
    funext index
    simp

/-- Exact bridge from the genuine order-two jet of the complete eleven-value
product to the assembled physical second-jet product used by T02. -/
noncomputable def programPT06ActualPhysicalValueProductFinsuppSecondJetEquiv :
    ThroatSpatialMultiindexJet2 ActualPhysicalValueProductFiber ≃
      ActualPhysicalSecondOrderJetProductFiber :=
  (throatSpatialFinsuppSecondJetEquiv
      ActualPhysicalValueProductFiber).trans
    programPT06ActualPhysicalValueProductSecondJetEquiv

end
end P0EFTJanusProgramPT06ThroatSpatialFinsuppSecondJetBridge4D
end JanusFormal
