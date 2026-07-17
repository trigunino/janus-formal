import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPositiveRawDoubleSingleSingleHermiteRoot4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPositiveRawFourSimpleLagrangeRoot4D

/-!
# Closure of the positive split raw characteristic-polynomial locus

The four roots of the monic characteristic polynomial are extracted with
multiplicity.  Their equality partition gives exactly one of the already
closed raw annihilators: `4`, `3 + 1`, `2 + 2`, `2 + 1 + 1`, or four simple
nodes.  All factor reordering is performed in the commutative polynomial
ring before Cayley--Hamilton is evaluated at the matrix.
-/

namespace JanusFormal
namespace P0EFTJanusPositiveRawSplitCharpolyRootClosure4D

set_option autoImplicit false

noncomputable section

open scoped MatrixOrder
open Polynomial
open P0EFTJanusMatrixSquareRootFrechetSylvester
open P0EFTJanusPositiveSingleEigenvalueJordanRoot4D
open P0EFTJanusPositiveRawPolynomialRootReduction4D
open P0EFTJanusPositiveRawDoubleDoubleHermiteRoot4D
open P0EFTJanusPositiveRawTripleSingleHermiteRoot4D
open P0EFTJanusPositiveRawDoubleSingleSingleHermiteRoot4D
open P0EFTJanusPositiveRawFourSimpleLagrangeRoot4D
open P0EFTJanusPositiveRealJordanPresentationBridge4D
open P0EFTJanusRealSquareRootSpectralObstructions4D
open P0EFTJanusRawSpectralBridgeReduction4D

abbrev Matrix4 := P0EFTJanusRawSpectralBridgeReduction4D.Matrix4

private theorem fourDisplacements_zero_of_charpoly_eq
    {target : Matrix4} {first second third fourth : Real}
    (hCharpoly : target.charpoly =
      (X - C first) * (X - C second) * (X - C third) *
        (X - C fourth)) :
    let firstDisplacement := target - first • (1 : Matrix4)
    let secondDisplacement := target - second • (1 : Matrix4)
    let thirdDisplacement := target - third • (1 : Matrix4)
    let fourthDisplacement := target - fourth • (1 : Matrix4)
    firstDisplacement * secondDisplacement * thirdDisplacement *
      fourthDisplacement = 0 := by
  have hCayley := Matrix.aeval_self_charpoly target
  rw [hCharpoly] at hCayley
  simpa [Algebra.smul_def, mul_assoc] using hCayley

/-- The five equality partitions of the four positive roots, expressed as
the corresponding raw matrix annihilator. -/
def PositiveSplitRelationPartition4 (target : Matrix4) : Prop :=
  HasPositiveSingleEigenvalueQuarticRelation4 target ∨
    HasPositiveDistinctDoubleDoubleRelation4 target ∨
      HasPositiveDistinctTripleSingleRelation4 target ∨
        HasPositiveDistinctDoubleSingleSingleRelation4 target ∨
          HasPositiveFourSimpleRelation4 target

theorem positiveRealSplitCharpoly_relationPartition
    {target : Matrix4} (hSpectrum : PositiveRealSplitCharpoly4 target) :
    PositiveSplitRelationPartition4 target := by
  have hCard : target.charpoly.roots.card = 4 := by
    calc
      target.charpoly.roots.card = target.charpoly.natDegree :=
        hSpectrum.1.natDegree_eq_card_roots.symm
      _ = 4 := by rw [Matrix.charpoly_natDegree_eq_dim]; rfl
  obtain ⟨first, second, third, fourth, hRoots⟩ :=
    Multiset.card_eq_four.mp hCard
  have hCharpoly : target.charpoly =
      (X - C first) * (X - C second) * (X - C third) *
        (X - C fourth) := by
    calc
      target.charpoly =
          (target.charpoly.roots.map (X - C ·)).prod :=
        hSpectrum.1.eq_prod_roots_of_monic (Matrix.charpoly_monic target)
      _ = (X - C first) * (X - C second) * (X - C third) *
          (X - C fourth) := by
        rw [hRoots]
        simp
        ring
  have hFirstMem : first ∈ target.charpoly.roots := by
    rw [hRoots]
    simp
  have hSecondMem : second ∈ target.charpoly.roots := by
    rw [hRoots]
    simp
  have hThirdMem : third ∈ target.charpoly.roots := by
    rw [hRoots]
    simp
  have hFourthMem : fourth ∈ target.charpoly.roots := by
    rw [hRoots]
    simp
  have hFirst : 0 < first :=
    hSpectrum.2 first (isRoot_of_mem_roots hFirstMem)
  have hSecond : 0 < second :=
    hSpectrum.2 second (isRoot_of_mem_roots hSecondMem)
  have hThird : 0 < third :=
    hSpectrum.2 third (isRoot_of_mem_roots hThirdMem)
  have hFourth : 0 < fourth :=
    hSpectrum.2 fourth (isRoot_of_mem_roots hFourthMem)
  by_cases hFirstSecond : first = second
  · subst second
    by_cases hFirstThird : first = third
    · subst third
      by_cases hFirstFourth : first = fourth
      · subst fourth
        refine Or.inl ⟨⟨first, hFirst⟩, ?_⟩
        unfold scaledJordanDisplacementFourth
        exact fourDisplacements_zero_of_charpoly_eq hCharpoly
      · refine Or.inr (Or.inr (Or.inl ?_))
        refine ⟨first, fourth, hFirst, hFourth, hFirstFourth, ?_⟩
        exact fourDisplacements_zero_of_charpoly_eq hCharpoly
    · by_cases hFirstFourth : first = fourth
      · subst fourth
        refine Or.inr (Or.inr (Or.inl ?_))
        refine ⟨first, third, hFirst, hThird, hFirstThird, ?_⟩
        apply fourDisplacements_zero_of_charpoly_eq
        calc
          target.charpoly =
              (X - C first) * (X - C first) * (X - C third) *
                (X - C first) := hCharpoly
          _ = (X - C first) * (X - C first) * (X - C first) *
              (X - C third) := by ring
      · by_cases hThirdFourth : third = fourth
        · subst fourth
          refine Or.inr (Or.inl ?_)
          refine ⟨first, third, hFirst, hThird, hFirstThird, ?_⟩
          exact fourDisplacements_zero_of_charpoly_eq hCharpoly
        · refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
          refine ⟨first, third, fourth, hFirst, hThird, hFourth,
            hFirstThird, hFirstFourth, hThirdFourth, ?_⟩
          exact fourDisplacements_zero_of_charpoly_eq hCharpoly
  · by_cases hFirstThird : first = third
    · subst third
      by_cases hFirstFourth : first = fourth
      · subst fourth
        refine Or.inr (Or.inr (Or.inl ?_))
        refine ⟨first, second, hFirst, hSecond, hFirstSecond, ?_⟩
        apply fourDisplacements_zero_of_charpoly_eq
        calc
          target.charpoly =
              (X - C first) * (X - C second) * (X - C first) *
                (X - C first) := hCharpoly
          _ = (X - C first) * (X - C first) * (X - C first) *
              (X - C second) := by ring
      · by_cases hSecondFourth : second = fourth
        · subst fourth
          refine Or.inr (Or.inl ?_)
          refine ⟨first, second, hFirst, hSecond, hFirstSecond, ?_⟩
          apply fourDisplacements_zero_of_charpoly_eq
          calc
            target.charpoly =
                (X - C first) * (X - C second) * (X - C first) *
                  (X - C second) := hCharpoly
            _ = (X - C first) * (X - C first) * (X - C second) *
                (X - C second) := by ring
        · refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
          refine ⟨first, second, fourth, hFirst, hSecond, hFourth,
            hFirstSecond, hFirstFourth, hSecondFourth, ?_⟩
          apply fourDisplacements_zero_of_charpoly_eq
          calc
            target.charpoly =
                (X - C first) * (X - C second) * (X - C first) *
                  (X - C fourth) := hCharpoly
            _ = (X - C first) * (X - C first) * (X - C second) *
                (X - C fourth) := by ring
    · by_cases hFirstFourth : first = fourth
      · subst fourth
        by_cases hSecondThird : second = third
        · subst third
          refine Or.inr (Or.inl ?_)
          refine ⟨first, second, hFirst, hSecond, hFirstSecond, ?_⟩
          apply fourDisplacements_zero_of_charpoly_eq
          calc
            target.charpoly =
                (X - C first) * (X - C second) * (X - C second) *
                  (X - C first) := hCharpoly
            _ = (X - C first) * (X - C first) * (X - C second) *
                (X - C second) := by ring
        · refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
          refine ⟨first, second, third, hFirst, hSecond, hThird,
            hFirstSecond, hFirstThird, hSecondThird, ?_⟩
          apply fourDisplacements_zero_of_charpoly_eq
          calc
            target.charpoly =
                (X - C first) * (X - C second) * (X - C third) *
                  (X - C first) := hCharpoly
            _ = (X - C first) * (X - C first) * (X - C second) *
                (X - C third) := by ring
      · by_cases hSecondThird : second = third
        · subst third
          by_cases hSecondFourth : second = fourth
          · subst fourth
            refine Or.inr (Or.inr (Or.inl ?_))
            refine ⟨second, first, hSecond, hFirst, Ne.symm hFirstSecond, ?_⟩
            apply fourDisplacements_zero_of_charpoly_eq
            calc
              target.charpoly =
                  (X - C first) * (X - C second) * (X - C second) *
                    (X - C second) := hCharpoly
              _ = (X - C second) * (X - C second) * (X - C second) *
                  (X - C first) := by ring
          · refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
            refine ⟨second, first, fourth, hSecond, hFirst, hFourth,
              Ne.symm hFirstSecond, hSecondFourth, hFirstFourth, ?_⟩
            apply fourDisplacements_zero_of_charpoly_eq
            calc
              target.charpoly =
                  (X - C first) * (X - C second) * (X - C second) *
                    (X - C fourth) := hCharpoly
              _ = (X - C second) * (X - C second) * (X - C first) *
                  (X - C fourth) := by ring
        · by_cases hSecondFourth : second = fourth
          · subst fourth
            refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
            refine ⟨second, first, third, hSecond, hFirst, hThird,
              Ne.symm hFirstSecond, hSecondThird, hFirstThird, ?_⟩
            apply fourDisplacements_zero_of_charpoly_eq
            calc
              target.charpoly =
                  (X - C first) * (X - C second) * (X - C third) *
                    (X - C second) := hCharpoly
              _ = (X - C second) * (X - C second) * (X - C first) *
                  (X - C third) := by ring
          · by_cases hThirdFourth : third = fourth
            · subst fourth
              refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
              refine ⟨third, first, second, hThird, hFirst, hSecond,
                Ne.symm hFirstThird, Ne.symm hSecondThird, hFirstSecond, ?_⟩
              apply fourDisplacements_zero_of_charpoly_eq
              calc
                target.charpoly =
                    (X - C first) * (X - C second) * (X - C third) *
                      (X - C third) := hCharpoly
                _ = (X - C third) * (X - C third) * (X - C first) *
                    (X - C second) := by ring
            · refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
              refine ⟨first, second, third, fourth, hFirst, hSecond, hThird,
                hFourth, hFirstSecond, hFirstThird, hFirstFourth,
                hSecondThird, hSecondFourth, hThirdFourth, ?_⟩
              exact fourDisplacements_zero_of_charpoly_eq hCharpoly

theorem positiveRealSplitCharpoly_hasRealSquareRoot
    {target : Matrix4} (hSpectrum : PositiveRealSplitCharpoly4 target) :
    HasRealSquareRoot target := by
  rcases positiveRealSplitCharpoly_relationPartition hSpectrum with
    hQuartic | hDoubleDouble | hTripleSingle | hDoubleSingleSingle | hFourSimple
  · exact positiveSingleEigenvalueQuarticRelation_hasRealSquareRoot hQuartic
  · exact positiveDistinctDoubleDoubleRelation_hasRealSquareRoot hDoubleDouble
  · exact positiveDistinctTripleSingleRelation_hasRealSquareRoot hTripleSingle
  · exact positiveDistinctDoubleSingleSingleRelation_hasRealSquareRoot
      hDoubleSingleSingle
  · exact positiveFourSimpleRelation_hasRealSquareRoot hFourSimple

/-- Unconditional closure of the positive real split raw locus. -/
theorem positiveRawRootClosure : PositiveRawRootClosure4 := by
  intro target hSpectrum
  exact positiveRealSplitCharpoly_hasRealSquareRoot hSpectrum

end

end P0EFTJanusPositiveRawSplitCharpolyRootClosure4D
end JanusFormal
