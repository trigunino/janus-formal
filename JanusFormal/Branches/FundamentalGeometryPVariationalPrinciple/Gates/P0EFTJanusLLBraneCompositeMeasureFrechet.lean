import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Matrix.Normed
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusLLBraneCompositeMeasureVariation

/-!
# Frechet differential of the finite LL-brane composite measure

The signed composite measure `Phi(J) = det J` is differentiated as a map on
the full Frobenius-normed space of `3 x 3` first jets.  Its differential is an
explicit continuous linear covector and agrees entrywise with the previously
proved affine-curve variation.

This is still a finite, oriented, pointwise first-jet model.  It asserts no
worldvolume PDE, integration theorem, global auxiliary fields, or throat
solution.
-/

namespace JanusFormal
namespace P0EFTJanusLLBraneCompositeMeasureFrechet

set_option autoImplicit false

noncomputable section

open scoped Matrix.Norms.Frobenius
open P0EFTJanusLLBraneAuxiliaryActionVariation
open P0EFTJanusLLBraneCompositeMeasureVariation

abbrev Matrix3 := P0EFTJanusLLBraneCompositeMeasureVariation.Matrix3

/-- Frechet differentiability with the Frobenius norm on matrix first jets. -/
def FrobeniusHasFDerivAt
    (function : Matrix3 → ℝ) (derivative : Matrix3 →L[ℝ] ℝ)
    (jet : Matrix3) : Prop :=
  @HasFDerivAt ℝ DenselyNormedField.toNontriviallyNormedField Matrix3
    Matrix.frobeniusNormedAddCommGroup.toAddCommGroup
    Matrix.frobeniusNormedSpace.toModule
    Matrix.frobeniusNormedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    ℝ Real.normedAddCommGroup.toAddCommGroup
    (RCLike.toInnerProductSpaceReal : InnerProductSpace ℝ ℝ).toModule
    Real.normedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    function derivative jet

/-- Evaluation of one first-jet entry as a continuous linear covector. -/
def entryCovector (row column : Fin 3) : Matrix3 →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun variation : Matrix3 => variation row column
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

@[simp]
theorem entryCovector_apply
    (row column : Fin 3) (variation : Matrix3) :
    entryCovector row column variation = variation row column := by
  rfl

/-- Product-rule covector for a product of three matrix entries. -/
def tripleEntryProductDerivative
    (jet : Matrix3)
    (firstRow firstColumn secondRow secondColumn thirdRow thirdColumn : Fin 3) :
    Matrix3 →L[ℝ] ℝ :=
  (jet firstRow firstColumn * jet secondRow secondColumn) •
      entryCovector thirdRow thirdColumn +
    jet thirdRow thirdColumn •
      (jet firstRow firstColumn • entryCovector secondRow secondColumn +
        jet secondRow secondColumn • entryCovector firstRow firstColumn)

/-- Full determinant covector, valid at singular as well as invertible jets. -/
def compositeMeasureFrechetDerivative (jet : Matrix3) : Matrix3 →L[ℝ] ℝ :=
  ((((tripleEntryProductDerivative jet 0 0 1 1 2 2 -
          tripleEntryProductDerivative jet 0 0 1 2 2 1) -
        tripleEntryProductDerivative jet 0 1 1 0 2 2) +
      tripleEntryProductDerivative jet 0 1 1 2 2 0) +
    tripleEntryProductDerivative jet 0 2 1 0 2 1) -
  tripleEntryProductDerivative jet 0 2 1 1 2 0

/-- Applying the Frechet covector reproduces the earlier entrywise
directional coefficient exactly. -/
theorem compositeMeasureFrechetDerivative_apply
    (jet variation : Matrix3) :
    compositeMeasureFrechetDerivative jet variation =
      compositeMeasureVariation jet variation := by
  simp only [compositeMeasureFrechetDerivative, tripleEntryProductDerivative,
    add_apply, smul_apply, sub_apply, entryCovector_apply,
    compositeMeasureVariation]
  ring

/-- The determinant is genuinely Frechet differentiable on the entire
finite-dimensional first-jet space. -/
theorem compositeMeasure_hasFDerivAt (jet : Matrix3) :
    FrobeniusHasFDerivAt compositeMeasure
      (compositeMeasureFrechetDerivative jet) jet := by
  unfold FrobeniusHasFDerivAt compositeMeasure
  rw [show
      (fun point : Matrix3 => Matrix.det point) =
        (fun point : Matrix3 =>
          point 0 0 * point 1 1 * point 2 2 -
            point 0 0 * point 1 2 * point 2 1 -
            point 0 1 * point 1 0 * point 2 2 +
            point 0 1 * point 1 2 * point 2 0 +
            point 0 2 * point 1 0 * point 2 1 -
            point 0 2 * point 1 1 * point 2 0) by
        funext point
        simp [Matrix.det_fin_three]]
  have h00 := (entryCovector 0 0).hasFDerivAt (x := jet)
  have h01 := (entryCovector 0 1).hasFDerivAt (x := jet)
  have h02 := (entryCovector 0 2).hasFDerivAt (x := jet)
  have h10 := (entryCovector 1 0).hasFDerivAt (x := jet)
  have h11 := (entryCovector 1 1).hasFDerivAt (x := jet)
  have h12 := (entryCovector 1 2).hasFDerivAt (x := jet)
  have h20 := (entryCovector 2 0).hasFDerivAt (x := jet)
  have h21 := (entryCovector 2 1).hasFDerivAt (x := jet)
  have h22 := (entryCovector 2 2).hasFDerivAt (x := jet)
  have hFirst := (h00.mul h11).mul h22
  have hSecond := (h00.mul h12).mul h21
  have hThird := (h01.mul h10).mul h22
  have hFourth := (h01.mul h12).mul h20
  have hFifth := (h02.mul h10).mul h21
  have hSixth := (h02.mul h11).mul h20
  have hTotal :=
    ((((hFirst.sub hSecond).sub hThird).add hFourth).add hFifth).sub hSixth
  have hFunctionEquality :
      (fun point : Matrix3 =>
        point 0 0 * point 1 1 * point 2 2 -
          point 0 0 * point 1 2 * point 2 1 -
          point 0 1 * point 1 0 * point 2 2 +
          point 0 1 * point 1 2 * point 2 0 +
          point 0 2 * point 1 0 * point 2 1 -
          point 0 2 * point 1 1 * point 2 0) =
        (fun point : Matrix3 =>
          entryCovector 0 0 point * entryCovector 1 1 point *
                entryCovector 2 2 point -
              entryCovector 0 0 point * entryCovector 1 2 point *
                entryCovector 2 1 point -
            entryCovector 0 1 point * entryCovector 1 0 point *
              entryCovector 2 2 point +
          entryCovector 0 1 point * entryCovector 1 2 point *
            entryCovector 2 0 point +
          entryCovector 0 2 point * entryCovector 1 0 point *
            entryCovector 2 1 point -
          entryCovector 0 2 point * entryCovector 1 1 point *
            entryCovector 2 0 point) := by
    funext point
    simp only [entryCovector_apply]
  have hEventually : Filter.EventuallyEq (nhds jet)
      (fun point : Matrix3 =>
        point 0 0 * point 1 1 * point 2 2 -
          point 0 0 * point 1 2 * point 2 1 -
          point 0 1 * point 1 0 * point 2 2 +
          point 0 1 * point 1 2 * point 2 0 +
          point 0 2 * point 1 0 * point 2 1 -
          point 0 2 * point 1 1 * point 2 0)
      (fun point : Matrix3 =>
        entryCovector 0 0 point * entryCovector 1 1 point *
              entryCovector 2 2 point -
            entryCovector 0 0 point * entryCovector 1 2 point *
              entryCovector 2 1 point -
          entryCovector 0 1 point * entryCovector 1 0 point *
            entryCovector 2 2 point +
        entryCovector 0 1 point * entryCovector 1 2 point *
          entryCovector 2 0 point +
        entryCovector 0 2 point * entryCovector 1 0 point *
          entryCovector 2 1 point -
        entryCovector 0 2 point * entryCovector 1 1 point *
          entryCovector 2 0 point) :=
    Filter.Eventually.of_forall fun point => congrFun hFunctionEquality point
  have hRewritten := hTotal.congr_of_eventuallyEq hEventually
  refine hRewritten.congr_fderiv ?_
  rfl

end

end P0EFTJanusLLBraneCompositeMeasureFrechet
end JanusFormal
