import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12MaxwellTransportFirstJetSymbol4D
import Mathlib.Data.Matrix.Mul

/-! Matrix multiplication with its first spatial Leibniz jet. -/
namespace JanusFormal.P0EFTJanusProgramPT12MatrixFirstJetProduct4D
set_option autoImplicit false
noncomputable section
open P0EFTJanusProgramPT12MaxwellTransportFirstJetSymbol4D
open scoped ContDiff
private abbrev Matrix4 := Matrix (Fin 4) (Fin 4) Real

private def valueLinear : MatrixFirstJet →ₗ[Real] Matrix4 where
  toFun jet := jet.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def firstLinear (direction : Fin 4) : MatrixFirstJet →ₗ[Real] Matrix4 where
  toFun jet := jet.2 direction
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def leftProduct (left : Matrix4) : Matrix4 →ₗ[Real] Matrix4 where
  toFun right := left * right
  map_add' := Matrix.mul_add left
  map_smul' scalar right := Matrix.mul_smul left scalar right

private def rightProduct (right : Matrix4) : Matrix4 →ₗ[Real] Matrix4 where
  toFun left := left * right
  map_add' first second := Matrix.add_mul first second right
  map_smul' scalar left := Matrix.smul_mul scalar left right

def matrixFirstJetLeft (first : MatrixFirstJet) : MatrixFirstJet →L[Real] MatrixFirstJet :=
  LinearMap.toContinuousLinearMap {
    toFun := fun second => ((leftProduct first.1).comp valueLinear second,
      fun direction => ((leftProduct (first.2 direction)).comp valueLinear +
        (leftProduct first.1).comp (firstLinear direction)) second)
    map_add' := by intros; ext <;> simp only [map_add] <;> rfl
    map_smul' := by intros; ext <;> simp only [map_smul] <;> rfl }

def matrixFirstJetRight (second : MatrixFirstJet) : MatrixFirstJet →L[Real] MatrixFirstJet :=
  LinearMap.toContinuousLinearMap {
    toFun := fun first => ((rightProduct second.1).comp valueLinear first,
      fun direction => ((rightProduct second.1).comp (firstLinear direction) +
        (rightProduct (second.2 direction)).comp valueLinear) first)
    map_add' := by intros; ext <;> simp only [map_add] <;> rfl
    map_smul' := by intros; ext <;> simp only [map_smul] <;> rfl }

theorem matrixFirstJetRight_apply (first second : MatrixFirstJet) :
    matrixFirstJetRight second first = matrixFirstJetLeft first second := rfl

theorem matrixFirstJetLeft_contDiff :
    ContDiff Real ∞ (fun input : MatrixFirstJet × MatrixFirstJet => matrixFirstJetLeft input.1 input.2) := by
  change ContDiff Real ∞ (fun input : MatrixFirstJet × MatrixFirstJet =>
    (fun row column => ∑ middle, input.1.1 row middle * input.2.1 middle column,
     fun direction row column =>
       (∑ middle, input.1.2 direction row middle * input.2.1 middle column) +
       (∑ middle, input.1.1 row middle * input.2.2 direction middle column)))
  fun_prop

end
end JanusFormal.P0EFTJanusProgramPT12MatrixFirstJetProduct4D
