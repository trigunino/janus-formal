import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12CurvatureJetSymbol4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12VectorHessianPullback4D

/-! Coordinate assembly of first and second derivatives of the finite curvature jet. -/
namespace JanusFormal.P0EFTJanusProgramPT12CurvatureJetDifferentials4D
set_option autoImplicit false
noncomputable section
open P0EFTJanusProgramPT12CurvatureJetSymbol4D
open P0EFTJanusProgramPT12VectorHessianPullback4D

def valueReadout (row column : Fin 4) : CurvatureJet →L[Real] Real where
  toFun jet := jet.1 row column
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := by fun_prop

def inverseReadout (row column : Fin 4) : CurvatureJet →L[Real] Real where
  toFun jet := jet.2.1 row column
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := by fun_prop

def firstReadout (direction row column : Fin 4) : CurvatureJet →L[Real] Real where
  toFun jet := jet.2.2.1 direction row column
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := by fun_prop

def secondReadout (outer inner row column : Fin 4) : CurvatureJet →L[Real] Real where
  toFun jet := jet.2.2.2 outer inner row column
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := by fun_prop

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]

theorem curvatureJet_fderiv (field : E → CurvatureJet) (point direction : E)
    (hField : DifferentiableAt Real field point) :
    fderiv Real field point direction =
      (fun row column => fderiv Real (fun x => (field x).1 row column) point direction,
       fun row column => fderiv Real (fun x => (field x).2.1 row column) point direction,
       fun d row column => fderiv Real (fun x => (field x).2.2.1 d row column) point direction,
       fun outer inner row column =>
         fderiv Real (fun x => (field x).2.2.2 outer inner row column) point direction) := by
  have h (linear : CurvatureJet →L[Real] Real) :
      fderiv Real (linear ∘ field) point direction = linear (fderiv Real field point direction) :=
    congrArg (fun derivative : E →L[Real] Real => derivative direction)
      (linear.hasFDerivAt.comp point hField.hasFDerivAt).fderiv
  apply Prod.ext
  · funext row column
    exact (h (valueReadout row column)).symm
  apply Prod.ext
  · funext row column
    exact (h (inverseReadout row column)).symm
  apply Prod.ext
  · funext d row column
    exact (h (firstReadout d row column)).symm
  · funext outer inner row column
    exact (h (secondReadout outer inner row column)).symm

theorem curvatureJet_hessian (field : E → CurvatureJet) (point first second : E)
    (hField : ContDiffAt Real 2 field point) :
    fderiv Real (fderiv Real field) point first second =
      (fun row column => fderiv Real (fderiv Real (fun x => (field x).1 row column)) point first second,
       fun row column => fderiv Real (fderiv Real (fun x => (field x).2.1 row column)) point first second,
       fun d row column => fderiv Real (fderiv Real (fun x => (field x).2.2.1 d row column)) point first second,
       fun outer inner row column =>
         fderiv Real (fderiv Real (fun x => (field x).2.2.2 outer inner row column)) point first second) := by
  apply Prod.ext
  · funext row column
    exact (linearPostHessian (valueReadout row column) field point first second hField).symm
  apply Prod.ext
  · funext row column
    exact (linearPostHessian (inverseReadout row column) field point first second hField).symm
  apply Prod.ext
  · funext d row column
    exact (linearPostHessian (firstReadout d row column) field point first second hField).symm
  · funext outer inner row column
    exact (linearPostHessian (secondReadout outer inner row column) field point first second hField).symm

end
end JanusFormal.P0EFTJanusProgramPT12CurvatureJetDifferentials4D
