import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12MaxwellJetSymbol4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12VectorHessianPullback4D

/-! Coordinate assembly of the native Maxwell jet derivatives. -/
namespace JanusFormal.P0EFTJanusProgramPT12MaxwellJetDifferentials4D
set_option autoImplicit false
noncomputable section
open P0EFTJanusProgramPT12MaxwellJetSymbol4D
open P0EFTJanusProgramPT12VectorHessianPullback4D

def inverseReadout (row column : Fin 4) : MaxwellJet →L[Real] Real where
  toFun jet := jet.1 row column
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := by fun_prop

def curvatureReadout (component : Fin 2) (row column : Fin 4) : MaxwellJet →L[Real] Real where
  toFun jet := jet.2 component row column
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := by fun_prop

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]

theorem maxwellJet_fderiv (field : E → MaxwellJet) (point direction : E)
    (hField : DifferentiableAt Real field point) :
    fderiv Real field point direction =
      (fun row column => fderiv Real (fun current => (field current).1 row column) point direction,
       fun component row column =>
         fderiv Real (fun current => (field current).2 component row column) point direction) := by
  have h (linear : MaxwellJet →L[Real] Real) :
      fderiv Real (linear ∘ field) point direction = linear (fderiv Real field point direction) :=
    congrArg (fun derivative : E →L[Real] Real => derivative direction)
      (linear.hasFDerivAt.comp point hField.hasFDerivAt).fderiv
  apply Prod.ext
  · funext row column
    exact (h (inverseReadout row column)).symm
  · funext component row column
    exact (h (curvatureReadout component row column)).symm

theorem maxwellJet_hessian (field : E → MaxwellJet) (point first second : E)
    (hField : ContDiffAt Real 2 field point) :
    fderiv Real (fderiv Real field) point first second =
      (fun row column =>
         fderiv Real (fderiv Real (fun current => (field current).1 row column)) point first second,
       fun component row column =>
         fderiv Real (fderiv Real (fun current => (field current).2 component row column)) point first second) := by
  apply Prod.ext
  · funext row column
    exact (linearPostHessian (inverseReadout row column) field point first second hField).symm
  · funext component row column
    exact (linearPostHessian (curvatureReadout component row column) field point first second hField).symm

end
end JanusFormal.P0EFTJanusProgramPT12MaxwellJetDifferentials4D
