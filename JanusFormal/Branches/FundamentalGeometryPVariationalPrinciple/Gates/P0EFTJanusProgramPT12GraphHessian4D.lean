import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12VectorHessianPullback4D

/-! Derivatives of the graph of a C2 map. -/
namespace JanusFormal.P0EFTJanusProgramPT12GraphHessian4D
set_option autoImplicit false
noncomputable section
open scoped ContDiff
open P0EFTJanusProgramPT12VectorHessianPullback4D
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [NormedAddCommGroup F] [NormedSpace Real F]

theorem graph_fderiv (field : E → F) (point direction : E)
    (hField : DifferentiableAt Real field point) :
    fderiv Real (fun current => (current, field current)) point direction =
      (direction, fderiv Real field point direction) := by
  have h := (hasFDerivAt_id point).prodMk hField.hasFDerivAt
  simpa only [id_eq, ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply] using
    congrArg (fun derivative => derivative direction) h.fderiv

theorem graph_hessian (field : E → F) (point first second : E)
    (hField : ContDiffAt Real 2 field point) :
    fderiv Real (fderiv Real (fun current => (current, field current))) point first second =
      (0, fderiv Real (fderiv Real field) point first second) := by
  have hC2 : ContDiffAt Real 2 (fun current => (current, field current)) point :=
    contDiffAt_id.prodMk hField
  apply Prod.ext
  · have h := linearPostHessian (ContinuousLinearMap.fst Real E F)
      (fun current => (current, field current)) point first second hC2
    change fderiv Real (fderiv Real (fun current : E => current)) point first second = _ at h
    have hId : fderiv Real (fun current : E => current) =
        fun _ => ContinuousLinearMap.id Real E := funext fun current => (hasFDerivAt_id current).fderiv
    rw [hId] at h
    simp only [fderiv_const_apply, zero_apply] at h
    exact h.symm
  · exact (linearPostHessian (ContinuousLinearMap.snd Real E F)
      (fun current => (current, field current)) point first second hC2).symm

end
end JanusFormal.P0EFTJanusProgramPT12GraphHessian4D
