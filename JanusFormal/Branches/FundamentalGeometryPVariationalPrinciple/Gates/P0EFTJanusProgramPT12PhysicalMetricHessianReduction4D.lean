import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12PhysicalGaugeHessianReduction4D

/-! Exact five-block physical Hessian after the locally constant boundary blocks. -/
namespace JanusFormal.P0EFTJanusProgramPT12PhysicalMetricHessianReduction4D
set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology ContDiff
open P0EFTJanusConvexHelmholtzReconstruction
open P0EFTJanusProgramPFullCoupledHelmholtzAssembly4D
open P0EFTJanusProgramPGlobalCandidateALocalPhysicalHessianSplit4D
open P0EFTJanusProgramPT12PhysicalGaugeHessianReduction4D
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]

theorem secondFrechet_add (first second : E → Real) (point left right : E)
    (hFirst : ContDiffAt Real 2 first point) (hSecond : ContDiffAt Real 2 second point) :
    fderiv Real (fderiv Real (fun current => first current + second current)) point left right =
      fderiv Real (fderiv Real first) point left right + fderiv Real (fderiv Real second) point left right := by
  apply hessian_eq_sum_of_eventually_tested_gradient _ first second point left right
    (hFirst.add hSecond) hFirst hSecond
  filter_upwards [hFirst.eventually (by norm_num), hSecond.eventually (by norm_num)] with current hF hS
  rw [fderiv_fun_add (hF.differentiableAt (by norm_num)) (hS.differentiableAt (by norm_num)), add_apply]

theorem secondFrechet_zero_of_gradient (action : E → Real) (point left right : E)
    (hZero : fderiv Real action =ᶠ[𝓝 point] (fun _ => 0)) :
    fderiv Real (fderiv Real action) point left right = 0 := by
  rw [hZero.fderiv_eq]
  simp

theorem physicalHessian_eq_five (blocks : FullCoupledActionBlocks E) (point left right : E)
    (hC2 : FullCoupledC2At blocks point)
    (hRobin : fderiv Real blocks.robin =ᶠ[𝓝 point] (fun _ => 0))
    (hFinite : fderiv Real blocks.finiteBV =ᶠ[𝓝 point] (fun _ => 0)) :
    fderiv Real (fderiv Real (fullCoupledPhysicalAction blocks)) point left right =
      fderiv Real (fderiv Real blocks.candidateA) point left right +
      (fderiv Real (fderiv Real blocks.einsteinHilbertPlus) point left right +
       fderiv Real (fderiv Real blocks.einsteinHilbertMinus) point left right) +
      (fderiv Real (fderiv Real blocks.maxwellPlus) point left right +
       fderiv Real (fderiv Real blocks.maxwellMinus) point left right) := by
  unfold fullCoupledPhysicalAction
  rw [secondFrechet_add _ _ point left right
    (((((hC2.candidateA.add hC2.robin).add hC2.einsteinHilbertPlus).add
      hC2.einsteinHilbertMinus).add hC2.maxwellPlus).add hC2.maxwellMinus) hC2.finiteBV]
  rw [secondFrechet_add _ _ point left right
    ((((hC2.candidateA.add hC2.robin).add hC2.einsteinHilbertPlus).add
      hC2.einsteinHilbertMinus).add hC2.maxwellPlus) hC2.maxwellMinus]
  rw [secondFrechet_add _ _ point left right
    (((hC2.candidateA.add hC2.robin).add hC2.einsteinHilbertPlus).add hC2.einsteinHilbertMinus) hC2.maxwellPlus]
  rw [secondFrechet_add _ _ point left right
    ((hC2.candidateA.add hC2.robin).add hC2.einsteinHilbertPlus) hC2.einsteinHilbertMinus]
  rw [secondFrechet_add _ _ point left right (hC2.candidateA.add hC2.robin) hC2.einsteinHilbertPlus]
  rw [secondFrechet_add _ _ point left right hC2.candidateA hC2.robin,
    secondFrechet_zero_of_gradient _ _ _ _ hRobin, secondFrechet_zero_of_gradient _ _ _ _ hFinite]
  ring

end
end JanusFormal.P0EFTJanusProgramPT12PhysicalMetricHessianReduction4D
