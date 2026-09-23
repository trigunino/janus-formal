import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateALocalPhysicalHessianSplit4D
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-! Reduce a tested physical Hessian using local identities of its true gradients. -/
namespace JanusFormal.P0EFTJanusProgramPT12PhysicalGaugeHessianReduction4D
set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology ContDiff
open P0EFTJanusConvexHelmholtzReconstruction
open P0EFTJanusProgramPFullCoupledHelmholtzAssembly4D
open P0EFTJanusProgramPGlobalCandidateALocalPhysicalHessianSplit4D
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]

theorem physicalGradient_eq_maxwell_of_zero (blocks : FullCoupledActionBlocks E)
    (point test : E) (hC2 : FullCoupledC2At blocks point)
    (hCandidate : actionGradient blocks.candidateA point test = 0)
    (hRobin : actionGradient blocks.robin point test = 0)
    (hPlus : actionGradient blocks.einsteinHilbertPlus point test = 0)
    (hMinus : actionGradient blocks.einsteinHilbertMinus point test = 0)
    (hFinite : actionGradient blocks.finiteBV point test = 0) :
    actionGradient (fullCoupledPhysicalAction blocks) point test =
      actionGradient blocks.maxwellPlus point test + actionGradient blocks.maxwellMinus point test := by
  have h := ((((((hC2.candidateA.differentiableAt (by norm_num)).hasFDerivAt.add
    (hC2.robin.differentiableAt (by norm_num)).hasFDerivAt).add
    (hC2.einsteinHilbertPlus.differentiableAt (by norm_num)).hasFDerivAt).add
    (hC2.einsteinHilbertMinus.differentiableAt (by norm_num)).hasFDerivAt).add
    (hC2.maxwellPlus.differentiableAt (by norm_num)).hasFDerivAt).add
    (hC2.maxwellMinus.differentiableAt (by norm_num)).hasFDerivAt).add
    (hC2.finiteBV.differentiableAt (by norm_num)).hasFDerivAt
  have hEval := congrArg (fun derivative : E →L[Real] Real => derivative test) h.fderiv
  change actionGradient (fullCoupledPhysicalAction blocks) point test = _ at hEval
  simp only [actionGradient] at hCandidate hRobin hPlus hMinus hFinite hEval ⊢
  simpa only [add_apply, hCandidate, hRobin,
    hPlus, hMinus, hFinite, zero_add, add_zero] using hEval

theorem hessian_eval (action : E → Real) (point first test : E)
    (hSecond : DifferentiableAt Real (fderiv Real action) point) :
    fderiv Real (fun current => fderiv Real action current test) point first =
      fderiv Real (fderiv Real action) point first test := by
  have h := hSecond.hasFDerivAt.clm_apply (hasFDerivAt_const test point)
  rw [h.fderiv]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    zero_apply, map_zero, zero_add, ContinuousLinearMap.flip_apply]

theorem hessian_eq_sum_of_eventually_tested_gradient
    (action plus minus : E → Real) (point first test : E)
    (hAction : ContDiffAt Real 2 action point)
    (hPlus : ContDiffAt Real 2 plus point) (hMinus : ContDiffAt Real 2 minus point)
    (hEq : (fun current => fderiv Real action current test) =ᶠ[𝓝 point]
      (fun current => fderiv Real plus current test + fderiv Real minus current test)) :
    fderiv Real (fderiv Real action) point first test =
      fderiv Real (fderiv Real plus) point first test +
      fderiv Real (fderiv Real minus) point first test := by
  have hA := (hAction.fderiv_right (show (1 : ℕ∞ω) + 1 ≤ 2 by norm_num)).differentiableAt (by norm_num)
  have hP := (hPlus.fderiv_right (show (1 : ℕ∞ω) + 1 ≤ 2 by norm_num)).differentiableAt (by norm_num)
  have hM := (hMinus.fderiv_right (show (1 : ℕ∞ω) + 1 ≤ 2 by norm_num)).differentiableAt (by norm_num)
  have hPEval := hP.clm_apply (differentiableAt_const test)
  have hMEval := hM.clm_apply (differentiableAt_const test)
  have hSum := fderiv_add hPEval hMEval
  simp only [Pi.add_def] at hSum
  rw [← hessian_eval action point first test hA, hEq.fderiv_eq,
    hSum, add_apply,
    hessian_eval plus point first test hP, hessian_eval minus point first test hM]

end
end JanusFormal.P0EFTJanusProgramPT12PhysicalGaugeHessianReduction4D
