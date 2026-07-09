import JanusFormal.Branches.P0EarlyProgram.Gates.P0DoubleDualCartanConditionalClosure

namespace JanusFormal
namespace P0EFTLoopDoubleDualConditional

open P0DoubleDualCartanConditionalClosure
open P0ScalarVectorModeStability

set_option autoImplicit false

structure EFTLoopGeneratedDoubleDual where
  bulkModesIntegratedOut : Prop
  heatKernelExpansionAvailable : Prop
  curvatureRadionOperatorsGenerated : Prop
  nonHorndeskiTermsProjectedOut : Prop
  doubleDualCoefficientGenerated : Prop
  coefficientRenormalizationStable : Prop

def acceptedEFTLoopSource (e : EFTLoopGeneratedDoubleDual) : Prop :=
  e.bulkModesIntegratedOut /\
  e.heatKernelExpansionAvailable /\
  e.curvatureRadionOperatorsGenerated /\
  e.nonHorndeskiTermsProjectedOut /\
  e.doubleDualCoefficientGenerated /\
  e.coefficientRenormalizationStable

def doubleDualSourceFromEFT (e : EFTLoopGeneratedDoubleDual) : DoubleDualCartanSource :=
  { doubleDualCurvatureTorsionInvariant := e.doubleDualCoefficientGenerated
    orbifoldEven := e.nonHorndeskiTermsProjectedOut
    parityEven := e.nonHorndeskiTermsProjectedOut
    secondOrderEquations := e.nonHorndeskiTermsProjectedOut
    generatesHorndeskiRadion := e.curvatureRadionOperatorsGenerated /\ e.doubleDualCoefficientGenerated }

theorem eft_loop_source_gives_double_dual_source
    (e : EFTLoopGeneratedDoubleDual)
    (h : acceptedEFTLoopSource e) :
    acceptedDoubleDualSource (doubleDualSourceFromEFT e) := by
  rcases h with
    ⟨_hBulk, _hHeat, hCurv, hProject, hDoubleDual, _hStable⟩
  dsimp [acceptedDoubleDualSource, doubleDualSourceFromEFT]
  exact ⟨hDoubleDual, hProject, hProject, hProject, ⟨hCurv, hDoubleDual⟩⟩

theorem eft_loop_conditional_closure_gives_scalar_stability
    (e : EFTLoopGeneratedDoubleDual)
    {boundaryCompletion k2ContactClosed k4ContactClosed : Prop}
    {alphaDSPositive betaDSPositive soundSpeedPositive : Prop}
    (hEFT : acceptedEFTLoopSource e)
    (hBoundary : boundaryCompletion)
    (hK2 : k2ContactClosed)
    (hK4 : k4ContactClosed)
    (hAlpha : alphaDSPositive)
    (hBeta : betaDSPositive)
    (hSound : soundSpeedPositive) :
    scalarLinearModeStable
      (scalarCoefficientsFromClosure
        (closureFromDoubleDualSource
          (doubleDualSourceFromEFT e)
          boundaryCompletion k2ContactClosed k4ContactClosed
          alphaDSPositive betaDSPositive soundSpeedPositive)) := by
  exact double_dual_closure_gives_scalar_stability
    (doubleDualSourceFromEFT e)
    (eft_loop_source_gives_double_dual_source e hEFT)
    hBoundary
    hK2
    hK4
    hAlpha
    hBeta
    hSound

theorem missing_heat_kernel_blocks_eft_route
    (e : EFTLoopGeneratedDoubleDual)
    (hMissing : Not e.heatKernelExpansionAvailable) :
    Not (acceptedEFTLoopSource e) := by
  intro h
  exact hMissing h.right.left

theorem missing_projection_blocks_eft_route
    (e : EFTLoopGeneratedDoubleDual)
    (hMissing : Not e.nonHorndeskiTermsProjectedOut) :
    Not (acceptedEFTLoopSource e) := by
  intro h
  exact hMissing h.right.right.right.left

end P0EFTLoopDoubleDualConditional
end JanusFormal
