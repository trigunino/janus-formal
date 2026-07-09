import JanusFormal.Branches.P0EFTOrbifoldHolstPrototypeProgram.Gates.P0EFTBoundaryFactorizationAPSBridge

namespace JanusFormal
namespace P0EFTBoundaryRunTargets

set_option autoImplicit false

structure Run1CliffordMatching where
  mtotCoefficientsComputed : Prop
  nonTargetResiduesVanish : Prop
  orientationSignFixesRatio : Prop
  factorizationProved : Prop

structure Run2APSSpectrum where
  apsOperatorDerived : Prop
  gammaFiveCommutatorZero : Prop
  chiralEqualsAPSHalfSpace : Prop
  zeroModesAbsentOrEven : Prop

def run1Closed (r : Run1CliffordMatching) : Prop :=
  r.mtotCoefficientsComputed /\
  r.nonTargetResiduesVanish /\
  r.orientationSignFixesRatio /\
  r.factorizationProved

def run2Closed (r : Run2APSSpectrum) : Prop :=
  r.apsOperatorDerived /\
  r.gammaFiveCommutatorZero /\
  r.chiralEqualsAPSHalfSpace /\
  r.zeroModesAbsentOrEven

def bothBoundaryRunsClosed
    (r1 : Run1CliffordMatching)
    (r2 : Run2APSSpectrum) : Prop :=
  run1Closed r1 /\ run2Closed r2

theorem run1_inputs_close_factorization
    (r : Run1CliffordMatching)
    (hCoeff : r.mtotCoefficientsComputed)
    (hResidues : r.nonTargetResiduesVanish)
    (hRatio : r.orientationSignFixesRatio)
    (hFactor : r.factorizationProved) :
    run1Closed r := by
  exact And.intro hCoeff (And.intro hResidues (And.intro hRatio hFactor))

theorem run2_inputs_close_aps_bridge
    (r : Run2APSSpectrum)
    (hOp : r.apsOperatorDerived)
    (hComm : r.gammaFiveCommutatorZero)
    (hHalf : r.chiralEqualsAPSHalfSpace)
    (hZero : r.zeroModesAbsentOrEven) :
    run2Closed r := by
  exact And.intro hOp (And.intro hComm (And.intro hHalf hZero))

theorem missing_run1_blocks_boundary_runs
    (r1 : Run1CliffordMatching)
    (r2 : Run2APSSpectrum)
    (hMissing : Not (run1Closed r1)) :
    Not (bothBoundaryRunsClosed r1 r2) := by
  intro h
  exact hMissing h.left

theorem missing_run2_blocks_boundary_runs
    (r1 : Run1CliffordMatching)
    (r2 : Run2APSSpectrum)
    (hMissing : Not (run2Closed r2)) :
    Not (bothBoundaryRunsClosed r1 r2) := by
  intro h
  exact hMissing h.right

theorem run1_and_run2_close_boundary_targets
    (r1 : Run1CliffordMatching)
    (r2 : Run2APSSpectrum)
    (hRun1 : run1Closed r1)
    (hRun2 : run2Closed r2) :
    bothBoundaryRunsClosed r1 r2 := by
  exact And.intro hRun1 hRun2

end P0EFTBoundaryRunTargets
end JanusFormal
