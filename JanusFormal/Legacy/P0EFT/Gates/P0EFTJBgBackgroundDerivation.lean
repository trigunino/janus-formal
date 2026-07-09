import JanusFormal.Legacy.P0EFT.Gates.P0EFTChiInfinityStationaryClosure

namespace JanusFormal
namespace P0EFTJBgBackgroundDerivation

set_option autoImplicit false

structure JBgBackgroundDerivation where
  jbgDefinedFromDSTraceJump : Prop
  orientationSignExplicit : Prop
  coupledStationaryAndDSEquationsSolved : Prop
  existenceBoundSatisfied : Prop
  chiInfinityFixedByBranchData : Prop
  lambdaJFixedByBranchData : Prop
  run1OrientationConventionSelected : Prop
  unitsConventionFixed : Prop
  amplitudeClosedConditionally : Prop
  unconditionalNoFitReady : Prop

def jbgClosureConditional (j : JBgBackgroundDerivation) : Prop :=
  j.jbgDefinedFromDSTraceJump /\
  j.orientationSignExplicit /\
  j.coupledStationaryAndDSEquationsSolved /\
  j.existenceBoundSatisfied /\
  j.chiInfinityFixedByBranchData /\
  j.lambdaJFixedByBranchData /\
  j.amplitudeClosedConditionally

def jbgClosureReadyForNumerics (j : JBgBackgroundDerivation) : Prop :=
  jbgClosureConditional j /\
  j.run1OrientationConventionSelected /\
  j.unitsConventionFixed

def jbgClosureUnconditional (j : JBgBackgroundDerivation) : Prop :=
  jbgClosureReadyForNumerics j /\ j.unconditionalNoFitReady

theorem trace_jump_source_closes_jbg_conditionally
    (j : JBgBackgroundDerivation)
    (hJ : j.jbgDefinedFromDSTraceJump)
    (hOrient : j.orientationSignExplicit)
    (hSolved : j.coupledStationaryAndDSEquationsSolved)
    (hBound : j.existenceBoundSatisfied)
    (hChi : j.chiInfinityFixedByBranchData)
    (hLambda : j.lambdaJFixedByBranchData)
    (hAmp : j.amplitudeClosedConditionally) :
    jbgClosureConditional j := by
  exact And.intro hJ
    (And.intro hOrient
      (And.intro hSolved
        (And.intro hBound
          (And.intro hChi
            (And.intro hLambda hAmp)))))

theorem missing_orientation_blocks_numeric_jbg
    (j : JBgBackgroundDerivation)
    (hMissing : Not j.run1OrientationConventionSelected) :
    Not (jbgClosureReadyForNumerics j) := by
  intro h
  exact hMissing h.right.left

theorem missing_units_blocks_numeric_jbg
    (j : JBgBackgroundDerivation)
    (hMissing : Not j.unitsConventionFixed) :
    Not (jbgClosureReadyForNumerics j) := by
  intro h
  exact hMissing h.right.right

theorem jbg_ready_after_orientation_and_units
    (j : JBgBackgroundDerivation)
    (hConditional : jbgClosureConditional j)
    (hOrientation : j.run1OrientationConventionSelected)
    (hUnits : j.unitsConventionFixed) :
    jbgClosureReadyForNumerics j := by
  exact And.intro hConditional (And.intro hOrientation hUnits)

end P0EFTJBgBackgroundDerivation
end JanusFormal
