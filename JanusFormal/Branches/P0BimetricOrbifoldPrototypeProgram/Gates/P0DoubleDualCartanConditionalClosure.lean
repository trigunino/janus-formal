import JanusFormal.Branches.P0BimetricOrbifoldPrototypeProgram.Gates.P0ScalarVectorModeStability

namespace JanusFormal
namespace P0DoubleDualCartanConditionalClosure

open P0ScalarVectorModeStability

set_option autoImplicit false

structure DoubleDualCartanSource where
  doubleDualCurvatureTorsionInvariant : Prop
  orbifoldEven : Prop
  parityEven : Prop
  secondOrderEquations : Prop
  generatesHorndeskiRadion : Prop

def acceptedDoubleDualSource (s : DoubleDualCartanSource) : Prop :=
  s.doubleDualCurvatureTorsionInvariant /\
  s.orbifoldEven /\
  s.parityEven /\
  s.secondOrderEquations /\
  s.generatesHorndeskiRadion

structure HorndeskiRadionClosure where
  bulkHorndeskiRadion : Prop
  boundaryCompletion : Prop
  k2ContactClosed : Prop
  k4ContactClosed : Prop
  alphaDSPositive : Prop
  betaDSPositive : Prop
  soundSpeedPositive : Prop

def closureFromDoubleDualSource
    (s : DoubleDualCartanSource)
    (boundaryCompletion k2ContactClosed k4ContactClosed : Prop)
    (alphaDSPositive betaDSPositive soundSpeedPositive : Prop) :
    HorndeskiRadionClosure :=
  { bulkHorndeskiRadion := s.generatesHorndeskiRadion
    boundaryCompletion := boundaryCompletion
    k2ContactClosed := k2ContactClosed
    k4ContactClosed := k4ContactClosed
    alphaDSPositive := alphaDSPositive
    betaDSPositive := betaDSPositive
    soundSpeedPositive := soundSpeedPositive }

def scalarCoefficientsFromClosure (c : HorndeskiRadionClosure) : ScalarQuadraticCoefficients :=
  { scalarAlphaPositive := c.alphaDSPositive
    scalarBetaPositive := c.betaDSPositive
    scalarSpeedSquaredPositive := c.soundSpeedPositive
    scalarMassMatrixPositive := c.k2ContactClosed /\ c.k4ContactClosed
    scalarHyperbolicSector := c.bulkHorndeskiRadion /\ c.boundaryCompletion }

theorem accepted_double_dual_generates_horndeski
    (s : DoubleDualCartanSource)
    (h : acceptedDoubleDualSource s) :
    s.generatesHorndeskiRadion := by
  exact h.right.right.right.right

theorem double_dual_closure_gives_scalar_stability
    (s : DoubleDualCartanSource)
    {boundaryCompletion k2ContactClosed k4ContactClosed : Prop}
    {alphaDSPositive betaDSPositive soundSpeedPositive : Prop}
    (hSource : acceptedDoubleDualSource s)
    (hBoundary : boundaryCompletion)
    (hK2 : k2ContactClosed)
    (hK4 : k4ContactClosed)
    (hAlpha : alphaDSPositive)
    (hBeta : betaDSPositive)
    (hSound : soundSpeedPositive) :
    scalarLinearModeStable
      (scalarCoefficientsFromClosure
        (closureFromDoubleDualSource
          s boundaryCompletion k2ContactClosed k4ContactClosed
          alphaDSPositive betaDSPositive soundSpeedPositive)) := by
  dsimp [
    scalarLinearModeStable,
    noScalarGhost,
    noScalarGradientInstability,
    scalarSectorHyperbolic,
    scalarCoefficientsFromClosure,
    closureFromDoubleDualSource,
  ]
  exact And.intro hAlpha
    (And.intro (And.intro hBeta hSound)
      (And.intro
        (And.intro (accepted_double_dual_generates_horndeski s hSource) hBoundary)
        (And.intro hK2 hK4)))

theorem missing_double_dual_source_blocks_conditional_route
    (s : DoubleDualCartanSource)
    (hMissing : Not s.doubleDualCurvatureTorsionInvariant) :
    Not (acceptedDoubleDualSource s) := by
  intro h
  exact hMissing h.left

end P0DoubleDualCartanConditionalClosure
end JanusFormal
