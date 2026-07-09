import JanusFormal.Branches.P0EFTOrbifoldHolstPrototypeProgram.Gates.P0EFTVolumeLambdaPalatiniCalculation

namespace JanusFormal
namespace P0EFTVolumeLambdaOrientationClosure

set_option autoImplicit false

structure LambdaOrientationClosure where
  normalPointsMinusToPlus : Prop
  jumpDefinedPlusOverMinus : Prop
  boundaryActionCancelsOutwardTraceFlux : Prop
  lambdaEqualsMinusFourQT : Prop
  identityChannelClosed : Prop

def orientedLambdaClosed (o : LambdaOrientationClosure) : Prop :=
  o.normalPointsMinusToPlus /\
  o.jumpDefinedPlusOverMinus /\
  o.boundaryActionCancelsOutwardTraceFlux /\
  o.lambdaEqualsMinusFourQT /\
  o.identityChannelClosed

theorem orientation_fixes_lambda_sign
    (o : LambdaOrientationClosure)
    (hNormal : o.normalPointsMinusToPlus)
    (hJump : o.jumpDefinedPlusOverMinus)
    (hBoundary : o.boundaryActionCancelsOutwardTraceFlux)
    (hLambda : o.lambdaEqualsMinusFourQT)
    (hIdentity : o.identityChannelClosed) :
    orientedLambdaClosed o := by
  exact And.intro hNormal
    (And.intro hJump
      (And.intro hBoundary
        (And.intro hLambda hIdentity)))

end P0EFTVolumeLambdaOrientationClosure
end JanusFormal
