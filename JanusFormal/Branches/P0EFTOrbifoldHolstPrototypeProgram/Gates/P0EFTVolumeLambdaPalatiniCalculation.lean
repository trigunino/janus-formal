import JanusFormal.Branches.P0EFTOrbifoldHolstPrototypeProgram.Gates.P0EFTVolumeLambdaDerivation

namespace JanusFormal
namespace P0EFTVolumeLambdaPalatiniCalculation

set_option autoImplicit false

structure LambdaPalatiniCalculation where
  palatiniVariationPerformed : Prop
  deltaSourceExtracted : Prop
  factorFourDerivedFromDiracDimension : Prop
  lambdaMagnitudeFixed : Prop
  boundaryOrientationConventionFixed : Prop
  normalOrientationConventionFixed : Prop
  lambdaEqualsMinusFourQT : Prop

def lambdaMagnitudeDerived (c : LambdaPalatiniCalculation) : Prop :=
  c.palatiniVariationPerformed /\
  c.deltaSourceExtracted /\
  c.factorFourDerivedFromDiracDimension /\
  c.lambdaMagnitudeFixed

def lambdaSignFullyDerived (c : LambdaPalatiniCalculation) : Prop :=
  lambdaMagnitudeDerived c /\
  c.boundaryOrientationConventionFixed /\
  c.normalOrientationConventionFixed /\
  c.lambdaEqualsMinusFourQT

theorem palatini_calculation_derives_lambda_magnitude
    (c : LambdaPalatiniCalculation)
    (hPalatini : c.palatiniVariationPerformed)
    (hDelta : c.deltaSourceExtracted)
    (hFour : c.factorFourDerivedFromDiracDimension)
    (hMag : c.lambdaMagnitudeFixed) :
    lambdaMagnitudeDerived c := by
  exact And.intro hPalatini (And.intro hDelta (And.intro hFour hMag))

theorem missing_orientation_blocks_lambda_sign
    (c : LambdaPalatiniCalculation)
    (hMissing : Not c.boundaryOrientationConventionFixed) :
    Not (lambdaSignFullyDerived c) := by
  intro h
  exact hMissing h.right.left

theorem oriented_palatini_calculation_derives_lambda
    (c : LambdaPalatiniCalculation)
    (hMag : lambdaMagnitudeDerived c)
    (hBoundary : c.boundaryOrientationConventionFixed)
    (hNormal : c.normalOrientationConventionFixed)
    (hLambda : c.lambdaEqualsMinusFourQT) :
    lambdaSignFullyDerived c := by
  exact And.intro hMag (And.intro hBoundary (And.intro hNormal hLambda))

end P0EFTVolumeLambdaPalatiniCalculation
end JanusFormal
