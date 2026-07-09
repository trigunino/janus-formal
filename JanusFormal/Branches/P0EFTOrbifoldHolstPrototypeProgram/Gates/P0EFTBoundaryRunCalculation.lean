import JanusFormal.Branches.P0EFTOrbifoldHolstPrototypeProgram.Gates.P0EFTBoundaryRunTargets

namespace JanusFormal
namespace P0EFTBoundaryRunCalculation

set_option autoImplicit false

structure Run1CoefficientConditions where
  identityResidueZero : Prop
  chiralNormalResidueZero : Prop
  gammaFiveCoefficientMatchesNormal : Prop
  physicalCoefficientsKnown : Prop

structure Run2SpectralConditions where
  apsOperatorDefined : Prop
  intrinsicDiracAnticommutesGammaFive : Prop
  normalGammaAnticommutesGammaFive : Prop
  apsCommutesGammaFive : Prop
  boundarySpectrumKnown : Prop
  zeroModesEvenOrAbsent : Prop

def run1CalculatedClosure (r : Run1CoefficientConditions) : Prop :=
  r.identityResidueZero /\
  r.chiralNormalResidueZero /\
  r.gammaFiveCoefficientMatchesNormal /\
  r.physicalCoefficientsKnown

def run2CalculatedClosure (r : Run2SpectralConditions) : Prop :=
  r.apsOperatorDefined /\
  r.intrinsicDiracAnticommutesGammaFive /\
  r.normalGammaAnticommutesGammaFive /\
  r.apsCommutesGammaFive /\
  r.boundarySpectrumKnown /\
  r.zeroModesEvenOrAbsent

theorem run1_coefficient_equalities_close_when_coefficients_known
    (r : Run1CoefficientConditions)
    (hI : r.identityResidueZero)
    (hC : r.chiralNormalResidueZero)
    (hG : r.gammaFiveCoefficientMatchesNormal)
    (hPhys : r.physicalCoefficientsKnown) :
    run1CalculatedClosure r := by
  exact And.intro hI (And.intro hC (And.intro hG hPhys))

theorem run1_missing_physical_coefficients_blocks_closure
    (r : Run1CoefficientConditions)
    (hMissing : Not r.physicalCoefficientsKnown) :
    Not (run1CalculatedClosure r) := by
  intro h
  exact hMissing h.right.right.right

theorem run2_spectral_conditions_close_when_spectrum_known
    (r : Run2SpectralConditions)
    (hOp : r.apsOperatorDefined)
    (hD : r.intrinsicDiracAnticommutesGammaFive)
    (hN : r.normalGammaAnticommutesGammaFive)
    (hComm : r.apsCommutesGammaFive)
    (hSpec : r.boundarySpectrumKnown)
    (hZero : r.zeroModesEvenOrAbsent) :
    run2CalculatedClosure r := by
  exact And.intro hOp
    (And.intro hD
      (And.intro hN
        (And.intro hComm
          (And.intro hSpec hZero))))

theorem run2_missing_spectrum_blocks_closure
    (r : Run2SpectralConditions)
    (hMissing : Not r.boundarySpectrumKnown) :
    Not (run2CalculatedClosure r) := by
  intro h
  exact hMissing h.right.right.right.right.left

end P0EFTBoundaryRunCalculation
end JanusFormal
