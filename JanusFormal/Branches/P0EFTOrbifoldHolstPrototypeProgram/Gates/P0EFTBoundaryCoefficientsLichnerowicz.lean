import JanusFormal.Branches.P0EFTOrbifoldHolstPrototypeProgram.Gates.P0EFTBoundaryRunCalculation

namespace JanusFormal
namespace P0EFTBoundaryCoefficientsLichnerowicz

set_option autoImplicit false

structure BoundaryCoefficientMatching where
  bulkFluxNormalCoeffKnown : Prop
  diracBoundaryNormalCoeffKnown : Prop
  janusPinGammaFiveCoeffKnown : Prop
  literalJanusCandidateHasNoForbiddenResidues : Prop
  forbiddenResiduesCancelledByDerivedBoundaryTerms : Prop
  identityResidueZero : Prop
  chiralNormalResidueZero : Prop
  gammaFiveMatchesOrientedNormal : Prop

structure LichnerowiczZeroModeCheck where
  riemannianCompactAPSBoundary : Prop
  hSquaredPositive : Prop
  scalarCurvaturePositive : Prop
  lichnerowiczFormulaApplies : Prop
  zeroModesAbsent : Prop
  lorentzianSpectrumDefined : Prop

def coefficientMatchingClosed (c : BoundaryCoefficientMatching) : Prop :=
  c.bulkFluxNormalCoeffKnown /\
  c.diracBoundaryNormalCoeffKnown /\
  c.janusPinGammaFiveCoeffKnown /\
  c.literalJanusCandidateHasNoForbiddenResidues /\
  c.forbiddenResiduesCancelledByDerivedBoundaryTerms /\
  c.identityResidueZero /\
  c.chiralNormalResidueZero /\
  c.gammaFiveMatchesOrientedNormal

def zeroModesClosedConditionally (z : LichnerowiczZeroModeCheck) : Prop :=
  z.riemannianCompactAPSBoundary /\
  z.hSquaredPositive /\
  z.scalarCurvaturePositive /\
  z.lichnerowiczFormulaApplies /\
  z.zeroModesAbsent

theorem matching_coefficients_close_run1
    (c : BoundaryCoefficientMatching)
    (hBulk : c.bulkFluxNormalCoeffKnown)
    (hBnd : c.diracBoundaryNormalCoeffKnown)
    (hJanus : c.janusPinGammaFiveCoeffKnown)
    (hNoForbidden : c.literalJanusCandidateHasNoForbiddenResidues)
    (hCancel : c.forbiddenResiduesCancelledByDerivedBoundaryTerms)
    (hI : c.identityResidueZero)
    (hC : c.chiralNormalResidueZero)
    (hRatio : c.gammaFiveMatchesOrientedNormal) :
    coefficientMatchingClosed c := by
  exact And.intro hBulk
    (And.intro hBnd
      (And.intro hJanus
        (And.intro hNoForbidden
          (And.intro hCancel
            (And.intro hI
              (And.intro hC hRatio))))))

theorem missing_janus_pin_coefficient_blocks_run1
    (c : BoundaryCoefficientMatching)
    (hMissing : Not c.janusPinGammaFiveCoeffKnown) :
    Not (coefficientMatchingClosed c) := by
  intro h
  exact hMissing h.right.right.left

theorem literal_forbidden_residues_block_run1
    (c : BoundaryCoefficientMatching)
    (hForbidden : Not c.literalJanusCandidateHasNoForbiddenResidues) :
    Not (coefficientMatchingClosed c) := by
  intro h
  exact hForbidden h.right.right.right.left

theorem lichnerowicz_closes_zero_modes_on_riemannian_boundary
    (z : LichnerowiczZeroModeCheck)
    (hRiemannian : z.riemannianCompactAPSBoundary)
    (hH : z.hSquaredPositive)
    (hR : z.scalarCurvaturePositive)
    (hFormula : z.lichnerowiczFormulaApplies)
    (hZero : z.zeroModesAbsent) :
    zeroModesClosedConditionally z := by
  exact And.intro hRiemannian
    (And.intro hH
      (And.intro hR
        (And.intro hFormula hZero)))

end P0EFTBoundaryCoefficientsLichnerowicz
end JanusFormal
