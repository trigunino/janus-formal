import Mathlib
import JanusFormal.Branches.FundamentalGeometryD.Gates.P0EFTJanusZ4HolonomyEtaGap

namespace JanusFormal
namespace P0EFTJanusZ4DiracAlphaLock

set_option autoImplicit false

open P0EFTJanusZ4HolonomyEtaGap

/--
Synthesis of the primitive monopole, quarter-holonomy and two-fold PT sectors.

The new physical input is explicit: the parity-even LL charge scale is the sum
of the equal squared gaps of the two PT-related folds,

`q_LL = gap_+^2 + gap_-^2 = 2*gap^2`.

The parity-odd eta contributions cancel, while the even squared gaps add.
-/
structure PairedZ4DiracChargeLock where
  gapData : QuarterHolonomyGapData
  sphereFirstSquaredGap : ℝ
  llChargeUnit : ℝ
  alphaSquaredLength : ℝ
  sphereGapPositive : 0 < sphereFirstSquaredGap
  llChargePositive : 0 < llChargeUnit
  alphaSquaredLengthPositive : 0 < alphaSquaredLength
  sphereGapLaw :
    sphereFirstSquaredGap * gapData.geometricLength ^ 2 = 2
  twoFoldEvenGapLaw :
    llChargeUnit = 2 * gapData.gapSquared
  primitiveLLFluxLaw :
    16 * llChargeUnit ^ 2 * alphaSquaredLength ^ 4 = 1

/-- The paired quarter-holonomy modes fix `4*q_LL*L^2=1`. -/
theorem paired_gap_fixes_ll_charge_scale
    (s : PairedZ4DiracChargeLock) :
    4 * s.llChargeUnit * s.gapData.geometricLength ^ 2 = 1 := by
  have hGap := quarter_gap_under_spectral_isotropy s.gapData
  calc
    4 * s.llChargeUnit * s.gapData.geometricLength ^ 2 =
        4 * (2 * s.gapData.gapSquared) *
          s.gapData.geometricLength ^ 2 := by
      rw [s.twoFoldEvenGapLaw]
    _ = 8 * s.gapData.gapSquared *
          s.gapData.geometricLength ^ 2 := by ring
    _ = 1 := hGap

/-- The sphere gap and paired circle gap imply `lambda_S2 = 8*q_LL`. -/
theorem dirac_pair_derives_one_eighth_charge_coefficient
    (s : PairedZ4DiracChargeLock) :
    8 * s.llChargeUnit = s.sphereFirstSquaredGap := by
  have hCharge := paired_gap_fixes_ll_charge_scale s
  have hChargeDoubled :
      8 * s.llChargeUnit * s.gapData.geometricLength ^ 2 = 2 := by
    nlinarith [hCharge]
  have hFactor :
      (8 * s.llChargeUnit - s.sphereFirstSquaredGap) *
        s.gapData.geometricLength ^ 2 = 0 := by
    calc
      (8 * s.llChargeUnit - s.sphereFirstSquaredGap) *
          s.gapData.geometricLength ^ 2 =
        8 * s.llChargeUnit * s.gapData.geometricLength ^ 2 -
          s.sphereFirstSquaredGap *
            s.gapData.geometricLength ^ 2 := by ring
      _ = 2 - 2 := by rw [hChargeDoubled, s.sphereGapLaw]
      _ = 0 := by norm_num
  have hLengthSquareNonzero :
      s.gapData.geometricLength ^ 2 ≠ 0 :=
    pow_ne_zero 2 (ne_of_gt s.gapData.geometricLengthPositive)
  have hDifference :
      8 * s.llChargeUnit - s.sphereFirstSquaredGap = 0 :=
    (mul_eq_zero.mp hFactor).resolve_right hLengthSquareNonzero
  linarith

/-- The paired Dirac gap fixes the same coefficient `c_q=1/8` found previously. -/
theorem ll_charge_is_one_eighth_sphere_gap
    (s : PairedZ4DiracChargeLock) :
    s.llChargeUnit = s.sphereFirstSquaredGap / 8 := by
  have h := dirac_pair_derives_one_eighth_charge_coefficient s
  linarith

/-- The primitive LL flux law then forces the exact-solution radius to equal `L`. -/
theorem z4_dirac_lock_forces_alpha_equals_geometry
    (s : PairedZ4DiracChargeLock) :
    s.alphaSquaredLength = s.gapData.geometricLength := by
  have hCharge := paired_gap_fixes_ll_charge_scale s
  have hGeometryFlux :
      16 * s.llChargeUnit ^ 2 *
        s.gapData.geometricLength ^ 4 = 1 := by
    calc
      16 * s.llChargeUnit ^ 2 *
          s.gapData.geometricLength ^ 4 =
        (4 * s.llChargeUnit *
          s.gapData.geometricLength ^ 2) ^ 2 := by ring
      _ = 1 := by rw [hCharge]; norm_num
  have hFourth :
      s.alphaSquaredLength ^ 4 =
        s.gapData.geometricLength ^ 4 := by
    have hDifference :
        16 * s.llChargeUnit ^ 2 *
          (s.alphaSquaredLength ^ 4 -
            s.gapData.geometricLength ^ 4) = 0 := by
      nlinarith [s.primitiveLLFluxLaw, hGeometryFlux]
    have hCoefficientNonzero :
        16 * s.llChargeUnit ^ 2 ≠ 0 := by
      exact mul_ne_zero (by norm_num)
        (pow_ne_zero 2 (ne_of_gt s.llChargePositive))
    have hPowerDifference :
        s.alphaSquaredLength ^ 4 -
          s.gapData.geometricLength ^ 4 = 0 :=
      (mul_eq_zero.mp hDifference).resolve_left hCoefficientNonzero
    linarith
  have hSquareFactor :
      (s.alphaSquaredLength ^ 2 -
          s.gapData.geometricLength ^ 2) *
        (s.alphaSquaredLength ^ 2 +
          s.gapData.geometricLength ^ 2) = 0 := by
    nlinarith [hFourth]
  have hSquares :
      s.alphaSquaredLength ^ 2 =
        s.gapData.geometricLength ^ 2 := by
    rcases mul_eq_zero.mp hSquareFactor with hDifference | hSum
    · linarith
    · have hPositive :
          0 < s.alphaSquaredLength ^ 2 +
            s.gapData.geometricLength ^ 2 := by
        exact add_pos
          (pow_pos s.alphaSquaredLengthPositive 2)
          (pow_pos s.gapData.geometricLengthPositive 2)
      exact False.elim ((ne_of_gt hPositive) hSum)
  have hRootFactor :
      (s.alphaSquaredLength - s.gapData.geometricLength) *
        (s.alphaSquaredLength + s.gapData.geometricLength) = 0 := by
    nlinarith [hSquares]
  rcases mul_eq_zero.mp hRootFactor with hDifference | hSum
  · linarith
  · have hPositive :
        0 < s.alphaSquaredLength + s.gapData.geometricLength :=
      add_pos s.alphaSquaredLengthPositive
        s.gapData.geometricLengthPositive
    exact False.elim ((ne_of_gt hPositive) hSum)

/-- PT cancels the parity-odd eta term while retaining the parity-even gap sum. -/
theorem pt_pair_cancels_eta_but_doubles_even_gap
    (chernNumber : ℤ) (holonomy : ℚ) (gapSquared : ℝ) :
    chiralReducedEtaModel chernNumber holonomy +
        chiralReducedEtaModel (-chernNumber) holonomy = 0 /\
      gapSquared + gapSquared = 2 * gapSquared := by
  constructor
  · exact pt_paired_chiral_eta_cancels chernNumber holonomy
  · ring

/--
The synthesis closes the algebraic mechanism. Its physical promotion requires
proving the separated Dirac spectrum, quarter holonomy from the Pin lift, the
regularized eta formula and the two-fold even-gap normalization of `q_LL`.
-/
structure Z4DiracAlphaPhysicalStatus where
  primitiveMonopoleDiracSpectrumProved : Prop
  quarterHolonomyDerivedFromGlobalPinLift : Prop
  spectralIsotropyDerivedFromEffectiveAction : Prop
  pairedEtaCancellationRegularized : Prop
  twoFoldEvenGapChargeLawDerived : Prop
  llFluxNormalizationMatched : Prop
  bimetricRadiusIdentificationRecovered : Prop
  absoluteGeometryScaleDerived : Prop
  absoluteAlphaDerivedNoFit : Prop


def z4DiracAlphaPhysicalClosed
    (s : Z4DiracAlphaPhysicalStatus) : Prop :=
  s.primitiveMonopoleDiracSpectrumProved /\
  s.quarterHolonomyDerivedFromGlobalPinLift /\
  s.spectralIsotropyDerivedFromEffectiveAction /\
  s.pairedEtaCancellationRegularized /\
  s.twoFoldEvenGapChargeLawDerived /\
  s.llFluxNormalizationMatched /\
  s.bimetricRadiusIdentificationRecovered /\
  s.absoluteGeometryScaleDerived /\
  s.absoluteAlphaDerivedNoFit

end P0EFTJanusZ4DiracAlphaLock
end JanusFormal
