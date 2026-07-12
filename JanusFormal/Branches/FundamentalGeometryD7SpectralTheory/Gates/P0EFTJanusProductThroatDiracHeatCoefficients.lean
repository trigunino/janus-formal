import Mathlib
import JanusFormal.Branches.FundamentalGeometryD7SpectralTheory.Gates.P0EFTJanusUniversalClosedHeatCoefficients
import JanusFormal.Branches.FundamentalGeometryD.Gates.P0EFTJanusProductThroatLocalInvariants
import JanusFormal.Branches.FundamentalGeometryD.Gates.P0EFTJanusDiracSeeleyDeWittCandidate

namespace JanusFormal
namespace P0EFTJanusProductThroatDiracHeatCoefficients

set_option autoImplicit false

open P0EFTJanusUniversalClosedHeatCoefficients
open P0EFTJanusProductThroatLocalInvariants
open P0EFTJanusDiracSeeleyDeWittCandidate

/-- Universal rank-two Dirac trace data specialized to `S2_L x S1_(L*T)`. -/
noncomputable def productThroatDiracTraceData
    (s : ProductThroatInvariantData) : RankTwoDiracTraceData :=
  { volume := throatVolume s
    integratedScalarCurvature := integratedScalarCurvature s
    integratedScalarCurvatureSquared := integratedScalarCurvatureSquared s
    integratedRicciSquared := integratedRicciSquared s
    integratedRiemannSquared := integratedRiemannSquared s
    integratedGaugeFieldSquared := integratedMonopoleFieldSquared s }

/-- The universal `a0` reduction exactly matches the existing Program-D candidate. -/
theorem universal_a0_matches_candidate
    (s : ProductThroatInvariantData) :
    reducedA0
        (rankTwoDiracAsLaplaceData (productThroatDiracTraceData s)) =
      reducedDiracA0 s := by
  rw [rank_two_dirac_reduced_a0]
  rfl

/-- The universal `a2` reduction exactly matches the existing Program-D candidate. -/
theorem universal_a2_matches_candidate
    (s : ProductThroatInvariantData) :
    reducedA2
        (rankTwoDiracAsLaplaceData (productThroatDiracTraceData s)) =
      reducedDiracA2 s := by
  rw [rank_two_dirac_reduced_a2]
  rfl

/-- The universal `a4` reduction exactly matches the existing Program-D candidate. -/
theorem universal_a4_matches_candidate
    (s : ProductThroatInvariantData) :
    reducedA4
        (rankTwoDiracAsLaplaceData (productThroatDiracTraceData s)) =
      reducedDiracA4 s := by
  rw [rank_two_dirac_reduced_a4]
  rfl

/-- Explicit product-throat `a0 = 8*pi*L^3*T`. -/
theorem universal_product_throat_a0_formula
    (s : ProductThroatInvariantData) :
    reducedA0
        (rankTwoDiracAsLaplaceData (productThroatDiracTraceData s)) =
      8 * s.piConstant * s.geometricLength ^ 3 * s.circleModulus := by
  rw [universal_a0_matches_candidate, reduced_dirac_a0_formula]

/-- Explicit product-throat `a2 = -(4*pi/3)*L*T`. -/
theorem universal_product_throat_a2_formula
    (s : ProductThroatInvariantData) :
    reducedA2
        (rankTwoDiracAsLaplaceData (productThroatDiracTraceData s)) =
      -(4 * s.piConstant * s.geometricLength * s.circleModulus) / 3 := by
  rw [universal_a2_matches_candidate, reduced_dirac_a2_formula]

/-- Explicit product-throat Dirac/monopole `a4`. -/
theorem universal_product_throat_a4_formula
    (s : ProductThroatInvariantData) :
    reducedA4
        (rankTwoDiracAsLaplaceData (productThroatDiracTraceData s)) =
      2 * s.piConstant *
        (5 * (s.monopoleNumber : ℝ) ^ 2 - 1) *
        s.circleModulus /
        (15 * s.geometricLength) := by
  rw [universal_a4_matches_candidate, reduced_dirac_a4_formula]

/-- Primitive monopole specialization of the universal `a4` coefficient. -/
theorem primitive_universal_product_throat_a4
    (s : ProductThroatInvariantData)
    (hPrimitiveSquare : (s.monopoleNumber : ℝ) ^ 2 = 1) :
    reducedA4
        (rankTwoDiracAsLaplaceData (productThroatDiracTraceData s)) =
      8 * s.piConstant * s.circleModulus /
        (15 * s.geometricLength) := by
  rw [universal_a4_matches_candidate,
    primitive_reduced_dirac_a4_formula s hPrimitiveSquare]

/-- The primitive product-throat `a4` coefficient is strictly positive. -/
theorem primitive_universal_product_throat_a4_positive
    (s : ProductThroatInvariantData)
    (hPrimitiveSquare : (s.monopoleNumber : ℝ) ^ 2 = 1) :
    0 < reducedA4
      (rankTwoDiracAsLaplaceData (productThroatDiracTraceData s)) := by
  rw [primitive_universal_product_throat_a4 s hPrimitiveSquare]
  exact div_pos
    (mul_pos (mul_pos (by norm_num) s.piConstantPositive)
      s.circleModulusPositive)
    (mul_pos (by norm_num) s.geometricLengthPositive)

/-- All universal local coefficients remain linear in the dimensionless circle modulus. -/
theorem universal_product_coefficients_linear_in_circle
    (s : ProductThroatInvariantData) :
    reducedA0
        (rankTwoDiracAsLaplaceData (productThroatDiracTraceData s)) =
      s.circleModulus *
        (8 * s.piConstant * s.geometricLength ^ 3) /\
    reducedA2
        (rankTwoDiracAsLaplaceData (productThroatDiracTraceData s)) =
      s.circleModulus *
        (-(4 * s.piConstant * s.geometricLength) / 3) /\
    reducedA4
        (rankTwoDiracAsLaplaceData (productThroatDiracTraceData s)) =
      s.circleModulus *
        (2 * s.piConstant *
          (5 * (s.monopoleNumber : ℝ) ^ 2 - 1) /
          (15 * s.geometricLength)) := by
  constructor
  · rw [universal_product_throat_a0_formula]
    ring
  · constructor
    · rw [universal_product_throat_a2_formula]
      ring
    · rw [universal_product_throat_a4_formula]
      ring

/--
The trace-level reduction now explains the candidate coefficients, but the
actual geometric operator still has to realize the declared Lichnerowicz and
Abelian-curvature trace identities on the global Pin/SpinC bundle.
-/
structure ProductThroatDiracOperatorStatus where
  globalSpinCOrPinBundleConstructed : Prop
  monopoleConnectionGlobalized : Prop
  diracSquareWrittenAsLaplaceType : Prop
  traceEIdentityProved : Prop
  traceESquaredIdentityProved : Prop
  traceConnectionCurvatureSquaredIdentityProved : Prop
  universalCoefficientsApplied : Prop
  spectrumAndHeatTraceMatched : Prop


def productThroatDiracOperatorClosed
    (s : ProductThroatDiracOperatorStatus) : Prop :=
  s.globalSpinCOrPinBundleConstructed /\
  s.monopoleConnectionGlobalized /\
  s.diracSquareWrittenAsLaplaceType /\
  s.traceEIdentityProved /\
  s.traceESquaredIdentityProved /\
  s.traceConnectionCurvatureSquaredIdentityProved /\
  s.universalCoefficientsApplied /\
  s.spectrumAndHeatTraceMatched

end P0EFTJanusProductThroatDiracHeatCoefficients
end JanusFormal
