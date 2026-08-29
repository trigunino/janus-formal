import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveSpinCMatterCanonicalFourierGraph4D

/-!
# Canonical finite-core compatibility and weighted SpinC decay

The canonical Fourier map is built from the inverse signed geometric unitary,
so its finite-core behavior is a theorem.  The weighted finite-core behavior
then follows pointwise from the multiplier relation.  Neither statement should
remain an analytic input.

The final SpinC datum is reduced to two fields:

* a linear `ℓ²`-valued weighted coefficient map satisfying the exact
  `2D + m²` pointwise multiplier relation;
* the equality between the independently integrated smooth action and the
  resulting coefficient pairing.

The first field is precisely weighted Fourier decay; the second is the global
same-action identification.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPPrimitiveSpinCMatterCanonicalWeightedDecay4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 2400000

noncomputable section

open scoped ENNReal lp LinearPMap
open P0EFTJanusComplexDiagonalMaximalOperator4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricL2Pairing4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricSignedModeUnitary4D
open P0EFTJanusProgramPPrimitiveSpinCGeometricSignedFredholm4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPPrimitiveSpinCMatterCanonicalFourierGraph4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D

variable (period : Real) (hPeriod : period ≠ 0)

local instance matterHilbertRealInnerProductSpace :
    InnerProductSpace Real ProgramPPrimitiveSpinCMatterHilbert :=
  programPPrimitiveSpinCMatterHilbertRealInnerProductSpace

private def canonicalFiniteCoefficientEmbedding
    (Mode : Type*) [DecidableEq Mode] :
    (Mode →₀ Complex) →ₗ[Complex] ComplexDiagonalHilbert Mode :=
  Finsupp.linearCombination Complex (complexDiagonalBasis Mode)

@[simp]
private theorem canonicalFiniteCoefficientEmbedding_single
    (Mode : Type*) [DecidableEq Mode]
    (mode : Mode) (coefficient : Complex) :
    canonicalFiniteCoefficientEmbedding Mode
        (Finsupp.single mode coefficient) =
      lp.single 2 mode coefficient := by
  rw [canonicalFiniteCoefficientEmbedding, Finsupp.linearCombination_single,
    complexDiagonalBasis_eq_single]
  ext other
  by_cases hOther : other = mode
  · subst other
    simp [lp.single_apply]
  · simp [lp.single_apply, hOther]

@[simp]
private theorem canonicalFiniteCoefficientEmbedding_apply
    (Mode : Type*) [DecidableEq Mode]
    (coefficients : Mode →₀ Complex) (mode : Mode) :
    canonicalFiniteCoefficientEmbedding Mode coefficients mode =
      coefficients mode := by
  induction coefficients using Finsupp.induction with
  | zero =>
      simp [canonicalFiniteCoefficientEmbedding]
  | single_add other coefficient rest _ _ inductionHypothesis =>
      rw [map_add]
      change
        canonicalFiniteCoefficientEmbedding Mode
              (Finsupp.single other coefficient) mode +
            canonicalFiniteCoefficientEmbedding Mode rest mode =
          Finsupp.single other coefficient mode + rest mode
      rw [canonicalFiniteCoefficientEmbedding_single, inductionHypothesis]
      by_cases hMode : other = mode
      · subst other
        simp [lp.single_apply]
      · simp [lp.single_apply, hMode]

/-- One-sector canonical Fourier coefficients recover every finite signed
coefficient family exactly. -/
theorem primitiveSpinCOneSectorCanonicalFourierCoefficients_finite
    (coefficients : PrimitiveSpinCGeometricSignedFiniteCoefficients) :
    primitiveSpinCOneSectorCanonicalFourierCoefficients period hPeriod
        (primitiveSpinCGeometricSignedDiracFiniteSynthesis period hPeriod
          coefficients) =
      canonicalFiniteCoefficientEmbedding PrimitiveSpinCGeometricSignedMode
        coefficients := by
  induction coefficients using Finsupp.induction with
  | zero =>
      simp [primitiveSpinCOneSectorCanonicalFourierCoefficients]
  | single_add mode coefficient rest _ _ inductionHypothesis =>
      rw [map_add, map_add, inductionHypothesis,
        primitiveSpinCGeometricSignedDiracFiniteSynthesis_single,
        map_smul]
      apply
        (primitiveSpinCGeometricSignedDiracModeUnitary period hPeriod).injective
      simp only [map_add, map_smul,
        primitiveSpinCOneSectorCanonicalFourierCoefficients,
        ContinuousLinearMap.comp_apply]
      have hInverse :=
        (primitiveSpinCGeometricSignedDiracModeUnitary period hPeriod).apply_symm_apply
          ((d9PrimitiveSpinCGeometricL2Embedding period hPeriod .positiveQuarter)
            (primitiveSpinCGeometricSignedDiracModeSmoothVector period hPeriod
              mode))
      change
        (primitiveSpinCGeometricSignedDiracModeUnitary period hPeriod)
            ((primitiveSpinCGeometricSignedDiracModeUnitary period hPeriod).symm
              |>.toLinearIsometry.toContinuousLinearMap
              ((d9PrimitiveSpinCGeometricL2Embedding period hPeriod
                .positiveQuarter)
                (primitiveSpinCGeometricSignedDiracModeSmoothVector period
                  hPeriod mode))) = _ at hInverse
      rw [hInverse, canonicalFiniteCoefficientEmbedding_single,
        primitiveSpinCGeometricSignedDiracModeUnitary_single]
      rfl

/-- The exact two-sector canonical coefficient map recovers arbitrary finite
physical matter coefficients. -/
theorem programPPrimitiveSpinCMatterCanonicalFourierCoefficients_finite
    (finite : ProgramPPrimitiveSpinCMatterFiniteCoefficients) :
    programPPrimitiveSpinCMatterCanonicalFourierCoefficients period hPeriod
        (programPPrimitiveSpinCMatterSmoothFiniteSynthesis period hPeriod
          finite) =
      programPPrimitiveSpinCMatterFiniteHilbertEmbedding finite := by
  ext mode
  rw [programPPrimitiveSpinCMatterCanonicalFourierCoefficients_apply,
    programPPrimitiveSpinCMatterSmoothFiniteSynthesis_apply,
    primitiveSpinCOneSectorCanonicalFourierCoefficients_finite,
    canonicalFiniteCoefficientEmbedding_apply,
    programPPrimitiveSpinCMatterFiniteHilbertEmbedding_apply]
  rfl

/-- Minimal weighted-decay input.  The pointwise relation means the weighted
vector is uniquely the multiplier image of the canonical Fourier vector. -/
structure ProgramPPrimitiveSpinCMatterCanonicalWeightedDecayData4D
    (massSquared : Real) where
  weightedCoefficients :
    ProgramPPrimitiveSpinCMatterSmoothField period hPeriod →ₗ[Complex]
      ProgramPPrimitiveSpinCMatterHilbert
  weighted_relation : ∀ field mode,
    weightedCoefficients field mode =
      ((programPPrimitiveSpinCMatterHessianWeight period hPeriod massSquared
        mode : Real) : Complex) *
        programPPrimitiveSpinCMatterCanonicalFourierCoefficients period hPeriod
          field mode
  smoothAction_eq_pairing : ∀ field,
    programPPrimitiveSpinCMatterSmoothAction period hPeriod massSquared field =
      (1 / 2 : Real) *
        inner Real
          (programPPrimitiveSpinCMatterCanonicalFourierCoefficients period
            hPeriod field)
          (weightedCoefficients field)

/-- The weighted finite coefficient vector is forced by the multiplier
relation; no additional compatibility hypothesis is needed. -/
theorem canonicalWeightedDecay_finite_weightedCoefficients
    (massSquared : Real)
    (decay : ProgramPPrimitiveSpinCMatterCanonicalWeightedDecayData4D period
      hPeriod massSquared)
    (finite : ProgramPPrimitiveSpinCMatterFiniteCoefficients) :
    decay.weightedCoefficients
        (programPPrimitiveSpinCMatterSmoothFiniteSynthesis period hPeriod
          finite) =
      programPPrimitiveSpinCMatterFiniteHilbertEmbedding
        (programPPrimitiveSpinCMatterFiniteHessian period hPeriod massSquared
          finite) := by
  ext mode
  rw [decay.weighted_relation,
    programPPrimitiveSpinCMatterCanonicalFourierCoefficients_finite,
    programPPrimitiveSpinCMatterFiniteHilbertEmbedding_apply,
    programPPrimitiveSpinCMatterFiniteHilbertEmbedding_apply,
    programPPrimitiveSpinCMatterFiniteHessian_apply]

/-- Convert the minimal weighted-decay datum to the previous canonical
interface. -/
def programPPrimitiveSpinCMatterCanonicalWeightedFourierData_of_decay
    (massSquared : Real)
    (decay : ProgramPPrimitiveSpinCMatterCanonicalWeightedDecayData4D period
      hPeriod massSquared) :
    ProgramPPrimitiveSpinCMatterCanonicalWeightedFourierData4D period hPeriod
      massSquared where
  weightedCoefficients := decay.weightedCoefficients
  weighted_relation := decay.weighted_relation
  canonical_finite_coefficients :=
    programPPrimitiveSpinCMatterCanonicalFourierCoefficients_finite period
      hPeriod
  finite_weightedCoefficients :=
    canonicalWeightedDecay_finite_weightedCoefficients period hPeriod
      massSquared decay
  smoothAction_eq_pairing := decay.smoothAction_eq_pairing

/-- Final smooth-to-maximal-graph realization from weighted Fourier decay and
the same-action coefficient pairing. -/
def programPPrimitiveSpinCMatterSmoothGraphRealization_of_weightedDecay
    (massSquared : Real)
    (decay : ProgramPPrimitiveSpinCMatterCanonicalWeightedDecayData4D period
      hPeriod massSquared) :
    ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D period hPeriod
      massSquared :=
  programPPrimitiveSpinCMatterSmoothGraphRealization_of_canonicalFourier period
    hPeriod massSquared
      (programPPrimitiveSpinCMatterCanonicalWeightedFourierData_of_decay period
        hPeriod massSquared decay)

end
end P0EFTJanusProgramPPrimitiveSpinCMatterCanonicalWeightedDecay4D
end JanusFormal
