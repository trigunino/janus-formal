import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProductThroatHeatOperatorNuclearExpansion4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProductThroatNuclearHeatTraceSmooth4D

/-!
# Smooth product-throat heat-operator family

The nuclear rank-one expansion is extended to real time.  Arbitrary spectral
powers remain summable uniformly on every positive half-line, so all
operator-valued derivatives may be taken termwise in operator norm.  At every
positive time the order-zero nuclear sum is the previously constructed heat
operator.
-/

namespace JanusFormal
namespace P0EFTJanusProductThroatHeatOperatorSmooth4D

set_option autoImplicit false
set_option maxHeartbeats 700000

noncomputable section

open Set
open scoped ContDiff ENNReal lp
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusCircleDiracHeatFunctionalBridge
open P0EFTJanusCircleHeatNuclearTraceContinuity
open P0EFTJanusCircleHeatNuclearTraceSmooth
open P0EFTJanusProductThroatNuclearHeatTrace4D
open P0EFTJanusProductThroatNuclearHeatTraceSmooth4D
open P0EFTJanusProductThroatHeatOperator4D
open P0EFTJanusProductThroatHeatOperatorNuclearExpansion4D

def productThroatHeatModeSquaredEigenvalue
    (data : ProductThroatSpectralData) (fold : Fold) (twist : CircleTwist)
    (mode : ProductThroatHeatMode data) : Real :=
  productThroatSquaredEigenvalue data fold twist (mode.1.1, mode.2)

theorem productThroatHeatModeSquaredEigenvalue_nonnegative
    (data : ProductThroatSpectralData) (fold : Fold) (twist : CircleTwist)
    (mode : ProductThroatHeatMode data) :
    0 ≤ productThroatHeatModeSquaredEigenvalue data fold twist mode :=
  productThroatSquaredEigenvalue_nonnegative data fold twist (mode.1.1, mode.2)

def productThroatHeatModeWeightReal
    (data : ProductThroatSpectralData) (time : Real)
    (fold : Fold) (twist : CircleTwist)
    (mode : ProductThroatHeatMode data) : Real :=
  Real.exp (-time * productThroatHeatModeSquaredEigenvalue data fold twist mode)

theorem productThroatHeatModeWeightReal_of_heatTime
    (data : ProductThroatSpectralData) (time : HeatTime)
    (fold : Fold) (twist : CircleTwist)
    (mode : ProductThroatHeatMode data) :
    productThroatHeatModeWeightReal data time.1 fold twist mode =
      productThroatHeatWeight data time fold twist mode := by
  unfold productThroatHeatModeWeightReal productThroatHeatModeSquaredEigenvalue
    productThroatSquaredEigenvalue productThroatHeatWeight sphereModeHeatWeight
    circleOperatorHeatWeight
  rw [← Real.exp_add]
  congr 1
  ring

theorem productThroatHeatModeWeightReal_summable
    (data : ProductThroatSpectralData) (time : HeatTime)
    (fold : Fold) (twist : CircleTwist) :
    Summable (fun mode : ProductThroatHeatMode data =>
      productThroatHeatModeWeightReal data time.1 fold twist mode) :=
  (productThroatHeatWeight_summable data time fold twist).congr
    (fun mode => (productThroatHeatModeWeightReal_of_heatTime
      data time fold twist mode).symm)

def productThroatHeatProjection
    (data : ProductThroatSpectralData) (mode : ProductThroatHeatMode data) :
    ProductThroatHeatHilbert data →L[Complex] ProductThroatHeatHilbert data :=
  (lp.evalCLM Complex
      (fun _ : ProductThroatHeatMode data => Complex) 2 mode).smulRight
    (productThroatHeatBasis data mode)

theorem productThroatHeatProjection_opNorm_le_one
    (data : ProductThroatSpectralData) (mode : ProductThroatHeatMode data) :
    ‖productThroatHeatProjection data mode‖ ≤ 1 := by
  rw [productThroatHeatProjection, ContinuousLinearMap.norm_smulRight_apply,
    productThroatHeatBasis_norm, mul_one]
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro state
  change ‖state mode‖ ≤ 1 * ‖state‖
  simpa using lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0)
    state mode

def productThroatHeatRankOneRealIteratedDerivative
    (order : Nat) (data : ProductThroatSpectralData) (time : Real)
    (fold : Fold) (twist : CircleTwist)
    (mode : ProductThroatHeatMode data) :
    ProductThroatHeatHilbert data →L[Complex] ProductThroatHeatHilbert data :=
  ((-productThroatHeatModeSquaredEigenvalue data fold twist mode) ^ order *
      productThroatHeatModeWeightReal data time fold twist mode) •
    productThroatHeatProjection data mode

theorem productThroatHeatRankOneRealIteratedDerivative_hasDerivAt
    (order : Nat) (data : ProductThroatSpectralData) (time : Real)
    (fold : Fold) (twist : CircleTwist)
    (mode : ProductThroatHeatMode data) :
    HasDerivAt
      (fun s : Real => productThroatHeatRankOneRealIteratedDerivative
        order data s fold twist mode)
      (productThroatHeatRankOneRealIteratedDerivative
        (order + 1) data time fold twist mode) time := by
  let spectrum := productThroatHeatModeSquaredEigenvalue data fold twist mode
  have hInner : HasDerivAt (fun s : Real => -s * spectrum) (-spectrum) time := by
    simpa [mul_comm] using (hasDerivAt_id time).const_mul (-spectrum)
  have hWeight : HasDerivAt
      (fun s : Real => productThroatHeatModeWeightReal data s fold twist mode)
      (-spectrum * productThroatHeatModeWeightReal data time fold twist mode)
      time := by
    have hExp := (Real.hasDerivAt_exp (-time * spectrum)).comp time hInner
    have hFunctions :
        (fun s : Real => Real.exp (-s * spectrum)) =ᶠ[nhds time]
          (Real.exp ∘ fun s : Real => -s * spectrum) := by
      filter_upwards [] with parameter
      rfl
    simpa [productThroatHeatModeWeightReal, spectrum, mul_comm] using
      hExp.congr_of_eventuallyEq hFunctions
  have hCoefficient := hWeight.const_mul ((-spectrum) ^ order)
  have hOperator := hCoefficient.smul_const (productThroatHeatProjection data mode)
  simpa [productThroatHeatRankOneRealIteratedDerivative,
    spectrum, pow_succ, mul_assoc] using hOperator

theorem productThroatHeatRankOneRealIteratedDerivative_continuous
    (order : Nat) (data : ProductThroatSpectralData)
    (fold : Fold) (twist : CircleTwist)
    (mode : ProductThroatHeatMode data) :
    Continuous (fun time : Real => productThroatHeatRankOneRealIteratedDerivative
      order data time fold twist mode) := by
  rw [continuous_iff_continuousAt]
  intro time
  exact (productThroatHeatRankOneRealIteratedDerivative_hasDerivAt
    order data time fold twist mode).continuousAt

theorem productThroatHeatRankOneRealIteratedDerivative_norm_le
    (order : Nat) (data : ProductThroatSpectralData) (time : Real)
    (fold : Fold) (twist : CircleTwist)
    (mode : ProductThroatHeatMode data) :
    ‖productThroatHeatRankOneRealIteratedDerivative
        order data time fold twist mode‖ ≤
      productThroatHeatModeSquaredEigenvalue data fold twist mode ^ order *
        productThroatHeatModeWeightReal data time fold twist mode := by
  have hSpectrum := productThroatHeatModeSquaredEigenvalue_nonnegative
    data fold twist mode
  have hWeight : 0 ≤ productThroatHeatModeWeightReal data time fold twist mode := by
    unfold productThroatHeatModeWeightReal
    exact (Real.exp_pos _).le
  rw [productThroatHeatRankOneRealIteratedDerivative, norm_smul,
    Real.norm_eq_abs, abs_mul, abs_pow, abs_neg, abs_of_nonneg hSpectrum,
    abs_of_nonneg hWeight]
  exact mul_le_of_le_one_right
    (mul_nonneg (pow_nonneg hSpectrum order) hWeight)
    (productThroatHeatProjection_opNorm_le_one data mode)

theorem productThroatHeatRankOneRealIteratedDerivative_uniform_summable
    (order : Nat) (data : ProductThroatSpectralData) (epsilon : HeatTime)
    (fold : Fold) (twist : CircleTwist) :
    Summable (fun mode : ProductThroatHeatMode data =>
      spectralAbsorptionConstant order epsilon.1 *
        productThroatHeatModeWeightReal data
          (spectralAbsorptionTime order epsilon.1) fold twist mode) := by
  exact Summable.mul_left _ (productThroatHeatModeWeightReal_summable data
    ⟨spectralAbsorptionTime order epsilon.1,
      spectralAbsorptionTime_pos order epsilon.2⟩ fold twist)

theorem productThroatHeatRankOneRealIteratedDerivative_uniform_norm_le
    (order : Nat) (data : ProductThroatSpectralData) (epsilon : HeatTime)
    {time : Real} (hTime : epsilon.1 ≤ time)
    (fold : Fold) (twist : CircleTwist)
    (mode : ProductThroatHeatMode data) :
    ‖productThroatHeatRankOneRealIteratedDerivative
        order data time fold twist mode‖ ≤
      spectralAbsorptionConstant order epsilon.1 *
        productThroatHeatModeWeightReal data
          (spectralAbsorptionTime order epsilon.1) fold twist mode := by
  refine (productThroatHeatRankOneRealIteratedDerivative_norm_le
    order data time fold twist mode).trans ?_
  let spectrum := productThroatHeatModeSquaredEigenvalue data fold twist mode
  have hSpectrum : 0 ≤ spectrum :=
    productThroatHeatModeSquaredEigenvalue_nonnegative data fold twist mode
  have hTimeWeight :
      productThroatHeatModeWeightReal data time fold twist mode ≤
        productThroatHeatModeWeightReal data epsilon.1 fold twist mode := by
    unfold productThroatHeatModeWeightReal
    apply Real.exp_le_exp.mpr
    nlinarith
  refine (mul_le_mul_of_nonneg_left hTimeWeight
    (pow_nonneg hSpectrum order)).trans ?_
  unfold productThroatHeatModeWeightReal
  exact spectralFactor_pow_mul_exp_bound order epsilon.2 hSpectrum

def productThroatHeatOperatorRealIteratedDerivative
    (order : Nat) (data : ProductThroatSpectralData) (time : Real)
    (fold : Fold) (twist : CircleTwist) :
    ProductThroatHeatHilbert data →L[Complex] ProductThroatHeatHilbert data :=
  ∑' mode : ProductThroatHeatMode data,
    productThroatHeatRankOneRealIteratedDerivative
      order data time fold twist mode

/-- Reindexing which groups the explicit degeneracy label over its
`(sphere level, circle mode)` trace index. -/
def productThroatHeatModeTraceEquiv (data : ProductThroatSpectralData) :
    ProductThroatHeatMode data ≃
      Σ index : Nat × Int, Fin (sphereMultiplicity data index.1) where
  toFun mode := ⟨(mode.1.1, mode.2), mode.1.2⟩
  invFun indexed := (⟨indexed.1.1, indexed.2⟩, indexed.1.2)
  left_inv mode := by
    rcases mode with ⟨⟨level, degeneracy⟩, circleMode⟩
    rfl
  right_inv indexed := by
    rcases indexed with ⟨⟨level, circleMode⟩, degeneracy⟩
    rfl

/-- Scalar diagonal coefficient of the arbitrary-order operator derivative. -/
def productThroatHeatOperatorRealDiagonalCoefficient
    (order : Nat) (data : ProductThroatSpectralData) (time : Real)
    (fold : Fold) (twist : CircleTwist)
    (mode : ProductThroatHeatMode data) : Real :=
  (-productThroatHeatModeSquaredEigenvalue data fold twist mode) ^ order *
    productThroatHeatModeWeightReal data time fold twist mode

theorem productThroatHeatOperatorRealDiagonalCoefficient_summable
    (order : Nat) (data : ProductThroatSpectralData) (time : HeatTime)
    (fold : Fold) (twist : CircleTwist) :
    Summable (fun mode : ProductThroatHeatMode data =>
      productThroatHeatOperatorRealDiagonalCoefficient
        order data time.1 fold twist mode) := by
  apply Summable.of_norm_bounded
    (productThroatHeatRankOneRealIteratedDerivative_uniform_summable
      order data time fold twist)
  intro mode
  unfold productThroatHeatOperatorRealDiagonalCoefficient
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_neg,
    abs_of_nonneg (productThroatHeatModeSquaredEigenvalue_nonnegative
      data fold twist mode)]
  rw [abs_of_nonneg (by
    unfold productThroatHeatModeWeightReal
    exact (Real.exp_pos _).le)]
  unfold productThroatHeatModeWeightReal
  exact spectralFactor_pow_mul_exp_bound order time.2
    (productThroatHeatModeSquaredEigenvalue_nonnegative data fold twist mode)

/-- Summed diagonal of the arbitrary-order operator derivative. -/
def productThroatHeatOperatorRealDiagonalTrace
    (order : Nat) (data : ProductThroatSpectralData) (time : Real)
    (fold : Fold) (twist : CircleTwist) : Real :=
  ∑' mode : ProductThroatHeatMode data,
    productThroatHeatOperatorRealDiagonalCoefficient
      order data time fold twist mode

/-- The operator diagonal trace, including every explicit monopole
degeneracy label, is exactly the previously constructed nuclear trace
derivative at every order. -/
theorem productThroatHeatOperatorRealDiagonalTrace_eq_nuclearTraceDerivative
    (order : Nat) (data : ProductThroatSpectralData) (time : HeatTime)
    (fold : Fold) (twist : CircleTwist) :
    productThroatHeatOperatorRealDiagonalTrace
        order data time.1 fold twist =
      productThroatNuclearHeatTraceRealIteratedDerivative
        order data time.1 fold twist := by
  unfold productThroatHeatOperatorRealDiagonalTrace
    productThroatNuclearHeatTraceRealIteratedDerivative
  let reindex := productThroatHeatModeTraceEquiv data
  have hReindex := reindex.tsum_eq (fun indexed =>
    productThroatHeatOperatorRealDiagonalCoefficient
      order data time.1 fold twist (reindex.symm indexed))
  simp only [Equiv.symm_apply_apply] at hReindex
  rw [hReindex]
  have hSummable : Summable (fun indexed =>
      productThroatHeatOperatorRealDiagonalCoefficient
        order data time.1 fold twist (reindex.symm indexed)) :=
    (productThroatHeatOperatorRealDiagonalCoefficient_summable
      order data time fold twist).comp_injective reindex.symm.injective
  rw [hSummable.tsum_sigma]
  apply tsum_congr
  intro index
  change
    (∑' _ : Fin (sphereMultiplicity data index.1),
      (-productThroatSquaredEigenvalue data fold twist index) ^ order *
        Real.exp (-time.1 *
          productThroatSquaredEigenvalue data fold twist index)) =
      (-productThroatSquaredEigenvalue data fold twist index) ^ order *
        ((sphereMultiplicity data index.1 : Real) *
          Real.exp (-time.1 *
            productThroatSquaredEigenvalue data fold twist index))
  rw [tsum_fintype]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [Finset.card_univ, Fintype.card_fin]
  ring

theorem productThroatHeatOperatorRealDiagonalTrace_pt_eq_positive
    (order : Nat) (data : ProductThroatSpectralData)
    (time : HeatTime) (twist : CircleTwist) :
    productThroatHeatOperatorRealDiagonalTrace
        order data time.1 .pt twist =
      productThroatHeatOperatorRealDiagonalTrace
        order data time.1 .positive twist := by
  rw [productThroatHeatOperatorRealDiagonalTrace_eq_nuclearTraceDerivative,
    productThroatHeatOperatorRealDiagonalTrace_eq_nuclearTraceDerivative,
    productThroatNuclearHeatTraceRealIteratedDerivative_pt_eq_positive]

theorem productThroatHeatOperatorRealIteratedDerivative_continuousOn_Ioi
    (order : Nat) (data : ProductThroatSpectralData)
    (fold : Fold) (twist : CircleTwist) :
    ContinuousOn (fun time : Real => productThroatHeatOperatorRealIteratedDerivative
      order data time fold twist) (Ioi 0) := by
  intro time hTime
  let epsilon : HeatTime := ⟨time / 2, half_pos hTime⟩
  apply ContinuousOn.continuousAt
    (s := Ici epsilon.1)
    (continuousOn_tsum
      (fun mode =>
        (productThroatHeatRankOneRealIteratedDerivative_continuous
          order data fold twist mode).continuousOn)
      (productThroatHeatRankOneRealIteratedDerivative_uniform_summable
        order data epsilon fold twist)
      (fun mode parameter hParameter =>
        productThroatHeatRankOneRealIteratedDerivative_uniform_norm_le
          order data epsilon hParameter fold twist mode))
    (Ici_mem_nhds (half_lt_self hTime)) |>.continuousWithinAt

theorem productThroatHeatOperatorRealIteratedDerivative_hasDerivAt
    (order : Nat) (data : ProductThroatSpectralData) (time : HeatTime)
    (fold : Fold) (twist : CircleTwist) :
    HasDerivAt
      (fun s : Real => productThroatHeatOperatorRealIteratedDerivative
        order data s fold twist)
      (productThroatHeatOperatorRealIteratedDerivative
        (order + 1) data time.1 fold twist) time.1 := by
  unfold productThroatHeatOperatorRealIteratedDerivative
  let epsilon : HeatTime := ⟨time.1 / 2, half_pos time.2⟩
  apply hasDerivAt_tsum_of_isPreconnected
    (g := fun mode s => productThroatHeatRankOneRealIteratedDerivative
      order data s fold twist mode)
    (g' := fun mode s => productThroatHeatRankOneRealIteratedDerivative
      (order + 1) data s fold twist mode)
    (u := fun mode : ProductThroatHeatMode data =>
      spectralAbsorptionConstant (order + 1) epsilon.1 *
        productThroatHeatModeWeightReal data
          (spectralAbsorptionTime (order + 1) epsilon.1) fold twist mode)
    (t := Ioi epsilon.1) (y₀ := time.1) (y := time.1)
  · exact productThroatHeatRankOneRealIteratedDerivative_uniform_summable
      (order + 1) data epsilon fold twist
  · exact isOpen_Ioi
  · exact isPreconnected_Ioi
  · intro mode parameter _
    exact productThroatHeatRankOneRealIteratedDerivative_hasDerivAt
      order data parameter fold twist mode
  · intro mode parameter hParameter
    exact productThroatHeatRankOneRealIteratedDerivative_uniform_norm_le
      (order + 1) data epsilon hParameter.le fold twist mode
  · exact mem_Ioi.mpr (half_lt_self time.2)
  · apply Summable.of_norm_bounded
      (productThroatHeatRankOneRealIteratedDerivative_uniform_summable
        order data time fold twist)
    intro mode
    exact productThroatHeatRankOneRealIteratedDerivative_uniform_norm_le
      order data time le_rfl fold twist mode
  · exact mem_Ioi.mpr (half_lt_self time.2)

theorem productThroatHeatOperatorRealIteratedDerivative_contDiffOn_nat
    (derivativeOrder smoothnessOrder : Nat) (data : ProductThroatSpectralData)
    (fold : Fold) (twist : CircleTwist) :
    ContDiffOn ℝ smoothnessOrder
      (fun time : Real => productThroatHeatOperatorRealIteratedDerivative
        derivativeOrder data time fold twist) (Ioi 0) := by
  induction smoothnessOrder generalizing derivativeOrder with
  | zero =>
      exact contDiffOn_zero.mpr
        (productThroatHeatOperatorRealIteratedDerivative_continuousOn_Ioi
          derivativeOrder data fold twist)
  | succ smoothnessOrder ih =>
      change ContDiffOn ℝ (smoothnessOrder + 1)
        (fun time : Real => productThroatHeatOperatorRealIteratedDerivative
          derivativeOrder data time fold twist) (Ioi 0)
      rw [contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
      refine ⟨?_, ?_, ?_⟩
      · intro time hTime
        exact DifferentiableAt.differentiableWithinAt
          (productThroatHeatOperatorRealIteratedDerivative_hasDerivAt
            derivativeOrder data ⟨time, hTime⟩ fold twist).differentiableAt
      · intro hImpossible
        norm_num at hImpossible
      · exact (ih (derivativeOrder + 1)).congr fun time hTime =>
          (productThroatHeatOperatorRealIteratedDerivative_hasDerivAt
            derivativeOrder data ⟨time, hTime⟩ fold twist).deriv

theorem productThroatHeatOperatorReal_contDiffOn_infty
    (data : ProductThroatSpectralData) (fold : Fold) (twist : CircleTwist) :
    ContDiffOn ℝ ∞
      (fun time : Real => productThroatHeatOperatorRealIteratedDerivative
        0 data time fold twist) (Ioi 0) := by
  rw [contDiffOn_infty]
  intro order
  exact productThroatHeatOperatorRealIteratedDerivative_contDiffOn_nat
    0 order data fold twist

theorem productThroatHeatRankOneReal_zero_of_heatTime
    (data : ProductThroatSpectralData) (time : HeatTime)
    (fold : Fold) (twist : CircleTwist)
    (mode : ProductThroatHeatMode data) :
    productThroatHeatRankOneRealIteratedDerivative
        0 data time.1 fold twist mode =
      productThroatHeatRankOne data time fold twist mode := by
  have hRealSmul (state : ProductThroatHeatHilbert data) :
      (productThroatHeatWeight data time fold twist mode : Real) • state =
        (productThroatHeatWeight data time fold twist mode : Complex) • state := by
    ext other
    rfl
  apply ContinuousLinearMap.ext
  intro state
  simp only [productThroatHeatRankOneRealIteratedDerivative, pow_zero,
    one_mul, productThroatHeatProjection,
    productThroatHeatModeWeightReal_of_heatTime,
    smul_apply, ContinuousLinearMap.smulRight_apply,
    productThroatHeatRankOne_apply]
  rw [hRealSmul]
  have hEval :
      (lp.evalCLM Complex
        (fun _ : ProductThroatHeatMode data => Complex) 2 mode) state =
        state mode := rfl
  rw [hEval]
  exact smul_comm
    (productThroatHeatWeight data time fold twist mode : Complex)
    (state mode) (productThroatHeatBasis data mode)

theorem productThroatHeatOperatorReal_zero_of_heatTime
    (data : ProductThroatSpectralData) (time : HeatTime)
    (fold : Fold) (twist : CircleTwist) :
    productThroatHeatOperatorRealIteratedDerivative
        0 data time.1 fold twist =
      productThroatHeatOperator data time fold twist := by
  rw [productThroatHeatOperatorRealIteratedDerivative]
  calc
    (∑' mode : ProductThroatHeatMode data,
      productThroatHeatRankOneRealIteratedDerivative
        0 data time.1 fold twist mode) =
        ∑' mode : ProductThroatHeatMode data,
          productThroatHeatRankOne data time fold twist mode := by
            apply tsum_congr
            exact productThroatHeatRankOneReal_zero_of_heatTime
              data time fold twist
    _ = productThroatHeatNuclearSum data time fold twist := rfl
    _ = productThroatHeatOperator data time fold twist :=
      productThroatHeatNuclearSum_eq_operator data time fold twist

end
end P0EFTJanusProductThroatHeatOperatorSmooth4D
end JanusFormal
