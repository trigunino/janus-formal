import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProductThroatNuclearHeatTrace4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCircleHeatNuclearTraceCompleteMonotonicity

/-!
# Smooth product-throat nuclear heat trace

The total product eigenvalue is the sum of the sphere and circle squared
eigenvalues.  The arbitrary-order Gaussian absorption theorem therefore gives
termwise derivatives, complete monotonicity, PT covariance, and `C∞`
positive-time regularity for the genuine `ℕ × ℤ` product trace.
-/

namespace JanusFormal
namespace P0EFTJanusProductThroatNuclearHeatTraceSmooth4D

set_option autoImplicit false
set_option maxHeartbeats 600000

noncomputable section

open Set Filter
open scoped ContDiff
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusMonopoleSphereHeatTrace
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusCircleDiracHeatFunctionalBridge
open P0EFTJanusCircleHeatNuclearTraceClass
open P0EFTJanusCircleHeatNuclearTraceContinuity
open P0EFTJanusCircleHeatNuclearTraceSmooth
open P0EFTJanusCircleHeatNuclearTraceCompleteMonotonicity
open P0EFTJanusProductThroatNuclearHeatTrace4D

def productThroatSquaredEigenvalue
    (data : ProductThroatSpectralData) (fold : Fold) (twist : CircleTwist)
    (index : Nat × Int) : Real :=
  sphereEigenvalueSquared data index.1 +
    circleOperatorSquaredEigenvalue fold twist index.2

theorem productThroatSquaredEigenvalue_nonnegative
    (data : ProductThroatSpectralData) (fold : Fold) (twist : CircleTwist)
    (index : Nat × Int) :
    0 ≤ productThroatSquaredEigenvalue data fold twist index := by
  unfold productThroatSquaredEigenvalue sphereEigenvalueSquared
  have hCircle := circleOperatorSquaredEigenvalue_nonnegative fold twist index.2
  positivity

def productThroatNuclearHeatTermReal
    (data : ProductThroatSpectralData) (time : Real)
    (fold : Fold) (twist : CircleTwist) (index : Nat × Int) : Real :=
  (sphereMultiplicity data index.1 : Real) *
    Real.exp (-time * productThroatSquaredEigenvalue data fold twist index)

theorem productThroatNuclearHeatTermReal_nonnegative
    (data : ProductThroatSpectralData) (time : Real)
    (fold : Fold) (twist : CircleTwist) (index : Nat × Int) :
    0 ≤ productThroatNuclearHeatTermReal data time fold twist index := by
  unfold productThroatNuclearHeatTermReal
  positivity

theorem productThroatNuclearHeatTermReal_of_heatTime
    (data : ProductThroatSpectralData) (time : HeatTime)
    (fold : Fold) (twist : CircleTwist) (index : Nat × Int) :
    productThroatNuclearHeatTermReal data time.1 fold twist index =
      productThroatNuclearHeatTerm data time fold twist index := by
  unfold productThroatNuclearHeatTermReal productThroatNuclearHeatTerm
    productThroatSquaredEigenvalue sphereHeatTerm circleOperatorHeatWeight
  rw [mul_assoc]
  rw [← Real.exp_add]
  congr 2
  ring

theorem productThroatNuclearHeatTermReal_summable
    (data : ProductThroatSpectralData) (time : HeatTime)
    (fold : Fold) (twist : CircleTwist) :
    Summable (fun index : Nat × Int =>
      productThroatNuclearHeatTermReal data time.1 fold twist index) :=
  (productThroatNuclearHeatTerm_summable data time fold twist).congr
    (fun index => (productThroatNuclearHeatTermReal_of_heatTime
      data time fold twist index).symm)

def productThroatNuclearHeatTraceReal
    (data : ProductThroatSpectralData) (time : Real)
    (fold : Fold) (twist : CircleTwist) : Real :=
  ∑' index : Nat × Int,
    productThroatNuclearHeatTermReal data time fold twist index

theorem productThroatNuclearHeatTraceReal_of_heatTime
    (data : ProductThroatSpectralData) (time : HeatTime)
    (fold : Fold) (twist : CircleTwist) :
    productThroatNuclearHeatTraceReal data time.1 fold twist =
      productThroatNuclearHeatTrace data time fold twist := by
  unfold productThroatNuclearHeatTraceReal productThroatNuclearHeatTrace
  apply tsum_congr
  exact productThroatNuclearHeatTermReal_of_heatTime data time fold twist

def productThroatNuclearHeatTermRealIteratedDerivative
    (order : Nat) (data : ProductThroatSpectralData) (time : Real)
    (fold : Fold) (twist : CircleTwist) (index : Nat × Int) : Real :=
  (-productThroatSquaredEigenvalue data fold twist index) ^ order *
    productThroatNuclearHeatTermReal data time fold twist index

def productThroatNuclearHeatTraceRealIteratedDerivative
    (order : Nat) (data : ProductThroatSpectralData) (time : Real)
    (fold : Fold) (twist : CircleTwist) : Real :=
  ∑' index : Nat × Int,
    productThroatNuclearHeatTermRealIteratedDerivative
      order data time fold twist index

@[simp] theorem productThroatNuclearHeatTraceRealIteratedDerivative_zero
    (data : ProductThroatSpectralData) (time : Real)
    (fold : Fold) (twist : CircleTwist) :
    productThroatNuclearHeatTraceRealIteratedDerivative
        0 data time fold twist =
      productThroatNuclearHeatTraceReal data time fold twist := by
  simp [productThroatNuclearHeatTraceRealIteratedDerivative,
    productThroatNuclearHeatTermRealIteratedDerivative,
    productThroatNuclearHeatTraceReal]

theorem productThroatNuclearHeatTermRealIteratedDerivative_hasDerivAt
    (order : Nat) (data : ProductThroatSpectralData) (time : Real)
    (fold : Fold) (twist : CircleTwist) (index : Nat × Int) :
    HasDerivAt
      (fun s : Real => productThroatNuclearHeatTermRealIteratedDerivative
        order data s fold twist index)
      (productThroatNuclearHeatTermRealIteratedDerivative
        (order + 1) data time fold twist index) time := by
  let spectrum := productThroatSquaredEigenvalue data fold twist index
  let multiplicity : Real := sphereMultiplicity data index.1
  have hInner : HasDerivAt (fun s : Real => -s * spectrum) (-spectrum) time := by
    simpa [mul_comm] using (hasDerivAt_id time).const_mul (-spectrum)
  have hExp := (Real.hasDerivAt_exp (-time * spectrum)).comp time hInner
  have hBase : HasDerivAt
      (fun s : Real => productThroatNuclearHeatTermReal data s fold twist index)
      (-spectrum * productThroatNuclearHeatTermReal data time fold twist index)
      time := by
    have hScaled := hExp.const_mul multiplicity
    simpa [productThroatNuclearHeatTermReal, spectrum, multiplicity,
      mul_comm, mul_left_comm, mul_assoc] using hScaled
  have h := hBase.const_mul ((-spectrum) ^ order)
  simpa [productThroatNuclearHeatTermRealIteratedDerivative,
    spectrum, pow_succ, mul_assoc] using h

theorem productThroatNuclearHeatTermRealIteratedDerivative_continuous
    (order : Nat) (data : ProductThroatSpectralData)
    (fold : Fold) (twist : CircleTwist) (index : Nat × Int) :
    Continuous (fun time : Real =>
      productThroatNuclearHeatTermRealIteratedDerivative
        order data time fold twist index) := by
  unfold productThroatNuclearHeatTermRealIteratedDerivative
    productThroatNuclearHeatTermReal
  fun_prop

theorem productThroatNuclearHeatTermReal_le_of_le
    (data : ProductThroatSpectralData) {lower time : Real} (hTime : lower ≤ time)
    (fold : Fold) (twist : CircleTwist) (index : Nat × Int) :
    productThroatNuclearHeatTermReal data time fold twist index ≤
      productThroatNuclearHeatTermReal data lower fold twist index := by
  unfold productThroatNuclearHeatTermReal
  apply mul_le_mul_of_nonneg_left
  · apply Real.exp_le_exp.mpr
    have hSpectrum := productThroatSquaredEigenvalue_nonnegative
      data fold twist index
    nlinarith
  · positivity

theorem productThroatNuclearHeatTermRealIteratedDerivative_uniform_summable
    (order : Nat) (data : ProductThroatSpectralData) (epsilon : HeatTime)
    (fold : Fold) (twist : CircleTwist) :
    Summable (fun index : Nat × Int =>
      spectralAbsorptionConstant order epsilon.1 *
        productThroatNuclearHeatTermReal data
          (spectralAbsorptionTime order epsilon.1) fold twist index) := by
  exact Summable.mul_left _ (productThroatNuclearHeatTermReal_summable data
    ⟨spectralAbsorptionTime order epsilon.1,
      spectralAbsorptionTime_pos order epsilon.2⟩ fold twist)

theorem productThroatNuclearHeatTermRealIteratedDerivative_norm_le
    (order : Nat) (data : ProductThroatSpectralData) (epsilon : HeatTime)
    {time : Real} (hTime : epsilon.1 ≤ time)
    (fold : Fold) (twist : CircleTwist) (index : Nat × Int) :
    ‖productThroatNuclearHeatTermRealIteratedDerivative
        order data time fold twist index‖ ≤
      spectralAbsorptionConstant order epsilon.1 *
        productThroatNuclearHeatTermReal data
          (spectralAbsorptionTime order epsilon.1) fold twist index := by
  let spectrum := productThroatSquaredEigenvalue data fold twist index
  let multiplicity : Real := sphereMultiplicity data index.1
  have hSpectrum : 0 ≤ spectrum :=
    productThroatSquaredEigenvalue_nonnegative data fold twist index
  have hTerm : 0 ≤ productThroatNuclearHeatTermReal data time fold twist index :=
    productThroatNuclearHeatTermReal_nonnegative data time fold twist index
  rw [productThroatNuclearHeatTermRealIteratedDerivative,
    Real.norm_eq_abs, abs_mul, abs_pow, abs_neg, abs_of_nonneg hSpectrum,
    abs_of_nonneg hTerm]
  refine (mul_le_mul_of_nonneg_left
    (productThroatNuclearHeatTermReal_le_of_le
      data hTime fold twist index) (pow_nonneg hSpectrum order)).trans ?_
  unfold productThroatNuclearHeatTermReal
  change spectrum ^ order *
      (multiplicity * Real.exp (-epsilon.1 * spectrum)) ≤
    spectralAbsorptionConstant order epsilon.1 *
      (multiplicity * Real.exp
        (-spectralAbsorptionTime order epsilon.1 * spectrum))
  have hBound := spectralFactor_pow_mul_exp_bound order epsilon.2 hSpectrum
  have hMultiplicity : 0 ≤ multiplicity := by
    unfold multiplicity
    positivity
  calc
    spectrum ^ order *
        (multiplicity * Real.exp (-epsilon.1 * spectrum)) =
      multiplicity *
        (spectrum ^ order * Real.exp (-epsilon.1 * spectrum)) := by ring
    _ ≤ multiplicity *
        (spectralAbsorptionConstant order epsilon.1 *
          Real.exp (-spectralAbsorptionTime order epsilon.1 * spectrum)) :=
      mul_le_mul_of_nonneg_left hBound hMultiplicity
    _ = spectralAbsorptionConstant order epsilon.1 *
        (multiplicity * Real.exp
          (-spectralAbsorptionTime order epsilon.1 * spectrum)) := by ring

theorem productThroatNuclearHeatTermRealIteratedDerivative_summable
    (order : Nat) (data : ProductThroatSpectralData) (time : HeatTime)
    (fold : Fold) (twist : CircleTwist) :
    Summable (fun index : Nat × Int =>
      productThroatNuclearHeatTermRealIteratedDerivative
        order data time.1 fold twist index) := by
  apply Summable.of_norm_bounded
    (productThroatNuclearHeatTermRealIteratedDerivative_uniform_summable
      order data time fold twist)
  intro index
  exact productThroatNuclearHeatTermRealIteratedDerivative_norm_le
    order data time le_rfl fold twist index

theorem productThroatNuclearHeatTraceRealIteratedDerivative_continuousOn_Ioi
    (order : Nat) (data : ProductThroatSpectralData)
    (fold : Fold) (twist : CircleTwist) :
    ContinuousOn (fun time : Real =>
      productThroatNuclearHeatTraceRealIteratedDerivative
        order data time fold twist) (Ioi 0) := by
  intro time hTime
  let epsilon : HeatTime := ⟨time / 2, half_pos hTime⟩
  apply ContinuousOn.continuousAt
    (s := Ici epsilon.1)
    (continuousOn_tsum
      (fun index =>
        (productThroatNuclearHeatTermRealIteratedDerivative_continuous
          order data fold twist index).continuousOn)
      (productThroatNuclearHeatTermRealIteratedDerivative_uniform_summable
        order data epsilon fold twist)
      (fun index parameter hParameter =>
        productThroatNuclearHeatTermRealIteratedDerivative_norm_le
          order data epsilon hParameter fold twist index))
    (Ici_mem_nhds (half_lt_self hTime)) |>.continuousWithinAt

theorem productThroatNuclearHeatTraceRealIteratedDerivative_hasDerivAt
    (order : Nat) (data : ProductThroatSpectralData) (time : HeatTime)
    (fold : Fold) (twist : CircleTwist) :
    HasDerivAt
      (fun s : Real => productThroatNuclearHeatTraceRealIteratedDerivative
        order data s fold twist)
      (productThroatNuclearHeatTraceRealIteratedDerivative
        (order + 1) data time.1 fold twist) time.1 := by
  unfold productThroatNuclearHeatTraceRealIteratedDerivative
  let epsilon : HeatTime := ⟨time.1 / 2, half_pos time.2⟩
  apply hasDerivAt_tsum_of_isPreconnected
    (g := fun index s => productThroatNuclearHeatTermRealIteratedDerivative
      order data s fold twist index)
    (g' := fun index s => productThroatNuclearHeatTermRealIteratedDerivative
      (order + 1) data s fold twist index)
    (u := fun index : Nat × Int =>
      spectralAbsorptionConstant (order + 1) epsilon.1 *
        productThroatNuclearHeatTermReal data
          (spectralAbsorptionTime (order + 1) epsilon.1) fold twist index)
    (t := Ioi epsilon.1) (y₀ := time.1) (y := time.1)
  · exact productThroatNuclearHeatTermRealIteratedDerivative_uniform_summable
      (order + 1) data epsilon fold twist
  · exact isOpen_Ioi
  · exact isPreconnected_Ioi
  · intro index parameter _
    exact productThroatNuclearHeatTermRealIteratedDerivative_hasDerivAt
      order data parameter fold twist index
  · intro index parameter hParameter
    exact productThroatNuclearHeatTermRealIteratedDerivative_norm_le
      (order + 1) data epsilon hParameter.le fold twist index
  · exact mem_Ioi.mpr (half_lt_self time.2)
  · exact productThroatNuclearHeatTermRealIteratedDerivative_summable
      order data time fold twist
  · exact mem_Ioi.mpr (half_lt_self time.2)

theorem productThroatNuclearHeatTraceRealIteratedDerivative_deriv_eq
    (order : Nat) (data : ProductThroatSpectralData) (time : HeatTime)
    (fold : Fold) (twist : CircleTwist) :
    deriv (fun s : Real => productThroatNuclearHeatTraceRealIteratedDerivative
      order data s fold twist) time.1 =
      productThroatNuclearHeatTraceRealIteratedDerivative
        (order + 1) data time.1 fold twist :=
  (productThroatNuclearHeatTraceRealIteratedDerivative_hasDerivAt
    order data time fold twist).deriv

theorem productThroatNuclearHeatTraceRealIteratedDerivative_contDiffOn_nat
    (derivativeOrder smoothnessOrder : Nat) (data : ProductThroatSpectralData)
    (fold : Fold) (twist : CircleTwist) :
    ContDiffOn ℝ smoothnessOrder
      (fun time : Real => productThroatNuclearHeatTraceRealIteratedDerivative
        derivativeOrder data time fold twist) (Ioi 0) := by
  induction smoothnessOrder generalizing derivativeOrder with
  | zero =>
      exact contDiffOn_zero.mpr
        (productThroatNuclearHeatTraceRealIteratedDerivative_continuousOn_Ioi
          derivativeOrder data fold twist)
  | succ smoothnessOrder ih =>
      change ContDiffOn ℝ (smoothnessOrder + 1)
        (fun time : Real => productThroatNuclearHeatTraceRealIteratedDerivative
          derivativeOrder data time fold twist) (Ioi 0)
      rw [contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
      refine ⟨?_, ?_, ?_⟩
      · intro time hTime
        exact DifferentiableAt.differentiableWithinAt
          (productThroatNuclearHeatTraceRealIteratedDerivative_hasDerivAt
            derivativeOrder data ⟨time, hTime⟩ fold twist).differentiableAt
      · intro hImpossible
        norm_num at hImpossible
      · exact (ih (derivativeOrder + 1)).congr fun time hTime =>
          productThroatNuclearHeatTraceRealIteratedDerivative_deriv_eq
            derivativeOrder data ⟨time, hTime⟩ fold twist

theorem productThroatNuclearHeatTraceReal_contDiffOn_infty
    (data : ProductThroatSpectralData) (fold : Fold) (twist : CircleTwist) :
    ContDiffOn ℝ ∞
      (fun time : Real => productThroatNuclearHeatTraceReal
        data time fold twist) (Ioi 0) := by
  rw [contDiffOn_infty]
  intro order
  exact (productThroatNuclearHeatTraceRealIteratedDerivative_contDiffOn_nat
    0 order data fold twist).congr fun time _ => by simp

theorem productThroatNuclearHeatTraceReal_iteratedDeriv_eq
    (order : Nat) (data : ProductThroatSpectralData)
    (fold : Fold) (twist : CircleTwist) :
    ∀ ⦃time : Real⦄, 0 < time →
      iteratedDeriv order
          (fun s : Real => productThroatNuclearHeatTraceReal
            data s fold twist) time =
        productThroatNuclearHeatTraceRealIteratedDerivative
          order data time fold twist := by
  induction order with
  | zero => intro time _; simp
  | succ order ih =>
      intro time hTime
      rw [iteratedDeriv_succ]
      have hEventually :
          iteratedDeriv order
              (fun s : Real => productThroatNuclearHeatTraceReal
                data s fold twist) =ᶠ[nhds time]
            fun s : Real => productThroatNuclearHeatTraceRealIteratedDerivative
              order data s fold twist := by
        filter_upwards [Ioi_mem_nhds hTime] with parameter hParameter
        exact ih hParameter
      rw [hEventually.deriv_eq]
      exact productThroatNuclearHeatTraceRealIteratedDerivative_deriv_eq
        order data ⟨time, hTime⟩ fold twist

theorem productThroatNuclearHeatTraceReal_completeMonotonicity
    (data : ProductThroatSpectralData) (fold : Fold) (twist : CircleTwist) :
    CompletelyMonotoneOnPositive
      (fun time : Real => productThroatNuclearHeatTraceReal
        data time fold twist) := by
  constructor
  · exact productThroatNuclearHeatTraceReal_contDiffOn_infty data fold twist
  · intro order time hTime
    rw [productThroatNuclearHeatTraceReal_iteratedDeriv_eq
      order data fold twist hTime,
      productThroatNuclearHeatTraceRealIteratedDerivative, ← tsum_mul_left]
    apply tsum_nonneg
    intro index
    rw [productThroatNuclearHeatTermRealIteratedDerivative,
      ← mul_assoc, ← mul_pow]
    norm_num
    exact mul_nonneg
      (pow_nonneg (productThroatSquaredEigenvalue_nonnegative
        data fold twist index) order)
      (productThroatNuclearHeatTermReal_nonnegative
        data time fold twist index)

theorem productThroatNuclearHeatTraceRealIteratedDerivative_pt_eq_positive
    (order : Nat) (data : ProductThroatSpectralData)
    (time : Real) (twist : CircleTwist) :
    productThroatNuclearHeatTraceRealIteratedDerivative
        order data time .pt twist =
      productThroatNuclearHeatTraceRealIteratedDerivative
        order data time .positive twist := by
  unfold productThroatNuclearHeatTraceRealIteratedDerivative
    productThroatNuclearHeatTermRealIteratedDerivative
    productThroatNuclearHeatTermReal productThroatSquaredEigenvalue
  apply tsum_congr
  intro index
  rw [circleOperatorSquaredEigenvalue_eq_eigenvalueSq,
    circleOperatorSquaredEigenvalue_eq_eigenvalueSq,
    pt_eigenvalueSq_eq_positive]

end
end P0EFTJanusProductThroatNuclearHeatTraceSmooth4D
end JanusFormal
