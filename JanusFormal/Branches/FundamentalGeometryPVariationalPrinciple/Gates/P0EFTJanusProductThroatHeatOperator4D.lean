import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProductThroatNuclearHeatTrace4D

/-!
# Bounded heat operator on the infinite product-throat spectrum

The spectral Hilbert space retains every monopole level, its exact finite
multiplicity and every circle Fourier mode.  Gaussian multiplication defines
a contraction on this genuine `ℓ²` space.  Its summable diagonal trace is
identified exactly with the previously proved product-throat nuclear trace.
-/

namespace JanusFormal
namespace P0EFTJanusProductThroatHeatOperator4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusMonopoleSphereHeatTrace
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusCircleDiracHeatFunctionalBridge
open P0EFTJanusCircleHeatSemigroupOperator
open P0EFTJanusCircleHeatNuclearTraceClass
open P0EFTJanusCircleHeatNuclearTraceContinuity
open P0EFTJanusProductThroatNuclearHeatTrace4D
open scoped ENNReal lp

/-- Sphere level together with one of its exact monopole degeneracy labels. -/
abbrev ProductThroatSphereMode (data : ProductThroatSpectralData) :=
  Σ level : Nat, Fin (sphereMultiplicity data level)

/-- Full product spectral label. -/
abbrev ProductThroatHeatMode (data : ProductThroatSpectralData) :=
  ProductThroatSphereMode data × Int

/-- Genuine square-summable product-throat spectral Hilbert space. -/
abbrev ProductThroatHeatHilbert (data : ProductThroatSpectralData) :=
  lp (fun _ : ProductThroatHeatMode data => Complex) 2

/-- Heat weight of one sphere eigenvector; degeneracy is carried by the mode
index rather than inserted as a scalar coefficient. -/
def sphereModeHeatWeight
    (data : ProductThroatSpectralData) (time : HeatTime)
    (mode : ProductThroatSphereMode data) : Real :=
  Real.exp (-time.1 * sphereEigenvalueSquared data mode.1)

theorem sphereModeHeatWeight_nonnegative
    (data : ProductThroatSpectralData) (time : HeatTime)
    (mode : ProductThroatSphereMode data) :
    0 ≤ sphereModeHeatWeight data time mode :=
  (Real.exp_pos _).le

theorem sphereModeHeatWeight_le_one
    (data : ProductThroatSpectralData) (time : HeatTime)
    (mode : ProductThroatSphereMode data) :
    sphereModeHeatWeight data time mode ≤ 1 := by
  unfold sphereModeHeatWeight
  rw [Real.exp_le_one_iff]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr time.2.le)
    (sphere_eigenvalue_squared_positive data mode.1).le

theorem sphereModeHeatWeight_summable
    (data : ProductThroatSpectralData) (time : HeatTime) :
    Summable (sphereModeHeatWeight data time) := by
  apply (summable_sigma_of_nonneg
    (sphereModeHeatWeight_nonnegative data time)).2
  constructor
  · intro level
    exact Summable.of_finite
  · convert sphere_heat_trace_summable data time.1 time.2 using 1
    funext level
    rw [tsum_fintype]
    simp [sphereModeHeatWeight, sphereHeatTerm, Finset.sum_const,
      nsmul_eq_mul]

theorem sphereModeHeatWeight_tsum_eq_sphereHeatTrace
    (data : ProductThroatSpectralData) (time : HeatTime) :
    (∑' mode : ProductThroatSphereMode data,
      sphereModeHeatWeight data time mode) = sphereHeatTrace data time.1 := by
  rw [(sphereModeHeatWeight_summable data time).tsum_sigma]
  unfold sphereHeatTrace
  apply tsum_congr
  intro level
  rw [tsum_fintype]
  simp [sphereModeHeatWeight, sphereHeatTerm, Finset.sum_const,
    nsmul_eq_mul]

/-- Real product multiplier of one full spectral mode. -/
def productThroatHeatWeight
    (data : ProductThroatSpectralData) (time : HeatTime)
    (fold : Fold) (twist : CircleTwist)
    (mode : ProductThroatHeatMode data) : Real :=
  sphereModeHeatWeight data time mode.1 *
    circleOperatorHeatWeight time fold twist mode.2

theorem productThroatHeatWeight_nonnegative
    (data : ProductThroatSpectralData) (time : HeatTime)
    (fold : Fold) (twist : CircleTwist)
    (mode : ProductThroatHeatMode data) :
    0 ≤ productThroatHeatWeight data time fold twist mode := by
  exact mul_nonneg (sphereModeHeatWeight_nonnegative data time mode.1)
    (circleOperatorHeatWeight_nonnegative time fold twist mode.2)

theorem productThroatHeatWeight_le_one
    (data : ProductThroatSpectralData) (time : HeatTime)
    (fold : Fold) (twist : CircleTwist)
    (mode : ProductThroatHeatMode data) :
    productThroatHeatWeight data time fold twist mode ≤ 1 := by
  exact (mul_le_mul
    (sphereModeHeatWeight_le_one data time mode.1)
    (by
      unfold circleOperatorHeatWeight
      rw [Real.exp_le_one_iff]
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr time.2.le)
        (circleOperatorSquaredEigenvalue_nonnegative fold twist mode.2))
    (circleOperatorHeatWeight_nonnegative time fold twist mode.2)
    zero_le_one).trans_eq (mul_one 1)

theorem productThroatHeatWeight_summable
    (data : ProductThroatSpectralData) (time : HeatTime)
    (fold : Fold) (twist : CircleTwist) :
    Summable (productThroatHeatWeight data time fold twist) := by
  apply (summable_prod_of_nonneg
    (productThroatHeatWeight_nonnegative data time fold twist)).2
  constructor
  · intro sphereMode
    exact (circleOperatorHeatWeight_summable time fold twist).mul_left
      (sphereModeHeatWeight data time sphereMode)
  · have hSphere := sphereModeHeatWeight_summable data time
    have hScaled := hSphere.mul_right (circleHeatNuclearTrace time fold twist)
    exact hScaled.congr fun sphereMode => by
      unfold productThroatHeatWeight circleHeatNuclearTrace
      simp only [Prod.fst, Prod.snd]
      rw [tsum_mul_left]

/-- Coordinatewise Gaussian multiplication on the full spectral `ℓ²`. -/
def productThroatHeatLinearMap
    (data : ProductThroatSpectralData) (time : HeatTime)
    (fold : Fold) (twist : CircleTwist) :
    ProductThroatHeatHilbert data →ₗ[Complex] ProductThroatHeatHilbert data where
  toFun state := ⟨fun mode =>
    (productThroatHeatWeight data time fold twist mode : Complex) * state mode, by
      refine state.2.mono' ?_
      intro mode
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg
          (productThroatHeatWeight_nonnegative data time fold twist mode)]
      simpa using mul_le_mul_of_nonneg_right
        (productThroatHeatWeight_le_one data time fold twist mode)
        (norm_nonneg (state mode))⟩
  map_add' := by
    intro first second
    ext mode
    simp [mul_add]
  map_smul' := by
    intro scalar state
    ext mode
    simp [mul_left_comm]

/-- Bounded product-throat heat contraction. -/
def productThroatHeatOperator
    (data : ProductThroatSpectralData) (time : HeatTime)
    (fold : Fold) (twist : CircleTwist) :
    ProductThroatHeatHilbert data →L[Complex] ProductThroatHeatHilbert data :=
  (productThroatHeatLinearMap data time fold twist).mkContinuous 1 (by
    intro state
    rw [one_mul]
    apply lp.norm_mono (p := (2 : ENNReal)) (by norm_num)
    intro mode
    change ‖(productThroatHeatWeight data time fold twist mode : Complex) *
      state mode‖ ≤ ‖state mode‖
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (productThroatHeatWeight_nonnegative data time fold twist mode)]
    exact mul_le_of_le_one_left (norm_nonneg (state mode))
      (productThroatHeatWeight_le_one data time fold twist mode))

@[simp]
theorem productThroatHeatOperator_apply
    (data : ProductThroatSpectralData) (time : HeatTime)
    (fold : Fold) (twist : CircleTwist)
    (state : ProductThroatHeatHilbert data)
    (mode : ProductThroatHeatMode data) :
    productThroatHeatOperator data time fold twist state mode =
      (productThroatHeatWeight data time fold twist mode : Complex) * state mode :=
  rfl

theorem productThroatHeatOperator_opNorm_le_one
    (data : ProductThroatSpectralData) (time : HeatTime)
    (fold : Fold) (twist : CircleTwist) :
    ‖productThroatHeatOperator data time fold twist‖ ≤ 1 := by
  exact LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- Summable diagonal trace of the actual bounded operator. -/
def productThroatHeatOperatorDiagonalTrace
    (data : ProductThroatSpectralData) (time : HeatTime)
    (fold : Fold) (twist : CircleTwist) : Real :=
  ∑' mode : ProductThroatHeatMode data,
    productThroatHeatWeight data time fold twist mode

theorem productThroatHeatOperatorDiagonalTrace_factorizes
    (data : ProductThroatSpectralData) (time : HeatTime)
    (fold : Fold) (twist : CircleTwist) :
    productThroatHeatOperatorDiagonalTrace data time fold twist =
      sphereHeatTrace data time.1 * circleHeatNuclearTrace time fold twist := by
  unfold productThroatHeatOperatorDiagonalTrace
  rw [(productThroatHeatWeight_summable data time fold twist).tsum_prod]
  simp_rw [productThroatHeatWeight, tsum_mul_left]
  rw [tsum_mul_right, sphereModeHeatWeight_tsum_eq_sphereHeatTrace]
  rfl

/-- The diagonal trace of the bounded spectral operator is exactly the
product-throat nuclear trace. -/
theorem productThroatHeatOperatorDiagonalTrace_eq_nuclearTrace
    (data : ProductThroatSpectralData) (time : HeatTime)
    (fold : Fold) (twist : CircleTwist) :
    productThroatHeatOperatorDiagonalTrace data time fold twist =
      productThroatNuclearHeatTrace data time fold twist := by
  rw [productThroatHeatOperatorDiagonalTrace_factorizes,
    productThroatNuclearHeatTrace_factorizes]

end

end P0EFTJanusProductThroatHeatOperator4D
end JanusFormal
