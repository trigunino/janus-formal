import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProductThroatUnboundedDiracFredholm4D

/-!
# Common holonomy domain for the product-throat Dirac operator

The product eigenvalue is the norm of a two-component complex spectral
vector.  The reverse triangle inequality therefore gives a sharp uniform
Lipschitz bound in the circle holonomy.  The corresponding bounded diagonal
difference identifies all maximal first-order domains at fixed product
geometry and fold.

This is a common-domain result for the separated throat spectrum.  It does not
construct the global geometric Janus parameter space or its smooth family.
-/

namespace JanusFormal
namespace P0EFTJanusProductThroatHolonomyCommonDomain4D

set_option autoImplicit false

noncomputable section

open Set
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusCircleDiracHeatFunctionalBridge
open P0EFTJanusProductThroatHeatOperator4D
open P0EFTJanusProductThroatUnboundedDiracSquared4D
open P0EFTJanusProductThroatUnboundedDirac4D
open P0EFTJanusProductThroatUnboundedDiracFredholm4D
open scoped ENNReal lp LinearPMap

/-- Complex two-component representative of the positive product spectrum. -/
def productThroatHolonomySpectralVector
    (data : ProductThroatSpectralData) (twist : CircleTwist)
    (mode : ProductThroatHeatMode data) : Complex :=
  (Real.sqrt (sphereEigenvalueSquared data mode.1.1) : Complex) +
    (baseEigenvalue twist mode.2 : Complex) * Complex.I

theorem productThroatDiracSquaredEigenvalue_eq_base
    (data : ProductThroatSpectralData) (fold : Fold) (twist : CircleTwist)
    (mode : ProductThroatHeatMode data) :
    productThroatDiracSquaredEigenvalue data fold twist mode =
      sphereEigenvalueSquared data mode.1.1 +
        baseEigenvalue twist mode.2 ^ 2 := by
  rw [productThroatDiracSquaredEigenvalue,
    circleOperatorSquaredEigenvalue_eq_eigenvalueSq]
  cases fold <;> simp [eigenvalueSq, diracEigenvalue]

theorem productThroatHolonomySpectralVector_norm
    (data : ProductThroatSpectralData) (twist : CircleTwist)
    (mode : ProductThroatHeatMode data) :
    ‖productThroatHolonomySpectralVector data twist mode‖ =
      Real.sqrt (sphereEigenvalueSquared data mode.1.1 +
        baseEigenvalue twist mode.2 ^ 2) := by
  rw [Complex.norm_def, Complex.normSq_apply]
  simp [productThroatHolonomySpectralVector]
  rw [Real.mul_self_sqrt
    (sphere_eigenvalue_squared_positive data mode.1.1).le]
  ring

theorem productThroatDiracEigenvalue_abs_eq_spectralVector_norm
    (data : ProductThroatSpectralData) (fold : Fold) (twist : CircleTwist)
    (mode : ProductThroatHeatMode data) :
    |productThroatDiracEigenvalue data fold twist mode| =
      ‖productThroatHolonomySpectralVector data twist mode‖ := by
  rw [productThroatDiracEigenvalue, abs_mul]
  have hSign : |fold.spectralSign| = 1 := by cases fold <;> norm_num
  rw [hSign, one_mul, abs_of_nonneg (Real.sqrt_nonneg _),
    productThroatDiracSquaredEigenvalue_eq_base,
    productThroatHolonomySpectralVector_norm]

theorem productThroatHolonomySpectralVector_sub_norm
    (data : ProductThroatSpectralData) (first second : CircleTwist)
    (mode : ProductThroatHeatMode data) :
    ‖productThroatHolonomySpectralVector data first mode -
        productThroatHolonomySpectralVector data second mode‖ =
      |first.value - second.value| := by
  rw [Complex.norm_def, Complex.normSq_apply]
  simp [productThroatHolonomySpectralVector, baseEigenvalue]
  ring_nf
  convert Real.sqrt_sq_eq_abs (first.value - second.value) using 1 <;> ring

theorem productThroatDiracEigenvalue_holonomy_lipschitz
    (data : ProductThroatSpectralData) (fold : Fold)
    (first second : CircleTwist) (mode : ProductThroatHeatMode data) :
    |productThroatDiracEigenvalue data fold first mode -
        productThroatDiracEigenvalue data fold second mode| ≤
      |first.value - second.value| := by
  have hNorm := abs_norm_sub_norm_le
    (productThroatHolonomySpectralVector data first mode)
    (productThroatHolonomySpectralVector data second mode)
  rw [productThroatHolonomySpectralVector_sub_norm] at hNorm
  have hFirst : productThroatDiracEigenvalue data fold first mode =
      fold.spectralSign *
        ‖productThroatHolonomySpectralVector data first mode‖ := by
    rw [productThroatDiracEigenvalue,
      productThroatDiracSquaredEigenvalue_eq_base,
      productThroatHolonomySpectralVector_norm]
  have hSecond : productThroatDiracEigenvalue data fold second mode =
      fold.spectralSign *
        ‖productThroatHolonomySpectralVector data second mode‖ := by
    rw [productThroatDiracEigenvalue,
      productThroatDiracSquaredEigenvalue_eq_base,
      productThroatHolonomySpectralVector_norm]
  rw [hFirst, hSecond, ← mul_sub, abs_mul]
  have hSign : |fold.spectralSign| = 1 := by cases fold <;> norm_num
  rw [hSign, one_mul]
  exact hNorm

/-- Bounded diagonal difference between two holonomies. -/
def productThroatDiracHolonomyDifference
    (data : ProductThroatSpectralData) (fold : Fold)
    (first second : CircleTwist) (state : ProductThroatHeatHilbert data) :
    ProductThroatHeatHilbert data := by
  let difference : ProductThroatHeatMode data → Complex := fun mode =>
    ((productThroatDiracEigenvalue data fold second mode -
      productThroatDiracEigenvalue data fold first mode : Real) : Complex) *
        state mode
  have hBound : Memℓp
      (fun mode : ProductThroatHeatMode data =>
        ((|first.value - second.value| : Real) : Complex) * state mode) 2 :=
    (lp.memℓp state).const_mul
      ((|first.value - second.value| : Real) : Complex)
  have hDifference : Memℓp difference 2 := hBound.mono' (fun mode => by
    rw [show difference mode =
      ((productThroatDiracEigenvalue data fold second mode -
        productThroatDiracEigenvalue data fold first mode : Real) : Complex) *
          state mode by rfl,
      norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_abs]
    exact mul_le_mul_of_nonneg_right
      (by
        rw [abs_sub_comm]
        exact productThroatDiracEigenvalue_holonomy_lipschitz
          data fold first second mode)
      (norm_nonneg _))
  exact ⟨difference, hDifference⟩

@[simp]
theorem productThroatDiracHolonomyDifference_apply
    (data : ProductThroatSpectralData) (fold : Fold)
    (first second : CircleTwist) (state : ProductThroatHeatHilbert data)
    (mode : ProductThroatHeatMode data) :
    productThroatDiracHolonomyDifference data fold first second state mode =
      ((productThroatDiracEigenvalue data fold second mode -
        productThroatDiracEigenvalue data fold first mode : Real) : Complex) *
          state mode :=
  rfl

theorem productThroatDiracHolonomyDifference_norm_le
    (data : ProductThroatSpectralData) (fold : Fold)
    (first second : CircleTwist) (state : ProductThroatHeatHilbert data) :
    ‖productThroatDiracHolonomyDifference data fold first second state‖ ≤
      |first.value - second.value| * ‖state‖ := by
  calc
    _ ≤ ‖((|first.value - second.value| : Real) : Complex) • state‖ :=
      lp.norm_mono (by norm_num) (fun mode => by
        rw [productThroatDiracHolonomyDifference_apply]
        change ‖((productThroatDiracEigenvalue data fold second mode -
          productThroatDiracEigenvalue data fold first mode : Real) : Complex) *
            state mode‖ ≤
          ‖((|first.value - second.value| : Real) : Complex) * state mode‖
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs, abs_abs]
        exact mul_le_mul_of_nonneg_right
          (by
            rw [abs_sub_comm]
            exact productThroatDiracEigenvalue_holonomy_lipschitz
              data fold first second mode)
          (norm_nonneg _))
    _ = |first.value - second.value| * ‖state‖ := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_abs]

theorem productThroatDiracDomain_mono_holonomy
    (data : ProductThroatSpectralData) (fold : Fold)
    (first second : CircleTwist) :
    productThroatDiracDomain data fold first ≤
      productThroatDiracDomain data fold second := by
  intro state hState
  rcases hState with ⟨firstImage, hFirstImage⟩
  refine ⟨firstImage +
    productThroatDiracHolonomyDifference data fold first second state, ?_⟩
  intro mode
  change firstImage mode +
      productThroatDiracHolonomyDifference data fold first second state mode =
    (productThroatDiracEigenvalue data fold second mode : Complex) * state mode
  rw [hFirstImage mode, productThroatDiracHolonomyDifference_apply]
  push_cast
  ring

/-- All holonomies have exactly the same maximal first-order domain. -/
theorem productThroatDiracDomain_eq_holonomy
    (data : ProductThroatSpectralData) (fold : Fold)
    (first second : CircleTwist) :
    productThroatDiracDomain data fold first =
      productThroatDiracDomain data fold second :=
  le_antisymm
    (productThroatDiracDomain_mono_holonomy data fold first second)
    (productThroatDiracDomain_mono_holonomy data fold second first)

/-- Canonical transport between the equal maximal domains. -/
def productThroatDiracRebaseDomain
    (data : ProductThroatSpectralData) (fold : Fold)
    (first second : CircleTwist)
    (state : (productThroatUnboundedDirac data fold first).domain) :
    (productThroatUnboundedDirac data fold second).domain :=
  ⟨state.1, productThroatDiracDomain_mono_holonomy data fold first second
    state.property⟩

/-- Exact bounded-perturbation formula on the common domain. -/
theorem productThroatUnboundedDirac_rebase_apply
    (data : ProductThroatSpectralData) (fold : Fold)
    (first second : CircleTwist)
    (state : (productThroatUnboundedDirac data fold first).domain) :
    productThroatUnboundedDirac data fold second
        (productThroatDiracRebaseDomain data fold first second state) =
      productThroatUnboundedDirac data fold first state +
        productThroatDiracHolonomyDifference data fold first second state.1 := by
  ext mode
  rw [productThroatUnboundedDirac_apply]
  change (productThroatDiracEigenvalue data fold second mode : Complex) *
      state.1 mode =
    (productThroatUnboundedDirac data fold first state) mode +
      productThroatDiracHolonomyDifference data fold first second state.1 mode
  rw [productThroatUnboundedDirac_apply]
  change (productThroatDiracEigenvalue data fold second mode : Complex) *
      state.1 mode =
    (productThroatDiracEigenvalue data fold first mode : Complex) * state.1 mode +
      productThroatDiracHolonomyDifference data fold first second state.1 mode
  rw [productThroatDiracHolonomyDifference_apply]
  push_cast
  ring

end

end P0EFTJanusProductThroatHolonomyCommonDomain4D
end JanusFormal
