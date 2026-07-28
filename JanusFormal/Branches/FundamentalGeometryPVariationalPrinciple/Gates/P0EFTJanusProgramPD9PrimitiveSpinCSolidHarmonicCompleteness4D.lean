import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCSpherePolynomialDensity4D
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Finsupp.Supported

/-!
# Solid-harmonic completeness on the primitive SpinC sphere

Equatorial Cauchy data give the exact dimension `2d + 1` of homogeneous
solid harmonics.  The existing null packet is therefore a basis in every
degree.  A Fischer decomposition then identifies its spherical span with
all coordinate-polynomial restrictions, so Stone--Weierstrass promotes the
packet to a dense family in geometric sphere `L²`.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9PrimitiveSpinCSolidHarmonicCompleteness4D

set_option autoImplicit false
noncomputable section

open MvPolynomial
open P0EFTJanusProgramPPrimitiveMonopoleClutchingConnection4D
open P0EFTJanusProgramPD9PrimitiveSpinCAllLevelSolidHarmonicPacket4D
open P0EFTJanusProgramPD9PrimitiveSpinCSpherePolynomialDensity4D

local instance primitiveSpinCSolidHarmonicSphereMeasureFinite :
    MeasureTheory.IsFiniteMeasure primitiveSpinCSphereMeasure := by
  unfold primitiveSpinCSphereMeasure
  infer_instance

local instance primitiveSpinCSolidHarmonicSphereMeasureWeaklyRegular :
    primitiveSpinCSphereMeasure.WeaklyRegular := by
  infer_instance

theorem finSuccEquiv_pderiv_zero
    (polynomial : MvPolynomial (Fin 3) Complex) :
    MvPolynomial.finSuccEquiv Complex 2
        (pderiv 0 polynomial) =
      Polynomial.derivative
        (MvPolynomial.finSuccEquiv Complex 2 polynomial) := by
  induction polynomial using MvPolynomial.induction_on' with
  | add left right hLeft hRight =>
      simp only [map_add, hLeft, hRight]
  | monomial exponent coefficient =>
      rw [pderiv_monomial]
      simp [MvPolynomial.finSuccEquiv_apply,
        MvPolynomial.eval₂Hom_monomial, Fin.prod_univ_succ,
        Polynomial.derivative_pow]
      ring

theorem coeff_pderiv
    {variableType : Type} [DecidableEq variableType]
    (polynomial : MvPolynomial variableType Complex)
    (coordinate : variableType) (exponent : variableType →₀ Nat) :
    MvPolynomial.coeff exponent (pderiv coordinate polynomial) =
      (exponent coordinate + 1 : Nat) *
        MvPolynomial.coeff
          (exponent + Finsupp.single coordinate 1) polynomial := by
  induction polynomial using MvPolynomial.induction_on' with
  | add left right hLeft hRight =>
      simp only [map_add, MvPolynomial.coeff_add, hLeft, hRight]
      ring
  | monomial monomialExponent coefficient =>
      rw [pderiv_monomial]
      by_cases hCoordinate : monomialExponent coordinate = 0
      · have hExponentNe :
            monomialExponent ≠
              exponent + Finsupp.single coordinate 1 := by
          intro hEqual
          have hAtCoordinate := DFunLike.congr_fun hEqual coordinate
          simp [hCoordinate, Finsupp.single_apply] at hAtCoordinate
        simp [MvPolynomial.coeff_monomial, hCoordinate, hExponentNe]
      by_cases hExponent :
          monomialExponent =
            exponent + Finsupp.single coordinate 1
      · subst monomialExponent
        simp [Finsupp.single_apply]
        ring
      · have hSub :
            monomialExponent - Finsupp.single coordinate 1 ≠ exponent := by
          intro hEqual
          apply hExponent
          rw [← hEqual,
            Finsupp.sub_add_single_one_cancel hCoordinate]
        simp [MvPolynomial.coeff_monomial, hExponent, hSub]

theorem coeff_finSuccEquiv_pderiv_succ
    (polynomial : MvPolynomial (Fin 3) Complex)
    (coordinate : Fin 2) (power : Nat) :
    (MvPolynomial.finSuccEquiv Complex 2
        (pderiv coordinate.succ polynomial)).coeff power =
      pderiv coordinate
        ((MvPolynomial.finSuccEquiv Complex 2 polynomial).coeff power) := by
  classical
  ext exponent
  rw [MvPolynomial.finSuccEquiv_coeff_coeff,
    coeff_pderiv, coeff_pderiv,
    MvPolynomial.finSuccEquiv_coeff_coeff]
  have hCons :
      Finsupp.cons power exponent +
          Finsupp.single coordinate.succ 1 =
        Finsupp.cons power
          (exponent + Finsupp.single coordinate 1) := by
    ext index
    refine Fin.cases ?_ ?_ index
    · simp
    · intro tailIndex
      simp [Finsupp.single_apply]
  rw [hCons]
  simp

def planeLaplacian
    (polynomial : MvPolynomial (Fin 2) Complex) :
    MvPolynomial (Fin 2) Complex :=
  ∑ coordinate : Fin 2,
    pderiv coordinate (pderiv coordinate polynomial)

theorem coeff_finSuccEquiv_solidLaplacian
    (polynomial : PrimitiveSpinCSolidPolynomial) (power : Nat) :
    (MvPolynomial.finSuccEquiv Complex 2
        (primitiveSpinCSolidLaplacian polynomial)).coeff power =
      (((power + 1 : Nat) : Complex) *
          ((power + 2 : Nat) : Complex)) •
          (MvPolynomial.finSuccEquiv Complex 2 polynomial).coeff
            (power + 2) +
        planeLaplacian
          ((MvPolynomial.finSuccEquiv Complex 2 polynomial).coeff power) := by
  classical
  unfold primitiveSpinCSolidLaplacian planeLaplacian
  rw [Fin.sum_univ_succ]
  simp only [map_add, map_sum, Polynomial.coeff_add]
  rw [finSuccEquiv_pderiv_zero, finSuccEquiv_pderiv_zero,
    Polynomial.coeff_derivative, Polynomial.coeff_derivative]
  have hCoeffSum :
      (∑ coordinate : Fin 2,
          MvPolynomial.finSuccEquiv Complex 2
            (pderiv coordinate.succ
              (pderiv coordinate.succ polynomial))).coeff power =
        ∑ coordinate : Fin 2,
          (MvPolynomial.finSuccEquiv Complex 2
            (pderiv coordinate.succ
              (pderiv coordinate.succ polynomial))).coeff power := by
    rw [← Polynomial.lcoeff_apply, map_sum]
    rfl
  rw [hCoeffSum]
  simp_rw [coeff_finSuccEquiv_pderiv_succ]
  rw [MvPolynomial.smul_eq_C_mul]
  simp only [map_mul, map_add, map_natCast]
  push_cast
  ring

theorem solidHarmonic_eq_zero_of_boundary
    (polynomial : PrimitiveSpinCSolidPolynomial)
    (hHarmonic : primitiveSpinCSolidLaplacian polynomial = 0)
    (hZero :
      (MvPolynomial.finSuccEquiv Complex 2 polynomial).coeff 0 = 0)
    (hOne :
      (MvPolynomial.finSuccEquiv Complex 2 polynomial).coeff 1 = 0) :
    polynomial = 0 := by
  have hCoefficient :
      ∀ power : Nat,
        (MvPolynomial.finSuccEquiv Complex 2 polynomial).coeff power = 0 := by
    intro power
    induction power using Nat.twoStepInduction with
    | zero => exact hZero
    | one => exact hOne
    | more power hPower _ =>
        have hRecurrence :=
          coeff_finSuccEquiv_solidLaplacian polynomial power
        rw [hHarmonic, map_zero, Polynomial.coeff_zero,
          hPower, planeLaplacian] at hRecurrence
        simp only [map_zero, Finset.sum_const_zero, add_zero] at hRecurrence
        have hScalar :
            (((power + 1 : Nat) : Complex) *
              ((power + 2 : Nat) : Complex)) ≠ 0 := by
          apply mul_ne_zero
          · exact_mod_cast Nat.succ_ne_zero power
          · exact_mod_cast Nat.succ_ne_zero (power + 1)
        exact
          (smul_eq_zero.mp hRecurrence.symm).resolve_left hScalar
  apply (MvPolynomial.finSuccEquiv Complex 2).injective
  apply Polynomial.ext
  intro power
  rw [map_zero, Polynomial.coeff_zero, hCoefficient power]

def solidLaplacianLinearMap :
    PrimitiveSpinCSolidPolynomial →ₗ[Complex]
      PrimitiveSpinCSolidPolynomial :=
  ∑ coordinate : Fin 3,
    (pderiv coordinate).toLinearMap.comp
      (pderiv coordinate).toLinearMap

@[simp]
theorem solidLaplacianLinearMap_apply
    (polynomial : PrimitiveSpinCSolidPolynomial) :
    solidLaplacianLinearMap polynomial =
      primitiveSpinCSolidLaplacian polynomial := by
  rfl

def solidHarmonicHomogeneousSubmodule (degree : Nat) :
    Submodule Complex PrimitiveSpinCSolidPolynomial :=
  MvPolynomial.homogeneousSubmodule (Fin 3) Complex degree ⊓
    LinearMap.ker solidLaplacianLinearMap

def planeBoundaryZeroExponent (degree : Nat)
    (index : Fin (degree + 1)) : Fin 2 →₀ Nat :=
  Finsupp.single 0 index.val +
    Finsupp.single 1 (degree - index.val)

def planeBoundaryOneExponent (degree : Nat)
    (index : Fin degree) : Fin 2 →₀ Nat :=
  Finsupp.single 0 index.val +
    Finsupp.single 1 (degree - 1 - index.val)

theorem finTwo_degree_eq
    (exponent : Fin 2 →₀ Nat) :
    exponent.degree = exponent 0 + exponent 1 := by
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_succ,
    Fin.sum_univ_succ]
  simp

theorem degree_cons
    (head : Nat) (tail : Fin 2 →₀ Nat) :
    (Finsupp.cons head tail).degree = head + tail.degree := by
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_succ,
    Finsupp.degree_eq_sum]
  rfl

theorem exists_planeBoundaryZeroExponent
    (degree : Nat) (exponent : Fin 2 →₀ Nat)
    (hDegree : exponent.degree = degree) :
    ∃ index : Fin (degree + 1),
      planeBoundaryZeroExponent degree index = exponent := by
  have hCoordinate : exponent 0 ≤ degree := by
    rw [finTwo_degree_eq] at hDegree
    omega
  let index : Fin (degree + 1) :=
    ⟨exponent 0, by omega⟩
  refine ⟨index, ?_⟩
  ext coordinate
  fin_cases coordinate
  · simp [planeBoundaryZeroExponent, index]
  · simp [planeBoundaryZeroExponent, index]
    rw [finTwo_degree_eq] at hDegree
    omega

theorem exists_planeBoundaryOneExponent
    (degree : Nat) (exponent : Fin 2 →₀ Nat)
    (hDegree : exponent.degree + 1 = degree) :
    ∃ index : Fin degree,
      planeBoundaryOneExponent degree index = exponent := by
  have hCoordinate : exponent 0 < degree := by
    rw [finTwo_degree_eq] at hDegree
    omega
  let index : Fin degree := ⟨exponent 0, hCoordinate⟩
  refine ⟨index, ?_⟩
  ext coordinate
  fin_cases coordinate
  · simp [planeBoundaryOneExponent, index]
  · simp [planeBoundaryOneExponent, index]
    rw [finTwo_degree_eq] at hDegree
    omega

def solidHarmonicBoundaryMap (degree : Nat) :
    solidHarmonicHomogeneousSubmodule degree →ₗ[Complex]
      ((Fin (degree + 1) → Complex) × (Fin degree → Complex)) where
  toFun polynomial :=
    (fun index =>
      MvPolynomial.coeff (planeBoundaryZeroExponent degree index)
        ((MvPolynomial.finSuccEquiv Complex 2 polynomial.1).coeff 0),
    fun index =>
      MvPolynomial.coeff (planeBoundaryOneExponent degree index)
        ((MvPolynomial.finSuccEquiv Complex 2 polynomial.1).coeff 1))
  map_add' left right := by
    ext index <;>
      simp [planeBoundaryZeroExponent, planeBoundaryOneExponent]
  map_smul' scalar polynomial := by
    ext index <;>
      simp [planeBoundaryZeroExponent, planeBoundaryOneExponent]

theorem solidHarmonicBoundaryMap_injective (degree : Nat) :
    Function.Injective (solidHarmonicBoundaryMap degree) := by
  intro first second hEqual
  let difference :
      solidHarmonicHomogeneousSubmodule degree :=
    first - second
  have hDifferenceMap :
      solidHarmonicBoundaryMap degree difference = 0 := by
    simp [difference, hEqual]
  have hHomogeneous :
      difference.1.IsHomogeneous degree :=
    difference.property.1
  have hHarmonic :
      primitiveSpinCSolidLaplacian difference.1 = 0 := by
    have hKernel := difference.property.2
    change solidLaplacianLinearMap difference.1 = 0 at hKernel
    simpa using hKernel
  have hBoundaryZero (index : Fin (degree + 1)) :
      MvPolynomial.coeff (planeBoundaryZeroExponent degree index)
          ((MvPolynomial.finSuccEquiv Complex 2 difference.1).coeff 0) =
        0 := by
    have hAt := congrArg (fun value => value.1 index) hDifferenceMap
    simpa [solidHarmonicBoundaryMap] using hAt
  have hBoundaryOne (index : Fin degree) :
      MvPolynomial.coeff (planeBoundaryOneExponent degree index)
          ((MvPolynomial.finSuccEquiv Complex 2 difference.1).coeff 1) =
        0 := by
    have hAt := congrArg (fun value => value.2 index) hDifferenceMap
    simpa [solidHarmonicBoundaryMap] using hAt
  have hZero :
      (MvPolynomial.finSuccEquiv Complex 2 difference.1).coeff 0 = 0 := by
    ext exponent
    simp only [MvPolynomial.coeff_zero]
    by_cases hDegree : exponent.degree = degree
    · obtain ⟨index, hIndex⟩ :=
        exists_planeBoundaryZeroExponent degree exponent hDegree
      rw [← hIndex]
      exact hBoundaryZero index
    · rw [MvPolynomial.finSuccEquiv_coeff_coeff]
      exact hHomogeneous.coeff_eq_zero (by
        rw [degree_cons, zero_add]
        exact hDegree)
  have hOne :
      (MvPolynomial.finSuccEquiv Complex 2 difference.1).coeff 1 = 0 := by
    ext exponent
    simp only [MvPolynomial.coeff_zero]
    by_cases hDegree : exponent.degree + 1 = degree
    · obtain ⟨index, hIndex⟩ :=
        exists_planeBoundaryOneExponent degree exponent hDegree
      rw [← hIndex]
      exact hBoundaryOne index
    · rw [MvPolynomial.finSuccEquiv_coeff_coeff]
      exact hHomogeneous.coeff_eq_zero (by
        rw [degree_cons]
        omega)
  have hDifferenceZero :
      difference.1 = 0 :=
    solidHarmonic_eq_zero_of_boundary
      difference.1 hHarmonic hZero hOne
  have hSubtypeZero : difference = 0 :=
    Subtype.ext hDifferenceZero
  apply sub_eq_zero.mp
  simpa [difference] using hSubtypeZero

def solidHarmonicPacketElement (degree : Nat)
    (multiplicity : Fin (2 * degree + 1)) :
    solidHarmonicHomogeneousSubmodule degree :=
  ⟨primitiveSpinCSolidHarmonicPacket degree multiplicity,
    primitiveSpinCSolidHarmonicPacket_isHomogeneous degree multiplicity,
    by
      change
        solidLaplacianLinearMap
            (primitiveSpinCSolidHarmonicPacket degree multiplicity) = 0
      simpa using
        primitiveSpinCSolidHarmonicPacket_laplacian degree multiplicity⟩

theorem solidHarmonicPacketElement_linearIndependent (degree : Nat) :
    LinearIndependent Complex (solidHarmonicPacketElement degree) := by
  apply LinearIndependent.of_comp
    (solidHarmonicHomogeneousSubmodule degree).subtype
  simpa [Function.comp_def, solidHarmonicPacketElement] using
    primitiveSpinCSolidHarmonicPacket_linearIndependent degree

theorem solidHarmonicBoundaryTarget_finrank (degree : Nat) :
    Module.finrank Complex
        ((Fin (degree + 1) → Complex) × (Fin degree → Complex)) =
      2 * degree + 1 := by
  rw [Module.finrank_prod, Module.finrank_fin_fun,
    Module.finrank_fin_fun]
  omega

theorem solidHarmonicHomogeneousSubmodule_finrank (degree : Nat) :
    Module.finrank Complex
        (solidHarmonicHomogeneousSubmodule degree) =
      2 * degree + 1 := by
  letI :
      FiniteDimensional Complex
        (solidHarmonicHomogeneousSubmodule degree) :=
    FiniteDimensional.of_injective
      (solidHarmonicBoundaryMap degree)
      (solidHarmonicBoundaryMap_injective degree)
  apply le_antisymm
  · calc
      Module.finrank Complex
          (solidHarmonicHomogeneousSubmodule degree) ≤
          Module.finrank Complex
            ((Fin (degree + 1) → Complex) ×
              (Fin degree → Complex)) :=
        LinearMap.finrank_le_finrank_of_injective
          (solidHarmonicBoundaryMap_injective degree)
      _ = 2 * degree + 1 :=
        solidHarmonicBoundaryTarget_finrank degree
  · simpa using
      (solidHarmonicPacketElement_linearIndependent degree
        ).fintype_card_le_finrank

theorem solidHarmonicPacketElement_span_eq_top (degree : Nat) :
    Submodule.span Complex
        (Set.range (solidHarmonicPacketElement degree)) = ⊤ := by
  letI :
      FiniteDimensional Complex
        (solidHarmonicHomogeneousSubmodule degree) :=
    FiniteDimensional.of_injective
      (solidHarmonicBoundaryMap degree)
      (solidHarmonicBoundaryMap_injective degree)
  apply
    (solidHarmonicPacketElement_linearIndependent degree
      ).span_eq_top_of_card_eq_finrank'
  rw [solidHarmonicHomogeneousSubmodule_finrank]
  simp

abbrev SolidHomogeneousExponent (degree : Nat) :=
  {exponent : Fin 3 →₀ Nat // exponent.degree = degree}

noncomputable instance solidHomogeneousExponentFintype (degree : Nat) :
    Fintype (SolidHomogeneousExponent degree) :=
  ((Finsupp.finite_of_degree_le (σ := Fin 3) degree).subset
    (by
      intro exponent hDegree
      exact hDegree.le)).fintype

def solidHomogeneousExponentEquivSym (degree : Nat) :
    SolidHomogeneousExponent degree ≃ Sym (Fin 3) degree :=
  (Sym.equivNatSum (Fin 3) degree).symm

def solidHomogeneousSupportedEquiv (degree : Nat) :
    MvPolynomial.homogeneousSubmodule (Fin 3) Complex degree ≃ₗ[Complex]
      (SolidHomogeneousExponent degree →₀ Complex) :=
  (LinearEquiv.ofEq
      (MvPolynomial.homogeneousSubmodule (Fin 3) Complex degree)
      (Finsupp.supported Complex Complex
        {exponent : Fin 3 →₀ Nat | exponent.degree = degree})
      (MvPolynomial.homogeneousSubmodule_eq_finsupp_supported
        (Fin 3) Complex degree)
    ).trans
      (Finsupp.supportedEquivFinsupp
        {exponent : Fin 3 →₀ Nat | exponent.degree = degree})

theorem solidHomogeneousSubmodule_finrank (degree : Nat) :
    Module.finrank Complex
        (MvPolynomial.homogeneousSubmodule (Fin 3) Complex degree) =
      Nat.choose (degree + 2) 2 := by
  calc
    Module.finrank Complex
        (MvPolynomial.homogeneousSubmodule (Fin 3) Complex degree) =
        Module.finrank Complex
          (SolidHomogeneousExponent degree →₀ Complex) :=
      LinearEquiv.finrank_eq (solidHomogeneousSupportedEquiv degree)
    _ = Fintype.card (SolidHomogeneousExponent degree) := by
      rw [Module.finrank_finsupp_self]
    _ = Fintype.card (Sym (Fin 3) degree) :=
      Fintype.card_congr (solidHomogeneousExponentEquivSym degree)
    _ = Nat.choose (degree + 2) 2 := by
      rw [Sym.card_sym_eq_choose]
      norm_num
      rw [add_comm 2 degree]
      simpa using
        (Nat.choose_symm (n := degree + 2) (k := 2) (by omega))

def solidHarmonicNullCurveLinearMap (degree : Nat) :
    solidHarmonicHomogeneousSubmodule degree →ₗ[Complex]
      Polynomial Complex where
  toFun polynomial :=
    primitiveSpinCSolidNullCurveEvaluation polynomial.1
  map_add' left right := by
    simp
  map_smul' scalar polynomial := by
    simpa [Polynomial.smul_eq_C_mul] using
      primitiveSpinCSolidNullCurveEvaluation_smul scalar polynomial.1

theorem solidHarmonicNullCurvePacket_linearIndependent (degree : Nat) :
    LinearIndependent Complex
      (fun multiplicity : Fin (2 * degree + 1) =>
        primitiveSpinCSolidNullCurveEvaluation
          (primitiveSpinCSolidHarmonicPacket degree multiplicity)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro coefficients hSum multiplicity
  have hMoments (moment : Fin (2 * degree + 1)) :
      ∑ basis : Fin (2 * degree + 1),
          coefficients basis *
            primitiveSpinCSolidPacketParameter degree basis ^
              moment.val = 0 := by
    have hCoefficient :=
      congrArg
        (fun polynomial : Polynomial Complex =>
          polynomial.coeff (2 * degree - moment.val))
        hSum
    rw [← Polynomial.lcoeff_apply, map_sum] at hCoefficient
    simp only [Polynomial.lcoeff_apply, Polynomial.coeff_zero,
      Polynomial.smul_eq_C_mul, Polynomial.coeff_C_mul,
      primitiveSpinCSolidNullCurveEvaluation_packet_coeff] at hCoefficient
    have hFactored :
        primitiveSpinCSolidMomentFactor degree moment *
            (∑ basis : Fin (2 * degree + 1),
              coefficients basis *
                primitiveSpinCSolidPacketParameter degree basis ^
                  moment.val) = 0 := by
      rw [Finset.mul_sum]
      calc
        ∑ basis : Fin (2 * degree + 1),
            primitiveSpinCSolidMomentFactor degree moment *
              (coefficients basis *
                primitiveSpinCSolidPacketParameter degree basis ^
                  moment.val) =
            ∑ basis : Fin (2 * degree + 1),
              coefficients basis *
                (primitiveSpinCSolidMomentFactor degree moment *
                  primitiveSpinCSolidPacketParameter degree basis ^
                    moment.val) := by
              apply Finset.sum_congr rfl
              intro basis _
              ring
        _ = 0 := hCoefficient
    exact (mul_eq_zero.mp hFactored).resolve_left
      (primitiveSpinCSolidMomentFactor_ne_zero degree moment)
  have hCoefficients : coefficients = 0 :=
    Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero
      (primitiveSpinCSolidPacketParameter_injective degree) hMoments
  exact congrFun hCoefficients multiplicity

theorem solidHarmonicNullCurveLinearMap_injective (degree : Nat) :
    Function.Injective (solidHarmonicNullCurveLinearMap degree) := by
  apply LinearMap.injective_of_linearIndependent
    (solidHarmonicPacketElement_span_eq_top degree)
  simpa [Function.comp_def, solidHarmonicNullCurveLinearMap,
      solidHarmonicPacketElement] using
      solidHarmonicNullCurvePacket_linearIndependent degree

theorem solidRadiusSquared_isHomogeneous :
    primitiveSpinCSolidRadiusSquared.IsHomogeneous 2 := by
  unfold primitiveSpinCSolidRadiusSquared
  apply MvPolynomial.IsHomogeneous.sum
  intro coordinate _
  exact MvPolynomial.isHomogeneous_X_pow coordinate 2

theorem solidRadiusSquared_ne_zero :
    primitiveSpinCSolidRadiusSquared ≠ 0 := by
  intro hZero
  have hEvaluation :=
    congrArg
      (MvPolynomial.eval ![(1 : Complex), 0, 0])
      hZero
  simp [primitiveSpinCSolidRadiusSquared,
    Fin.sum_univ_succ] at hEvaluation

@[simp]
theorem solidNullCurveEvaluation_radiusSquared :
    primitiveSpinCSolidNullCurveEvaluation
        primitiveSpinCSolidRadiusSquared = 0 := by
  simp [primitiveSpinCSolidNullCurveEvaluation,
    primitiveSpinCSolidRadiusSquared, Fin.sum_univ_succ]
  ring_nf
  have hI :
      Polynomial.C Complex.I ^ 2 =
        (-1 : Polynomial Complex) := by
    rw [← Polynomial.C_pow, Complex.I_sq]
    simp
  rw [hI]
  ring

def solidRadiusSquaredHomogeneousLinearMap (degree : Nat) :
    MvPolynomial.homogeneousSubmodule (Fin 3) Complex degree →ₗ[Complex]
      MvPolynomial.homogeneousSubmodule (Fin 3) Complex (degree + 2) where
  toFun polynomial :=
    ⟨primitiveSpinCSolidRadiusSquared * polynomial.1,
      by
        simpa [add_comm] using
          solidRadiusSquared_isHomogeneous.mul polynomial.property⟩
  map_add' left right := by
    apply Subtype.ext
    exact mul_add _ _ _
  map_smul' scalar polynomial := by
    apply Subtype.ext
    simp only [Submodule.coe_smul, RingHom.id_apply,
      MvPolynomial.smul_eq_C_mul]
    ring

theorem solidRadiusSquaredHomogeneousLinearMap_injective (degree : Nat) :
    Function.Injective
      (solidRadiusSquaredHomogeneousLinearMap degree) := by
  intro left right hEqual
  apply Subtype.ext
  apply mul_left_cancel₀ solidRadiusSquared_ne_zero
  exact congrArg Subtype.val hEqual

def solidHarmonicToHomogeneousLinearMap (degree : Nat) :
    solidHarmonicHomogeneousSubmodule degree →ₗ[Complex]
      MvPolynomial.homogeneousSubmodule (Fin 3) Complex degree where
  toFun polynomial := ⟨polynomial.1, polynomial.property.1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem solidHarmonicToHomogeneousLinearMap_injective (degree : Nat) :
    Function.Injective (solidHarmonicToHomogeneousLinearMap degree) := by
  intro left right hEqual
  apply Subtype.ext
  exact congrArg
    (fun polynomial :
      MvPolynomial.homogeneousSubmodule (Fin 3) Complex degree =>
        polynomial.1)
    hEqual

def solidHarmonicHomogeneousRange (degree : Nat) :
    Submodule Complex
      (MvPolynomial.homogeneousSubmodule (Fin 3) Complex degree) :=
  LinearMap.range (solidHarmonicToHomogeneousLinearMap degree)

def solidRadialHomogeneousRange (degree : Nat) :
    Submodule Complex
      (MvPolynomial.homogeneousSubmodule (Fin 3) Complex (degree + 2)) :=
  LinearMap.range (solidRadiusSquaredHomogeneousLinearMap degree)

theorem solidHarmonic_radial_disjoint (degree : Nat) :
    Disjoint
      (solidHarmonicHomogeneousRange (degree + 2))
      (solidRadialHomogeneousRange degree) := by
  rw [Submodule.disjoint_def]
  intro polynomial hHarmonic hRadial
  obtain ⟨harmonic, hHarmonic⟩ := hHarmonic
  obtain ⟨radial, hRadial⟩ := hRadial
  have hPolynomial :
      harmonic.1 =
        primitiveSpinCSolidRadiusSquared * radial.1 := by
    exact congrArg Subtype.val (hHarmonic.trans hRadial.symm)
  have hNull :
      solidHarmonicNullCurveLinearMap (degree + 2) harmonic = 0 := by
    change
      primitiveSpinCSolidNullCurveEvaluation harmonic.1 = 0
    rw [hPolynomial, map_mul,
      solidNullCurveEvaluation_radiusSquared, zero_mul]
  have hHarmonicZero : harmonic = 0 := by
    apply solidHarmonicNullCurveLinearMap_injective (degree + 2)
    simpa using hNull
  rw [← hHarmonic, hHarmonicZero, map_zero]

theorem solidHarmonicHomogeneousRange_finrank (degree : Nat) :
    Module.finrank Complex
        (solidHarmonicHomogeneousRange degree) =
      2 * degree + 1 := by
  unfold solidHarmonicHomogeneousRange
  rw [LinearMap.finrank_range_of_inj
      (solidHarmonicToHomogeneousLinearMap_injective degree),
    solidHarmonicHomogeneousSubmodule_finrank]

theorem solidRadialHomogeneousRange_finrank (degree : Nat) :
    Module.finrank Complex
        (solidRadialHomogeneousRange degree) =
      Nat.choose (degree + 2) 2 := by
  unfold solidRadialHomogeneousRange
  rw [LinearMap.finrank_range_of_inj
      (solidRadiusSquaredHomogeneousLinearMap_injective degree),
    solidHomogeneousSubmodule_finrank]

theorem choose_fischer_dimension (degree : Nat) :
    Nat.choose (degree + 4) 2 =
      (2 * (degree + 2) + 1) + Nat.choose (degree + 2) 2 := by
  simp [Nat.choose]
  omega

theorem solidFischer_sup_eq_top (degree : Nat) :
    solidHarmonicHomogeneousRange (degree + 2) ⊔
        solidRadialHomogeneousRange degree =
      ⊤ := by
  letI :
      FiniteDimensional Complex
        (MvPolynomial.homogeneousSubmodule
          (Fin 3) Complex (degree + 2)) :=
    FiniteDimensional.of_injective
      (solidHomogeneousSupportedEquiv (degree + 2)).toLinearMap
      (solidHomogeneousSupportedEquiv (degree + 2)).injective
  apply Submodule.eq_top_of_disjoint
  · rw [solidHomogeneousSubmodule_finrank,
      solidHarmonicHomogeneousRange_finrank,
      solidRadialHomogeneousRange_finrank]
    exact (choose_fischer_dimension degree).le
  · exact solidHarmonic_radial_disjoint degree

abbrev SolidHarmonicPacketLabel :=
  Σ degree : Nat, Fin (2 * degree + 1)

def solidHarmonicPacketSphereRestriction
    (label : SolidHarmonicPacketLabel) :
    C(MonopoleSphere, Complex) :=
  primitiveSpinCSpherePolynomialRestriction
    (primitiveSpinCSolidHarmonicPacket label.1 label.2)

def solidHarmonicPacketSphereSpan :
    Submodule Complex C(MonopoleSphere, Complex) :=
  Submodule.span Complex
    (Set.range solidHarmonicPacketSphereRestriction)

def solidHarmonicSphereRestrictionLinearMap (degree : Nat) :
    solidHarmonicHomogeneousSubmodule degree →ₗ[Complex]
      C(MonopoleSphere, Complex) :=
  primitiveSpinCSpherePolynomialRestriction.toLinearMap.comp
    (solidHarmonicHomogeneousSubmodule degree).subtype

theorem solidHarmonicSphereRestriction_mem_packetSpan
    (degree : Nat)
    (harmonic : solidHarmonicHomogeneousSubmodule degree) :
    primitiveSpinCSpherePolynomialRestriction harmonic.1 ∈
      solidHarmonicPacketSphereSpan := by
  have hMembership :
      harmonic ∈
        Submodule.span Complex
          (Set.range (solidHarmonicPacketElement degree)) := by
    rw [solidHarmonicPacketElement_span_eq_top]
    exact Submodule.mem_top
  change
    solidHarmonicSphereRestrictionLinearMap degree harmonic ∈
      solidHarmonicPacketSphereSpan
  induction hMembership using Submodule.span_induction with
  | mem packet hPacket =>
      obtain ⟨multiplicity, rfl⟩ := hPacket
      exact Submodule.subset_span
        ⟨⟨degree, multiplicity⟩, rfl⟩
  | zero =>
      simpa using solidHarmonicPacketSphereSpan.zero_mem
  | add left right _ _ hLeft hRight =>
      simpa using solidHarmonicPacketSphereSpan.add_mem hLeft hRight
  | smul scalar polynomial _ hPolynomial =>
      simpa using
        solidHarmonicPacketSphereSpan.smul_mem scalar hPolynomial

@[simp]
theorem solidRadiusSquared_sphereRestriction :
    primitiveSpinCSpherePolynomialRestriction
        primitiveSpinCSolidRadiusSquared = 1 := by
  ext point
  have hNorm :
      ‖(point.1 : EuclideanSpace Real (Fin 3))‖ = 1 := by
    simpa [Metric.mem_sphere, dist_zero_right] using point.2
  have hNormSquared :=
    congrArg (fun value : Real => value ^ 2) hNorm
  rw [EuclideanSpace.real_norm_sq_eq] at hNormSquared
  simp [Fin.sum_univ_succ] at hNormSquared
  change
    monopoleSphereCoordinate point 0 ^ 2 +
        (monopoleSphereCoordinate point 1 ^ 2 +
          monopoleSphereCoordinate point 2 ^ 2) = 1 at hNormSquared
  simp [primitiveSpinCSpherePolynomialRestriction,
    primitiveSpinCSphereCoordinateContinuousMap,
    primitiveSpinCSolidRadiusSquared, Fin.sum_univ_succ,
    monopoleSphereCoordinate]
  norm_num at hNormSquared ⊢
  exact_mod_cast hNormSquared

theorem solidHarmonicHomogeneousRange_eq_top_of_lt_two
    (degree : Nat) (hDegree : degree < 2) :
    solidHarmonicHomogeneousRange degree = ⊤ := by
  letI :
      FiniteDimensional Complex
        (MvPolynomial.homogeneousSubmodule
          (Fin 3) Complex degree) :=
    FiniteDimensional.of_injective
      (solidHomogeneousSupportedEquiv degree).toLinearMap
      (solidHomogeneousSupportedEquiv degree).injective
  apply Submodule.eq_top_of_finrank_eq
  rw [solidHarmonicHomogeneousRange_finrank,
    solidHomogeneousSubmodule_finrank]
  interval_cases degree <;> norm_num [Nat.choose]

theorem solidFischer_exists_harmonic_add_radial
    (degree : Nat)
    (polynomial :
      MvPolynomial.homogeneousSubmodule
        (Fin 3) Complex (degree + 2)) :
    ∃ harmonic : solidHarmonicHomogeneousSubmodule (degree + 2),
      ∃ radial :
        MvPolynomial.homogeneousSubmodule (Fin 3) Complex degree,
        polynomial.1 =
          harmonic.1 +
            primitiveSpinCSolidRadiusSquared * radial.1 := by
  have hMembership :
      polynomial ∈
        solidHarmonicHomogeneousRange (degree + 2) ⊔
          solidRadialHomogeneousRange degree := by
    rw [solidFischer_sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨harmonicPart, hHarmonicPart,
      radialPart, hRadialPart, hSum⟩ :=
    Submodule.mem_sup.mp hMembership
  obtain ⟨harmonic, rfl⟩ := hHarmonicPart
  obtain ⟨radial, rfl⟩ := hRadialPart
  refine ⟨harmonic, radial, ?_⟩
  exact congrArg Subtype.val hSum.symm

theorem solidHomogeneousSphereRestriction_mem_packetSpan
    (degree : Nat)
    (polynomial :
      MvPolynomial.homogeneousSubmodule (Fin 3) Complex degree) :
    primitiveSpinCSpherePolynomialRestriction polynomial.1 ∈
      solidHarmonicPacketSphereSpan := by
  induction degree using Nat.strong_induction_on with
  | h degree inductionHypothesis =>
      by_cases hSmall : degree < 2
      · have hTop :=
          solidHarmonicHomogeneousRange_eq_top_of_lt_two
            degree hSmall
        have hRange :
            polynomial ∈ solidHarmonicHomogeneousRange degree := by
          rw [hTop]
          exact Submodule.mem_top
        obtain ⟨harmonic, hHarmonic⟩ := hRange
        rw [← hHarmonic]
        exact
          solidHarmonicSphereRestriction_mem_packetSpan
            degree harmonic
      · obtain ⟨radialDegree, rfl⟩ :
            ∃ radialDegree : Nat, degree = radialDegree + 2 := by
          refine ⟨degree - 2, ?_⟩
          omega
        obtain ⟨harmonic, radial, hDecomposition⟩ :=
          solidFischer_exists_harmonic_add_radial
            radialDegree polynomial
        have hRestriction :
            primitiveSpinCSpherePolynomialRestriction polynomial.1 =
              primitiveSpinCSpherePolynomialRestriction harmonic.1 +
                primitiveSpinCSpherePolynomialRestriction radial.1 := by
          rw [hDecomposition, map_add, map_mul,
            solidRadiusSquared_sphereRestriction, one_mul]
        rw [hRestriction]
        apply solidHarmonicPacketSphereSpan.add_mem
        · exact
            solidHarmonicSphereRestriction_mem_packetSpan
              (radialDegree + 2) harmonic
        · exact inductionHypothesis radialDegree (by omega) radial

theorem solidPolynomialSphereRestriction_mem_packetSpan
    (polynomial : PrimitiveSpinCSolidPolynomial) :
    primitiveSpinCSpherePolynomialRestriction polynomial ∈
      solidHarmonicPacketSphereSpan := by
  rw [← polynomial.sum_homogeneousComponent, map_sum]
  apply Submodule.sum_mem
  intro degree _
  exact
    solidHomogeneousSphereRestriction_mem_packetSpan degree
      ⟨polynomial.homogeneousComponent degree,
        MvPolynomial.homogeneousComponent_isHomogeneous
          degree polynomial⟩

theorem solidHarmonicPacketSphereSpan_eq_polynomialSubmodule :
    solidHarmonicPacketSphereSpan =
      primitiveSpinCSpherePolynomialContinuousSubmodule := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨label, rfl⟩
    exact
      ⟨primitiveSpinCSolidHarmonicPacket label.1 label.2, rfl⟩
  · rintro _ ⟨polynomial, rfl⟩
    exact solidPolynomialSphereRestriction_mem_packetSpan polynomial

theorem solidHarmonicPacketSphereSpan_closure_eq_top :
    solidHarmonicPacketSphereSpan.topologicalClosure = ⊤ := by
  rw [solidHarmonicPacketSphereSpan_eq_polynomialSubmodule]
  exact
    primitiveSpinCSpherePolynomialRestriction_range_closure_eq_top

def solidHarmonicPacketSphereToL2 :
    solidHarmonicPacketSphereSpan →L[Complex]
      MeasureTheory.Lp Complex (2 : ENNReal) primitiveSpinCSphereMeasure :=
  (ContinuousMap.toLp
      (2 : ENNReal) primitiveSpinCSphereMeasure Complex).comp
    solidHarmonicPacketSphereSpan.subtypeL

theorem solidHarmonicPacketSphereToL2_denseRange :
    DenseRange solidHarmonicPacketSphereToL2 := by
  have hLp :
      DenseRange
        (ContinuousMap.toLp (2 : ENNReal)
          primitiveSpinCSphereMeasure Complex) :=
    ContinuousMap.toLp_denseRange Complex
      primitiveSpinCSphereMeasure Complex
      (by norm_num : (2 : ENNReal) ≠ ⊤)
  have hSubtype :
      DenseRange solidHarmonicPacketSphereSpan.subtypeL := by
    change Dense (Set.range solidHarmonicPacketSphereSpan.subtypeL)
    rw [show
      Set.range solidHarmonicPacketSphereSpan.subtypeL =
        (solidHarmonicPacketSphereSpan :
          Set C(MonopoleSphere, Complex)) by
      ext continuousFunction
      constructor
      · rintro ⟨packetFunction, rfl⟩
        exact packetFunction.property
      · intro hPacket
        exact ⟨⟨continuousFunction, hPacket⟩, rfl⟩]
    exact Submodule.dense_iff_topologicalClosure_eq_top.mpr
      solidHarmonicPacketSphereSpan_closure_eq_top
  unfold solidHarmonicPacketSphereToL2
  simpa only [ContinuousLinearMap.coe_comp] using
    hLp.comp hSubtype
      (ContinuousMap.toLp (2 : ENNReal)
        primitiveSpinCSphereMeasure Complex).continuous

end
end P0EFTJanusProgramPD9PrimitiveSpinCSolidHarmonicCompleteness4D
end JanusFormal
