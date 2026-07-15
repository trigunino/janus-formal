import Mathlib

namespace JanusFormal
namespace P0EFTJanusFiniteRankPolynomialHelmholtz

set_option autoImplicit false

/--
Coefficient data for a degree-two Euler source on a finite collection of
fields.  With the normalization used below,
`E i = affine i + linear i j * x j + quadratic i j k * x j * x k / 2`.
The last two indices of the quadratic coefficient are the two field slots.
-/
structure QuadraticEulerCoefficients (ι : Type*) where
  affine : ι → ℝ
  linear : ι → ι → ℝ
  quadratic : ι → ι → ι → ℝ
  quadratic_field_symmetric :
    ∀ i j k, quadratic i j k = quadratic i k j

/-- Explicit six-term formulation of symmetry of a trilinear coefficient. -/
def FullySymmetric3 {ι : Type*} (coefficient : ι → ι → ι → ℝ) : Prop :=
  ∀ i j k,
    coefficient i j k = coefficient i k j ∧
    coefficient i j k = coefficient j i k ∧
    coefficient i j k = coefficient j k i ∧
    coefficient i j k = coefficient k i j ∧
    coefficient i j k = coefficient k j i

/-- Coefficients of a potential through cubic order. -/
structure CubicPotentialCoefficients (ι : Type*) where
  linear : ι → ℝ
  quadratic : ι → ι → ℝ
  cubic : ι → ι → ι → ℝ
  quadratic_symmetric : ∀ i j, quadratic i j = quadratic j i
  cubic_fully_symmetric : FullySymmetric3 cubic

/-- Reciprocity of the constant Jacobian of the Euler source. -/
def LinearReciprocity {ι : Type*}
    (euler : QuadraticEulerCoefficients ι) : Prop :=
  ∀ i j, euler.linear i j = euler.linear j i

/--
The quadratic Helmholtz swap exchanges the Euler-component index with the
first field index.  Symmetry of the two field indices is already part of the
Euler coefficient data.
-/
def QuadraticHelmholtzSwap {ι : Type*}
    (euler : QuadraticEulerCoefficients ι) : Prop :=
  ∀ i j k, euler.quadratic i j k = euler.quadratic j i k

/--
Coefficient-level formal gradient relation.  The factors `1/2` and `1/6` in
the normalized finite sums make these three equalities the formal derivative
relations.
-/
def IsFormalGradient {ι : Type*}
    (euler : QuadraticEulerCoefficients ι)
    (potential : CubicPotentialCoefficients ι) : Prop :=
  (∀ i, euler.affine i = potential.linear i) ∧
  (∀ i j, euler.linear i j = potential.quadratic i j) ∧
  (∀ i j k, euler.quadratic i j k = potential.cubic i j k)

/-- Field-slot symmetry plus the Helmholtz swap generates all permutations. -/
theorem fully_symmetric_of_field_symmetry_and_helmholtz
    {ι : Type*}
    (coefficient : ι → ι → ι → ℝ)
    (hField : ∀ i j k, coefficient i j k = coefficient i k j)
    (hHelmholtz : ∀ i j k, coefficient i j k = coefficient j i k) :
    FullySymmetric3 coefficient := by
  intro i j k
  refine ⟨hField i j k, hHelmholtz i j k, ?_, ?_, ?_⟩
  · calc
      coefficient i j k = coefficient j i k := hHelmholtz i j k
      _ = coefficient j k i := hField j i k
  · calc
      coefficient i j k = coefficient i k j := hField i j k
      _ = coefficient k i j := hHelmholtz i k j
  · calc
      coefficient i j k = coefficient j k i := by
        rw [hHelmholtz i j k, hField j i k]
      _ = coefficient k j i := hHelmholtz j k i

/-- Canonical potential coefficients reconstructed from a Helmholtz source. -/
def reconstructedPotential {ι : Type*}
    (euler : QuadraticEulerCoefficients ι)
    (hLinear : LinearReciprocity euler)
    (hQuadratic : QuadraticHelmholtzSwap euler) :
    CubicPotentialCoefficients ι where
  linear := euler.affine
  quadratic := euler.linear
  cubic := euler.quadratic
  quadratic_symmetric := hLinear
  cubic_fully_symmetric :=
    fully_symmetric_of_field_symmetry_and_helmholtz
      euler.quadratic euler.quadratic_field_symmetric hQuadratic

/-- The canonical reconstruction has exactly the requested gradient data. -/
theorem reconstructed_is_formal_gradient
    {ι : Type*}
    (euler : QuadraticEulerCoefficients ι)
    (hLinear : LinearReciprocity euler)
    (hQuadratic : QuadraticHelmholtzSwap euler) :
    IsFormalGradient euler
      (reconstructedPotential euler hLinear hQuadratic) := by
  exact ⟨fun _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl⟩

/-- Every formal gradient satisfies both coefficient Helmholtz conditions. -/
theorem formal_gradient_implies_helmholtz
    {ι : Type*}
    (euler : QuadraticEulerCoefficients ι)
    (potential : CubicPotentialCoefficients ι)
    (hGradient : IsFormalGradient euler potential) :
    LinearReciprocity euler ∧ QuadraticHelmholtzSwap euler := by
  rcases hGradient with ⟨_, hLinear, hQuadratic⟩
  constructor
  · intro i j
    calc
      euler.linear i j = potential.quadratic i j := hLinear i j
      _ = potential.quadratic j i := potential.quadratic_symmetric i j
      _ = euler.linear j i := (hLinear j i).symm
  · intro i j k
    calc
      euler.quadratic i j k = potential.cubic i j k := hQuadratic i j k
      _ = potential.cubic j i k :=
        (potential.cubic_fully_symmetric i j k).2.1
      _ = euler.quadratic j i k := (hQuadratic j i k).symm

/--
Finite-index, coefficient-level polynomial Helmholtz classification through
cubic potential order.  This theorem does not assert nonlinear Janus
variational cohomology or global field-space reconstruction.
-/
theorem finite_rank_polynomial_helmholtz_iff
    {ι : Type*} [Fintype ι]
    (euler : QuadraticEulerCoefficients ι) :
    (∃ potential : CubicPotentialCoefficients ι,
      IsFormalGradient euler potential) ↔
      LinearReciprocity euler ∧ QuadraticHelmholtzSwap euler := by
  constructor
  · rintro ⟨potential, hGradient⟩
    exact formal_gradient_implies_helmholtz euler potential hGradient
  · rintro ⟨hLinear, hQuadratic⟩
    exact ⟨reconstructedPotential euler hLinear hQuadratic,
      reconstructed_is_formal_gradient euler hLinear hQuadratic⟩

/-- Normalized finite-sum evaluation of a quadratic Euler source. -/
noncomputable def eulerValue {ι : Type*} [Fintype ι]
    (euler : QuadraticEulerCoefficients ι)
    (x : ι → ℝ)
    (i : ι) : ℝ :=
  euler.affine i +
    ∑ j, euler.linear i j * x j +
    (1 / 2 : ℝ) * ∑ j, ∑ k, euler.quadratic i j k * x j * x k

/-- The actual finite-dimensional Euler map assembled from its components. -/
noncomputable def eulerVector {ι : Type*} [Fintype ι]
    (euler : QuadraticEulerCoefficients ι) :
    (ι → ℝ) → (ι → ℝ) :=
  fun x i => eulerValue euler x i

@[simp]
theorem eulerVector_apply
    {ι : Type*} [Fintype ι]
    (euler : QuadraticEulerCoefficients ι)
    (x : ι → ℝ)
    (i : ι) :
    eulerVector euler x i = eulerValue euler x i := rfl

/-- Matrix coefficient of the Jacobian of the quadratic Euler map. -/
noncomputable def eulerJacobianCoefficient
    {ι : Type*} [Fintype ι]
    (euler : QuadraticEulerCoefficients ι)
    (x : ι → ℝ)
    (i j : ι) : ℝ :=
  euler.linear i j + ∑ k, euler.quadratic i j k * x k

/-- The Jacobian as an actual continuous linear operator on field space. -/
noncomputable def eulerJacobian
    {ι : Type*} [Fintype ι]
    (euler : QuadraticEulerCoefficients ι)
    (x : ι → ℝ) :
    (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  ContinuousLinearMap.pi fun i =>
    ∑ j, (eulerJacobianCoefficient euler x i j) •
      (ContinuousLinearMap.proj j : (ι → ℝ) →L[ℝ] ℝ)

@[simp]
theorem eulerJacobian_apply
    {ι : Type*} [Fintype ι]
    (euler : QuadraticEulerCoefficients ι)
    (x direction : ι → ℝ)
    (i : ι) :
    eulerJacobian euler x direction i =
      ∑ j, eulerJacobianCoefficient euler x i j * direction j := by
  simp [eulerJacobian, smul_eq_mul]

/-- The unsimplified product-rule derivative of one Euler component. -/
noncomputable def eulerComponentDerivativeRaw
    {ι : Type*} [Fintype ι]
    (euler : QuadraticEulerCoefficients ι)
    (x : ι → ℝ)
    (i : ι) :
    (ι → ℝ) →L[ℝ] ℝ :=
  (∑ j, euler.linear i j •
      (ContinuousLinearMap.proj j : (ι → ℝ) →L[ℝ] ℝ)) +
    (1 / 2 : ℝ) •
      (∑ j, ∑ k, (
        (euler.quadratic i j k * x j) •
            (ContinuousLinearMap.proj k : (ι → ℝ) →L[ℝ] ℝ) +
          (euler.quadratic i j k * x k) •
            (ContinuousLinearMap.proj j : (ι → ℝ) →L[ℝ] ℝ)))

/-- Product-rule derivative of one normalized Euler component. -/
theorem eulerValue_hasFDerivAt_raw
    {ι : Type*} [Fintype ι]
    (euler : QuadraticEulerCoefficients ι)
    (x : ι → ℝ)
    (i : ι) :
    HasFDerivAt (fun y : ι → ℝ => eulerValue euler y i)
      (eulerComponentDerivativeRaw euler x i) x := by
  let coordinate (j : ι) : (ι → ℝ) →L[ℝ] ℝ :=
    ContinuousLinearMap.proj j
  have hCoordinate (j : ι) :
      HasFDerivAt (fun y : ι → ℝ => y j) (coordinate j) x := by
    exact (coordinate j).hasFDerivAt
  have hLinear :
      HasFDerivAt
        (fun y : ι → ℝ => ∑ j, euler.linear i j * y j)
        (∑ j, euler.linear i j • coordinate j) x := by
    apply HasFDerivAt.fun_sum
    intro j _
    exact (hCoordinate j).const_mul (euler.linear i j)
  have hQuadratic :
      HasFDerivAt
        (fun y : ι → ℝ =>
          ∑ j, ∑ k, euler.quadratic i j k * y j * y k)
        (∑ j, ∑ k, (
          (euler.quadratic i j k * x j) • coordinate k +
            (euler.quadratic i j k * x k) • coordinate j)) x := by
    apply HasFDerivAt.fun_sum
    intro j _
    apply HasFDerivAt.fun_sum
    intro k _
    convert ((hCoordinate j).const_mul
      (euler.quadratic i j k)).mul (hCoordinate k) using 1
    all_goals
      ext direction
      simp [coordinate]
      try ring
  have hCombined :=
    (hLinear.add (hQuadratic.const_mul (1 / 2 : ℝ))).const_add
      (euler.affine i)
  simpa [eulerValue, eulerComponentDerivativeRaw, coordinate,
    add_assoc] using hCombined

/-- Field-slot symmetry collapses the raw derivative to the Jacobian row. -/
theorem eulerComponentDerivativeRaw_eq_jacobian_row
    {ι : Type*} [Fintype ι]
    (euler : QuadraticEulerCoefficients ι)
    (x : ι → ℝ)
    (i : ι) :
    eulerComponentDerivativeRaw euler x i =
      ∑ j, (eulerJacobianCoefficient euler x i j) •
        (ContinuousLinearMap.proj j : (ι → ℝ) →L[ℝ] ℝ) := by
  classical
  ext direction
  have hSwap :
      (∑ j, ∑ k,
        euler.quadratic i j k * x j * direction k) =
        ∑ j, ∑ k,
          euler.quadratic i j k * x k * direction j := by
    calc
      (∑ j, ∑ k,
          euler.quadratic i j k * x j * direction k) =
          ∑ j, ∑ k,
            euler.quadratic i k j * x j * direction k := by
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro k _
        rw [euler.quadratic_field_symmetric i j k]
      _ = ∑ j, ∑ k,
          euler.quadratic i j k * x k * direction j := by
        rw [Finset.sum_comm]
  simp [eulerComponentDerivativeRaw, eulerJacobianCoefficient,
    Finset.sum_add_distrib, smul_eq_mul]
  rw [hSwap]
  have hHalf :
      (2 : ℝ)⁻¹ * (∑ j, ∑ k,
          euler.quadratic i j k * x k * direction j) +
        (2 : ℝ)⁻¹ * (∑ j, ∑ k,
          euler.quadratic i j k * x k * direction j) =
        ∑ j, ∑ k,
          euler.quadratic i j k * x k * direction j := by
    ring
  rw [hHalf]
  simp only [add_mul, Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_mul]

/-- Each Euler component has the corresponding Jacobian row as its actual
Fréchet derivative. -/
theorem eulerValue_hasFDerivAt
    {ι : Type*} [Fintype ι]
    (euler : QuadraticEulerCoefficients ι)
    (x : ι → ℝ)
    (i : ι) :
    HasFDerivAt (fun y : ι → ℝ => eulerValue euler y i)
      (∑ j, (eulerJacobianCoefficient euler x i j) •
        (ContinuousLinearMap.proj j : (ι → ℝ) →L[ℝ] ℝ)) x :=
  (eulerValue_hasFDerivAt_raw euler x i).congr_fderiv
    (eulerComponentDerivativeRaw_eq_jacobian_row euler x i)

/-- The actual Euler vector has the stated Jacobian as its Fréchet
derivative. -/
theorem eulerVector_hasFDerivAt
    {ι : Type*} [Fintype ι]
    (euler : QuadraticEulerCoefficients ι)
    (x : ι → ℝ) :
    HasFDerivAt (eulerVector euler) (eulerJacobian euler x) x := by
  unfold eulerVector eulerJacobian
  rw [hasFDerivAt_pi]
  intro i
  exact eulerValue_hasFDerivAt euler x i

/-- Exact `fderiv` formula for the actual quadratic Euler map. -/
theorem eulerVector_fderiv
    {ι : Type*} [Fintype ι]
    (euler : QuadraticEulerCoefficients ι)
    (x : ι → ℝ) :
    fderiv ℝ (eulerVector euler) x = eulerJacobian euler x :=
  (eulerVector_hasFDerivAt euler x).fderiv

/-- The coefficient Helmholtz conditions make every Jacobian matrix
symmetric. -/
theorem eulerJacobianCoefficient_symmetric
    {ι : Type*} [Fintype ι]
    (euler : QuadraticEulerCoefficients ι)
    (hLinear : LinearReciprocity euler)
    (hQuadratic : QuadraticHelmholtzSwap euler)
    (x : ι → ℝ)
    (i j : ι) :
    eulerJacobianCoefficient euler x i j =
      eulerJacobianCoefficient euler x j i := by
  unfold eulerJacobianCoefficient
  rw [hLinear i j]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [hQuadratic i j k]

/-- Coefficient Helmholtz symmetry implies pairing-level self-adjointness of
the actual Jacobian at every field value. -/
theorem eulerJacobian_pairing_self_adjoint
    {ι : Type*} [Fintype ι]
    (euler : QuadraticEulerCoefficients ι)
    (hLinear : LinearReciprocity euler)
    (hQuadratic : QuadraticHelmholtzSwap euler)
    (x left right : ι → ℝ) :
    (∑ i, eulerJacobian euler x left i * right i) =
      ∑ i, left i * eulerJacobian euler x right i := by
  simp only [eulerJacobian_apply]
  calc
    (∑ i, (∑ j,
        eulerJacobianCoefficient euler x i j * left j) * right i) =
        ∑ i, ∑ j,
          eulerJacobianCoefficient euler x i j * left j * right i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_mul]
    _ = ∑ i, ∑ j,
        eulerJacobianCoefficient euler x j i * left j * right i := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [eulerJacobianCoefficient_symmetric euler hLinear hQuadratic x i j]
    _ = ∑ i, ∑ j,
        left i * (eulerJacobianCoefficient euler x i j * right j) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = ∑ i, left i *
        (∑ j, eulerJacobianCoefficient euler x i j * right j) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]

/-- The actual derivative of the Euler vector is self-adjoint in the standard
finite coordinate pairing under the coefficient Helmholtz conditions. -/
theorem eulerVector_fderiv_pairing_self_adjoint
    {ι : Type*} [Fintype ι]
    (euler : QuadraticEulerCoefficients ι)
    (hLinear : LinearReciprocity euler)
    (hQuadratic : QuadraticHelmholtzSwap euler)
    (x left right : ι → ℝ) :
    (∑ i, (fderiv ℝ (eulerVector euler) x) left i * right i) =
      ∑ i, left i * (fderiv ℝ (eulerVector euler) x) right i := by
  rw [eulerVector_fderiv]
  exact eulerJacobian_pairing_self_adjoint
    euler hLinear hQuadratic x left right

/-- Actual finite-dimensional Helmholtz condition: the genuine Jacobian of
the Euler vector is self-adjoint in the standard coordinate pairing at every
field value. -/
def ActualFiniteHelmholtz
    {ι : Type*} [Fintype ι]
    (euler : QuadraticEulerCoefficients ι) : Prop :=
  ∀ x left right : ι → ℝ,
    (∑ i, (fderiv ℝ (eulerVector euler) x) left i * right i) =
      ∑ i, left i * (fderiv ℝ (eulerVector euler) x) right i

/-- Pairing-level self-adjointness recovers symmetry of every displayed
Jacobian coefficient by testing coordinate basis vectors. -/
theorem actual_finite_helmholtz_implies_jacobian_coefficient_symmetric
    {ι : Type*} [Fintype ι]
    (euler : QuadraticEulerCoefficients ι)
    (hActual : ActualFiniteHelmholtz euler)
    (x : ι → ℝ) (i j : ι) :
    eulerJacobianCoefficient euler x i j =
      eulerJacobianCoefficient euler x j i := by
  classical
  let basis (index : ι) : ι → ℝ :=
    fun coordinate => if coordinate = index then 1 else 0
  have hPairing := hActual x (basis j) (basis i)
  simpa [eulerVector_fderiv, eulerJacobian_apply, basis] using hPairing

/-- For a finite quadratic Euler family, self-adjointness of the actual
Jacobian at every field value is exactly the pair of coefficient Helmholtz
conditions. -/
theorem actual_finite_helmholtz_iff_coefficient_helmholtz
    {ι : Type*} [Fintype ι]
    (euler : QuadraticEulerCoefficients ι) :
    ActualFiniteHelmholtz euler ↔
      LinearReciprocity euler ∧ QuadraticHelmholtzSwap euler := by
  classical
  constructor
  · intro hActual
    have hJacobian :=
      actual_finite_helmholtz_implies_jacobian_coefficient_symmetric
        euler hActual
    have hLinear : LinearReciprocity euler := by
      intro i j
      simpa [eulerJacobianCoefficient] using
        hJacobian (0 : ι → ℝ) i j
    refine ⟨hLinear, ?_⟩
    intro i j k
    have hAtBasis := hJacobian
      (fun coordinate => if coordinate = k then (1 : ℝ) else 0) i j
    simp [eulerJacobianCoefficient] at hAtBasis
    rw [hLinear i j] at hAtBasis
    linarith
  · rintro ⟨hLinear, hQuadratic⟩
    intro x left right
    exact eulerVector_fderiv_pairing_self_adjoint
      euler hLinear hQuadratic x left right

/-- Normalized finite-sum value of a potential through cubic order. -/
noncomputable def potentialValue {ι : Type*} [Fintype ι]
    (potential : CubicPotentialCoefficients ι)
    (x : ι → ℝ) : ℝ :=
  (∑ i, potential.linear i * x i) +
    (1 / 2 : ℝ) *
      ∑ i, ∑ j, potential.quadratic i j * x i * x j +
    (1 / 6 : ℝ) *
      ∑ i, ∑ j, ∑ k, potential.cubic i j k * x i * x j * x k

/-- Coefficientwise formal gradient of the normalized potential sum. -/
noncomputable def formalGradientValue {ι : Type*} [Fintype ι]
    (potential : CubicPotentialCoefficients ι)
    (x : ι → ℝ)
    (i : ι) : ℝ :=
  potential.linear i +
    ∑ j, potential.quadratic i j * x j +
    (1 / 2 : ℝ) * ∑ j, ∑ k, potential.cubic i j k * x j * x k

/-- Coefficient agreement gives equality of all normalized finite sums. -/
theorem eulerValue_eq_formalGradientValue
    {ι : Type*} [Fintype ι]
    (euler : QuadraticEulerCoefficients ι)
    (potential : CubicPotentialCoefficients ι)
    (hGradient : IsFormalGradient euler potential)
    (x : ι → ℝ)
    (i : ι) :
    eulerValue euler x i = formalGradientValue potential x i := by
  rcases hGradient with ⟨hAffine, hLinear, hQuadratic⟩
  simp only [eulerValue, formalGradientValue, hAffine, hLinear, hQuadratic]

/-- The reconstructed potential agrees with the Euler family at every point. -/
theorem reconstructed_gradient_agreement
    {ι : Type*} [Fintype ι]
    (euler : QuadraticEulerCoefficients ι)
    (hLinear : LinearReciprocity euler)
    (hQuadratic : QuadraticHelmholtzSwap euler)
    (x : ι → ℝ)
    (i : ι) :
    eulerValue euler x i =
      formalGradientValue (reconstructedPotential euler hLinear hQuadratic) x i := by
  exact eulerValue_eq_formalGradientValue euler
    (reconstructedPotential euler hLinear hQuadratic)
    (reconstructed_is_formal_gradient euler hLinear hQuadratic) x i

/-- The continuous linear functional represented by the formal gradient. -/
noncomputable def formalGradientFunctional
    {ι : Type*} [Fintype ι]
    (potential : CubicPotentialCoefficients ι)
    (x : ι → ℝ) : (ι → ℝ) →L[ℝ] ℝ :=
  ∑ i, formalGradientValue potential x i •
    (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ)

/-- Evaluation of the formal-gradient functional is the expected pairing. -/
theorem formalGradientFunctional_apply
    {ι : Type*} [Fintype ι]
    (potential : CubicPotentialCoefficients ι)
    (x direction : ι → ℝ) :
    formalGradientFunctional potential x direction =
      ∑ i, formalGradientValue potential x i * direction i := by
  simp [formalGradientFunctional]

/-- Continuous linear functional represented by the original Euler vector in
the standard finite coordinate pairing. -/
noncomputable def eulerGradientFunctional
    {ι : Type*} [Fintype ι]
    (euler : QuadraticEulerCoefficients ι)
    (x : ι → ℝ) : (ι → ℝ) →L[ℝ] ℝ :=
  ∑ i, eulerValue euler x i •
    (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ)

@[simp]
theorem eulerGradientFunctional_apply
    {ι : Type*} [Fintype ι]
    (euler : QuadraticEulerCoefficients ι)
    (x direction : ι → ℝ) :
    eulerGradientFunctional euler x direction =
      ∑ i, eulerValue euler x i * direction i := by
  simp [eulerGradientFunctional]

/-- Formal coefficient agreement identifies the polynomial gradient
functional with the functional represented by the Euler vector. -/
theorem formalGradientFunctional_eq_eulerGradientFunctional
    {ι : Type*} [Fintype ι]
    (euler : QuadraticEulerCoefficients ι)
    (potential : CubicPotentialCoefficients ι)
    (hGradient : IsFormalGradient euler potential)
    (x : ι → ℝ) :
    formalGradientFunctional potential x =
      eulerGradientFunctional euler x := by
  ext direction
  rw [formalGradientFunctional_apply, eulerGradientFunctional_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [eulerValue_eq_formalGradientValue euler potential hGradient x i]

/-- Raw product-rule derivative of the normalized polynomial potential. -/
noncomputable def potentialDerivativeRaw
    {ι : Type*} [Fintype ι]
    (potential : CubicPotentialCoefficients ι)
    (x : ι → ℝ) : (ι → ℝ) →L[ℝ] ℝ :=
  (∑ i, potential.linear i •
      (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ)) +
    (1 / 2 : ℝ) •
      (∑ i, ∑ j, (
        (potential.quadratic i j * x i) •
            (ContinuousLinearMap.proj j : (ι → ℝ) →L[ℝ] ℝ) +
          (potential.quadratic i j * x j) •
            (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ))) +
    (1 / 6 : ℝ) •
      (∑ i, ∑ j, ∑ k, (
        (potential.cubic i j k * x i * x j) •
            (ContinuousLinearMap.proj k : (ι → ℝ) →L[ℝ] ℝ) +
          (potential.cubic i j k * x i * x k) •
            (ContinuousLinearMap.proj j : (ι → ℝ) →L[ℝ] ℝ) +
          (potential.cubic i j k * x j * x k) •
            (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ)))

/-- The raw product-rule expression is the Fréchet derivative. -/
theorem potentialValue_hasFDerivAt_raw
    {ι : Type*} [Fintype ι]
    (potential : CubicPotentialCoefficients ι)
    (x : ι → ℝ) :
    HasFDerivAt (potentialValue potential)
      (potentialDerivativeRaw potential x) x := by
  let coordinate (i : ι) : (ι → ℝ) →L[ℝ] ℝ :=
    ContinuousLinearMap.proj i
  have hCoordinate (i : ι) :
      HasFDerivAt (fun y : ι → ℝ => y i) (coordinate i) x := by
    exact (coordinate i).hasFDerivAt
  have hLinear :
      HasFDerivAt
        (fun y : ι → ℝ => ∑ i, potential.linear i * y i)
        (∑ i, potential.linear i • coordinate i) x := by
    apply HasFDerivAt.fun_sum
    intro i _
    exact (hCoordinate i).const_mul (potential.linear i)
  have hQuadratic :
      HasFDerivAt
        (fun y : ι → ℝ =>
          ∑ i, ∑ j, potential.quadratic i j * y i * y j)
        (∑ i, ∑ j, (
          (potential.quadratic i j * x i) • coordinate j +
            (potential.quadratic i j * x j) • coordinate i)) x := by
    apply HasFDerivAt.fun_sum
    intro i _
    apply HasFDerivAt.fun_sum
    intro j _
    convert ((hCoordinate i).const_mul (potential.quadratic i j)).mul
      (hCoordinate j) using 1
    all_goals
      ext direction
      simp [coordinate]
      try ring
  have hCubic :
      HasFDerivAt
        (fun y : ι → ℝ =>
          ∑ i, ∑ j, ∑ k, potential.cubic i j k * y i * y j * y k)
        (∑ i, ∑ j, ∑ k, (
          (potential.cubic i j k * x i * x j) • coordinate k +
            (potential.cubic i j k * x i * x k) • coordinate j +
            (potential.cubic i j k * x j * x k) • coordinate i)) x := by
    apply HasFDerivAt.fun_sum
    intro i _
    apply HasFDerivAt.fun_sum
    intro j _
    apply HasFDerivAt.fun_sum
    intro k _
    convert (((hCoordinate i).const_mul (potential.cubic i j k)).mul
      (hCoordinate j)).mul (hCoordinate k) using 1
    all_goals
      ext direction
      simp [coordinate]
      try ring
  have hCombined :=
    (hLinear.add (hQuadratic.const_mul (1 / 2 : ℝ))).add
      (hCubic.const_mul (1 / 6 : ℝ))
  have hMap :
      (∑ i, potential.linear i • coordinate i) +
          (1 / 2 : ℝ) •
            (∑ i, ∑ j, (
              (potential.quadratic i j * x i) • coordinate j +
                (potential.quadratic i j * x j) • coordinate i)) +
        (1 / 6 : ℝ) •
          (∑ i, ∑ j, ∑ k, (
            (potential.cubic i j k * x i * x j) • coordinate k +
              (potential.cubic i j k * x i * x k) • coordinate j +
              (potential.cubic i j k * x j * x k) • coordinate i)) =
        potentialDerivativeRaw potential x := by
    rfl
  apply (hCombined.congr_fderiv hMap).congr_of_eventuallyEq
  filter_upwards with y
  rfl

/-- Symmetry collapses the raw product-rule derivative to the formal gradient. -/
theorem potentialDerivativeRaw_eq_formalGradientFunctional
    {ι : Type*} [Fintype ι]
    (potential : CubicPotentialCoefficients ι)
    (x : ι → ℝ) :
    potentialDerivativeRaw potential x =
      formalGradientFunctional potential x := by
  classical
  ext direction
  have hQuadratic :
      (∑ i, ∑ j, potential.quadratic i j * x i * direction j) =
        ∑ i, ∑ j, potential.quadratic i j * x j * direction i := by
    calc
      (∑ i, ∑ j, potential.quadratic i j * x i * direction j) =
          ∑ i, ∑ j, potential.quadratic j i * x i * direction j := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [potential.quadratic_symmetric i j]
      _ = ∑ i, ∑ j, potential.quadratic i j * x j * direction i := by
        rw [Finset.sum_comm]
  have hCubicFirst :
      (∑ i, ∑ j, ∑ k,
        potential.cubic i j k * x i * x j * direction k) =
        ∑ i, ∑ j, ∑ k,
          potential.cubic i j k * x j * x k * direction i := by
    calc
      (∑ i, ∑ j, ∑ k,
          potential.cubic i j k * x i * x j * direction k) =
          ∑ i, ∑ j, ∑ k,
            potential.cubic k i j * x i * x j * direction k := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro k _
        rw [(potential.cubic_fully_symmetric i j k).2.2.2.1]
      _ = ∑ i, ∑ j, ∑ k,
          potential.cubic i j k * x j * x k * direction i := by
        calc
          (∑ i, ∑ j, ∑ k,
              potential.cubic k i j * x i * x j * direction k) =
              ∑ i, ∑ k, ∑ j,
                potential.cubic k i j * x i * x j * direction k := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.sum_comm]
          _ = ∑ k, ∑ i, ∑ j,
              potential.cubic k i j * x i * x j * direction k := by
            rw [Finset.sum_comm]
          _ = ∑ i, ∑ j, ∑ k,
              potential.cubic i j k * x j * x k * direction i := by
            rfl
  have hCubicSecond :
      (∑ i, ∑ j, ∑ k,
        potential.cubic i j k * x i * x k * direction j) =
        ∑ i, ∑ j, ∑ k,
          potential.cubic i j k * x j * x k * direction i := by
    calc
      (∑ i, ∑ j, ∑ k,
          potential.cubic i j k * x i * x k * direction j) =
          ∑ i, ∑ j, ∑ k,
            potential.cubic j i k * x i * x k * direction j := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro k _
        rw [(potential.cubic_fully_symmetric i j k).2.1]
      _ = ∑ i, ∑ j, ∑ k,
          potential.cubic i j k * x j * x k * direction i := by
        rw [Finset.sum_comm]
  have hCubicCollected :
      (∑ i, (∑ j, ∑ k, potential.cubic i j k * x j * x k) *
        direction i) =
        ∑ i, ∑ j, ∑ k,
          potential.cubic i j k * x j * x k * direction i := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_mul]
  have hCubicCollectedHalf :
      (∑ i, ((1 / 2 : ℝ) *
        ∑ j, ∑ k, potential.cubic i j k * x j * x k) * direction i) =
        (1 / 2 : ℝ) *
          ∑ i, ∑ j, ∑ k,
            potential.cubic i j k * x j * x k * direction i := by
    calc
      (∑ i, ((1 / 2 : ℝ) *
          ∑ j, ∑ k, potential.cubic i j k * x j * x k) * direction i) =
          ∑ i, (1 / 2 : ℝ) *
            ((∑ j, ∑ k, potential.cubic i j k * x j * x k) *
              direction i) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = (1 / 2 : ℝ) *
          ∑ i, (∑ j, ∑ k, potential.cubic i j k * x j * x k) *
            direction i := by
        rw [Finset.mul_sum]
      _ = (1 / 2 : ℝ) *
          ∑ i, ∑ j, ∑ k,
            potential.cubic i j k * x j * x k * direction i := by
        rw [hCubicCollected]
  simp only [one_div] at hCubicCollectedHalf
  simp [potentialDerivativeRaw, formalGradientFunctional,
    formalGradientValue, Finset.sum_add_distrib, add_mul, Finset.sum_mul]
  rw [hQuadratic, hCubicFirst, hCubicSecond]
  rw [hCubicCollectedHalf]
  ring

/-- The normalized polynomial potential has its formal gradient as its actual
Fréchet derivative. -/
theorem potentialValue_hasFDerivAt
    {ι : Type*} [Fintype ι]
    (potential : CubicPotentialCoefficients ι)
    (x : ι → ℝ) :
    HasFDerivAt (potentialValue potential)
      (formalGradientFunctional potential x) x :=
  (potentialValue_hasFDerivAt_raw potential x).congr_fderiv
    (potentialDerivativeRaw_eq_formalGradientFunctional potential x)

/-- Exact `fderiv` formula for the normalized finite-dimensional potential. -/
theorem potentialValue_fderiv
    {ι : Type*} [Fintype ι]
    (potential : CubicPotentialCoefficients ι)
    (x : ι → ℝ) :
    fderiv ℝ (potentialValue potential) x =
      formalGradientFunctional potential x :=
  (potentialValue_hasFDerivAt potential x).fderiv

/-- In every direction, the actual derivative of the reconstructed potential
is the pairing with the original Euler source. -/
theorem reconstructed_potential_fderiv_apply
    {ι : Type*} [Fintype ι]
    (euler : QuadraticEulerCoefficients ι)
    (hLinear : LinearReciprocity euler)
    (hQuadratic : QuadraticHelmholtzSwap euler)
    (x direction : ι → ℝ) :
    (fderiv ℝ
      (potentialValue (reconstructedPotential euler hLinear hQuadratic)) x)
        direction =
      ∑ i, eulerValue euler x i * direction i := by
  rw [potentialValue_fderiv, formalGradientFunctional_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [← reconstructed_gradient_agreement euler hLinear hQuadratic x i]

/-- Equality with the prescribed actual derivative determines every component
of the polynomial gradient. -/
theorem eulerValue_eq_formalGradientValue_of_hasFDerivAt
    {ι : Type*} [Fintype ι]
    (euler : QuadraticEulerCoefficients ι)
    (potential : CubicPotentialCoefficients ι)
    (hDerivative : ∀ x : ι → ℝ,
      HasFDerivAt (potentialValue potential)
        (eulerGradientFunctional euler x) x)
    (x : ι → ℝ) (i : ι) :
    eulerValue euler x i = formalGradientValue potential x i := by
  classical
  let basis : ι → ℝ := fun coordinate => if coordinate = i then 1 else 0
  have hMaps :
      formalGradientFunctional potential x =
        eulerGradientFunctional euler x := by
    calc
      formalGradientFunctional potential x =
          fderiv ℝ (potentialValue potential) x :=
        (potentialValue_fderiv potential x).symm
      _ = eulerGradientFunctional euler x := (hDerivative x).fderiv
  have hEvaluation := congrArg (fun functional => functional basis) hMaps
  simpa [formalGradientFunctional_apply, eulerGradientFunctional_apply,
    basis] using hEvaluation.symm

/-- A normalized cubic potential whose genuine derivative is the Euler
pairing functional everywhere necessarily has the matching formal
coefficients. -/
theorem hasFDerivAt_eulerGradientFunctional_implies_formal_gradient
    {ι : Type*} [Fintype ι]
    (euler : QuadraticEulerCoefficients ι)
    (potential : CubicPotentialCoefficients ι)
    (hDerivative : ∀ x : ι → ℝ,
      HasFDerivAt (potentialValue potential)
        (eulerGradientFunctional euler x) x) :
    IsFormalGradient euler potential := by
  classical
  let basis (index : ι) : ι → ℝ :=
    fun coordinate => if coordinate = index then 1 else 0
  have hValue (x : ι → ℝ) (i : ι) :=
    eulerValue_eq_formalGradientValue_of_hasFDerivAt
      euler potential hDerivative x i
  have hAffine : ∀ i, euler.affine i = potential.linear i := by
    intro i
    simpa [eulerValue, formalGradientValue] using
      hValue (0 : ι → ℝ) i
  have hLinear : ∀ i j, euler.linear i j = potential.quadratic i j := by
    intro i j
    have hPositive := hValue (basis j) i
    have hNegative := hValue (fun coordinate => -basis j coordinate) i
    simp [eulerValue, formalGradientValue, basis] at hPositive hNegative
    linarith
  refine ⟨hAffine, hLinear, ?_⟩
  intro i j k
  by_cases hIndices : j = k
  · subst k
    have hPositive := hValue (basis j) i
    have hNegative := hValue (fun coordinate => -basis j coordinate) i
    have hZero := hValue (0 : ι → ℝ) i
    simp [eulerValue, formalGradientValue, basis] at hPositive hNegative hZero
    linarith
  · have hSum := hValue (fun coordinate =>
        basis j coordinate + basis k coordinate) i
    have hFirst := hValue (basis j) i
    have hSecond := hValue (basis k) i
    have hZero := hValue (0 : ι → ℝ) i
    simp [eulerValue, formalGradientValue, basis] at hFirst hSecond hZero
    simp only [eulerValue, formalGradientValue] at hSum
    simp_rw [mul_add, add_mul, Finset.sum_add_distrib] at hSum
    simp [basis] at hSum
    rw [euler.quadratic_field_symmetric i k j] at hSum
    rw [(potential.cubic_fully_symmetric i k j).1] at hSum
    linarith

/-- A finite polynomial potential is an actual gradient realization of the
Euler family when its genuine Fréchet derivative is the Euler pairing
functional at every field value. -/
def IsActualPolynomialGradient
    {ι : Type*} [Fintype ι]
    (euler : QuadraticEulerCoefficients ι)
    (potential : CubicPotentialCoefficients ι) : Prop :=
  ∀ x : ι → ℝ,
    HasFDerivAt (potentialValue potential)
      (eulerGradientFunctional euler x) x

/-- Formal gradient coefficient agreement upgrades to a verified actual
Fréchet-gradient realization for the normalized polynomial potential. -/
theorem formal_gradient_is_actual_polynomial_gradient
    {ι : Type*} [Fintype ι]
    (euler : QuadraticEulerCoefficients ι)
    (potential : CubicPotentialCoefficients ι)
    (hGradient : IsFormalGradient euler potential) :
    IsActualPolynomialGradient euler potential := by
  intro x
  exact (potentialValue_hasFDerivAt potential x).congr_fderiv
    (formalGradientFunctional_eq_eulerGradientFunctional
      euler potential hGradient x)

/-- Exact finite-rank actual Helmholtz theorem: self-adjointness of the true
Euler Jacobian is equivalent to realization by a normalized cubic polynomial
whose true Fréchet derivative is the Euler pairing functional. -/
theorem actual_finite_helmholtz_iff_actual_polynomial_gradient
    {ι : Type*} [Fintype ι]
    (euler : QuadraticEulerCoefficients ι) :
    ActualFiniteHelmholtz euler ↔
      ∃ potential : CubicPotentialCoefficients ι,
        IsActualPolynomialGradient euler potential := by
  constructor
  · intro hActual
    rcases (actual_finite_helmholtz_iff_coefficient_helmholtz euler).1
      hActual with ⟨hLinear, hQuadratic⟩
    let potential := reconstructedPotential euler hLinear hQuadratic
    refine ⟨potential, ?_⟩
    exact formal_gradient_is_actual_polynomial_gradient
      euler potential
        (reconstructed_is_formal_gradient euler hLinear hQuadratic)
  · rintro ⟨potential, hGradient⟩
    apply (actual_finite_helmholtz_iff_coefficient_helmholtz euler).2
    exact formal_gradient_implies_helmholtz
      euler potential
        (hasFDerivAt_eulerGradientFunctional_implies_formal_gradient
          euler potential hGradient)

/-- Constructive actual-derivative corollary: every finite quadratic Euler
family satisfying the actual Helmholtz condition has a normalized cubic
polynomial primitive with the prescribed genuine derivative everywhere. -/
theorem actual_finite_helmholtz_hasFDerivAt_polynomial_primitive
    {ι : Type*} [Fintype ι]
    (euler : QuadraticEulerCoefficients ι)
    (hActual : ActualFiniteHelmholtz euler) :
    ∃ potential : CubicPotentialCoefficients ι,
      ∀ x : ι → ℝ,
        HasFDerivAt (potentialValue potential)
          (eulerGradientFunctional euler x) x := by
  rcases (actual_finite_helmholtz_iff_actual_polynomial_gradient euler).1
    hActual with ⟨potential, hDerivative⟩
  exact ⟨potential, hDerivative⟩

end P0EFTJanusFiniteRankPolynomialHelmholtz
end JanusFormal
