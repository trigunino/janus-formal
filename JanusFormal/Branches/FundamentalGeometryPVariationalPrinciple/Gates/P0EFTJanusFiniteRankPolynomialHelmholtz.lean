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

end P0EFTJanusFiniteRankPolynomialHelmholtz
end JanusFormal
