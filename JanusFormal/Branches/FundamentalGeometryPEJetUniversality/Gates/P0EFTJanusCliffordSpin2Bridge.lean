import Mathlib.LinearAlgebra.CliffordAlgebra.EvenEquiv
import Mathlib.LinearAlgebra.CliffordAlgebra.Equivs
import Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusCircleSO2Equivalence

namespace JanusFormal
namespace P0EFTJanusCliffordSpin2Bridge

set_option autoImplicit false

noncomputable section

open P0EFTJanusSpin2CircleModel
open P0EFTJanusCircleSO2Equivalence

/-- The negative one-dimensional quadratic form whose Clifford algebra is
canonically the complex numbers. -/
abbrev spin2LineForm : QuadraticForm ℝ ℝ :=
  CliffordAlgebraComplex.Q

/-- The two-dimensional negative Euclidean form produced by the standard
`CliffordAlgebra.equivEven` construction. Explicitly,
`spin2PlaneForm (x,y) = -(x^2+y^2)`. -/
abbrev spin2PlaneForm : QuadraticForm ℝ (ℝ × ℝ) :=
  CliffordAlgebra.EquivEven.Q' spin2LineForm

/-- The real Clifford algebra used for the concrete Mathlib `Spin(2)` model. -/
abbrev Spin2Clifford := CliffordAlgebra spin2PlaneForm

/-- Mathlib's even unitary Lipschitz definition of `Spin(2)` for the negative
Euclidean plane. -/
abbrev CliffordSpin2 := spinGroup spin2PlaneForm

/-- The even Clifford algebra of the negative Euclidean plane is canonically
isomorphic to `ℂ`: first use the inverse of `equivEven`, then the standard
one-dimensional Clifford/complex equivalence. -/
def spin2EvenEquivComplex :
    CliffordAlgebra.even spin2PlaneForm ≃ₐ[ℝ] ℂ :=
  (CliffordAlgebra.equivEven spin2LineForm).symm.trans
    CliffordAlgebraComplex.equiv

/-- The explicit value of the plane quadratic form. -/
theorem spin2PlaneForm_apply (vector : ℝ × ℝ) :
    spin2PlaneForm vector =
      -(vector.1 * vector.1 + vector.2 * vector.2) := by
  rw [CliffordAlgebra.EquivEven.Q'_apply]
  simp only [CliffordAlgebraComplex.Q_apply]
  ring

/-- Fixed unit vector used to factor every even rotor as a product of two unit
vectors. -/
def referenceUnitVector : ℝ × ℝ := (0, 1)

/-- The second unit vector associated with a circle phase `a+ib`. The product
`ι(0,1) * ι(b,-a)` is the rotor corresponding to that phase. -/
def phaseUnitVector (phase : Circle) : ℝ × ℝ :=
  ((phase : ℂ).im, -((phase : ℂ).re))

@[simp]
theorem spin2PlaneForm_referenceUnitVector :
    spin2PlaneForm referenceUnitVector = -1 := by
  simp [referenceUnitVector]

@[simp]
theorem spin2PlaneForm_phaseUnitVector (phase : Circle) :
    spin2PlaneForm (phaseUnitVector phase) = -1 := by
  have hNormSq := Circle.normSq_coe phase
  rw [spin2PlaneForm_apply]
  simp only [phaseUnitVector, neg_mul, mul_neg]
  simp only [Complex.normSq_apply] at hNormSq
  nlinarith

/-- A vector of quadratic norm `-1` is a unit in the Clifford algebra, with
inverse its negative. -/
def negativeUnitVectorUnit
    (vector : ℝ × ℝ)
    (hNorm : spin2PlaneForm vector = -1) :
    Spin2Cliffordˣ where
  val := CliffordAlgebra.ι spin2PlaneForm vector
  inv := -CliffordAlgebra.ι spin2PlaneForm vector
  val_inv := by
    rw [mul_neg, CliffordAlgebra.ι_sq_scalar, hNorm]
    simp
  inv_val := by
    rw [neg_mul, CliffordAlgebra.ι_sq_scalar, hNorm]
    simp

/-- Every unit vector generator belongs to the Lipschitz group. -/
theorem negativeUnitVectorUnit_mem_lipschitz
    (vector : ℝ × ℝ)
    (hNorm : spin2PlaneForm vector = -1) :
    negativeUnitVectorUnit vector hNorm ∈
      lipschitzGroup spin2PlaneForm := by
  apply Subgroup.subset_closure
  change
    ((negativeUnitVectorUnit vector hNorm : Spin2Clifford)) ∈
      Set.range (CliffordAlgebra.ι spin2PlaneForm)
  exact ⟨vector, rfl⟩

/-- Circle phase transported into the even Clifford algebra. -/
def circleEvenRotor (phase : Circle) :
    CliffordAlgebra.even spin2PlaneForm :=
  spin2EvenEquivComplex.symm (phase : ℂ)

/-- The same rotor written as a product of two Clifford vectors. -/
def phaseEvenProduct (phase : Circle) :
    CliffordAlgebra.even spin2PlaneForm :=
  (CliffordAlgebra.even.ι spin2PlaneForm).bilin
    referenceUnitVector (phaseUnitVector phase)

/-- Under the even-Clifford/complex equivalence, the explicit product rotor is
exactly the original circle phase. -/
theorem spin2EvenEquivComplex_phaseEvenProduct (phase : Circle) :
    spin2EvenEquivComplex (phaseEvenProduct phase) = (phase : ℂ) := by
  change
    CliffordAlgebraComplex.toComplex
      (CliffordAlgebra.ofEven spin2LineForm
        ((CliffordAlgebra.even.ι
          (CliffordAlgebra.EquivEven.Q' spin2LineForm)).bilin
            referenceUnitVector (phaseUnitVector phase))) =
      (phase : ℂ)
  rw [CliffordAlgebra.ofEven_ι]
  apply Complex.ext <;>
    simp [referenceUnitVector, phaseUnitVector,
      CliffordAlgebraComplex.toComplex_ι]

/-- The abstract rotor obtained from the algebra equivalence agrees with the
product of the two unit vectors. -/
theorem circleEvenRotor_eq_phaseEvenProduct (phase : Circle) :
    circleEvenRotor phase = phaseEvenProduct phase := by
  apply spin2EvenEquivComplex.injective
  simp [circleEvenRotor, spin2EvenEquivComplex_phaseEvenProduct]

/-- The product rotor is unitary. -/
theorem phaseEvenProduct_mem_unitary (phase : Circle) :
    (phaseEvenProduct phase : Spin2Clifford) ∈
      unitary Spin2Clifford := by
  rw [Unitary.mem_iff]
  constructor
  · calc
      star (phaseEvenProduct phase : Spin2Clifford) *
          (phaseEvenProduct phase : Spin2Clifford) =
        (CliffordAlgebra.ι spin2PlaneForm (phaseUnitVector phase) *
            CliffordAlgebra.ι spin2PlaneForm referenceUnitVector) *
          (CliffordAlgebra.ι spin2PlaneForm referenceUnitVector *
            CliffordAlgebra.ι spin2PlaneForm (phaseUnitVector phase)) := by
              simp [phaseEvenProduct]
      _ = CliffordAlgebra.ι spin2PlaneForm (phaseUnitVector phase) *
          (CliffordAlgebra.ι spin2PlaneForm referenceUnitVector *
            CliffordAlgebra.ι spin2PlaneForm referenceUnitVector) *
          CliffordAlgebra.ι spin2PlaneForm (phaseUnitVector phase) := by
            simp only [mul_assoc]
      _ = 1 := by
        rw [CliffordAlgebra.ι_sq_scalar,
          spin2PlaneForm_referenceUnitVector,
          CliffordAlgebra.ι_sq_scalar,
          spin2PlaneForm_phaseUnitVector]
        simp
  · calc
      (phaseEvenProduct phase : Spin2Clifford) *
          star (phaseEvenProduct phase : Spin2Clifford) =
        (CliffordAlgebra.ι spin2PlaneForm referenceUnitVector *
            CliffordAlgebra.ι spin2PlaneForm (phaseUnitVector phase)) *
          (CliffordAlgebra.ι spin2PlaneForm (phaseUnitVector phase) *
            CliffordAlgebra.ι spin2PlaneForm referenceUnitVector) := by
              simp [phaseEvenProduct]
      _ = CliffordAlgebra.ι spin2PlaneForm referenceUnitVector *
          (CliffordAlgebra.ι spin2PlaneForm (phaseUnitVector phase) *
            CliffordAlgebra.ι spin2PlaneForm (phaseUnitVector phase)) *
          CliffordAlgebra.ι spin2PlaneForm referenceUnitVector := by
            simp only [mul_assoc]
      _ = 1 := by
        rw [CliffordAlgebra.ι_sq_scalar,
          spin2PlaneForm_phaseUnitVector,
          CliffordAlgebra.ι_sq_scalar,
          spin2PlaneForm_referenceUnitVector]
        simp

/-- The circle rotor belongs to Mathlib's pin group because it is the product of
two vector generators and is unitary. -/
theorem circleEvenRotor_mem_pin (phase : Circle) :
    (circleEvenRotor phase : Spin2Clifford) ∈
      pinGroup spin2PlaneForm := by
  rw [pinGroup.mem_iff]
  constructor
  · rw [circleEvenRotor_eq_phaseEvenProduct]
    change
      (((negativeUnitVectorUnit referenceUnitVector
              spin2PlaneForm_referenceUnitVector) *
            (negativeUnitVectorUnit (phaseUnitVector phase)
              (spin2PlaneForm_phaseUnitVector phase)) : Spin2Cliffordˣ) :
        Spin2Clifford) ∈
          (lipschitzGroup spin2PlaneForm).toSubmonoid.map
            (Units.coeHom Spin2Clifford)
    rw [lipschitzGroup.coe_mem_iff_mem]
    exact Subgroup.mul_mem _
      (negativeUnitVectorUnit_mem_lipschitz referenceUnitVector
        spin2PlaneForm_referenceUnitVector)
      (negativeUnitVectorUnit_mem_lipschitz (phaseUnitVector phase)
        (spin2PlaneForm_phaseUnitVector phase))
  · rw [circleEvenRotor_eq_phaseEvenProduct]
    exact phaseEvenProduct_mem_unitary phase

/-- Circle phase as an actual element of Mathlib's Clifford `spinGroup`. -/
def circleToCliffordSpin2 (phase : Circle) : CliffordSpin2 where
  val := circleEvenRotor phase
  property :=
    ⟨circleEvenRotor_mem_pin phase, (circleEvenRotor phase).property⟩

@[simp]
theorem circleToCliffordSpin2_coe (phase : Circle) :
    (circleToCliffordSpin2 phase : Spin2Clifford) =
      circleEvenRotor phase := by
  rfl

/-- The Clifford rotor construction is multiplicative. -/
def circleToCliffordSpin2Hom : Circle →* CliffordSpin2 where
  toFun := circleToCliffordSpin2
  map_one' := by
    apply Subtype.ext
    change
      ((spin2EvenEquivComplex.symm (1 : ℂ) :
        CliffordAlgebra.even spin2PlaneForm) : Spin2Clifford) = 1
    simp
  map_mul' := by
    intro first second
    apply Subtype.ext
    change
      ((spin2EvenEquivComplex.symm ((first : ℂ) * (second : ℂ)) :
        CliffordAlgebra.even spin2PlaneForm) : Spin2Clifford) =
      ((spin2EvenEquivComplex.symm (first : ℂ) :
          CliffordAlgebra.even spin2PlaneForm) *
        spin2EvenEquivComplex.symm (second : ℂ) :
          CliffordAlgebra.even spin2PlaneForm)
    simp

/-- Extract the complex coordinate of a Clifford spin rotor. -/
def cliffordSpin2Complex (rotor : CliffordSpin2) : ℂ :=
  spin2EvenEquivComplex
    ⟨(rotor : Spin2Clifford), spinGroup.mem_even rotor.property⟩

/-- The Clifford conjugate of an even spin rotor corresponds to complex
conjugation. -/
theorem cliffordSpin2Complex_star (rotor : CliffordSpin2) :
    spin2EvenEquivComplex
      ⟨star (rotor : Spin2Clifford),
        spinGroup.mem_even
          (spinGroup.star_mem rotor.property)⟩ =
      Complex.conj (cliffordSpin2Complex rotor) := by
  let evenRotor : CliffordAlgebra.even spin2PlaneForm :=
    ⟨(rotor : Spin2Clifford),
      spinGroup.mem_even rotor.property⟩
  have hOfEven :
      CliffordAlgebra.ofEven spin2LineForm
          ⟨star (rotor : Spin2Clifford),
            spinGroup.mem_even
              (spinGroup.star_mem rotor.property)⟩ =
        CliffordAlgebra.involute
          (CliffordAlgebra.ofEven spin2LineForm evenRotor) := by
    apply (CliffordAlgebra.equivEven spin2LineForm).injective
    apply Subtype.ext
    rw [AlgEquiv.apply_symm_apply]
    change
      star (rotor : Spin2Clifford) =
        ((CliffordAlgebra.toEven spin2LineForm
          (CliffordAlgebra.involute
            (CliffordAlgebra.ofEven spin2LineForm evenRotor)) :
            CliffordAlgebra.even spin2PlaneForm) : Spin2Clifford)
    rw [CliffordAlgebra.star_def,
      CliffordAlgebra.involute_eq_of_mem_even
        (spinGroup.mem_even rotor.property)]
    symm
    calc
      ((CliffordAlgebra.toEven spin2LineForm
          (CliffordAlgebra.involute
            (CliffordAlgebra.ofEven spin2LineForm evenRotor)) :
          CliffordAlgebra.even spin2PlaneForm) : Spin2Clifford) =
        ((CliffordAlgebra.toEven spin2LineForm
          (CliffordAlgebra.reverse
            (CliffordAlgebra.involute
              (CliffordAlgebra.ofEven spin2LineForm evenRotor))) :
          CliffordAlgebra.even spin2PlaneForm) : Spin2Clifford) := by
            rw [CliffordAlgebraComplex.reverse_apply]
      _ = CliffordAlgebra.reverse (evenRotor : Spin2Clifford) :=
        CliffordAlgebra.coe_toEven_reverse_involute _
      _ = CliffordAlgebra.reverse (rotor : Spin2Clifford) := by
        rfl
  change
    CliffordAlgebraComplex.toComplex
      (CliffordAlgebra.ofEven spin2LineForm
        ⟨star (rotor : Spin2Clifford), _⟩) =
      Complex.conj
        (CliffordAlgebraComplex.toComplex
          (CliffordAlgebra.ofEven spin2LineForm
            ⟨(rotor : Spin2Clifford), _⟩))
  rw [hOfEven, CliffordAlgebraComplex.toComplex_involute]

/-- The complex coordinate of every Clifford spin rotor has norm one. -/
theorem cliffordSpin2Complex_norm (rotor : CliffordSpin2) :
    ‖cliffordSpin2Complex rotor‖ = 1 := by
  let evenRotor : CliffordAlgebra.even spin2PlaneForm :=
    ⟨(rotor : Spin2Clifford),
      spinGroup.mem_even rotor.property⟩
  let starEvenRotor : CliffordAlgebra.even spin2PlaneForm :=
    ⟨star (rotor : Spin2Clifford),
      spinGroup.mem_even
        (spinGroup.star_mem rotor.property)⟩
  have hProduct : starEvenRotor * evenRotor = 1 := by
    apply Subtype.ext
    exact spinGroup.star_mul_self_of_mem rotor.property
  have hComplex := congrArg spin2EvenEquivComplex hProduct
  have hConjMul :
      Complex.conj (cliffordSpin2Complex rotor) *
          cliffordSpin2Complex rotor = 1 := by
    simpa [evenRotor, starEvenRotor, map_mul,
      cliffordSpin2Complex_star] using hComplex
  have hReal := congrArg Complex.re hConjMul
  have hNormSq : Complex.normSq (cliffordSpin2Complex rotor) = 1 := by
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im,
      Complex.one_re] at hReal
    simp only [Complex.normSq_apply]
    nlinarith
  rw [Complex.norm_def, hNormSq]
  norm_num

/-- Inverse map from Mathlib's Clifford spin group to the circle. -/
def cliffordSpin2ToCircle (rotor : CliffordSpin2) : Circle where
  val := cliffordSpin2Complex rotor
  property := mem_sphere_zero_iff_norm.mpr
    (cliffordSpin2Complex_norm rotor)

@[simp]
theorem cliffordSpin2ToCircle_circleToCliffordSpin2 (phase : Circle) :
    cliffordSpin2ToCircle (circleToCliffordSpin2 phase) = phase := by
  apply Circle.ext
  change spin2EvenEquivComplex (spin2EvenEquivComplex.symm (phase : ℂ)) =
    (phase : ℂ)
  simp

@[simp]
theorem circleToCliffordSpin2_cliffordSpin2ToCircle
    (rotor : CliffordSpin2) :
    circleToCliffordSpin2 (cliffordSpin2ToCircle rotor) = rotor := by
  apply Subtype.ext
  let evenRotor : CliffordAlgebra.even spin2PlaneForm :=
    ⟨(rotor : Spin2Clifford),
      spinGroup.mem_even rotor.property⟩
  have hInverse := spin2EvenEquivComplex.symm_apply_apply evenRotor
  exact congrArg Subtype.val hInverse

/-- Concrete group equivalence between the circle model and Mathlib's
Clifford-algebra definition of `Spin(2)`. -/
def circleEquivCliffordSpin2 : Circle ≃* CliffordSpin2 where
  toFun := circleToCliffordSpin2
  invFun := cliffordSpin2ToCircle
  left_inv := cliffordSpin2ToCircle_circleToCliffordSpin2
  right_inv := circleToCliffordSpin2_cliffordSpin2ToCircle
  map_mul' := circleToCliffordSpin2Hom.map_mul

/-- Matrix-valued Spin projection transported from the circle model to Mathlib's
Clifford `Spin(2)`. -/
def cliffordSpin2ToMatrixSO2Projection : CliffordSpin2 →* MatrixSO2 :=
  spin2ToMatrixSO2Projection.comp
    circleEquivCliffordSpin2.symm.toMonoidHom

@[simp]
theorem cliffordSpin2ToMatrixSO2Projection_circle
    (phase : Circle) :
    cliffordSpin2ToMatrixSO2Projection
        (circleEquivCliffordSpin2 phase) =
      spin2ToMatrixSO2Projection phase := by
  rfl

/-- The Clifford-algebra Spin projection is surjective. -/
theorem cliffordSpin2ToMatrixSO2Projection_surjective :
    Function.Surjective cliffordSpin2ToMatrixSO2Projection := by
  intro rotation
  rcases spin2ToMatrixSO2Projection_surjective rotation with
    ⟨phase, hPhase⟩
  exact ⟨circleEquivCliffordSpin2 phase, by simpa using hPhase⟩

/-- The Clifford projection has exactly the expected two-element fibers. -/
theorem cliffordSpin2ToMatrixSO2Projection_eq_iff
    (first second : CliffordSpin2) :
    cliffordSpin2ToMatrixSO2Projection first =
        cliffordSpin2ToMatrixSO2Projection second ↔
      first = second ∨ first =
        circleEquivCliffordSpin2 (-1) * second := by
  let firstPhase := circleEquivCliffordSpin2.symm first
  let secondPhase := circleEquivCliffordSpin2.symm second
  change
    spin2ToMatrixSO2Projection firstPhase =
        spin2ToMatrixSO2Projection secondPhase ↔ _
  rw [spin2ToMatrixSO2Projection_eq_iff]
  constructor
  · rintro (hEqual | hNegative)
    · left
      exact circleEquivCliffordSpin2.symm.injective hEqual
    · right
      apply circleEquivCliffordSpin2.symm.injective
      simpa [firstPhase, secondPhase] using hNegative
  · rintro (hEqual | hNegative)
    · left
      exact congrArg circleEquivCliffordSpin2.symm hEqual
    · right
      have h := congrArg circleEquivCliffordSpin2.symm hNegative
      simpa [firstPhase, secondPhase] using h

/-- Exact progress boundary after identifying the circle and Clifford models. -/
structure CliffordSpin2BridgeStatus where
  negativeEuclideanPlaneFormInserted : Prop
  evenCliffordComplexEquivalenceConstructed : Prop
  circleRotorFactoredIntoUnitVectors : Prop
  rotorLipschitzMembershipProved : Prop
  rotorUnitarityProved : Prop
  circleToCliffordSpinHomConstructed : Prop
  circleCliffordSpinGroupEquivalenceProved : Prop
  matrixProjectionCompatibilityProved : Prop
  matrixProjectionSurjective : Prop
  matrixProjectionFiberTheoremProved : Prop
  smoothLieGroupEquivalenceProved : Prop
  principalSpinBundleConstructed : Prop

/-- Closure of the full geometric rank-two Spin bridge. -/
def cliffordSpin2BridgeClosed (s : CliffordSpin2BridgeStatus) : Prop :=
  s.negativeEuclideanPlaneFormInserted /\
  s.evenCliffordComplexEquivalenceConstructed /\
  s.circleRotorFactoredIntoUnitVectors /\
  s.rotorLipschitzMembershipProved /\
  s.rotorUnitarityProved /\
  s.circleToCliffordSpinHomConstructed /\
  s.circleCliffordSpinGroupEquivalenceProved /\
  s.matrixProjectionCompatibilityProved /\
  s.matrixProjectionSurjective /\
  s.matrixProjectionFiberTheoremProved /\
  s.smoothLieGroupEquivalenceProved /\
  s.principalSpinBundleConstructed

/-- The algebraic group equivalence does not by itself supply a smooth principal
Spin bundle over the Janus frame bundle. -/
theorem missing_principal_bundle_blocks_geometric_spin2
    (s : CliffordSpin2BridgeStatus)
    (hMissing : Not s.principalSpinBundleConstructed) :
    Not (cliffordSpin2BridgeClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2.2.2.2.2.2.2

end

end P0EFTJanusCliffordSpin2Bridge
end JanusFormal
