import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06DiagonalPolynomialFrechetDerivative4D

/-!
# Higher Frechet derivatives of diagonal polynomials

This support gate extends Gate876 from the first derivative to arbitrary
finite derivative order.  For a degree-`n` continuous multilinear form, the
order-`k` derivative of its diagonal evaluation is the sum over embeddings
`Fin k ↪ Fin n`: the labelled variations occupy distinct slots and the
remaining slots contain the base field.

The construction is specialized explicitly at orders two, three and four,
then assembled for Gate876's polynomial of degree at most four.  It supplies
fiberwise higher derivatives only.  No Euler operator, T02 transition
naturality, or kernel classification is asserted here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06DiagonalPolynomialHigherFrechetDerivative4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000
set_option maxRecDepth 100000
noncomputable section

open scoped BigOperators ContDiff
open P0EFTJanusProgramPT06DiagonalPolynomialFrechetDerivative4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule

universe u

variable {FieldFiber : Type u}
variable [NormedAddCommGroup FieldFiber] [NormedSpace Real FieldFiber]

/-- Diagonal continuous-linear embedding into the product of `degree`
copies of the field fiber. -/
def programPT06DiagonalFieldEmbedding (degree : Nat) :
    FieldFiber →L[Real] (Fin degree → FieldFiber) :=
  ContinuousLinearMap.pi
    (fun _ : Fin degree => ContinuousLinearMap.id Real FieldFiber)

@[simp] theorem programPT06DiagonalFieldEmbedding_apply
    (degree : Nat) (field : FieldFiber) (slot : Fin degree) :
    (programPT06DiagonalFieldEmbedding
      (FieldFiber := FieldFiber) degree) field slot = field := by
  rfl

/-- Arguments obtained by injecting labelled variations into distinct slots
of a diagonal multilinear evaluation. -/
def programPT06DiagonalInjectedArguments
    {degree order : Nat} (field : FieldFiber)
    (variations : Fin order → FieldFiber)
    (injection : Fin order ↪ Fin degree) : Fin degree → FieldFiber :=
  fun slot =>
    if h : slot ∈ Set.range injection then
      variations (injection.toEquivRange.symm ⟨slot, h⟩)
    else
      field

/-- Order-`k` derivative candidate for the diagonal evaluation of one
homogeneous form.  Mathlib's multilinear derivative differentiates on the
full product; composition with the diagonal embedding makes every labelled
variation constant across that product before distinct slots are selected. -/
def programPT06DiagonalHomogeneousHigherDerivative
    {degree : Nat} (order : Nat)
    (form : ProgramPT06ContinuousHomogeneousForm4D FieldFiber degree)
    (field : FieldFiber) :
    ContinuousMultilinearMap Real (fun _ : Fin order => FieldFiber) Real :=
  (form.iteratedFDeriv order (fun _ => field)).compContinuousLinearMap
    (fun _ : Fin order =>
      programPT06DiagonalFieldEmbedding (FieldFiber := FieldFiber) degree)

/-- Explicit injection formula for every finite derivative order. -/
@[simp] theorem programPT06DiagonalHomogeneousHigherDerivative_apply
    {degree : Nat} (order : Nat)
    (form : ProgramPT06ContinuousHomogeneousForm4D FieldFiber degree)
    (field : FieldFiber) (variations : Fin order → FieldFiber) :
    programPT06DiagonalHomogeneousHigherDerivative order form field variations =
      ∑ injection : Fin order ↪ Fin degree,
        form (programPT06DiagonalInjectedArguments
          field variations injection) := by
  classical
  simp only [programPT06DiagonalHomogeneousHigherDerivative,
    ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.iteratedFDeriv,
    ContinuousMultilinearMap.sum_apply,
    ContinuousMultilinearMap.iteratedFDerivComponent_apply,
    Pi.compRightL_apply, programPT06DiagonalFieldEmbedding_apply]
  apply Finset.sum_congr rfl
  intro injection _
  apply congrArg form
  funext slot
  by_cases h : slot ∈ Set.range injection
  · simp [programPT06DiagonalInjectedArguments, h,
      Function.Embedding.toEquivRange_eq_ofInjective]
  · simp [programPT06DiagonalInjectedArguments, h]

/-- The explicit injection sum is the actual iterated Frechet derivative of
the diagonal homogeneous term. -/
theorem programPT06DiagonalHomogeneousHigherDerivative_eq_iteratedFDeriv
    {degree : Nat} (order : Nat)
    (form : ProgramPT06ContinuousHomogeneousForm4D FieldFiber degree)
    (field : FieldFiber) :
    programPT06DiagonalHomogeneousHigherDerivative order form field =
      iteratedFDeriv Real order
        (programPT06DiagonalHomogeneousTerm form) field := by
  let diagonal := programPT06DiagonalFieldEmbedding
    (FieldFiber := FieldFiber) degree
  have hTerm :
      programPT06DiagonalHomogeneousTerm form = form ∘ diagonal := by
    rfl
  rw [hTerm,
    ContinuousLinearMap.iteratedFDeriv_comp_right
      diagonal form.contDiff field le_top,
    form.iteratedFDeriv_eq]
  rfl

/-- Every diagonal homogeneous term is smooth to all finite orders. -/
theorem programPT06DiagonalHomogeneousTerm_contDiff
    {degree : Nat}
    (form : ProgramPT06ContinuousHomogeneousForm4D FieldFiber degree) :
    ContDiff Real ∞ (programPT06DiagonalHomogeneousTerm form) := by
  let diagonal := programPT06DiagonalFieldEmbedding
    (FieldFiber := FieldFiber) degree
  have hTerm :
      programPT06DiagonalHomogeneousTerm form = form ∘ diagonal := by
    rfl
  rw [hTerm]
  exact form.contDiff.comp diagonal.contDiff

/-! ## Explicit orders two, three and four -/

def programPT06DiagonalHomogeneousSecondDerivative
    {degree : Nat}
    (form : ProgramPT06ContinuousHomogeneousForm4D FieldFiber degree)
    (field : FieldFiber) : FieldFiber [×2]→L[Real] Real :=
  programPT06DiagonalHomogeneousHigherDerivative 2 form field

@[simp] theorem programPT06DiagonalHomogeneousSecondDerivative_apply
    {degree : Nat}
    (form : ProgramPT06ContinuousHomogeneousForm4D FieldFiber degree)
    (field : FieldFiber) (variations : Fin 2 → FieldFiber) :
    programPT06DiagonalHomogeneousSecondDerivative form field variations =
      ∑ injection : Fin 2 ↪ Fin degree,
        form (programPT06DiagonalInjectedArguments
          field variations injection) := by
  exact programPT06DiagonalHomogeneousHigherDerivative_apply
    2 form field variations

theorem programPT06DiagonalHomogeneousSecondDerivative_eq_iteratedFDeriv
    {degree : Nat}
    (form : ProgramPT06ContinuousHomogeneousForm4D FieldFiber degree)
    (field : FieldFiber) :
    programPT06DiagonalHomogeneousSecondDerivative form field =
      iteratedFDeriv Real 2
        (programPT06DiagonalHomogeneousTerm form) field :=
  programPT06DiagonalHomogeneousHigherDerivative_eq_iteratedFDeriv
    2 form field

def programPT06DiagonalHomogeneousThirdDerivative
    {degree : Nat}
    (form : ProgramPT06ContinuousHomogeneousForm4D FieldFiber degree)
    (field : FieldFiber) : FieldFiber [×3]→L[Real] Real :=
  programPT06DiagonalHomogeneousHigherDerivative 3 form field

@[simp] theorem programPT06DiagonalHomogeneousThirdDerivative_apply
    {degree : Nat}
    (form : ProgramPT06ContinuousHomogeneousForm4D FieldFiber degree)
    (field : FieldFiber) (variations : Fin 3 → FieldFiber) :
    programPT06DiagonalHomogeneousThirdDerivative form field variations =
      ∑ injection : Fin 3 ↪ Fin degree,
        form (programPT06DiagonalInjectedArguments
          field variations injection) := by
  exact programPT06DiagonalHomogeneousHigherDerivative_apply
    3 form field variations

theorem programPT06DiagonalHomogeneousThirdDerivative_eq_iteratedFDeriv
    {degree : Nat}
    (form : ProgramPT06ContinuousHomogeneousForm4D FieldFiber degree)
    (field : FieldFiber) :
    programPT06DiagonalHomogeneousThirdDerivative form field =
      iteratedFDeriv Real 3
        (programPT06DiagonalHomogeneousTerm form) field :=
  programPT06DiagonalHomogeneousHigherDerivative_eq_iteratedFDeriv
    3 form field

def programPT06DiagonalHomogeneousFourthDerivative
    {degree : Nat}
    (form : ProgramPT06ContinuousHomogeneousForm4D FieldFiber degree)
    (field : FieldFiber) : FieldFiber [×4]→L[Real] Real :=
  programPT06DiagonalHomogeneousHigherDerivative 4 form field

@[simp] theorem programPT06DiagonalHomogeneousFourthDerivative_apply
    {degree : Nat}
    (form : ProgramPT06ContinuousHomogeneousForm4D FieldFiber degree)
    (field : FieldFiber) (variations : Fin 4 → FieldFiber) :
    programPT06DiagonalHomogeneousFourthDerivative form field variations =
      ∑ injection : Fin 4 ↪ Fin degree,
        form (programPT06DiagonalInjectedArguments
          field variations injection) := by
  exact programPT06DiagonalHomogeneousHigherDerivative_apply
    4 form field variations

theorem programPT06DiagonalHomogeneousFourthDerivative_eq_iteratedFDeriv
    {degree : Nat}
    (form : ProgramPT06ContinuousHomogeneousForm4D FieldFiber degree)
    (field : FieldFiber) :
    programPT06DiagonalHomogeneousFourthDerivative form field =
      iteratedFDeriv Real 4
        (programPT06DiagonalHomogeneousTerm form) field :=
  programPT06DiagonalHomogeneousHigherDerivative_eq_iteratedFDeriv
    4 form field

/-! ## Degree-at-most-four polynomial assembly -/

/-- Constant term represented uniformly as a degree-zero multilinear form. -/
def programPT06DiagonalConstantHomogeneousForm (constant : Real) :
    ProgramPT06ContinuousHomogeneousForm4D FieldFiber 0 :=
  ContinuousMultilinearMap.uncurry0 Real FieldFiber constant

/-- Linear term represented uniformly as a degree-one multilinear form. -/
def programPT06DiagonalLinearHomogeneousForm
    (linear : FieldFiber →L[Real] Real) :
    ProgramPT06ContinuousHomogeneousForm4D FieldFiber 1 :=
  (continuousMultilinearCurryFin1 Real FieldFiber Real).symm linear

@[simp] theorem programPT06DiagonalConstantHomogeneousForm_evaluation
    (constant : Real) (field : FieldFiber) :
    programPT06DiagonalHomogeneousTerm
        (programPT06DiagonalConstantHomogeneousForm
          (FieldFiber := FieldFiber) constant) field = constant := by
  simp [programPT06DiagonalHomogeneousTerm,
    programPT06DiagonalConstantHomogeneousForm]

@[simp] theorem programPT06DiagonalLinearHomogeneousForm_evaluation
    (linear : FieldFiber →L[Real] Real) (field : FieldFiber) :
    programPT06DiagonalHomogeneousTerm
        (programPT06DiagonalLinearHomogeneousForm linear) field =
      linear field := by
  rfl

/-- Uniform order-`k` derivative assembled from all five homogeneous
components of a Gate876 polynomial. -/
def programPT06DiagonalPolynomialHigherDerivative
    (order : Nat)
    (polynomial : ProgramPT06DiagonalPolynomialUpToFour4D FieldFiber)
    (field : FieldFiber) : FieldFiber [×order]→L[Real] Real :=
  programPT06DiagonalHomogeneousHigherDerivative order
      (programPT06DiagonalConstantHomogeneousForm
        (FieldFiber := FieldFiber) polynomial.constant) field +
    programPT06DiagonalHomogeneousHigherDerivative order
      (programPT06DiagonalLinearHomogeneousForm polynomial.linear) field +
    programPT06DiagonalHomogeneousHigherDerivative order
      polynomial.quadratic field +
    programPT06DiagonalHomogeneousHigherDerivative order
      polynomial.cubic field +
    programPT06DiagonalHomogeneousHigherDerivative order
      polynomial.quartic field

/-- Explicit sum-over-injections formula for the assembled polynomial. -/
@[simp] theorem programPT06DiagonalPolynomialHigherDerivative_apply
    (order : Nat)
    (polynomial : ProgramPT06DiagonalPolynomialUpToFour4D FieldFiber)
    (field : FieldFiber) (variations : Fin order → FieldFiber) :
    programPT06DiagonalPolynomialHigherDerivative order polynomial field
        variations =
      (∑ injection : Fin order ↪ Fin 0,
        programPT06DiagonalConstantHomogeneousForm
          (FieldFiber := FieldFiber) polynomial.constant
          (programPT06DiagonalInjectedArguments
            field variations injection)) +
      (∑ injection : Fin order ↪ Fin 1,
        programPT06DiagonalLinearHomogeneousForm polynomial.linear
          (programPT06DiagonalInjectedArguments
            field variations injection)) +
      (∑ injection : Fin order ↪ Fin 2,
        polynomial.quadratic
          (programPT06DiagonalInjectedArguments
            field variations injection)) +
      (∑ injection : Fin order ↪ Fin 3,
        polynomial.cubic
          (programPT06DiagonalInjectedArguments
            field variations injection)) +
      ∑ injection : Fin order ↪ Fin 4,
        polynomial.quartic
          (programPT06DiagonalInjectedArguments
            field variations injection) := by
  simp only [programPT06DiagonalPolynomialHigherDerivative,
    ContinuousMultilinearMap.add_apply,
    programPT06DiagonalHomogeneousHigherDerivative_apply]

/-- The assembled injection sum is the actual iterated Frechet derivative
of Gate876's complete polynomial evaluation. -/
theorem programPT06DiagonalPolynomialHigherDerivative_eq_iteratedFDeriv
    (order : Nat)
    (polynomial : ProgramPT06DiagonalPolynomialUpToFour4D FieldFiber)
    (field : FieldFiber) :
    programPT06DiagonalPolynomialHigherDerivative order polynomial field =
      iteratedFDeriv Real order
        (programPT06DiagonalPolynomialEvaluation polynomial) field := by
  let constantForm := programPT06DiagonalConstantHomogeneousForm
    (FieldFiber := FieldFiber) polynomial.constant
  let linearForm :=
    programPT06DiagonalLinearHomogeneousForm polynomial.linear
  have hConstant := programPT06DiagonalHomogeneousTerm_contDiff constantForm
  have hLinear := programPT06DiagonalHomogeneousTerm_contDiff linearForm
  have hQuadratic :=
    programPT06DiagonalHomogeneousTerm_contDiff polynomial.quadratic
  have hCubic := programPT06DiagonalHomogeneousTerm_contDiff polynomial.cubic
  have hQuartic :=
    programPT06DiagonalHomogeneousTerm_contDiff polynomial.quartic
  have hConstantOrder :
      ContDiff Real order
        (programPT06DiagonalHomogeneousTerm constantForm) :=
    hConstant.of_le
      (show (order : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  have hLinearOrder :
      ContDiff Real order
        (programPT06DiagonalHomogeneousTerm linearForm) :=
    hLinear.of_le
      (show (order : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  have hQuadraticOrder :
      ContDiff Real order
        (programPT06DiagonalHomogeneousTerm polynomial.quadratic) :=
    hQuadratic.of_le
      (show (order : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  have hCubicOrder :
      ContDiff Real order
        (programPT06DiagonalHomogeneousTerm polynomial.cubic) :=
    hCubic.of_le
      (show (order : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  have hQuarticOrder :
      ContDiff Real order
        (programPT06DiagonalHomogeneousTerm polynomial.quartic) :=
    hQuartic.of_le
      (show (order : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  have hConstantLinear := hConstantOrder.add hLinearOrder
  have hThroughQuadratic := hConstantLinear.add hQuadraticOrder
  have hThroughCubic := hThroughQuadratic.add hCubicOrder
  have iteratedAdd {f g : FieldFiber → Real}
      (hf : ContDiff Real order f) (hg : ContDiff Real order g) :
      iteratedFDeriv Real order (fun candidate => f candidate + g candidate) field =
        iteratedFDeriv Real order f field +
          iteratedFDeriv Real order g field := by
    convert congrFun (iteratedFDeriv_add hf hg) field using 1 <;> rfl
  have hEvaluation :
      programPT06DiagonalPolynomialEvaluation polynomial =
        programPT06DiagonalHomogeneousTerm constantForm +
          programPT06DiagonalHomogeneousTerm linearForm +
          programPT06DiagonalHomogeneousTerm polynomial.quadratic +
          programPT06DiagonalHomogeneousTerm polynomial.cubic +
          programPT06DiagonalHomogeneousTerm polynomial.quartic := by
    funext candidate
    simp [programPT06DiagonalPolynomialEvaluation,
      programPT06DiagonalConstantTerm, programPT06DiagonalLinearTerm,
      programPT06DiagonalQuadraticTerm, programPT06DiagonalCubicTerm,
      programPT06DiagonalQuarticTerm, constantForm, linearForm]
  rw [hEvaluation]
  change _ = iteratedFDeriv Real order
    (fun candidate =>
      (((programPT06DiagonalHomogeneousTerm constantForm candidate +
          programPT06DiagonalHomogeneousTerm linearForm candidate) +
        programPT06DiagonalHomogeneousTerm polynomial.quadratic candidate) +
        programPT06DiagonalHomogeneousTerm polynomial.cubic candidate) +
        programPT06DiagonalHomogeneousTerm polynomial.quartic candidate) field
  rw [iteratedAdd
      hThroughCubic hQuarticOrder,
    iteratedAdd hThroughQuadratic hCubicOrder,
    iteratedAdd hConstantLinear hQuadraticOrder,
    iteratedAdd hConstantOrder hLinearOrder]
  rw [← programPT06DiagonalHomogeneousHigherDerivative_eq_iteratedFDeriv
      order constantForm field,
    ← programPT06DiagonalHomogeneousHigherDerivative_eq_iteratedFDeriv
      order linearForm field,
    ← programPT06DiagonalHomogeneousHigherDerivative_eq_iteratedFDeriv
      order polynomial.quadratic field,
    ← programPT06DiagonalHomogeneousHigherDerivative_eq_iteratedFDeriv
      order polynomial.cubic field,
    ← programPT06DiagonalHomogeneousHigherDerivative_eq_iteratedFDeriv
      order polynomial.quartic field]
  rfl

def programPT06DiagonalPolynomialSecondDerivative
    (polynomial : ProgramPT06DiagonalPolynomialUpToFour4D FieldFiber)
    (field : FieldFiber) : FieldFiber [×2]→L[Real] Real :=
  programPT06DiagonalPolynomialHigherDerivative 2 polynomial field

theorem programPT06DiagonalPolynomialSecondDerivative_eq_iteratedFDeriv
    (polynomial : ProgramPT06DiagonalPolynomialUpToFour4D FieldFiber)
    (field : FieldFiber) :
    programPT06DiagonalPolynomialSecondDerivative polynomial field =
      iteratedFDeriv Real 2
        (programPT06DiagonalPolynomialEvaluation polynomial) field :=
  programPT06DiagonalPolynomialHigherDerivative_eq_iteratedFDeriv
    2 polynomial field

def programPT06DiagonalPolynomialThirdDerivative
    (polynomial : ProgramPT06DiagonalPolynomialUpToFour4D FieldFiber)
    (field : FieldFiber) : FieldFiber [×3]→L[Real] Real :=
  programPT06DiagonalPolynomialHigherDerivative 3 polynomial field

theorem programPT06DiagonalPolynomialThirdDerivative_eq_iteratedFDeriv
    (polynomial : ProgramPT06DiagonalPolynomialUpToFour4D FieldFiber)
    (field : FieldFiber) :
    programPT06DiagonalPolynomialThirdDerivative polynomial field =
      iteratedFDeriv Real 3
        (programPT06DiagonalPolynomialEvaluation polynomial) field :=
  programPT06DiagonalPolynomialHigherDerivative_eq_iteratedFDeriv
    3 polynomial field

def programPT06DiagonalPolynomialFourthDerivative
    (polynomial : ProgramPT06DiagonalPolynomialUpToFour4D FieldFiber)
    (field : FieldFiber) : FieldFiber [×4]→L[Real] Real :=
  programPT06DiagonalPolynomialHigherDerivative 4 polynomial field

theorem programPT06DiagonalPolynomialFourthDerivative_eq_iteratedFDeriv
    (polynomial : ProgramPT06DiagonalPolynomialUpToFour4D FieldFiber)
    (field : FieldFiber) :
    programPT06DiagonalPolynomialFourthDerivative polynomial field =
      iteratedFDeriv Real 4
        (programPT06DiagonalPolynomialEvaluation polynomial) field :=
  programPT06DiagonalPolynomialHigherDerivative_eq_iteratedFDeriv
    4 polynomial field

end
end P0EFTJanusProgramPT06DiagonalPolynomialHigherFrechetDerivative4D
end JanusFormal
