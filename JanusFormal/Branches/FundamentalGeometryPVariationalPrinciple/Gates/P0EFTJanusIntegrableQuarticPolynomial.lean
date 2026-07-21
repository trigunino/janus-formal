import Mathlib

/-! Integration and differentiation of an integrable quartic polynomial. -/

namespace JanusFormal
namespace P0EFTJanusIntegrableQuarticPolynomial

set_option autoImplicit false
noncomputable section

open MeasureTheory

variable {α : Type*} [MeasurableSpace α]

theorem quartic_integrable
    (mu : Measure α) (C0 C1 C2 C3 C4 : α → Real)
    (h0 : Integrable C0 mu) (h1 : Integrable C1 mu)
    (h2 : Integrable C2 mu) (h3 : Integrable C3 mu)
    (h4 : Integrable C4 mu) (t : Real) :
    Integrable (fun p => C0 p + t * C1 p + t ^ 2 * C2 p +
      t ^ 3 * C3 p + t ^ 4 * C4 p) mu := by
  exact (((h0.add (h1.const_mul t)).add (h2.const_mul (t ^ 2))).add
    (h3.const_mul (t ^ 3))).add (h4.const_mul (t ^ 4))

theorem integral_quartic
    (mu : Measure α) (C0 C1 C2 C3 C4 : α → Real)
    (h0 : Integrable C0 mu) (h1 : Integrable C1 mu)
    (h2 : Integrable C2 mu) (h3 : Integrable C3 mu)
    (h4 : Integrable C4 mu) (t : Real) :
    (∫ p, C0 p + t * C1 p + t ^ 2 * C2 p +
      t ^ 3 * C3 p + t ^ 4 * C4 p ∂mu) =
      (∫ p, C0 p ∂mu) + t * (∫ p, C1 p ∂mu) +
        t ^ 2 * (∫ p, C2 p ∂mu) + t ^ 3 * (∫ p, C3 p ∂mu) +
        t ^ 4 * (∫ p, C4 p ∂mu) := by
  calc
    _ = (∫ p, C0 p + t * C1 p + t ^ 2 * C2 p + t ^ 3 * C3 p ∂mu) +
        ∫ p, t ^ 4 * C4 p ∂mu := by
      simpa only [Pi.add_apply] using integral_add
        (((h0.add (h1.const_mul t)).add (h2.const_mul (t ^ 2))).add
          (h3.const_mul (t ^ 3))) (h4.const_mul (t ^ 4))
    _ = ((∫ p, C0 p + t * C1 p + t ^ 2 * C2 p ∂mu) +
        ∫ p, t ^ 3 * C3 p ∂mu) + ∫ p, t ^ 4 * C4 p ∂mu := by
      exact congrArg (fun value => value + ∫ p, t ^ 4 * C4 p ∂mu) (by
        simpa only [Pi.add_apply] using integral_add
          ((h0.add (h1.const_mul t)).add (h2.const_mul (t ^ 2)))
          (h3.const_mul (t ^ 3)))
    _ = (((∫ p, C0 p + t * C1 p ∂mu) + ∫ p, t ^ 2 * C2 p ∂mu) +
        ∫ p, t ^ 3 * C3 p ∂mu) + ∫ p, t ^ 4 * C4 p ∂mu := by
      exact congrArg (fun value => value + ∫ p, t ^ 4 * C4 p ∂mu)
        (congrArg (fun value => value + ∫ p, t ^ 3 * C3 p ∂mu) (by
          simpa only [Pi.add_apply] using integral_add
            (h0.add (h1.const_mul t)) (h2.const_mul (t ^ 2))))
    _ = ((((∫ p, C0 p ∂mu) + ∫ p, t * C1 p ∂mu) +
        ∫ p, t ^ 2 * C2 p ∂mu) + ∫ p, t ^ 3 * C3 p ∂mu) +
        ∫ p, t ^ 4 * C4 p ∂mu := by
      exact congrArg (fun value => value + ∫ p, t ^ 4 * C4 p ∂mu)
        (congrArg (fun value => value + ∫ p, t ^ 3 * C3 p ∂mu)
          (congrArg (fun value => value + ∫ p, t ^ 2 * C2 p ∂mu) (by
            simpa only [Pi.add_apply] using integral_add h0 (h1.const_mul t))))
    _ = _ := by simp only [integral_const_mul]

theorem integral_quartic_hasDerivAt_zero
    (mu : Measure α) (C0 C1 C2 C3 C4 : α → Real) :
    HasDerivAt
      (fun t : Real =>
        (∫ p, C0 p ∂mu) + t * (∫ p, C1 p ∂mu) +
          t ^ 2 * (∫ p, C2 p ∂mu) + t ^ 3 * (∫ p, C3 p ∂mu) +
          t ^ 4 * (∫ p, C4 p ∂mu))
      (∫ p, C1 p ∂mu) 0 := by
  have hDerivative :=
    (((((hasDerivAt_const (x := (0 : Real)) (∫ p, C0 p ∂mu)).add
      ((hasDerivAt_id (x := (0 : Real))).mul_const (∫ p, C1 p ∂mu))).add
      (((hasDerivAt_id (x := (0 : Real))).pow 2).mul_const
        (∫ p, C2 p ∂mu))).add
      (((hasDerivAt_id (x := (0 : Real))).pow 3).mul_const
        (∫ p, C3 p ∂mu))).add
      (((hasDerivAt_id (x := (0 : Real))).pow 4).mul_const
        (∫ p, C4 p ∂mu)))
  have hFunction :
      (((((fun _ : Real => ∫ p, C0 p ∂mu) +
        (fun t => t * ∫ p, C1 p ∂mu)) +
        (fun t => t ^ 2 * ∫ p, C2 p ∂mu)) +
        (fun t => t ^ 3 * ∫ p, C3 p ∂mu)) +
        (fun t => t ^ 4 * ∫ p, C4 p ∂mu)) =
      (fun t : Real =>
        (∫ p, C0 p ∂mu) + t * (∫ p, C1 p ∂mu) +
          t ^ 2 * (∫ p, C2 p ∂mu) + t ^ 3 * (∫ p, C3 p ∂mu) +
          t ^ 4 * (∫ p, C4 p ∂mu)) := by
    funext t
    simp only [Pi.add_apply]
  rw [← hFunction]
  simpa [id] using hDerivative

end
end P0EFTJanusIntegrableQuarticPolynomial
end JanusFormal
