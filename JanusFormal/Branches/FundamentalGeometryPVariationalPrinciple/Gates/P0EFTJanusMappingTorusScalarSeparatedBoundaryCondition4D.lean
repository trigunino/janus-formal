import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkGlobalScalarBoundaryForm4D

/-!
# Separated scalar boundary conditions and Green isotropy

At every canonical boundary base point, a nonzero real coefficient pair
`(a,b)` imposes the separated condition

`a * value + b * normalDerivative = 0`.

Two scalar fields obeying the same condition have zero Green boundary form.
This contains Dirichlet, Neumann and arbitrary real Robin graphs.  The result is
algebraic at the smooth boundary-data level; no closed Hilbert operator domain
or maximality statement is claimed.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarSeparatedBoundaryCondition4D

set_option autoImplicit false
noncomputable section

open MeasureTheory
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCutBulkGlobalScalarBoundaryForm4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Pointwise separated real boundary condition. -/
def CanonicalLatitudeScalarSeparatedBoundaryCondition
    (valueCoefficient normalCoefficient : CanonicalLatitudeBase → Real)
    (field : SmoothQuotientField period hPeriod Real) : Prop :=
  ∀ base : CanonicalLatitudeBase,
    valueCoefficient base *
        canonicalLatitudeScalarBoundaryValue period hPeriod field base +
      normalCoefficient base *
        canonicalLatitudeScalarBoundaryNormalDerivative period hPeriod field base = 0

/-- The coefficient pair must not vanish simultaneously at any boundary base
point. -/
def CanonicalLatitudeScalarSeparatedBoundaryNondegenerate
    (valueCoefficient normalCoefficient : CanonicalLatitudeBase → Real) : Prop :=
  ∀ base : CanonicalLatitudeBase,
    valueCoefficient base ≠ 0 ∨ normalCoefficient base ≠ 0

/-- A common nondegenerate separated boundary line is pointwise isotropic for
the scalar Green form. -/
theorem canonicalLatitudeScalarBoundaryGreenForm_eq_zero_of_separated
    (valueCoefficient normalCoefficient : CanonicalLatitudeBase → Real)
    (hNondegenerate : CanonicalLatitudeScalarSeparatedBoundaryNondegenerate
      valueCoefficient normalCoefficient)
    (field test : SmoothQuotientField period hPeriod Real)
    (hField : CanonicalLatitudeScalarSeparatedBoundaryCondition period hPeriod
      valueCoefficient normalCoefficient field)
    (hTest : CanonicalLatitudeScalarSeparatedBoundaryCondition period hPeriod
      valueCoefficient normalCoefficient test)
    (base : CanonicalLatitudeBase) :
    canonicalLatitudeScalarBoundaryGreenForm period hPeriod field test base = 0 := by
  by_cases hNormal : normalCoefficient base = 0
  · have hValueCoefficient : valueCoefficient base ≠ 0 := by
      rcases hNondegenerate base with hValue | hNormal'
      · exact hValue
      · exact False.elim (hNormal hNormal')
    have hFieldValue :
        canonicalLatitudeScalarBoundaryValue period hPeriod field base = 0 := by
      have hEquation : valueCoefficient base *
          canonicalLatitudeScalarBoundaryValue period hPeriod field base = 0 := by
        simpa [hNormal] using hField base
      exact (mul_eq_zero.mp hEquation).resolve_left hValueCoefficient
    have hTestValue :
        canonicalLatitudeScalarBoundaryValue period hPeriod test base = 0 := by
      have hEquation : valueCoefficient base *
          canonicalLatitudeScalarBoundaryValue period hPeriod test base = 0 := by
        simpa [hNormal] using hTest base
      exact (mul_eq_zero.mp hEquation).resolve_left hValueCoefficient
    simp [canonicalLatitudeScalarBoundaryGreenForm, hFieldValue, hTestValue]
  · have hMultiple : normalCoefficient base *
        canonicalLatitudeScalarBoundaryGreenForm period hPeriod field test base = 0 := by
      calc
        normalCoefficient base *
            canonicalLatitudeScalarBoundaryGreenForm period hPeriod field test base =
          canonicalLatitudeScalarBoundaryValue period hPeriod field base *
              (valueCoefficient base *
                  canonicalLatitudeScalarBoundaryValue period hPeriod test base +
                normalCoefficient base *
                  canonicalLatitudeScalarBoundaryNormalDerivative period hPeriod test base) -
            canonicalLatitudeScalarBoundaryValue period hPeriod test base *
              (valueCoefficient base *
                  canonicalLatitudeScalarBoundaryValue period hPeriod field base +
                normalCoefficient base *
                  canonicalLatitudeScalarBoundaryNormalDerivative period hPeriod field base) := by
            unfold canonicalLatitudeScalarBoundaryGreenForm
            ring
        _ = 0 := by rw [hTest base, hField base]; ring
    exact (mul_eq_zero.mp hMultiple).resolve_left hNormal

/-- The measured one-sheet boundary form vanishes on every common separated
boundary condition. -/
theorem canonicalLatitudeMeasuredScalarBoundaryGreenForm_eq_zero_of_separated
    (valueCoefficient normalCoefficient : CanonicalLatitudeBase → Real)
    (hNondegenerate : CanonicalLatitudeScalarSeparatedBoundaryNondegenerate
      valueCoefficient normalCoefficient)
    (field test : SmoothQuotientField period hPeriod Real)
    (hField : CanonicalLatitudeScalarSeparatedBoundaryCondition period hPeriod
      valueCoefficient normalCoefficient field)
    (hTest : CanonicalLatitudeScalarSeparatedBoundaryCondition period hPeriod
      valueCoefficient normalCoefficient test) :
    canonicalLatitudeMeasuredScalarBoundaryGreenForm period hPeriod field test = 0 := by
  unfold canonicalLatitudeMeasuredScalarBoundaryGreenForm
  apply integral_eq_zero_of_ae
  exact Filter.Eventually.of_forall fun base =>
    canonicalLatitudeScalarBoundaryGreenForm_eq_zero_of_separated
      period hPeriod valueCoefficient normalCoefficient hNondegenerate
      field test hField hTest base

/-- The exact global manifold-boundary form vanishes on the same separated
boundary condition. -/
theorem cutBulkGlobalScalarBoundaryGreenForm_eq_zero_of_separated
    (valueCoefficient normalCoefficient : CanonicalLatitudeBase → Real)
    (hNondegenerate : CanonicalLatitudeScalarSeparatedBoundaryNondegenerate
      valueCoefficient normalCoefficient)
    (field test : SmoothQuotientField period hPeriod Real)
    (hField : CanonicalLatitudeScalarSeparatedBoundaryCondition period hPeriod
      valueCoefficient normalCoefficient field)
    (hTest : CanonicalLatitudeScalarSeparatedBoundaryCondition period hPeriod
      valueCoefficient normalCoefficient test) :
    cutBulkGlobalScalarBoundaryGreenForm period hPeriod field test = 0 := by
  rw [cutBulkGlobalScalarBoundaryGreenForm_eq_two_mul_measured,
    canonicalLatitudeMeasuredScalarBoundaryGreenForm_eq_zero_of_separated
      period hPeriod valueCoefficient normalCoefficient hNondegenerate
        field test hField hTest]
  ring

/-- Dirichlet is the separated line `(1,0)`. -/
def CanonicalLatitudeScalarDirichletBoundaryCondition
    (field : SmoothQuotientField period hPeriod Real) : Prop :=
  CanonicalLatitudeScalarSeparatedBoundaryCondition period hPeriod
    (fun _ => 1) (fun _ => 0) field

/-- Neumann is the separated line `(0,1)`. -/
def CanonicalLatitudeScalarNeumannBoundaryCondition
    (field : SmoothQuotientField period hPeriod Real) : Prop :=
  CanonicalLatitudeScalarSeparatedBoundaryCondition period hPeriod
    (fun _ => 0) (fun _ => 1) field

/-- A real, possibly base-dependent Robin graph is the separated line
`(-kappa,1)`. -/
def CanonicalLatitudeScalarRobinBoundaryCondition
    (coefficient : CanonicalLatitudeBase → Real)
    (field : SmoothQuotientField period hPeriod Real) : Prop :=
  CanonicalLatitudeScalarSeparatedBoundaryCondition period hPeriod
    (fun base => -coefficient base) (fun _ => 1) field

private theorem dirichletBoundaryCoefficients_nondegenerate :
    CanonicalLatitudeScalarSeparatedBoundaryNondegenerate
      (fun _ : CanonicalLatitudeBase => (1 : Real)) (fun _ => 0) := by
  intro base
  exact Or.inl one_ne_zero

private theorem neumannBoundaryCoefficients_nondegenerate :
    CanonicalLatitudeScalarSeparatedBoundaryNondegenerate
      (fun _ : CanonicalLatitudeBase => (0 : Real)) (fun _ => 1) := by
  intro base
  exact Or.inr one_ne_zero

private theorem robinBoundaryCoefficients_nondegenerate
    (coefficient : CanonicalLatitudeBase → Real) :
    CanonicalLatitudeScalarSeparatedBoundaryNondegenerate
      (fun base => -coefficient base) (fun _ => 1) := by
  intro base
  exact Or.inr one_ne_zero

theorem canonicalLatitudeScalarDirichletBoundaryCondition_iff
    (field : SmoothQuotientField period hPeriod Real) :
    CanonicalLatitudeScalarDirichletBoundaryCondition period hPeriod field ↔
      ∀ base, canonicalLatitudeScalarBoundaryValue period hPeriod field base = 0 := by
  simp [CanonicalLatitudeScalarDirichletBoundaryCondition,
    CanonicalLatitudeScalarSeparatedBoundaryCondition]

theorem canonicalLatitudeScalarNeumannBoundaryCondition_iff
    (field : SmoothQuotientField period hPeriod Real) :
    CanonicalLatitudeScalarNeumannBoundaryCondition period hPeriod field ↔
      ∀ base,
        canonicalLatitudeScalarBoundaryNormalDerivative period hPeriod field base = 0 := by
  simp [CanonicalLatitudeScalarNeumannBoundaryCondition,
    CanonicalLatitudeScalarSeparatedBoundaryCondition]

theorem canonicalLatitudeScalarRobinBoundaryCondition_iff
    (coefficient : CanonicalLatitudeBase → Real)
    (field : SmoothQuotientField period hPeriod Real) :
    CanonicalLatitudeScalarRobinBoundaryCondition period hPeriod coefficient field ↔
      ∀ base,
        canonicalLatitudeScalarBoundaryNormalDerivative period hPeriod field base =
          coefficient base *
            canonicalLatitudeScalarBoundaryValue period hPeriod field base := by
  constructor
  · intro hBoundary base
    have hEquation := hBoundary base
    unfold CanonicalLatitudeScalarRobinBoundaryCondition
      CanonicalLatitudeScalarSeparatedBoundaryCondition at hEquation
    dsimp at hEquation
    linarith
  · intro hBoundary base
    unfold CanonicalLatitudeScalarRobinBoundaryCondition
      CanonicalLatitudeScalarSeparatedBoundaryCondition
    dsimp
    rw [hBoundary base]
    ring

/-- The existing homogeneous throat-Dirichlet condition feeds the canonical
separated Dirichlet line. -/
theorem canonicalLatitudeScalarDirichletBoundaryCondition_of_homogeneousDirichlet
    (field : SmoothQuotientField period hPeriod Real)
    (hDirichlet : SatisfiesDirichlet period hPeriod Real 0 field) :
    CanonicalLatitudeScalarDirichletBoundaryCondition period hPeriod field := by
  rw [canonicalLatitudeScalarDirichletBoundaryCondition_iff]
  intro base
  unfold canonicalLatitudeScalarBoundaryValue
  exact canonicalLatitudeValue_zero_eq_zero_of_homogeneousDirichlet
    period hPeriod field hDirichlet base

/-- Global Green isotropy of the Dirichlet line. -/
theorem cutBulkGlobalScalarBoundaryGreenForm_eq_zero_of_dirichlet
    (field test : SmoothQuotientField period hPeriod Real)
    (hField : CanonicalLatitudeScalarDirichletBoundaryCondition period hPeriod field)
    (hTest : CanonicalLatitudeScalarDirichletBoundaryCondition period hPeriod test) :
    cutBulkGlobalScalarBoundaryGreenForm period hPeriod field test = 0 :=
  cutBulkGlobalScalarBoundaryGreenForm_eq_zero_of_separated
    period hPeriod (fun _ => 1) (fun _ => 0)
      dirichletBoundaryCoefficients_nondegenerate field test hField hTest

/-- Global Green isotropy of the Neumann line. -/
theorem cutBulkGlobalScalarBoundaryGreenForm_eq_zero_of_neumann
    (field test : SmoothQuotientField period hPeriod Real)
    (hField : CanonicalLatitudeScalarNeumannBoundaryCondition period hPeriod field)
    (hTest : CanonicalLatitudeScalarNeumannBoundaryCondition period hPeriod test) :
    cutBulkGlobalScalarBoundaryGreenForm period hPeriod field test = 0 :=
  cutBulkGlobalScalarBoundaryGreenForm_eq_zero_of_separated
    period hPeriod (fun _ => 0) (fun _ => 1)
      neumannBoundaryCoefficients_nondegenerate field test hField hTest

/-- Global Green isotropy of every real Robin graph, including variable
coefficients on the canonical boundary base. -/
theorem cutBulkGlobalScalarBoundaryGreenForm_eq_zero_of_robin
    (coefficient : CanonicalLatitudeBase → Real)
    (field test : SmoothQuotientField period hPeriod Real)
    (hField : CanonicalLatitudeScalarRobinBoundaryCondition period hPeriod
      coefficient field)
    (hTest : CanonicalLatitudeScalarRobinBoundaryCondition period hPeriod
      coefficient test) :
    cutBulkGlobalScalarBoundaryGreenForm period hPeriod field test = 0 :=
  cutBulkGlobalScalarBoundaryGreenForm_eq_zero_of_separated
    period hPeriod (fun base => -coefficient base) (fun _ => 1)
      (robinBoundaryCoefficients_nondegenerate coefficient)
      field test hField hTest

/-- Existing homogeneous Dirichlet fields therefore have zero exact global
boundary Green form. -/
theorem cutBulkGlobalScalarBoundaryGreenForm_eq_zero_of_homogeneousDirichlet
    (field test : SmoothQuotientField period hPeriod Real)
    (hField : SatisfiesDirichlet period hPeriod Real 0 field)
    (hTest : SatisfiesDirichlet period hPeriod Real 0 test) :
    cutBulkGlobalScalarBoundaryGreenForm period hPeriod field test = 0 :=
  cutBulkGlobalScalarBoundaryGreenForm_eq_zero_of_dirichlet
    period hPeriod field test
      (canonicalLatitudeScalarDirichletBoundaryCondition_of_homogeneousDirichlet
        period hPeriod field hField)
      (canonicalLatitudeScalarDirichletBoundaryCondition_of_homogeneousDirichlet
        period hPeriod test hTest)

end
end P0EFTJanusMappingTorusScalarSeparatedBoundaryCondition4D
end JanusFormal
