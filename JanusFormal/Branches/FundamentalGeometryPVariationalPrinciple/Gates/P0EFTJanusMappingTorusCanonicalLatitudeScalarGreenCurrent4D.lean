import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeScalarIPP4D
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Scalar Green current on the canonical D8 latitude collar

The antisymmetric Green--Wronskian current is constructed from two smooth
scalar fields.  Its derivative is the antisymmetric pairing of their exact
collar Euler residuals, hence it is constant for two solutions with the same
mass.  No global manifold Stokes theorem is used.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalLatitudeScalarGreenCurrent4D

set_option autoImplicit false

noncomputable section

open MeasureTheory
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalLatitudeScalarIPP4D

/-- Scalar derivative predicate with the same explicit real module instance
as the canonical latitude derivative API. -/
abbrev CanonicalLatitudeScalarHasDerivAt
    (function : Real → Real) (derivative point : Real) : Prop :=
  @HasDerivAt Real DenselyNormedField.toNontriviallyNormedField Real
    Real.normedAddCommGroup.toAddCommGroup
    (RCLike.toInnerProductSpaceReal : InnerProductSpace Real Real).toModule
    Real.normedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    (inferInstance : ContinuousSMul Real Real)
    function derivative point

/-- The one-dimensional scalar Euler residual `phi'' + m² phi` on each
canonical latitude fiber.  Its zero set agrees with the sign convention
`-phi'' - m² phi = 0` of the weak scalar Euler gate. -/
def canonicalLatitudeScalarEulerResidual
    (period : Real) (hPeriod : period ≠ 0) (massSquared : Real)
    (field : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) (normal : Real) : Real :=
  canonicalLatitudeSecondDerivative period hPeriod field base normal +
    massSquared * canonicalLatitudeValue period hPeriod field base normal

/-- Explicit smooth solutions of the collar Euler equation on every latitude
fiber. -/
def CanonicalLatitudeScalarEulerSolution
    (period : Real) (hPeriod : period ≠ 0) (massSquared : Real)
    (field : SmoothQuotientField period hPeriod Real) : Prop :=
  ∀ (base : CanonicalLatitudeBase) (normal : Real),
    canonicalLatitudeScalarEulerResidual period hPeriod massSquared field
      base normal = 0

/-- Antisymmetric scalar Green--Wronskian current.  For two equal-mass real
scalars this is also the local `O(2)` rotation Noether pairing. -/
def canonicalLatitudeScalarGreenCurrent
    (period : Real) (hPeriod : period ≠ 0)
    (field test : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) (normal : Real) : Real :=
  canonicalLatitudeValue period hPeriod field base normal *
      canonicalLatitudeDerivative period hPeriod test base normal -
    canonicalLatitudeDerivative period hPeriod field base normal *
      canonicalLatitudeValue period hPeriod test base normal

theorem canonicalLatitudeScalarGreenCurrent_eq_normalNoetherPairing
    (period : Real) (hPeriod : period ≠ 0)
    (field test : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) (normal : Real) :
    canonicalLatitudeScalarGreenCurrent period hPeriod field test base normal =
      canonicalLatitudeValue period hPeriod field base normal *
          canonicalLatitudeDerivative period hPeriod test base normal -
        canonicalLatitudeValue period hPeriod test base normal *
          canonicalLatitudeDerivative period hPeriod field base normal := by
  unfold canonicalLatitudeScalarGreenCurrent
  ring

theorem canonicalLatitudeScalarGreenCurrent_antisymm
    (period : Real) (hPeriod : period ≠ 0)
    (field test : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) (normal : Real) :
    canonicalLatitudeScalarGreenCurrent period hPeriod field test base normal =
      -canonicalLatitudeScalarGreenCurrent period hPeriod test field base normal := by
  unfold canonicalLatitudeScalarGreenCurrent
  ring

@[simp]
theorem canonicalLatitudeScalarGreenCurrent_self
    (period : Real) (hPeriod : period ≠ 0)
    (field : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) (normal : Real) :
    canonicalLatitudeScalarGreenCurrent period hPeriod field field base normal = 0 := by
  unfold canonicalLatitudeScalarGreenCurrent
  ring

/-- Local Green identity: the derivative of the current is exactly the
antisymmetric pairing of the two Euler residuals. -/
theorem canonicalLatitudeScalarGreenCurrent_hasDerivAt
    (period : Real) (hPeriod : period ≠ 0) (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) (normal : Real) :
    CanonicalLatitudeScalarHasDerivAt
      (canonicalLatitudeScalarGreenCurrent period hPeriod field test base)
      (canonicalLatitudeValue period hPeriod field base normal *
          canonicalLatitudeScalarEulerResidual period hPeriod massSquared test
            base normal -
        canonicalLatitudeScalarEulerResidual period hPeriod massSquared field
            base normal *
          canonicalLatitudeValue period hPeriod test base normal)
      normal := by
  unfold CanonicalLatitudeScalarHasDerivAt
  have hRaw :=
    ((canonicalLatitudeValue_hasDerivAt period hPeriod field base normal).mul
      (canonicalLatitudeDerivative_hasDerivAt period hPeriod test base normal)).sub
    ((canonicalLatitudeDerivative_hasDerivAt period hPeriod field base normal).mul
      (canonicalLatitudeValue_hasDerivAt period hPeriod test base normal))
  convert hRaw using 1 <;>
    first | rfl | exact Subsingleton.elim _ _ |
      (unfold canonicalLatitudeScalarEulerResidual; ring)

theorem canonicalLatitudeScalarGreenCurrent_hasDerivAt_zero_of_euler
    (period : Real) (hPeriod : period ≠ 0) (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real)
    (hField : CanonicalLatitudeScalarEulerSolution period hPeriod massSquared field)
    (hTest : CanonicalLatitudeScalarEulerSolution period hPeriod massSquared test)
    (base : CanonicalLatitudeBase) (normal : Real) :
    CanonicalLatitudeScalarHasDerivAt
      (canonicalLatitudeScalarGreenCurrent period hPeriod field test base)
      0 normal := by
  simpa [hField base normal, hTest base normal] using
    (canonicalLatitudeScalarGreenCurrent_hasDerivAt period hPeriod massSquared
      field test base normal)

/-- Conservation of the local scalar current between arbitrary normal
coordinates on the same canonical latitude fiber. -/
theorem canonicalLatitudeScalarGreenCurrent_eq_of_euler
    (period : Real) (hPeriod : period ≠ 0) (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real)
    (hField : CanonicalLatitudeScalarEulerSolution period hPeriod massSquared field)
    (hTest : CanonicalLatitudeScalarEulerSolution period hPeriod massSquared test)
    (base : CanonicalLatitudeBase) (first second : Real) :
    canonicalLatitudeScalarGreenCurrent period hPeriod field test base first =
      canonicalLatitudeScalarGreenCurrent period hPeriod field test base second := by
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := first) (b := second)
    (f := canonicalLatitudeScalarGreenCurrent period hPeriod field test base)
    (f' := fun _ : Real => 0)
    (fun normal _ => by
      have hZero :=
        canonicalLatitudeScalarGreenCurrent_hasDerivAt_zero_of_euler period
          hPeriod massSquared field test hField hTest base normal
      unfold CanonicalLatitudeScalarHasDerivAt at hZero
      exact hZero)
    (continuous_const.intervalIntegrable first second)
  have hDifference :
      canonicalLatitudeScalarGreenCurrent period hPeriod field test base second -
        canonicalLatitudeScalarGreenCurrent period hPeriod field test base first = 0 := by
    simpa using hFTC.symm
  linarith

/-- The current jump is exactly the antisymmetrization of the concrete
boundary functional constructed by the collar IPP gate. -/
theorem canonicalLatitudeScalarGreenCurrent_endpointJump_eq_boundary_antisymm
    (period : Real) (hPeriod : period ≠ 0)
    (field test : SmoothQuotientField period hPeriod Real)
    (base : CanonicalLatitudeBase) :
    canonicalLatitudeScalarGreenCurrent period hPeriod field test base 1 -
        canonicalLatitudeScalarGreenCurrent period hPeriod field test base 0 =
      canonicalLatitudeScalarBoundaryFiber period hPeriod test field base -
        canonicalLatitudeScalarBoundaryFiber period hPeriod field test base := by
  unfold canonicalLatitudeScalarGreenCurrent canonicalLatitudeScalarBoundaryFiber
  ring

/-- The measured current through a fixed normal latitude, using the same
canonical throat-base measure as the exact collar IPP. -/
def canonicalLatitudeMeasuredScalarGreenCurrent
    (period : Real) (hPeriod : period ≠ 0)
    (field test : SmoothQuotientField period hPeriod Real)
    (normal : Real) : Real :=
  ∫ base,
    canonicalLatitudeScalarGreenCurrent period hPeriod field test base normal
    ∂(canonicalLatitudeBaseMeasure period)

theorem canonicalLatitudeMeasuredScalarGreenCurrent_eq_of_euler
    (period : Real) (hPeriod : period ≠ 0) (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real)
    (hField : CanonicalLatitudeScalarEulerSolution period hPeriod massSquared field)
    (hTest : CanonicalLatitudeScalarEulerSolution period hPeriod massSquared test)
    (first second : Real) :
    canonicalLatitudeMeasuredScalarGreenCurrent period hPeriod field test first =
      canonicalLatitudeMeasuredScalarGreenCurrent period hPeriod field test second := by
  unfold canonicalLatitudeMeasuredScalarGreenCurrent
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun base =>
    canonicalLatitudeScalarGreenCurrent_eq_of_euler period hPeriod massSquared
      field test hField hTest base first second

/-- Explicit class of global smooth collar solutions obeying homogeneous
Dirichlet data at the throat and at the outer unit-latitude endpoint. -/
structure CanonicalLatitudeScalarDirichletEulerSolution
    (period : Real) (hPeriod : period ≠ 0) (massSquared : Real)
    (field : SmoothQuotientField period hPeriod Real) : Prop where
  euler : CanonicalLatitudeScalarEulerSolution period hPeriod massSquared field
  inner : SatisfiesDirichlet period hPeriod Real 0 field
  outer : CanonicalLatitudeOuterHomogeneousDirichlet period hPeriod field

theorem canonicalLatitudeScalarGreenCurrent_zero_of_dirichletEuler
    (period : Real) (hPeriod : period ≠ 0) (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real)
    (hField : CanonicalLatitudeScalarDirichletEulerSolution period hPeriod
      massSquared field)
    (hTest : CanonicalLatitudeScalarDirichletEulerSolution period hPeriod
      massSquared test)
    (base : CanonicalLatitudeBase) (normal : Real) :
    canonicalLatitudeScalarGreenCurrent period hPeriod field test base normal = 0 := by
  calc
    canonicalLatitudeScalarGreenCurrent period hPeriod field test base normal =
        canonicalLatitudeScalarGreenCurrent period hPeriod field test base 0 :=
      canonicalLatitudeScalarGreenCurrent_eq_of_euler period hPeriod massSquared
        field test hField.euler hTest.euler base normal 0
    _ = 0 := by
      unfold canonicalLatitudeScalarGreenCurrent
      rw [canonicalLatitudeValue_zero_eq_zero_of_homogeneousDirichlet
          period hPeriod field hField.inner base,
        canonicalLatitudeValue_zero_eq_zero_of_homogeneousDirichlet
          period hPeriod test hTest.inner base]
      ring

theorem canonicalLatitudeMeasuredScalarGreenCurrent_zero_of_dirichletEuler
    (period : Real) (hPeriod : period ≠ 0) (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real)
    (hField : CanonicalLatitudeScalarDirichletEulerSolution period hPeriod
      massSquared field)
    (hTest : CanonicalLatitudeScalarDirichletEulerSolution period hPeriod
      massSquared test)
    (normal : Real) :
    canonicalLatitudeMeasuredScalarGreenCurrent period hPeriod field test normal = 0 := by
  unfold canonicalLatitudeMeasuredScalarGreenCurrent
  apply integral_eq_zero_of_ae
  exact Filter.Eventually.of_forall fun base =>
    canonicalLatitudeScalarGreenCurrent_zero_of_dirichletEuler period hPeriod
      massSquared field test hField hTest base normal

end

end P0EFTJanusMappingTorusCanonicalLatitudeScalarGreenCurrent4D
end JanusFormal
