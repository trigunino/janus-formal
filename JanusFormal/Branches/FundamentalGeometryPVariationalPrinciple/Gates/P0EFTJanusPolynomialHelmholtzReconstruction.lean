import Mathlib

namespace JanusFormal
namespace P0EFTJanusPolynomialHelmholtzReconstruction

set_option autoImplicit false

/--
Quadratic Euler--Lagrange source in two fields.  The corresponding action is
cubic.  Coefficients are named by the monomial in each equation.
-/
@[ext] structure QuadraticEulerSystem2 where
  exX : ℝ
  exY : ℝ
  exXX : ℝ
  exXY : ℝ
  exYY : ℝ
  eyX : ℝ
  eyY : ℝ
  eyXX : ℝ
  eyXY : ℝ
  eyYY : ℝ

/-- First Euler component. -/
def eulerX
    (system : QuadraticEulerSystem2)
    (x y : ℝ) : ℝ :=
  system.exX * x +
    system.exY * y +
    system.exXX * x ^ 2 +
    system.exXY * x * y +
    system.exYY * y ^ 2

/-- Second Euler component. -/
def eulerY
    (system : QuadraticEulerSystem2)
    (x y : ℝ) : ℝ :=
  system.eyX * x +
    system.eyY * y +
    system.eyXX * x ^ 2 +
    system.eyXY * x * y +
    system.eyYY * y ^ 2

/-- Cross derivative `∂_y E_x`. -/
def crossDerivativeX
    (system : QuadraticEulerSystem2)
    (x y : ℝ) : ℝ :=
  system.exY + system.exXY * x + 2 * system.exYY * y

/-- Cross derivative `∂_x E_y`. -/
def crossDerivativeY
    (system : QuadraticEulerSystem2)
    (x y : ℝ) : ℝ :=
  system.eyX + 2 * system.eyXX * x + system.eyXY * y

/-- Pointwise Helmholtz condition. -/
def HelmholtzAtAllPoints
    (system : QuadraticEulerSystem2) : Prop :=
  ∀ x y : ℝ,
    crossDerivativeX system x y =
      crossDerivativeY system x y

/-- Coefficient form of the nonlinear Helmholtz conditions. -/
def HelmholtzCoefficients
    (system : QuadraticEulerSystem2) : Prop :=
  system.exY = system.eyX /\
  system.exXY = 2 * system.eyXX /\
  2 * system.exYY = system.eyXY

/-- Coefficient conditions imply the pointwise cross-derivative identity. -/
theorem helmholtz_coefficients_imply_pointwise
    (system : QuadraticEulerSystem2)
    (hCoefficients : HelmholtzCoefficients system) :
    HelmholtzAtAllPoints system := by
  rcases hCoefficients with ⟨hLinear, hX, hY⟩
  intro x y
  unfold crossDerivativeX crossDerivativeY
  rw [hLinear, hX, ← hY]
  ring

/-- Pointwise Helmholtz implies the three coefficient relations. -/
theorem pointwise_helmholtz_implies_coefficients
    (system : QuadraticEulerSystem2)
    (hPointwise : HelmholtzAtAllPoints system) :
    HelmholtzCoefficients system := by
  have hOrigin := hPointwise 0 0
  have hXPoint := hPointwise 1 0
  have hYPoint := hPointwise 0 1
  unfold crossDerivativeX crossDerivativeY at
    hOrigin hXPoint hYPoint
  constructor
  · linarith
  · constructor <;> linarith

/-- Exact finite polynomial Helmholtz classification. -/
theorem helmholtz_pointwise_iff_coefficients
    (system : QuadraticEulerSystem2) :
    HelmholtzAtAllPoints system ↔
      HelmholtzCoefficients system := by
  exact ⟨pointwise_helmholtz_implies_coefficients system,
    helmholtz_coefficients_imply_pointwise system⟩

/-- Cubic potential with zero affine part. -/
@[ext] structure CubicPotential2 where
  x2 : ℝ
  xy : ℝ
  y2 : ℝ
  x3 : ℝ
  x2y : ℝ
  xy2 : ℝ
  y3 : ℝ

/-- Potential value. -/
def potentialValue
    (potential : CubicPotential2)
    (x y : ℝ) : ℝ :=
  potential.x2 * x ^ 2 / 2 +
    potential.xy * x * y +
    potential.y2 * y ^ 2 / 2 +
    potential.x3 * x ^ 3 / 3 +
    potential.x2y * x ^ 2 * y / 2 +
    potential.xy2 * x * y ^ 2 +
    potential.y3 * y ^ 3 / 3

/-- Algebraic `x` derivative of the cubic potential. -/
def gradientX
    (potential : CubicPotential2)
    (x y : ℝ) : ℝ :=
  potential.x2 * x +
    potential.xy * y +
    potential.x3 * x ^ 2 +
    potential.x2y * x * y +
    potential.xy2 * y ^ 2

/-- Algebraic `y` derivative of the cubic potential. -/
def gradientY
    (potential : CubicPotential2)
    (x y : ℝ) : ℝ :=
  potential.xy * x +
    potential.y2 * y +
    potential.x2y * x ^ 2 / 2 +
    2 * potential.xy2 * x * y +
    potential.y3 * y ^ 2

/-- Canonical homotopy primitive reconstructed from the first equation. -/
def reconstructedPotential
    (system : QuadraticEulerSystem2) : CubicPotential2 :=
  { x2 := system.exX
    xy := system.exY
    y2 := system.eyY
    x3 := system.exXX
    x2y := system.exXY
    xy2 := system.exYY
    y3 := system.eyYY }

/-- The reconstructed potential always reproduces the first Euler component. -/
theorem reconstructed_gradient_x
    (system : QuadraticEulerSystem2)
    (x y : ℝ) :
    gradientX (reconstructedPotential system) x y =
      eulerX system x y := by
  rfl

/-- Under Helmholtz, the reconstructed potential reproduces the second equation. -/
theorem reconstructed_gradient_y
    (system : QuadraticEulerSystem2)
    (hHelmholtz : HelmholtzCoefficients system)
    (x y : ℝ) :
    gradientY (reconstructedPotential system) x y =
      eulerY system x y := by
  rcases hHelmholtz with ⟨hLinear, hX, hY⟩
  unfold gradientY reconstructedPotential eulerY
  have hHalf : system.exXY / 2 = system.eyXX := by
    linarith
  rw [hLinear, hHalf, hY]
  ring

/-- Nonlinear reconstruction theorem through cubic order. -/
theorem polynomial_helmholtz_reconstruction
    (system : QuadraticEulerSystem2)
    (hHelmholtz : HelmholtzAtAllPoints system) :
    ∃ potential : CubicPotential2,
      (∀ x y,
        gradientX potential x y = eulerX system x y) /\
      (∀ x y,
        gradientY potential x y = eulerY system x y) := by
  have hCoefficients :=
    pointwise_helmholtz_implies_coefficients system hHelmholtz
  exact ⟨reconstructedPotential system,
    reconstructed_gradient_x system,
    reconstructed_gradient_y system hCoefficients⟩

/-- A concrete non-Helmholtz source. -/
def nonVariationalSystem : QuadraticEulerSystem2 :=
  { exX := 1
    exY := 0
    exXX := 0
    exXY := 1
    exYY := 0
    eyX := 0
    eyY := 1
    eyXX := 0
    eyXY := 0
    eyYY := 0 }

/-- The concrete system fails the nonlinear Helmholtz test. -/
theorem nonvariational_system_fails_helmholtz :
    Not (HelmholtzAtAllPoints nonVariationalSystem) := by
  intro hHelmholtz
  have hCoefficients :=
    pointwise_helmholtz_implies_coefficients
      nonVariationalSystem hHelmholtz
  norm_num [HelmholtzCoefficients,
    nonVariationalSystem] at hCoefficients

/--
P-C nonlinear frontier: unlike a Hessian at one background, a complete local
Euler source contains higher-variation information.  Helmholtz reconstructs a
local action through the tested order, but global field theory additionally
requires gauge/Noether compatibility, boundary terms and variational
cohomology.
-/
structure PolynomialHelmholtzPhysicalStatus where
  localFieldCoordinatesConstructed : Prop
  completeEulerSourceDerived : Prop
  crossLinearizationComputed : Prop
  helmholtzIdentityProved : Prop
  homotopyPrimitiveConstructed : Prop
  gaugeNoetherIdentitiesCompatible : Prop
  patchingAcrossFieldSpaceProved : Prop
  nullLagrangiansClassified : Prop
  boundaryFunctionalsClassified : Prop
  higherOrdersControlled : Prop


def polynomialHelmholtzPhysicalClosure
    (s : PolynomialHelmholtzPhysicalStatus) : Prop :=
  s.localFieldCoordinatesConstructed /\
  s.completeEulerSourceDerived /\
  s.crossLinearizationComputed /\
  s.helmholtzIdentityProved /\
  s.homotopyPrimitiveConstructed /\
  s.gaugeNoetherIdentitiesCompatible /\
  s.patchingAcrossFieldSpaceProved /\
  s.nullLagrangiansClassified /\
  s.boundaryFunctionalsClassified /\
  s.higherOrdersControlled

end P0EFTJanusPolynomialHelmholtzReconstruction
end JanusFormal
