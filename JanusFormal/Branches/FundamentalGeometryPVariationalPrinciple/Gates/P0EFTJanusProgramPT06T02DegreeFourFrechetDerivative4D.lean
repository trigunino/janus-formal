import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT02InvariantLocalFunctionalBasisTerminalCertificate4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06DiagonalPolynomialFrechetDerivative4D

/-!
# Fiberwise Frechet derivative of the terminal T02 functional

This gate converts the curried continuous forms carried by the terminal T02
degree-four functional into continuous multilinear maps and applies the
degree-at-most-four derivative calculation of Gate876.  The result is only a
fiberwise Frechet derivative on the actual physical second-jet fiber.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06T02DegreeFourFrechetDerivative4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000
set_option maxRecDepth 100000
noncomputable section

open scoped BigOperators

open P0EFTJanusProgramPActualLLSecondOrderJetProductVectorBundleCore4D
open P0EFTJanusProgramPActualPhysicalSecondOrderJetProductVectorBundleCore4D
open P0EFTJanusProgramPActualPhysicalSecondOrderJetInvariantLinearFunctionalBasis4D
open P0EFTJanusProgramPActualPhysicalSecondOrderJetInvariantQuadraticFunctionalBasis4D
open P0EFTJanusProgramPActualPhysicalSecondOrderJetInvariantDegreeTwoFunctionalBasis4D
open P0EFTJanusProgramPActualPhysicalSecondOrderJetInvariantCubicFunctionalBasis4D
open P0EFTJanusProgramPActualPhysicalSecondOrderJetInvariantDegreeThreeFunctionalBasis4D
open P0EFTJanusProgramPActualPhysicalSecondOrderJetInvariantQuarticFunctionalBasis4D
open P0EFTJanusProgramPActualPhysicalSecondOrderJetInvariantDegreeFourFunctionalBasis4D
open P0EFTJanusProgramPT02InvariantLocalFunctionalBasisTerminalCertificate4D
open P0EFTJanusProgramPT06DiagonalPolynomialFrechetDerivative4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule

local instance gate878ActualLLNormedAddCommGroup :
    NormedAddCommGroup ActualLLSecondOrderJetFiber :=
  actualLLNormedAddCommGroup

local instance gate878ActualLLNormedSpace :
    NormedSpace Real ActualLLSecondOrderJetFiber :=
  actualLLNormedSpace

local instance gate878ActualPhysicalFiniteDimensional :
    FiniteDimensional Real ActualPhysicalSecondOrderJetProductFiber :=
  actualPhysicalFiniteDimensional

private abbrev Fiber := ActualPhysicalSecondOrderJetProductFiber

local instance gate878ActualPhysicalNormedAddCommGroup :
    NormedAddCommGroup Fiber := inferInstance

local instance gate878ActualPhysicalNormedSpace :
    NormedSpace Real Fiber := inferInstance

private abbrev LinearForm := Fiber →L[Real] Real
private abbrev BilinearForm := Fiber →L[Real] LinearForm
private abbrev TrilinearForm := Fiber →L[Real] BilinearForm
private abbrev QuadrilinearForm := Fiber →L[Real] TrilinearForm

local instance gate878LinearNormedAddCommGroup :
    NormedAddCommGroup LinearForm := inferInstance
local instance gate878LinearNormedSpace :
    NormedSpace Real LinearForm := inferInstance
local instance gate878BilinearNormedAddCommGroup :
    NormedAddCommGroup BilinearForm := inferInstance
local instance gate878BilinearNormedSpace :
    NormedSpace Real BilinearForm := inferInstance
local instance gate878TrilinearNormedAddCommGroup :
    NormedAddCommGroup TrilinearForm := inferInstance
local instance gate878TrilinearNormedSpace :
    NormedSpace Real TrilinearForm := inferInstance
local instance gate878QuadrilinearNormedAddCommGroup :
    NormedAddCommGroup QuadrilinearForm := inferInstance
local instance gate878QuadrilinearNormedSpace :
    NormedSpace Real QuadrilinearForm := inferInstance

private abbrev HomogeneousForm (degree : Nat) :=
  ProgramPT06ContinuousHomogeneousForm4D Fiber degree

local instance gate878HomogeneousNormedAddCommGroup (degree : Nat) :
    NormedAddCommGroup (HomogeneousForm degree) := inferInstance
local instance gate878HomogeneousNormedSpace (degree : Nat) :
    NormedSpace Real (HomogeneousForm degree) := inferInstance

/-- The canonical one-variable multilinear presentation of a continuous
linear form. -/
def programPT06T02UncurryLinearForm
    (form : LinearForm) : HomogeneousForm 1 :=
  (continuousMultilinearCurryFin1 Real Fiber Real).symm form

@[simp] theorem programPT06T02UncurryLinearForm_apply
    (form : LinearForm) (arguments : Fin 1 → Fiber) :
    programPT06T02UncurryLinearForm form arguments = form (arguments 0) := by
  rfl

/-- The canonical two-variable multilinear presentation of a curried
continuous bilinear form. -/
def programPT06T02UncurryBilinearForm
    (form : BilinearForm) : HomogeneousForm 2 :=
  let inner : Fiber →ₗ[Real] HomogeneousForm 1 :=
    { toFun := fun x => programPT06T02UncurryLinearForm (form x)
      map_add' := by
        intro x y
        ext arguments
        simp
      map_smul' := by
        intro scalar x
        ext arguments
        simp }
  inner.toContinuousLinearMap.uncurryLeft

@[simp] theorem programPT06T02UncurryBilinearForm_apply
    (form : BilinearForm) (arguments : Fin 2 → Fiber) :
    programPT06T02UncurryBilinearForm form arguments =
      form (arguments 0) (arguments 1) := by
  simp [programPT06T02UncurryBilinearForm, Fin.tail]

/-- The canonical three-variable multilinear presentation of a curried
continuous trilinear form. -/
def programPT06T02UncurryTrilinearForm
    (form : TrilinearForm) : HomogeneousForm 3 :=
  let inner : Fiber →ₗ[Real] HomogeneousForm 2 :=
    { toFun := fun x => programPT06T02UncurryBilinearForm (form x)
      map_add' := by
        intro x y
        ext arguments
        simp
      map_smul' := by
        intro scalar x
        ext arguments
        simp }
  inner.toContinuousLinearMap.uncurryLeft

@[simp] theorem programPT06T02UncurryTrilinearForm_apply
    (form : TrilinearForm) (arguments : Fin 3 → Fiber) :
    programPT06T02UncurryTrilinearForm form arguments =
      form (arguments 0) (arguments 1) (arguments 2) := by
  simp [programPT06T02UncurryTrilinearForm, Fin.tail]

/-- The canonical four-variable multilinear presentation of a curried
continuous quadrilinear form. -/
def programPT06T02UncurryQuadrilinearForm
    (form : QuadrilinearForm) : HomogeneousForm 4 :=
  let inner : Fiber →ₗ[Real] HomogeneousForm 3 :=
    { toFun := fun x => programPT06T02UncurryTrilinearForm (form x)
      map_add' := by
        intro x y
        ext arguments
        simp
      map_smul' := by
        intro scalar x
        ext arguments
        simp }
  inner.toContinuousLinearMap.uncurryLeft

@[simp] theorem programPT06T02UncurryQuadrilinearForm_apply
    (form : QuadrilinearForm) (arguments : Fin 4 → Fiber) :
    programPT06T02UncurryQuadrilinearForm form arguments =
      form (arguments 0) (arguments 1) (arguments 2) (arguments 3) := by
  simp [programPT06T02UncurryQuadrilinearForm, Fin.tail]

variable (period : Real) (hPeriod : period ≠ 0)

/-- The terminal T02 functional, presented as the diagonal polynomial data
used by Gate876. -/
def programPT06T02DegreeFourDiagonalPolynomial
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod) :
    ProgramPT06DiagonalPolynomialUpToFour4D Fiber where
  constant := functional.lower.lower.constant
  linear := functional.lower.lower.linear.1
  quadratic :=
    programPT06T02UncurryBilinearForm functional.lower.lower.quadratic.1
  cubic := programPT06T02UncurryTrilinearForm functional.lower.cubic.1
  quartic := programPT06T02UncurryQuadrilinearForm functional.quartic.1

/-- The diagonal polynomial presentation evaluates to the original nested
T02 functional. -/
@[simp] theorem programPT06T02DegreeFourDiagonalPolynomial_evaluation
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (jet : Fiber) :
    programPT06DiagonalPolynomialEvaluation
        (programPT06T02DegreeFourDiagonalPolynomial period hPeriod functional) jet =
      actualPhysicalSecondOrderJetInvariantDegreeFourEvaluation period hPeriod
        functional jet := by
  simp [programPT06DiagonalPolynomialEvaluation,
    programPT06T02DegreeFourDiagonalPolynomial,
    programPT06DiagonalConstantTerm,
    programPT06DiagonalLinearTerm,
    programPT06DiagonalQuadraticTerm,
    programPT06DiagonalCubicTerm,
    programPT06DiagonalQuarticTerm,
    programPT06DiagonalHomogeneousTerm,
    actualPhysicalSecondOrderJetInvariantDegreeFourEvaluation,
    actualPhysicalSecondOrderJetInvariantDegreeThreeEvaluation,
    actualPhysicalSecondOrderJetInvariantDegreeTwoEvaluation,
    actualPhysicalSecondOrderJetInvariantQuadraticEvaluation,
    actualPhysicalSecondOrderJetInvariantCubicEvaluation,
    actualPhysicalSecondOrderJetInvariantQuarticEvaluation]

theorem programPT06T02DegreeFourEvaluation_eq
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod) :
    actualPhysicalSecondOrderJetInvariantDegreeFourEvaluation period hPeriod
        functional =
      programPT06DiagonalPolynomialEvaluation
        (programPT06T02DegreeFourDiagonalPolynomial period hPeriod functional) := by
  funext jet
  exact (programPT06T02DegreeFourDiagonalPolynomial_evaluation
    period hPeriod functional jet).symm

/-- The complete fiberwise Frechet derivative of the terminal T02 evaluation. -/
def programPT06T02DegreeFourFrechetDerivative
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (jet : Fiber) : Fiber →L[Real] Real :=
  programPT06DiagonalPolynomialDerivative
    (programPT06T02DegreeFourDiagonalPolynomial period hPeriod functional) jet

@[simp] theorem programPT06T02DegreeFourFrechetDerivative_apply
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (jet direction : Fiber) :
    programPT06T02DegreeFourFrechetDerivative period hPeriod functional jet direction =
      functional.lower.lower.linear.1 direction +
        (∑ slot : Fin 2,
          programPT06T02UncurryBilinearForm functional.lower.lower.quadratic.1
            (Function.update (fun _ => jet) slot direction)) +
        (∑ slot : Fin 3,
          programPT06T02UncurryTrilinearForm functional.lower.cubic.1
            (Function.update (fun _ => jet) slot direction)) +
        ∑ slot : Fin 4,
          programPT06T02UncurryQuadrilinearForm functional.quartic.1
            (Function.update (fun _ => jet) slot direction) := by
  simpa [programPT06T02DegreeFourFrechetDerivative,
    programPT06T02DegreeFourDiagonalPolynomial] using
    programPT06DiagonalPolynomialDerivative_apply
      (programPT06T02DegreeFourDiagonalPolynomial period hPeriod functional)
      jet direction

/-- The original T02 evaluation has the explicit Gate876 derivative at every
actual physical second jet. -/
theorem programPT06T02DegreeFourEvaluation_hasFDerivAt
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (jet : Fiber) :
    HasFDerivAt
      (actualPhysicalSecondOrderJetInvariantDegreeFourEvaluation period hPeriod
        functional)
      (programPT06T02DegreeFourFrechetDerivative period hPeriod functional jet)
      jet := by
  rw [programPT06T02DegreeFourEvaluation_eq period hPeriod functional]
  exact programPT06DiagonalPolynomialEvaluation_hasFDerivAt
    (programPT06T02DegreeFourDiagonalPolynomial period hPeriod functional) jet

/-- `fderiv` of the original T02 evaluation is the complete explicit
degree-at-most-four derivative. -/
theorem programPT06T02DegreeFourEvaluation_fderiv
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (jet : Fiber) :
    fderiv Real
        (actualPhysicalSecondOrderJetInvariantDegreeFourEvaluation period hPeriod
          functional) jet =
      programPT06T02DegreeFourFrechetDerivative period hPeriod functional jet :=
  (programPT06T02DegreeFourEvaluation_hasFDerivAt
    period hPeriod functional jet).fderiv

end

end P0EFTJanusProgramPT06T02DegreeFourFrechetDerivative4D
end JanusFormal
