import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06SecondOrderRadialCartanHomotopy4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06T02FinsuppSecondJetHigherFrechetDerivative4D

/-!
# Radial Cartan classification of the terminal T02 density

The three radial samples `1/4`, `1/2`, and `3/4` recover all nonconstant
homogeneous pieces of a polynomial of degree at most four.  Combined with
the second-order radial Cartan identity, this gives an explicit horizontal
primitive for every terminal T02 density in the Euler kernel.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06T02DegreeFourRadialCartanClassification4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000
set_option maxRecDepth 100000
noncomputable section

open scoped BigOperators ContDiff

open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusProgramPActualLLSecondOrderJetProductVectorBundleCore4D
open P0EFTJanusProgramPActualPhysicalSecondOrderJetProductVectorBundleCore4D
open P0EFTJanusProgramPActualPhysicalSecondOrderJetInvariantLinearFunctionalBasis4D
open P0EFTJanusProgramPActualPhysicalSecondOrderJetInvariantDegreeFourFunctionalBasis4D
open P0EFTJanusProgramPT02InvariantLocalFunctionalBasisTerminalCertificate4D
open P0EFTJanusProgramPT06ThroatSpatialFinsuppJetTower4D
open P0EFTJanusProgramPT06LocalFunctionTotalDerivative4D
open P0EFTJanusProgramPT06SecondOrderLocalEuler4D
open P0EFTJanusProgramPT06ActualPhysicalValueProductSecondJetBridge4D
open P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D
open P0EFTJanusProgramPT06DiagonalPolynomialFrechetDerivative4D
open P0EFTJanusProgramPT06DiagonalPolynomialHigherFrechetDerivative4D
open P0EFTJanusProgramPT06DiagonalHomogeneousEulerIdentity4D
open P0EFTJanusProgramPT06T02DegreeFourFrechetDerivative4D
open P0EFTJanusProgramPT06T02FinsuppSecondJetFrechetDerivative4D
open P0EFTJanusProgramPT06T02FinsuppSecondJetHigherFrechetDerivative4D
open P0EFTJanusProgramPT06SecondOrderRadialCartanHomotopy4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

attribute [local instance]
  P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D.actualPhysicalValueProductNormedAddCommGroup
  P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D.actualPhysicalValueProductNormedSpace
  P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D.actualPhysicalValueProductFinsuppSecondJetFiniteDimensional
  P0EFTJanusProgramPT06T02DegreeFourFrechetDerivative4D.gate878ActualPhysicalFiniteDimensional
  P0EFTJanusProgramPT06T02DegreeFourFrechetDerivative4D.gate878ActualPhysicalNormedAddCommGroup
  P0EFTJanusProgramPT06T02DegreeFourFrechetDerivative4D.gate878ActualPhysicalNormedSpace

universe u

section Scaling

variable {Fiber : Type u} [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]

/-- Scalar multiplication as a continuous linear endomorphism of a finite
spatial jet. -/
def programPT06ThroatSpatialJetScalingContinuousLinearMap
    (order : Nat) (scalar : Real) :
    TruncatedThroatSpatialMultiindexJet Fiber order →L[Real]
      TruncatedThroatSpatialMultiindexJet Fiber order :=
  scalar • ContinuousLinearMap.id Real
    (TruncatedThroatSpatialMultiindexJet Fiber order)

@[simp] theorem programPT06ThroatSpatialJetScalingContinuousLinearMap_apply
    (order : Nat) (scalar : Real)
    (jet : TruncatedThroatSpatialMultiindexJet Fiber order) :
    programPT06ThroatSpatialJetScalingContinuousLinearMap
        (Fiber := Fiber) order scalar jet = scalar • jet := by
  simp [programPT06ThroatSpatialJetScalingContinuousLinearMap]

@[simp] theorem programPT06TruncateThroatSpatialMultiindexJet_smul
    {lower higher : Nat} (hOrder : lower ≤ higher) (scalar : Real)
    (jet : TruncatedThroatSpatialMultiindexJet Fiber higher) :
    truncateThroatSpatialMultiindexJet hOrder (scalar • jet) =
      scalar • truncateThroatSpatialMultiindexJet hOrder jet := by
  rfl

@[simp] theorem programPT06ThroatSpatialTotalDerivative_smul
    {order : Nat} (direction : Fin 3) (scalar : Real)
    (jet : TruncatedThroatSpatialMultiindexJet Fiber (order + 1)) :
    throatSpatialTotalDerivative direction (scalar • jet) =
      scalar • throatSpatialTotalDerivative direction jet := by
  rfl

/-- A total derivative commutes with precomposition by scalar multiplication
of jets. -/
theorem programPT06ThroatSpatialLocalFunctionTotalDerivative_precomposeScaling
    {order : Nat}
    (localFunction :
      TruncatedThroatSpatialMultiindexJet Fiber order → Real)
    (hLocalFunction : Differentiable Real localFunction)
    (scalar : Real) (direction : Fin 3)
    (jet : TruncatedThroatSpatialMultiindexJet Fiber (order + 1)) :
    programPT06ThroatSpatialLocalFunctionTotalDerivative direction
        (localFunction ∘
          programPT06ThroatSpatialJetScalingContinuousLinearMap
            (Fiber := Fiber) order scalar) jet =
      programPT06ThroatSpatialLocalFunctionTotalDerivative direction
        localFunction (scalar • jet) := by
  let scaling := programPT06ThroatSpatialJetScalingContinuousLinearMap
    (Fiber := Fiber) order scalar
  let base := truncateThroatSpatialMultiindexJet (Nat.le_succ order) jet
  have hDerivative : HasFDerivAt (localFunction ∘ scaling)
      ((fderiv Real localFunction (scaling base)).comp scaling) base :=
    ((hLocalFunction (scaling base)).hasFDerivAt).comp base
      scaling.hasFDerivAt
  change
    (fderiv Real (localFunction ∘ scaling) base)
        (throatSpatialTotalDerivative direction jet) =
      (fderiv Real localFunction
          (truncateThroatSpatialMultiindexJet (Nat.le_succ order)
            (scalar • jet)))
        (throatSpatialTotalDerivative direction (scalar • jet))
  rw [hDerivative.fderiv]
  simp [scaling, base]

/-- Precompose every component of a second-order horizontal current with
scalar multiplication of its third-jet argument. -/
def programPT06SecondOrderHorizontalCurrentPrecomposeScaling
    (scalar : Real)
    (current : ProgramPT06SecondOrderHorizontalCurrent4D
      (Fiber := Fiber)) :
    ProgramPT06SecondOrderHorizontalCurrent4D (Fiber := Fiber) :=
  fun direction => current direction ∘
    programPT06ThroatSpatialJetScalingContinuousLinearMap
      (Fiber := Fiber) 3 scalar

theorem
    programPT06SecondOrderHorizontalCurrentPrecomposeScaling_differentiable
    (scalar : Real)
    (current : ProgramPT06SecondOrderHorizontalCurrent4D
      (Fiber := Fiber))
    (hCurrent : ∀ direction, Differentiable Real (current direction))
    (direction : Fin 3) :
    Differentiable Real
      (programPT06SecondOrderHorizontalCurrentPrecomposeScaling
        scalar current direction) := by
  change Differentiable Real
    (current direction ∘
      programPT06ThroatSpatialJetScalingContinuousLinearMap
        (Fiber := Fiber) 3 scalar)
  exact (hCurrent direction).comp
    (programPT06ThroatSpatialJetScalingContinuousLinearMap
      (Fiber := Fiber) 3 scalar).differentiable

/-- Horizontal divergence commutes with the preceding current scaling. -/
theorem programPT06SecondOrderHorizontalCurrentDH_precomposeScaling
    (scalar : Real)
    (current : ProgramPT06SecondOrderHorizontalCurrent4D
      (Fiber := Fiber))
    (hCurrent : ∀ direction, Differentiable Real (current direction))
    (jet : ThroatSpatialMultiindexJet4 Fiber) :
    programPT06SecondOrderHorizontalCurrentDH
        (programPT06SecondOrderHorizontalCurrentPrecomposeScaling
          scalar current) jet =
      programPT06SecondOrderHorizontalCurrentDH current (scalar • jet) := by
  change
    (∑ direction : Fin 3,
      programPT06ThroatSpatialLocalFunctionTotalDerivative direction
        (current direction ∘
          programPT06ThroatSpatialJetScalingContinuousLinearMap
            (Fiber := Fiber) 3 scalar) jet) =
      ∑ direction : Fin 3,
        programPT06ThroatSpatialLocalFunctionTotalDerivative direction
          (current direction) (scalar • jet)
  apply Finset.sum_congr rfl
  intro direction _
  exact
    programPT06ThroatSpatialLocalFunctionTotalDerivative_precomposeScaling
      (current direction) (hCurrent direction) scalar direction jet

theorem programPT06ThroatSpatialLocalFunctionTotalDerivative_add
    {order : Nat}
    (first second :
      TruncatedThroatSpatialMultiindexJet Fiber order → Real)
    (hFirst : Differentiable Real first)
    (hSecond : Differentiable Real second)
    (direction : Fin 3)
    (jet : TruncatedThroatSpatialMultiindexJet Fiber (order + 1)) :
    programPT06ThroatSpatialLocalFunctionTotalDerivative direction
        (fun candidate => first candidate + second candidate) jet =
      programPT06ThroatSpatialLocalFunctionTotalDerivative direction first jet +
        programPT06ThroatSpatialLocalFunctionTotalDerivative direction
          second jet := by
  let base := truncateThroatSpatialMultiindexJet (Nat.le_succ order) jet
  let tangent := throatSpatialTotalDerivative direction jet
  have hDerivative := fderiv_add (hFirst base) (hSecond base)
  have hPoint := congrArg (fun derivative => derivative tangent) hDerivative
  convert hPoint using 1 <;> rfl

theorem programPT06ThroatSpatialLocalFunctionTotalDerivative_const_smul
    {order : Nat} (scalar : Real)
    (localFunction :
      TruncatedThroatSpatialMultiindexJet Fiber order → Real)
    (hLocalFunction : Differentiable Real localFunction)
    (direction : Fin 3)
    (jet : TruncatedThroatSpatialMultiindexJet Fiber (order + 1)) :
    programPT06ThroatSpatialLocalFunctionTotalDerivative direction
        (fun candidate => scalar • localFunction candidate) jet =
      scalar • programPT06ThroatSpatialLocalFunctionTotalDerivative direction
        localFunction jet := by
  let base := truncateThroatSpatialMultiindexJet (Nat.le_succ order) jet
  have hDerivative : HasFDerivAt
      (fun candidate => scalar • localFunction candidate)
      (scalar • fderiv Real localFunction base) base := by
    (convert ((hLocalFunction base).hasFDerivAt).const_smul scalar using 1;
      rfl)
  rw [programPT06ThroatSpatialLocalFunctionTotalDerivative_eq_of_hasFDerivAt
    direction _ jet _ hDerivative]
  rfl

theorem programPT06SecondOrderHorizontalCurrentDH_add
    (first second : ProgramPT06SecondOrderHorizontalCurrent4D
      (Fiber := Fiber))
    (hFirst : ∀ direction, Differentiable Real (first direction))
    (hSecond : ∀ direction, Differentiable Real (second direction))
    (jet : ThroatSpatialMultiindexJet4 Fiber) :
    programPT06SecondOrderHorizontalCurrentDH (first + second) jet =
      programPT06SecondOrderHorizontalCurrentDH first jet +
        programPT06SecondOrderHorizontalCurrentDH second jet := by
  change
    (∑ direction : Fin 3,
      programPT06ThroatSpatialLocalFunctionTotalDerivative direction
        (fun candidate => first direction candidate +
          second direction candidate) jet) =
      (∑ direction : Fin 3,
        programPT06ThroatSpatialLocalFunctionTotalDerivative direction
          (first direction) jet) +
      ∑ direction : Fin 3,
        programPT06ThroatSpatialLocalFunctionTotalDerivative direction
          (second direction) jet
  calc
    _ = ∑ direction : Fin 3,
        (programPT06ThroatSpatialLocalFunctionTotalDerivative direction
            (first direction) jet +
          programPT06ThroatSpatialLocalFunctionTotalDerivative direction
            (second direction) jet) := by
      apply Finset.sum_congr rfl
      intro direction _
      exact programPT06ThroatSpatialLocalFunctionTotalDerivative_add
        (first direction) (second direction)
        (hFirst direction) (hSecond direction) direction jet
    _ = _ := Finset.sum_add_distrib

theorem programPT06SecondOrderHorizontalCurrentDH_const_smul
    (scalar : Real)
    (current : ProgramPT06SecondOrderHorizontalCurrent4D
      (Fiber := Fiber))
    (hCurrent : ∀ direction, Differentiable Real (current direction))
    (jet : ThroatSpatialMultiindexJet4 Fiber) :
    programPT06SecondOrderHorizontalCurrentDH (scalar • current) jet =
      scalar • programPT06SecondOrderHorizontalCurrentDH current jet := by
  change
    (∑ direction : Fin 3,
      programPT06ThroatSpatialLocalFunctionTotalDerivative direction
        (fun candidate => scalar • current direction candidate) jet) =
      scalar • ∑ direction : Fin 3,
        programPT06ThroatSpatialLocalFunctionTotalDerivative direction
          (current direction) jet
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro direction _
  exact programPT06ThroatSpatialLocalFunctionTotalDerivative_const_smul
    scalar (current direction) (hCurrent direction) direction jet

/-- The three-sample quadrature current associated with a current. -/
def programPT06SecondOrderRadialQuadratureCurrent
    (current : ProgramPT06SecondOrderHorizontalCurrent4D
      (Fiber := Fiber)) :
    ProgramPT06SecondOrderHorizontalCurrent4D (Fiber := Fiber) :=
  (8 / 3 : Real) •
      programPT06SecondOrderHorizontalCurrentPrecomposeScaling
        (1 / 4 : Real) current +
    (-2 / 3 : Real) •
      programPT06SecondOrderHorizontalCurrentPrecomposeScaling
        (1 / 2 : Real) current +
    (8 / 9 : Real) •
      programPT06SecondOrderHorizontalCurrentPrecomposeScaling
        (3 / 4 : Real) current

theorem programPT06SecondOrderRadialQuadratureCurrent_DH
    (current : ProgramPT06SecondOrderHorizontalCurrent4D
      (Fiber := Fiber))
    (hCurrent : ∀ direction, Differentiable Real (current direction))
    (jet : ThroatSpatialMultiindexJet4 Fiber) :
    programPT06SecondOrderHorizontalCurrentDH
        (programPT06SecondOrderRadialQuadratureCurrent current) jet =
      (8 / 3 : Real) • programPT06SecondOrderHorizontalCurrentDH current
          ((1 / 4 : Real) • jet) +
        (-2 / 3 : Real) • programPT06SecondOrderHorizontalCurrentDH current
          ((1 / 2 : Real) • jet) +
        (8 / 9 : Real) • programPT06SecondOrderHorizontalCurrentDH current
          ((3 / 4 : Real) • jet) := by
  let first := programPT06SecondOrderHorizontalCurrentPrecomposeScaling
    (Fiber := Fiber) (1 / 4 : Real) current
  let second := programPT06SecondOrderHorizontalCurrentPrecomposeScaling
    (Fiber := Fiber) (1 / 2 : Real) current
  let third := programPT06SecondOrderHorizontalCurrentPrecomposeScaling
    (Fiber := Fiber) (3 / 4 : Real) current
  have hFirst : ∀ direction, Differentiable Real (first direction) :=
    fun direction =>
      programPT06SecondOrderHorizontalCurrentPrecomposeScaling_differentiable
        (1 / 4 : Real) current hCurrent direction
  have hSecond : ∀ direction, Differentiable Real (second direction) :=
    fun direction =>
      programPT06SecondOrderHorizontalCurrentPrecomposeScaling_differentiable
        (1 / 2 : Real) current hCurrent direction
  have hThird : ∀ direction, Differentiable Real (third direction) :=
    fun direction =>
      programPT06SecondOrderHorizontalCurrentPrecomposeScaling_differentiable
        (3 / 4 : Real) current hCurrent direction
  change programPT06SecondOrderHorizontalCurrentDH
      (((8 / 3 : Real) • first + (-2 / 3 : Real) • second) +
        (8 / 9 : Real) • third) jet = _
  rw [programPT06SecondOrderHorizontalCurrentDH_add
      ((8 / 3 : Real) • first + (-2 / 3 : Real) • second)
      ((8 / 9 : Real) • third)
      (fun direction =>
        ((hFirst direction).const_smul (8 / 3 : Real)).add
          ((hSecond direction).const_smul (-2 / 3 : Real)))
      (fun direction => (hThird direction).const_smul (8 / 9 : Real)) jet,
    programPT06SecondOrderHorizontalCurrentDH_add
      ((8 / 3 : Real) • first) ((-2 / 3 : Real) • second)
      (fun direction => (hFirst direction).const_smul (8 / 3 : Real))
      (fun direction => (hSecond direction).const_smul (-2 / 3 : Real)) jet,
    programPT06SecondOrderHorizontalCurrentDH_const_smul
      (8 / 3 : Real) first hFirst jet,
    programPT06SecondOrderHorizontalCurrentDH_const_smul
      (-2 / 3 : Real) second hSecond jet,
    programPT06SecondOrderHorizontalCurrentDH_const_smul
      (8 / 9 : Real) third hThird jet,
    programPT06SecondOrderHorizontalCurrentDH_precomposeScaling
      (1 / 4 : Real) current hCurrent jet,
    programPT06SecondOrderHorizontalCurrentDH_precomposeScaling
      (1 / 2 : Real) current hCurrent jet,
    programPT06SecondOrderHorizontalCurrentDH_precomposeScaling
      (3 / 4 : Real) current hCurrent jet]

end Scaling

section Quadrature

variable {FieldFiber : Type u}
variable [NormedAddCommGroup FieldFiber] [NormedSpace Real FieldFiber]

/-- Radial derivative of a polynomial of degree at most four. -/
theorem programPT06DiagonalPolynomial_radialFrechetDerivative
    (polynomial : ProgramPT06DiagonalPolynomialUpToFour4D FieldFiber)
    (scalar : Real) (field : FieldFiber) :
    fderiv Real (programPT06DiagonalPolynomialEvaluation polynomial)
        (scalar • field) (scalar • field) =
      scalar * polynomial.linear field +
        (2 : Real) * scalar ^ 2 *
          programPT06DiagonalHomogeneousTerm polynomial.quadratic field +
        (3 : Real) * scalar ^ 3 *
          programPT06DiagonalHomogeneousTerm polynomial.cubic field +
        (4 : Real) * scalar ^ 4 *
          programPT06DiagonalHomogeneousTerm polynomial.quartic field := by
  rw [programPT06DiagonalPolynomialEvaluation_fderiv]
  simp only [programPT06DiagonalPolynomialDerivative,
    add_apply,
    programPT06DiagonalQuadraticDerivative,
    programPT06DiagonalCubicDerivative,
    programPT06DiagonalQuarticDerivative]
  rw [programPT06DiagonalHomogeneousDerivative_self
      polynomial.quadratic (scalar • field),
    programPT06DiagonalHomogeneousDerivative_self
      polynomial.cubic (scalar • field),
    programPT06DiagonalHomogeneousDerivative_self
      polynomial.quartic (scalar • field),
    map_smul,
    programPT06DiagonalHomogeneousTerm_smul
      polynomial.quadratic scalar field,
    programPT06DiagonalHomogeneousTerm_smul
      polynomial.cubic scalar field,
    programPT06DiagonalHomogeneousTerm_smul
      polynomial.quartic scalar field]
  ring

/-- Three radial derivative samples recover all nonconstant terms through
degree four. -/
theorem programPT06DiagonalPolynomial_radialQuadrature
    (polynomial : ProgramPT06DiagonalPolynomialUpToFour4D FieldFiber)
    (field : FieldFiber) :
    programPT06DiagonalPolynomialEvaluation polynomial field =
      polynomial.constant +
        (8 / 3 : Real) •
          fderiv Real (programPT06DiagonalPolynomialEvaluation polynomial)
            ((1 / 4 : Real) • field) ((1 / 4 : Real) • field) +
        (-2 / 3 : Real) •
          fderiv Real (programPT06DiagonalPolynomialEvaluation polynomial)
            ((1 / 2 : Real) • field) ((1 / 2 : Real) • field) +
        (8 / 9 : Real) •
          fderiv Real (programPT06DiagonalPolynomialEvaluation polynomial)
            ((3 / 4 : Real) • field) ((3 / 4 : Real) • field) := by
  rw [programPT06DiagonalPolynomial_radialFrechetDerivative polynomial
      (1 / 4 : Real) field,
    programPT06DiagonalPolynomial_radialFrechetDerivative polynomial
      (1 / 2 : Real) field,
    programPT06DiagonalPolynomial_radialFrechetDerivative polynomial
      (3 / 4 : Real) field]
  simp only [programPT06DiagonalPolynomialEvaluation,
    programPT06DiagonalConstantTerm,
    programPT06DiagonalLinearTerm,
    programPT06DiagonalQuadraticTerm,
    programPT06DiagonalCubicTerm,
    programPT06DiagonalQuarticTerm, smul_eq_mul]
  ring

end Quadrature

private abbrev Fiber := ActualPhysicalValueProductFiber
private abbrev SecondJet := ThroatSpatialMultiindexJet2 Fiber
private abbrev ThirdJet := ThroatSpatialMultiindexJet3 Fiber
private abbrev FourthJet := ThroatSpatialMultiindexJet4 Fiber

variable (period : Real) (hPeriod : period ≠ 0)

/-- The same quadrature identity for the genuine finsupp T02 Lagrangian. -/
theorem programPT06T02FinsuppSecondJetLocalLagrangian_radialQuadrature
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (jet : SecondJet) :
    programPT06T02FinsuppSecondJetLocalLagrangian
        period hPeriod functional jet =
      functional.lower.lower.constant +
        (8 / 3 : Real) •
          fderiv Real
            (programPT06T02FinsuppSecondJetLocalLagrangian
              period hPeriod functional)
            ((1 / 4 : Real) • jet) ((1 / 4 : Real) • jet) +
        (-2 / 3 : Real) •
          fderiv Real
            (programPT06T02FinsuppSecondJetLocalLagrangian
              period hPeriod functional)
            ((1 / 2 : Real) • jet) ((1 / 2 : Real) • jet) +
        (8 / 9 : Real) •
          fderiv Real
            (programPT06T02FinsuppSecondJetLocalLagrangian
              period hPeriod functional)
            ((3 / 4 : Real) • jet) ((3 / 4 : Real) • jet) := by
  let polynomial :=
    programPT06T02DegreeFourDiagonalPolynomial period hPeriod functional
  let bridge := programPT06T02FinsuppSecondJetBridge
  let localLagrangian :=
    programPT06T02FinsuppSecondJetLocalLagrangian period hPeriod functional
  have hRadial (scalar : Real) :
      fderiv Real localLagrangian (scalar • jet) (scalar • jet) =
        fderiv Real (programPT06DiagonalPolynomialEvaluation polynomial)
          (scalar • bridge jet) (scalar • bridge jet) := by
    rw [programPT06T02FinsuppSecondJetLocalLagrangian_fderiv,
      programPT06DiagonalPolynomialEvaluation_fderiv]
    change
      programPT06DiagonalPolynomialDerivative polynomial
          (bridge (scalar • jet)) (bridge (scalar • jet)) =
        programPT06DiagonalPolynomialDerivative polynomial
          (scalar • bridge jet) (scalar • bridge jet)
    simp
  have hPhysical :=
    programPT06DiagonalPolynomial_radialQuadrature polynomial (bridge jet)
  change localLagrangian jet = _
  calc
    localLagrangian jet =
        actualPhysicalSecondOrderJetInvariantDegreeFourEvaluation
          period hPeriod functional (bridge jet) := by
      rfl
    _ = programPT06DiagonalPolynomialEvaluation polynomial (bridge jet) := by
      rw [programPT06T02DegreeFourEvaluation_eq period hPeriod functional]
    _ = polynomial.constant +
          (8 / 3 : Real) •
            fderiv Real (programPT06DiagonalPolynomialEvaluation polynomial)
              ((1 / 4 : Real) • bridge jet)
              ((1 / 4 : Real) • bridge jet) +
          (-2 / 3 : Real) •
            fderiv Real (programPT06DiagonalPolynomialEvaluation polynomial)
              ((1 / 2 : Real) • bridge jet)
              ((1 / 2 : Real) • bridge jet) +
          (8 / 9 : Real) •
            fderiv Real (programPT06DiagonalPolynomialEvaluation polynomial)
              ((3 / 4 : Real) • bridge jet)
              ((3 / 4 : Real) • bridge jet) := hPhysical
    _ = functional.lower.lower.constant +
          (8 / 3 : Real) •
            fderiv Real localLagrangian
              ((1 / 4 : Real) • jet) ((1 / 4 : Real) • jet) +
          (-2 / 3 : Real) •
            fderiv Real localLagrangian
              ((1 / 2 : Real) • jet) ((1 / 2 : Real) • jet) +
          (8 / 9 : Real) •
            fderiv Real localLagrangian
              ((3 / 4 : Real) • jet) ((3 / 4 : Real) • jet) := by
      rw [hRadial (1 / 4 : Real), hRadial (1 / 2 : Real),
        hRadial (3 / 4 : Real)]
      rfl

/-- Explicit three-sample Cartan current for the terminal T02 density. -/
def programPT06T02DegreeFourRadialCartanCurrent
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod) :
    ProgramPT06SecondOrderHorizontalCurrent4D (Fiber := Fiber) :=
  programPT06SecondOrderRadialQuadratureCurrent
    (programPT06SecondOrderRadialCartanCurrent
      (programPT06T02FinsuppSecondJetLocalLagrangian
        period hPeriod functional))

/-- A terminal T02 density whose genuine second-order Euler expression
vanishes is its constant term plus the horizontal differential of the
explicit quadrature Cartan current. -/
theorem
    programPT06T02DegreeFourLocalLagrangian_eq_constant_add_currentDH
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (hEuler : ∀ jet : FourthJet,
      programPT06SecondOrderLocalEuler
        (programPT06T02FinsuppSecondJetLocalLagrangian
          period hPeriod functional) jet = 0)
    (jet : FourthJet) :
    programPT06T02FinsuppSecondJetLocalLagrangian period hPeriod functional
        (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 4) jet) =
      functional.lower.lower.constant +
        programPT06SecondOrderHorizontalCurrentDH
          (programPT06T02DegreeFourRadialCartanCurrent
            period hPeriod functional) jet := by
  let localLagrangian :=
    programPT06T02FinsuppSecondJetLocalLagrangian period hPeriod functional
  let jetTwo :=
    truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 4) jet
  let baseCurrent :=
    programPT06SecondOrderRadialCartanCurrent localLagrangian
  have hLagrangian : ContDiff Real 3 localLagrangian :=
    (programPT06T02FinsuppSecondJetLocalLagrangian_contDiff
      period hPeriod functional).of_le
      (show (3 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  have hCurrent : ∀ direction,
      Differentiable Real (baseCurrent direction) :=
    fun direction =>
      programPT06SecondOrderRadialCartanCurrentComponent_differentiable
        localLagrangian hLagrangian direction
  have hCartanAt (scalar : Real) :
      fderiv Real localLagrangian (scalar • jetTwo) (scalar • jetTwo) =
        programPT06SecondOrderHorizontalCurrentDH baseCurrent
          (scalar • jet) := by
    have hIdentity := programPT06SecondOrderRadialCartanIdentity
      localLagrangian hLagrangian (scalar • jet)
    rw [hEuler (scalar • jet)] at hIdentity
    simpa only [programPT06TruncateThroatSpatialMultiindexJet_smul,
      zero_apply, zero_add, jetTwo, baseCurrent,
      programPT06SecondOrderRadialCartanCurrentDH] using hIdentity
  have hQuadrature :=
    programPT06T02FinsuppSecondJetLocalLagrangian_radialQuadrature
      period hPeriod functional jetTwo
  change localLagrangian jetTwo = _
  calc
    localLagrangian jetTwo =
        functional.lower.lower.constant +
          (8 / 3 : Real) •
            fderiv Real localLagrangian
              ((1 / 4 : Real) • jetTwo) ((1 / 4 : Real) • jetTwo) +
          (-2 / 3 : Real) •
            fderiv Real localLagrangian
              ((1 / 2 : Real) • jetTwo) ((1 / 2 : Real) • jetTwo) +
          (8 / 9 : Real) •
            fderiv Real localLagrangian
              ((3 / 4 : Real) • jetTwo) ((3 / 4 : Real) • jetTwo) :=
      hQuadrature
    _ = functional.lower.lower.constant +
          (8 / 3 : Real) •
            programPT06SecondOrderHorizontalCurrentDH baseCurrent
              ((1 / 4 : Real) • jet) +
          (-2 / 3 : Real) •
            programPT06SecondOrderHorizontalCurrentDH baseCurrent
              ((1 / 2 : Real) • jet) +
          (8 / 9 : Real) •
            programPT06SecondOrderHorizontalCurrentDH baseCurrent
              ((3 / 4 : Real) • jet) := by
      rw [hCartanAt (1 / 4 : Real), hCartanAt (1 / 2 : Real),
        hCartanAt (3 / 4 : Real)]
    _ = functional.lower.lower.constant +
          programPT06SecondOrderHorizontalCurrentDH
            (programPT06T02DegreeFourRadialCartanCurrent
              period hPeriod functional) jet := by
      rw [programPT06T02DegreeFourRadialCartanCurrent,
        programPT06SecondOrderRadialQuadratureCurrent_DH
          baseCurrent hCurrent jet]
      ring

/-- Existential form of the terminal T02 Euler-kernel classification. -/
theorem programPT06T02DegreeFour_exists_current_of_euler_eq_zero
    (functional :
      ProgramPT02AdmissibleInvariantLocalFunctional4D period hPeriod)
    (hEuler : ∀ jet : FourthJet,
      programPT06SecondOrderLocalEuler
        (programPT06T02FinsuppSecondJetLocalLagrangian
          period hPeriod functional) jet = 0) :
    ∃ current : Fin 3 → ThirdJet → Real,
      ∀ jet : FourthJet,
        programPT06T02FinsuppSecondJetLocalLagrangian
            period hPeriod functional
            (truncateThroatSpatialMultiindexJet (by omega : 2 ≤ 4) jet) =
          functional.lower.lower.constant +
            programPT06SecondOrderHorizontalCurrentDH current jet := by
  refine ⟨programPT06T02DegreeFourRadialCartanCurrent
    period hPeriod functional, ?_⟩
  intro jet
  exact
    programPT06T02DegreeFourLocalLagrangian_eq_constant_add_currentDH
      period hPeriod functional hEuler jet

end
end P0EFTJanusProgramPT06T02DegreeFourRadialCartanClassification4D
end JanusFormal
