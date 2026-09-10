import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06ThroatSpatialFinsuppJetTower4D

/-!
# Vertical and total derivatives of local functions

This gate defines coordinate variations in a finite spatial multi-index jet,
vertical partial derivatives through `fderiv`, and the formal total derivative
of a local function by the jet-chain-rule formula.

As in Mathlib, `fderiv` is totalized by zero away from differentiability
points.  The accompanying `HasFDerivAt` formulas record the intended C1 use.
No Euler operator, horizontal exactness or terminal T06 classification is
asserted here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06LocalFunctionTotalDerivative4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPT06ThroatSpatialFinsuppJetTower4D

universe u v

variable {Fiber : Type u} [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
variable {Target : Type v} [NormedAddCommGroup Target] [NormedSpace Real Target]

/-- Inject one field variation into one truncated multi-index coordinate. -/
def programPT06ThroatSpatialJetCoordinateInjection
    {order : Nat} (index : ThroatSpatialTruncatedIndex order) :
    Fiber →L[Real] TruncatedThroatSpatialMultiindexJet Fiber order :=
  ContinuousLinearMap.single Real
    (fun _ : ThroatSpatialTruncatedIndex order => Fiber) index

@[simp] theorem programPT06ThroatSpatialJetCoordinateInjection_same
    {order : Nat} (index : ThroatSpatialTruncatedIndex order)
    (variation : Fiber) :
    programPT06ThroatSpatialJetCoordinateInjection index variation index =
      variation := by
  simp [programPT06ThroatSpatialJetCoordinateInjection]

@[simp] theorem programPT06ThroatSpatialJetCoordinateInjection_of_ne
    {order : Nat} (index coordinate : ThroatSpatialTruncatedIndex order)
    (hCoordinate : coordinate ≠ index) (variation : Fiber) :
    programPT06ThroatSpatialJetCoordinateInjection index variation coordinate =
      0 := by
  simp [programPT06ThroatSpatialJetCoordinateInjection, hCoordinate]

/-- Vertical partial derivative of a local function in one multi-index slot. -/
def programPT06ThroatSpatialVerticalPartialDerivative
    {order : Nat}
    (localFunction : TruncatedThroatSpatialMultiindexJet Fiber order → Target)
    (jet : TruncatedThroatSpatialMultiindexJet Fiber order)
    (index : ThroatSpatialTruncatedIndex order) : Fiber →L[Real] Target :=
  (fderiv Real localFunction jet).comp
    (programPT06ThroatSpatialJetCoordinateInjection index)

@[simp] theorem programPT06ThroatSpatialVerticalPartialDerivative_apply
    {order : Nat}
    (localFunction : TruncatedThroatSpatialMultiindexJet Fiber order → Target)
    (jet : TruncatedThroatSpatialMultiindexJet Fiber order)
    (index : ThroatSpatialTruncatedIndex order) (variation : Fiber) :
    programPT06ThroatSpatialVerticalPartialDerivative
        localFunction jet index variation =
      fderiv Real localFunction jet
        (programPT06ThroatSpatialJetCoordinateInjection index variation) :=
  rfl

/-- At a differentiability point, the vertical partial is the supplied
Frechet derivative restricted to the selected jet coordinate. -/
theorem programPT06ThroatSpatialVerticalPartialDerivative_eq_of_hasFDerivAt
    {order : Nat}
    (localFunction : TruncatedThroatSpatialMultiindexJet Fiber order → Target)
    (jet : TruncatedThroatSpatialMultiindexJet Fiber order)
    (index : ThroatSpatialTruncatedIndex order)
    (derivative :
      TruncatedThroatSpatialMultiindexJet Fiber order →L[Real] Target)
    (hDerivative : HasFDerivAt localFunction derivative jet) :
    programPT06ThroatSpatialVerticalPartialDerivative
        localFunction jet index =
      derivative.comp
        (programPT06ThroatSpatialJetCoordinateInjection index) := by
  rw [programPT06ThroatSpatialVerticalPartialDerivative,
    hDerivative.fderiv]

/-- Formal total derivative of a local function in one throat direction.  It
is evaluated on one higher jet by the chain-rule contraction
`fderiv F (truncate j) (D_i j)`. -/
def programPT06ThroatSpatialLocalFunctionTotalDerivative
    {order : Nat} (direction : Fin 3)
    (localFunction : TruncatedThroatSpatialMultiindexJet Fiber order → Target) :
    TruncatedThroatSpatialMultiindexJet Fiber (order + 1) → Target :=
  fun jet =>
    fderiv Real localFunction
      (truncateThroatSpatialMultiindexJet (Nat.le_succ order) jet)
      (throatSpatialTotalDerivative direction jet)

@[simp] theorem programPT06ThroatSpatialLocalFunctionTotalDerivative_apply
    {order : Nat} (direction : Fin 3)
    (localFunction : TruncatedThroatSpatialMultiindexJet Fiber order → Target)
    (jet : TruncatedThroatSpatialMultiindexJet Fiber (order + 1)) :
    programPT06ThroatSpatialLocalFunctionTotalDerivative
        direction localFunction jet =
      fderiv Real localFunction
        (truncateThroatSpatialMultiindexJet (Nat.le_succ order) jet)
        (throatSpatialTotalDerivative direction jet) :=
  rfl

@[simp] theorem programPT06ThroatSpatialLocalFunctionTotalDerivative_const
    {order : Nat} (direction : Fin 3) (constant : Target) :
    programPT06ThroatSpatialLocalFunctionTotalDerivative
        (Fiber := Fiber) direction
        (fun _ : TruncatedThroatSpatialMultiindexJet Fiber order => constant) = 0 := by
  funext jet
  simp [programPT06ThroatSpatialLocalFunctionTotalDerivative]

@[simp] theorem programPT06ThroatSpatialLocalFunctionTotalDerivative_zero
    {order : Nat} (direction : Fin 3) :
    programPT06ThroatSpatialLocalFunctionTotalDerivative
        (Fiber := Fiber) (Target := Target) direction
        (0 : TruncatedThroatSpatialMultiindexJet Fiber order → Target) = 0 := by
  funext jet
  simp [programPT06ThroatSpatialLocalFunctionTotalDerivative]

/-- Chain-rule formula using any certified Frechet derivative of the local
function at the truncated jet. -/
theorem programPT06ThroatSpatialLocalFunctionTotalDerivative_eq_of_hasFDerivAt
    {order : Nat} (direction : Fin 3)
    (localFunction : TruncatedThroatSpatialMultiindexJet Fiber order → Target)
    (jet : TruncatedThroatSpatialMultiindexJet Fiber (order + 1))
    (derivative :
      TruncatedThroatSpatialMultiindexJet Fiber order →L[Real] Target)
    (hDerivative : HasFDerivAt localFunction derivative
      (truncateThroatSpatialMultiindexJet (Nat.le_succ order) jet)) :
    programPT06ThroatSpatialLocalFunctionTotalDerivative
        direction localFunction jet =
      derivative (throatSpatialTotalDerivative direction jet) := by
  rw [programPT06ThroatSpatialLocalFunctionTotalDerivative,
    hDerivative.fderiv]

/-- For a continuous linear local function, every vertical partial is its
restriction to the selected coordinate injection. -/
@[simp] theorem programPT06ThroatSpatialVerticalPartialDerivative_linear
    {order : Nat}
    (linear :
      TruncatedThroatSpatialMultiindexJet Fiber order →L[Real] Target)
    (jet : TruncatedThroatSpatialMultiindexJet Fiber order)
    (index : ThroatSpatialTruncatedIndex order) :
    programPT06ThroatSpatialVerticalPartialDerivative
        linear jet index =
      linear.comp
        (programPT06ThroatSpatialJetCoordinateInjection index) := by
  simp [programPT06ThroatSpatialVerticalPartialDerivative]

/-- The total derivative of a continuous linear local function is that map
applied to the formal total derivative of the higher jet. -/
@[simp] theorem programPT06ThroatSpatialLocalFunctionTotalDerivative_linear
    {order : Nat} (direction : Fin 3)
    (linear :
      TruncatedThroatSpatialMultiindexJet Fiber order →L[Real] Target)
    (jet : TruncatedThroatSpatialMultiindexJet Fiber (order + 1)) :
    programPT06ThroatSpatialLocalFunctionTotalDerivative
        direction linear jet =
      linear (throatSpatialTotalDerivative direction jet) := by
  simp [programPT06ThroatSpatialLocalFunctionTotalDerivative]

end
end P0EFTJanusProgramPT06LocalFunctionTotalDerivative4D
end JanusFormal
