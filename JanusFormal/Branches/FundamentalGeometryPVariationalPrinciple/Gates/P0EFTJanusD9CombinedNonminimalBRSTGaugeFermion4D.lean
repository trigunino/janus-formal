import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusD9AbelianNonminimalBRSTGaugeFermion4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusD9DiffeomorphismNonminimalBRSTGaugeFermion4D

/-!
# Combined nonminimal D9 gauge fermion

This gate assembles the already proved Abelian and diffeomorphism
nonminimal symbol complexes without identifying any ghost, antighost or
Nakanishi--Lautrup type.

The combined action is exactly the sum of the two graded gauge-fermion
variations.  Its polarization is an explicit symmetric Hessian at every D9
covector.  Eliminating both auxiliary fields gives the longitudinal Maxwell
and de Donder quadratic forms together with the scalar and vector
Faddeev--Popov pairings.  The latter pairing is exactly the installed D9
ghost principal symbol.

This remains a principal-symbol statement.  It does not construct the
global field-space chart, integrated graded action, Einstein metric symbol,
boundary domain or Fredholm realization.
-/

namespace JanusFormal
namespace P0EFTJanusD9CombinedNonminimalBRSTGaugeFermion4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusImmersionFiberAlgebra
open P0EFTJanusGaugeFixedPrincipalSymbols
open P0EFTJanusCompleteGaugeFixedEllipticSymbol
open P0EFTJanusD9AbelianNonminimalBRSTGaugeFermion4D
open P0EFTJanusD9DiffeomorphismNonminimalBRSTGaugeFermion4D

/-- Direct product of the two distinct nonminimal D9 states. -/
@[ext]
structure D9CombinedNonminimalBRSTState where
  abelian : D9AbelianNonminimalBRSTState
  diffeomorphism : D9DiffeomorphismNonminimalBRSTState

def zeroD9CombinedNonminimalBRSTState :
    D9CombinedNonminimalBRSTState where
  abelian := zeroD9AbelianNonminimalBRSTState
  diffeomorphism := zeroD9DiffeomorphismNonminimalBRSTState

/-- Componentwise combined BRST differential. -/
def d9CombinedNonminimalBRST
    (covector : TangentVector3)
    (state : D9CombinedNonminimalBRSTState) :
    D9CombinedNonminimalBRSTState where
  abelian := d9AbelianNonminimalBRST covector state.abelian
  diffeomorphism :=
    d9DiffeomorphismNonminimalBRST covector state.diffeomorphism

theorem d9CombinedNonminimalBRST_square_zero
    (covector : TangentVector3)
    (state : D9CombinedNonminimalBRSTState) :
    d9CombinedNonminimalBRST covector
        (d9CombinedNonminimalBRST covector state) =
      zeroD9CombinedNonminimalBRSTState := by
  apply D9CombinedNonminimalBRSTState.ext
  · exact d9AbelianNonminimalBRST_square_zero covector state.abelian
  · exact d9DiffeomorphismNonminimalBRST_square_zero
      covector state.diffeomorphism

/-- Sum of the two odd quadratic gauge-fermion coefficients. -/
def d9CombinedGaugeFermionCoefficient
    (covector : TangentVector3)
    (state : D9CombinedNonminimalBRSTState) : Real :=
  d9AbelianGaugeFermionCoefficient covector state.abelian +
    d9DiffeomorphismGaugeFermionCoefficient
      covector state.diffeomorphism

/-- The combined symbolic gauge-fixing/ghost action is, by construction,
the sum of the two exact `s Psi` coefficients. -/
def d9CombinedGaugeFixingGhostAction
    (covector : TangentVector3)
    (state : D9CombinedNonminimalBRSTState) : Real :=
  d9AbelianGaugeFermionBRSTVariation covector state.abelian +
    d9DiffeomorphismGaugeFermionBRSTVariation
      covector state.diffeomorphism

/-- Simultaneous addition of two Abelian nonminimal symbol states. -/
def addD9AbelianNonminimalBRSTState
    (first second : D9AbelianNonminimalBRSTState) :
    D9AbelianNonminimalBRSTState where
  potential := addTangent first.potential second.potential
  ghost := ⟨first.ghost.coefficient + second.ghost.coefficient⟩
  antighost :=
    ⟨first.antighost.coefficient + second.antighost.coefficient⟩
  nakanishiLautrup :=
    ⟨first.nakanishiLautrup.coefficient +
      second.nakanishiLautrup.coefficient⟩

/-- Simultaneous addition of two diffeomorphism nonminimal states. -/
def addD9DiffeomorphismNonminimalBRSTState
    (first second : D9DiffeomorphismNonminimalBRSTState) :
    D9DiffeomorphismNonminimalBRSTState where
  metricPerturbation :=
    addSymmetric first.metricPerturbation second.metricPerturbation
  ghost := ⟨addTangent first.ghost.vector second.ghost.vector⟩
  antighost :=
    ⟨addTangent first.antighost.vector second.antighost.vector⟩
  nakanishiLautrup :=
    ⟨addTangent first.nakanishiLautrup.vector
      second.nakanishiLautrup.vector⟩

def addD9CombinedNonminimalBRSTState
    (first second : D9CombinedNonminimalBRSTState) :
    D9CombinedNonminimalBRSTState where
  abelian :=
    addD9AbelianNonminimalBRSTState first.abelian second.abelian
  diffeomorphism :=
    addD9DiffeomorphismNonminimalBRSTState
      first.diffeomorphism second.diffeomorphism

/-- Explicit Abelian off-shell Hessian of the generated quadratic action. -/
def d9AbelianGaugeFermionHessian
    (covector : TangentVector3)
    (first second : D9AbelianNonminimalBRSTState) : Real :=
  first.nakanishiLautrup.coefficient *
      divergenceSymbol covector second.potential +
    second.nakanishiLautrup.coefficient *
      divergenceSymbol covector first.potential -
    first.nakanishiLautrup.coefficient *
      second.nakanishiLautrup.coefficient +
    first.antighost.coefficient *
      (normSquared covector * second.ghost.coefficient) +
    second.antighost.coefficient *
      (normSquared covector * first.ghost.coefficient)

/-- Explicit diffeomorphism off-shell Hessian of the generated quadratic
action. -/
def d9DiffeomorphismGaugeFermionHessian
    (covector : TangentVector3)
    (first second : D9DiffeomorphismNonminimalBRSTState) : Real :=
  tangentDot first.nakanishiLautrup.vector
      (deDonderSymbol covector second.metricPerturbation) +
    tangentDot second.nakanishiLautrup.vector
      (deDonderSymbol covector first.metricPerturbation) -
    tangentDot first.nakanishiLautrup.vector
      second.nakanishiLautrup.vector +
    tangentDot first.antighost.vector
      (ghostLaplacianSymbol covector second.ghost.vector) +
    tangentDot second.antighost.vector
      (ghostLaplacianSymbol covector first.ghost.vector)

/-- Combined off-shell Hessian. -/
def d9CombinedGaugeFermionHessian
    (covector : TangentVector3)
    (first second : D9CombinedNonminimalBRSTState) : Real :=
  d9AbelianGaugeFermionHessian covector first.abelian second.abelian +
    d9DiffeomorphismGaugeFermionHessian
      covector first.diffeomorphism second.diffeomorphism

/-- Exact polarization of the Abelian `s Psi`. -/
theorem d9AbelianGaugeFermionBRSTVariation_polarization
    (covector : TangentVector3)
    (first second : D9AbelianNonminimalBRSTState) :
    d9AbelianGaugeFermionBRSTVariation covector
        (addD9AbelianNonminimalBRSTState first second) -
        d9AbelianGaugeFermionBRSTVariation covector first -
        d9AbelianGaugeFermionBRSTVariation covector second =
      d9AbelianGaugeFermionHessian covector first second := by
  rw [d9AbelianGaugeFermionBRSTVariation_formula,
    d9AbelianGaugeFermionBRSTVariation_formula,
    d9AbelianGaugeFermionBRSTVariation_formula]
  unfold d9AbelianGaugeFermionHessian
  simp [addD9AbelianNonminimalBRSTState, divergenceSymbol,
    addTangent, tangentDot]
  ring

/-- Exact polarization of the diffeomorphism `s Psi`. -/
theorem d9DiffeomorphismGaugeFermionBRSTVariation_polarization
    (covector : TangentVector3)
    (first second : D9DiffeomorphismNonminimalBRSTState) :
    d9DiffeomorphismGaugeFermionBRSTVariation covector
        (addD9DiffeomorphismNonminimalBRSTState first second) -
        d9DiffeomorphismGaugeFermionBRSTVariation covector first -
        d9DiffeomorphismGaugeFermionBRSTVariation covector second =
      d9DiffeomorphismGaugeFermionHessian covector first second := by
  rw [d9DiffeomorphismGaugeFermionBRSTVariation_formula,
    d9DiffeomorphismGaugeFermionBRSTVariation_formula,
    d9DiffeomorphismGaugeFermionBRSTVariation_formula]
  unfold d9DiffeomorphismGaugeFermionHessian
  simp [addD9DiffeomorphismNonminimalBRSTState,
    deDonderSymbol, symmetricTrace, addSymmetric,
    ghostLaplacianSymbol, addTangent, scaleTangent, tangentDot]
  ring

/-- The displayed combined bilinear form is exactly the polarization of the
action generated by both gauge fermions. -/
theorem d9CombinedGaugeFixingGhostAction_polarization
    (covector : TangentVector3)
    (first second : D9CombinedNonminimalBRSTState) :
    d9CombinedGaugeFixingGhostAction covector
        (addD9CombinedNonminimalBRSTState first second) -
        d9CombinedGaugeFixingGhostAction covector first -
        d9CombinedGaugeFixingGhostAction covector second =
      d9CombinedGaugeFermionHessian covector first second := by
  calc
    _ =
        (d9AbelianGaugeFermionBRSTVariation covector
            (addD9AbelianNonminimalBRSTState
              first.abelian second.abelian) -
          d9AbelianGaugeFermionBRSTVariation covector first.abelian -
          d9AbelianGaugeFermionBRSTVariation covector second.abelian) +
        (d9DiffeomorphismGaugeFermionBRSTVariation covector
            (addD9DiffeomorphismNonminimalBRSTState
              first.diffeomorphism second.diffeomorphism) -
          d9DiffeomorphismGaugeFermionBRSTVariation
            covector first.diffeomorphism -
          d9DiffeomorphismGaugeFermionBRSTVariation
            covector second.diffeomorphism) := by
          unfold d9CombinedGaugeFixingGhostAction
            addD9CombinedNonminimalBRSTState
          ring
    _ =
        d9AbelianGaugeFermionHessian covector
            first.abelian second.abelian +
          d9DiffeomorphismGaugeFermionHessian covector
            first.diffeomorphism second.diffeomorphism := by
          rw [d9AbelianGaugeFermionBRSTVariation_polarization,
            d9DiffeomorphismGaugeFermionBRSTVariation_polarization]
    _ = d9CombinedGaugeFermionHessian covector first second := rfl

/-- Exact symmetry of the combined nonminimal Hessian. -/
theorem d9CombinedGaugeFermionHessian_symmetric
    (covector : TangentVector3)
    (first second : D9CombinedNonminimalBRSTState) :
    d9CombinedGaugeFermionHessian covector first second =
      d9CombinedGaugeFermionHessian covector second first := by
  simp [d9CombinedGaugeFermionHessian,
    d9AbelianGaugeFermionHessian,
    d9DiffeomorphismGaugeFermionHessian,
    tangentDot, ghostLaplacianSymbol, scaleTangent]
  ring

/-- Eliminate both algebraic Nakanishi--Lautrup fields. -/
def d9CombinedAuxiliaryOnShell
    (covector : TangentVector3)
    (state : D9CombinedNonminimalBRSTState) :
    D9CombinedNonminimalBRSTState where
  abelian := d9AbelianAuxiliaryOnShell covector state.abelian
  diffeomorphism :=
    d9DiffeomorphismAuxiliaryOnShell covector state.diffeomorphism

/-- Reduced action after both exact auxiliary equations. -/
def d9CombinedReducedGaugeFixingGhostAction
    (covector : TangentVector3)
    (state : D9CombinedNonminimalBRSTState) : Real :=
  (1 / 2 : Real) *
      (divergenceSymbol covector state.abelian.potential) ^ 2 +
    state.abelian.antighost.coefficient *
      (normSquared covector * state.abelian.ghost.coefficient) +
    (1 / 2 : Real) *
      tangentDot
        (deDonderSymbol covector
          state.diffeomorphism.metricPerturbation)
        (deDonderSymbol covector
          state.diffeomorphism.metricPerturbation) +
    tangentDot state.diffeomorphism.antighost.vector
      (ghostLaplacianSymbol covector
        state.diffeomorphism.ghost.vector)

theorem d9CombinedGaugeFixingGhostAction_onShell
    (covector : TangentVector3)
    (state : D9CombinedNonminimalBRSTState) :
    d9CombinedGaugeFixingGhostAction covector
        (d9CombinedAuxiliaryOnShell covector state) =
      d9CombinedReducedGaugeFixingGhostAction covector state := by
  unfold d9CombinedGaugeFixingGhostAction
    d9CombinedAuxiliaryOnShell
  rw [d9AbelianGaugeFermionBRSTVariation_onShell,
    d9DiffeomorphismGaugeFermionBRSTVariation_onShell]
  unfold d9CombinedReducedGaugeFixingGhostAction
  ring

/-- Hessian of the reduced action, with both auxiliary directions removed. -/
def d9CombinedReducedGaugeFermionHessian
    (covector : TangentVector3)
    (first second : D9CombinedNonminimalBRSTState) : Real :=
  divergenceSymbol covector first.abelian.potential *
      divergenceSymbol covector second.abelian.potential +
    first.abelian.antighost.coefficient *
      (normSquared covector * second.abelian.ghost.coefficient) +
    second.abelian.antighost.coefficient *
      (normSquared covector * first.abelian.ghost.coefficient) +
    tangentDot
      (deDonderSymbol covector
        first.diffeomorphism.metricPerturbation)
      (deDonderSymbol covector
        second.diffeomorphism.metricPerturbation) +
    tangentDot first.diffeomorphism.antighost.vector
      (ghostLaplacianSymbol covector
        second.diffeomorphism.ghost.vector) +
    tangentDot second.diffeomorphism.antighost.vector
      (ghostLaplacianSymbol covector
        first.diffeomorphism.ghost.vector)

theorem d9CombinedReducedGaugeFixingGhostAction_polarization
    (covector : TangentVector3)
    (first second : D9CombinedNonminimalBRSTState) :
    d9CombinedReducedGaugeFixingGhostAction covector
        (addD9CombinedNonminimalBRSTState first second) -
        d9CombinedReducedGaugeFixingGhostAction covector first -
        d9CombinedReducedGaugeFixingGhostAction covector second =
      d9CombinedReducedGaugeFermionHessian covector first second := by
  simp [d9CombinedReducedGaugeFixingGhostAction,
    d9CombinedReducedGaugeFermionHessian,
    addD9CombinedNonminimalBRSTState,
    addD9AbelianNonminimalBRSTState,
    addD9DiffeomorphismNonminimalBRSTState,
    divergenceSymbol, deDonderSymbol, symmetricTrace,
    addTangent, addSymmetric, ghostLaplacianSymbol,
    scaleTangent, tangentDot]
  ring

theorem d9CombinedReducedGaugeFermionHessian_symmetric
    (covector : TangentVector3)
    (first second : D9CombinedNonminimalBRSTState) :
    d9CombinedReducedGaugeFermionHessian covector first second =
      d9CombinedReducedGaugeFermionHessian covector second first := by
  simp [d9CombinedReducedGaugeFermionHessian,
    tangentDot, ghostLaplacianSymbol, scaleTangent]
  ring

/-- Minimal ghost field consumed by the installed complete D9 symbol. -/
def d9CombinedGhostField
    (state : D9CombinedNonminimalBRSTState) :
    GaugeFixedGhostField where
  u1Ghost := state.abelian.ghost.coefficient
  diffeomorphismGhost := state.diffeomorphism.ghost.vector

/-- Its independent antighost partner, represented only for the final
mixed pairing and never identified with the ghost field. -/
def d9CombinedAntighostField
    (state : D9CombinedNonminimalBRSTState) :
    GaugeFixedGhostField where
  u1Ghost := state.abelian.antighost.coefficient
  diffeomorphismGhost := state.diffeomorphism.antighost.vector

def d9GhostFieldPairing
    (first second : GaugeFixedGhostField) : Real :=
  first.u1Ghost * second.u1Ghost +
    tangentDot first.diffeomorphismGhost second.diffeomorphismGhost

/-- The reduced mixed ghost action is exactly antighost paired with the
already installed scalar/vector D9 ghost principal symbol. -/
theorem d9CombinedGhostAction_eq_D9PrincipalSymbolPairing
    (covector : TangentVector3)
    (state : D9CombinedNonminimalBRSTState) :
    state.abelian.antighost.coefficient *
          (normSquared covector * state.abelian.ghost.coefficient) +
        tangentDot state.diffeomorphism.antighost.vector
          (ghostLaplacianSymbol covector
            state.diffeomorphism.ghost.vector) =
      d9GhostFieldPairing
        (d9CombinedAntighostField state)
        (ghostPrincipalSymbol covector
          (d9CombinedGhostField state)) := by
  rfl

end
end P0EFTJanusD9CombinedNonminimalBRSTGaugeFermion4D
end JanusFormal
