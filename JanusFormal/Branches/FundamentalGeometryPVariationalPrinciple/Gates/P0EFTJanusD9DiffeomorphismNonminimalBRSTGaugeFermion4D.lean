import JanusFormal.Branches.FundamentalGeometryD9ImmersedSpinCEllipticComplex.Gates.P0EFTJanusCompleteGaugeFixedEllipticSymbol

/-!
# Diffeomorphism nonminimal BRST gauge fermion at D9 symbol level

This is the de Donder analogue of the Abelian nonminimal symbol gate.  The
diffeomorphism ghost, antighost and Nakanishi--Lautrup vector are three
distinct types.  For one D9 covector it constructs

`s(h,c,cbar,B) = (-symGrad c,0,B,0)`

and the quadratic gauge fermion

`Psi = <cbar, deDonder h - B/2>`.

Its exact graded variation supplies the de Donder auxiliary quadratic form
and the installed vector ghost Laplacian.  Eliminating `B` gives
`|deDonder h|^2 / 2`.

The repository does not yet contain the ungauge-fixed Einstein metric
principal symbol or the adjoint of the de Donder symbol for a selected
symmetric-tensor pairing.  Therefore this gate proves the genuine
gauge-fixing Hessian pairing, but does not assert the still-missing operator
identity `H_EH + G*G = metricLaplacianSymbol`.
-/

namespace JanusFormal
namespace P0EFTJanusD9DiffeomorphismNonminimalBRSTGaugeFermion4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusImmersionFiberAlgebra
open P0EFTJanusGaugeFixedPrincipalSymbols
open P0EFTJanusCompleteGaugeFixedEllipticSymbol

/-- Diffeomorphism ghost vector, kept distinct from its dual partner. -/
@[ext]
structure D9DiffeomorphismGhost where
  vector : TangentVector3

/-- Independent diffeomorphism antighost vector. -/
@[ext]
structure D9DiffeomorphismAntighost where
  vector : TangentVector3

/-- Independent diffeomorphism Nakanishi--Lautrup vector. -/
@[ext]
structure D9DiffeomorphismNakanishiLautrup where
  vector : TangentVector3

def zeroD9DiffeomorphismGhost : D9DiffeomorphismGhost :=
  ⟨zeroTangent⟩

def zeroD9DiffeomorphismAntighost : D9DiffeomorphismAntighost :=
  ⟨zeroTangent⟩

def zeroD9DiffeomorphismNakanishiLautrup :
    D9DiffeomorphismNakanishiLautrup :=
  ⟨zeroTangent⟩

/-- One nonminimal diffeomorphism BRST state at symbol level. -/
@[ext]
structure D9DiffeomorphismNonminimalBRSTState where
  metricPerturbation : SymmetricTensor3
  ghost : D9DiffeomorphismGhost
  antighost : D9DiffeomorphismAntighost
  nakanishiLautrup : D9DiffeomorphismNakanishiLautrup

def zeroD9DiffeomorphismNonminimalBRSTState :
    D9DiffeomorphismNonminimalBRSTState where
  metricPerturbation := zeroSymmetric
  ghost := zeroD9DiffeomorphismGhost
  antighost := zeroD9DiffeomorphismAntighost
  nakanishiLautrup := zeroD9DiffeomorphismNakanishiLautrup

/-- Symbol differential `s h = -symGrad c`, `s c = 0`, `s cbar = B`,
`s B = 0`. -/
def d9DiffeomorphismNonminimalBRST
    (covector : TangentVector3)
    (state : D9DiffeomorphismNonminimalBRSTState) :
    D9DiffeomorphismNonminimalBRSTState where
  metricPerturbation :=
    symGradientSymbol covector
      (scaleTangent (-1) state.ghost.vector)
  ghost := zeroD9DiffeomorphismGhost
  antighost := ⟨state.nakanishiLautrup.vector⟩
  nakanishiLautrup := zeroD9DiffeomorphismNakanishiLautrup

theorem d9DiffeomorphismNonminimalBRST_square_zero
    (covector : TangentVector3)
    (state : D9DiffeomorphismNonminimalBRSTState) :
    d9DiffeomorphismNonminimalBRST covector
        (d9DiffeomorphismNonminimalBRST covector state) =
      zeroD9DiffeomorphismNonminimalBRSTState := by
  apply D9DiffeomorphismNonminimalBRSTState.ext
  · ext <;>
      simp [d9DiffeomorphismNonminimalBRST,
        zeroD9DiffeomorphismNonminimalBRSTState,
        zeroD9DiffeomorphismGhost, symGradientSymbol,
        scaleTangent, zeroTangent, zeroSymmetric]
  · rfl
  · rfl
  · rfl

/-- Scalar coefficient of
`Psi = <cbar, deDonder h - B/2>`. -/
def d9DiffeomorphismGaugeFermionCoefficient
    (covector : TangentVector3)
    (state : D9DiffeomorphismNonminimalBRSTState) : Real :=
  tangentDot state.antighost.vector
    (subTangent
      (deDonderSymbol covector state.metricPerturbation)
      (scaleTangent (1 / 2 : Real) state.nakanishiLautrup.vector))

def scaleD9DiffeomorphismNonminimalBRSTState
    (scalar : Real)
    (state : D9DiffeomorphismNonminimalBRSTState) :
    D9DiffeomorphismNonminimalBRSTState where
  metricPerturbation :=
    scaleSymmetric scalar state.metricPerturbation
  ghost := ⟨scaleTangent scalar state.ghost.vector⟩
  antighost := ⟨scaleTangent scalar state.antighost.vector⟩
  nakanishiLautrup :=
    ⟨scaleTangent scalar state.nakanishiLautrup.vector⟩

/-- The de Donder gauge fermion is homogeneous quadratic. -/
theorem d9DiffeomorphismGaugeFermionCoefficient_scale
    (covector : TangentVector3)
    (scalar : Real)
    (state : D9DiffeomorphismNonminimalBRSTState) :
    d9DiffeomorphismGaugeFermionCoefficient covector
        (scaleD9DiffeomorphismNonminimalBRSTState scalar state) =
      scalar ^ 2 *
        d9DiffeomorphismGaugeFermionCoefficient covector state := by
  simp [d9DiffeomorphismGaugeFermionCoefficient,
    scaleD9DiffeomorphismNonminimalBRSTState, deDonderSymbol,
    symmetricTrace, scaleSymmetric, subTangent, scaleTangent,
    tangentDot]
  ring

/-- Graded variation of the displayed odd gauge-fermion monomial. -/
def d9DiffeomorphismGaugeFermionBRSTVariation
    (covector : TangentVector3)
    (state : D9DiffeomorphismNonminimalBRSTState) : Real :=
  tangentDot state.nakanishiLautrup.vector
      (subTangent
        (deDonderSymbol covector state.metricPerturbation)
        (scaleTangent (1 / 2 : Real) state.nakanishiLautrup.vector)) -
    tangentDot state.antighost.vector
      (deDonderSymbol covector
        (d9DiffeomorphismNonminimalBRST covector state).metricPerturbation)

/-- Exact `s Psi` formula: de Donder auxiliary term plus the vector
Faddeev--Popov Laplacian. -/
theorem d9DiffeomorphismGaugeFermionBRSTVariation_formula
    (covector : TangentVector3)
    (state : D9DiffeomorphismNonminimalBRSTState) :
    d9DiffeomorphismGaugeFermionBRSTVariation covector state =
      tangentDot state.nakanishiLautrup.vector
          (deDonderSymbol covector state.metricPerturbation) -
        (1 / 2 : Real) *
          tangentDot state.nakanishiLautrup.vector
            state.nakanishiLautrup.vector +
        tangentDot state.antighost.vector
          (ghostLaplacianSymbol covector state.ghost.vector) := by
  unfold d9DiffeomorphismGaugeFermionBRSTVariation
    d9DiffeomorphismNonminimalBRST
  rw [de_donder_sym_gradient]
  simp [subTangent, scaleTangent, tangentDot,
    ghostLaplacianSymbol]
  ring

/-- Off-shell de Donder/Nakanishi--Lautrup coefficient. -/
def d9DiffeomorphismAuxiliaryGaugeFixingCoefficient
    (covector : TangentVector3)
    (state : D9DiffeomorphismNonminimalBRSTState) : Real :=
  tangentDot state.nakanishiLautrup.vector
      (deDonderSymbol covector state.metricPerturbation) -
    (1 / 2 : Real) *
      tangentDot state.nakanishiLautrup.vector
        state.nakanishiLautrup.vector

/-- Mixed diffeomorphism ghost--antighost coefficient. -/
def d9DiffeomorphismGhostActionCoefficient
    (covector : TangentVector3)
    (state : D9DiffeomorphismNonminimalBRSTState) : Real :=
  tangentDot state.antighost.vector
    (ghostLaplacianSymbol covector state.ghost.vector)

theorem d9DiffeomorphismGaugeFermionBRSTVariation_decomposition
    (covector : TangentVector3)
    (state : D9DiffeomorphismNonminimalBRSTState) :
    d9DiffeomorphismGaugeFermionBRSTVariation covector state =
      d9DiffeomorphismAuxiliaryGaugeFixingCoefficient covector state +
        d9DiffeomorphismGhostActionCoefficient covector state := by
  rw [d9DiffeomorphismGaugeFermionBRSTVariation_formula]
  rfl

theorem
    d9DiffeomorphismAuxiliaryGaugeFixingCoefficient_completeSquare
    (covector : TangentVector3)
    (state : D9DiffeomorphismNonminimalBRSTState) :
    d9DiffeomorphismAuxiliaryGaugeFixingCoefficient covector state =
      (1 / 2 : Real) *
          tangentDot
            (deDonderSymbol covector state.metricPerturbation)
            (deDonderSymbol covector state.metricPerturbation) -
        (1 / 2 : Real) *
          tangentDot
            (subTangent state.nakanishiLautrup.vector
              (deDonderSymbol covector state.metricPerturbation))
            (subTangent state.nakanishiLautrup.vector
              (deDonderSymbol covector state.metricPerturbation)) := by
  unfold d9DiffeomorphismAuxiliaryGaugeFixingCoefficient
  simp [subTangent, tangentDot]
  ring

def d9DiffeomorphismAuxiliaryOnShell
    (covector : TangentVector3)
    (state : D9DiffeomorphismNonminimalBRSTState) :
    D9DiffeomorphismNonminimalBRSTState :=
  { state with
    nakanishiLautrup :=
      ⟨deDonderSymbol covector state.metricPerturbation⟩ }

/-- Eliminating `B` leaves the reduced de Donder quadratic form and the
vector Faddeev--Popov pairing. -/
theorem d9DiffeomorphismGaugeFermionBRSTVariation_onShell
    (covector : TangentVector3)
    (state : D9DiffeomorphismNonminimalBRSTState) :
    d9DiffeomorphismGaugeFermionBRSTVariation covector
        (d9DiffeomorphismAuxiliaryOnShell covector state) =
      (1 / 2 : Real) *
          tangentDot
            (deDonderSymbol covector state.metricPerturbation)
            (deDonderSymbol covector state.metricPerturbation) +
        tangentDot state.antighost.vector
          (ghostLaplacianSymbol covector state.ghost.vector) := by
  rw [d9DiffeomorphismGaugeFermionBRSTVariation_formula]
  simp [d9DiffeomorphismAuxiliaryOnShell, tangentDot]
  ring

/-- Reduced bosonic action supplied by the gauge fermion. -/
def d9DiffeomorphismReducedDeDonderAction
    (covector : TangentVector3)
    (metricPerturbation : SymmetricTensor3) : Real :=
  (1 / 2 : Real) *
    tangentDot
      (deDonderSymbol covector metricPerturbation)
      (deDonderSymbol covector metricPerturbation)

/-- Exact polarization of the reduced action.  This is the genuine
gauge-fixing Hessian pairing available before choosing a tensor pairing and
constructing the adjoint `G*`. -/
theorem d9DiffeomorphismReducedDeDonderAction_polarization
    (covector : TangentVector3)
    (first second : SymmetricTensor3) :
    d9DiffeomorphismReducedDeDonderAction covector
        (addSymmetric first second) -
        d9DiffeomorphismReducedDeDonderAction covector first -
        d9DiffeomorphismReducedDeDonderAction covector second =
      tangentDot
        (deDonderSymbol covector first)
        (deDonderSymbol covector second) := by
  simp [d9DiffeomorphismReducedDeDonderAction,
    deDonderSymbol, symmetricTrace, addSymmetric, tangentDot]
  ring

/-- Vector Faddeev--Popov symbol read from the mixed ghost term. -/
def d9DiffeomorphismFaddeevPopovSymbol
    (covector : TangentVector3)
    (ghost : D9DiffeomorphismGhost) : D9DiffeomorphismGhost :=
  ⟨ghostLaplacianSymbol covector ghost.vector⟩

theorem d9DiffeomorphismFaddeevPopovSymbol_eq_deDonder_symGradient
    (covector : TangentVector3)
    (ghost : D9DiffeomorphismGhost) :
    (d9DiffeomorphismFaddeevPopovSymbol covector ghost).vector =
      deDonderSymbol covector
        (symGradientSymbol covector ghost.vector) := by
  exact (de_donder_sym_gradient covector ghost.vector).symm

/-- The mixed ghost Hessian is exactly the diffeomorphism component of the
installed D9 ghost principal symbol. -/
theorem d9DiffeomorphismFaddeevPopovSymbol_eq_D9GhostPrincipalSymbol
    (covector : TangentVector3)
    (ghost : D9DiffeomorphismGhost) :
    (d9DiffeomorphismFaddeevPopovSymbol covector ghost).vector =
      (ghostPrincipalSymbol covector
        { u1Ghost := 0
          diffeomorphismGhost := ghost.vector }).diffeomorphismGhost := by
  rfl

end
end P0EFTJanusD9DiffeomorphismNonminimalBRSTGaugeFermion4D
end JanusFormal
