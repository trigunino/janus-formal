import JanusFormal.Branches.FundamentalGeometryD9ImmersedSpinCEllipticComplex.Gates.P0EFTJanusCompleteGaugeFixedEllipticSymbol

/-!
# Abelian nonminimal BRST gauge fermion at D9 symbol level

This gate keeps the ghost, antighost and Nakanishi--Lautrup coefficient in
three distinct types.  It does not reinterpret either coordinate of the
historical `GhostFiber`.

For one D9 covector it constructs

`s(A,c,cbar,B) = (-dc,0,B,0)`

and the quadratic gauge fermion

`Psi = cbar (div A - B/2)`.

The graded Leibniz rule for this single odd monomial gives an exact
`s Psi`: its on-shell bosonic part is the longitudinal Maxwell gauge-fixing
quadratic form and its mixed ghost part is the scalar D9 Laplace symbol.

This is an unconditional principal-symbol calculation.  It is not yet an
integrated gauge fermion on the global field chart and does not add a
Grassmann/Berezin functional calculus.
-/

namespace JanusFormal
namespace P0EFTJanusD9AbelianNonminimalBRSTGaugeFermion4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusImmersionFiberAlgebra
open P0EFTJanusGaugeFixedPrincipalSymbols
open P0EFTJanusCompleteGaugeFixedEllipticSymbol

/-- Abelian ghost coefficient.  This is deliberately not an alias of the
historical two-component `GhostFiber`. -/
@[ext]
structure D9AbelianGhost where
  coefficient : Real

/-- Independent Abelian antighost coefficient. -/
@[ext]
structure D9AbelianAntighost where
  coefficient : Real

/-- Independent Nakanishi--Lautrup coefficient. -/
@[ext]
structure D9AbelianNakanishiLautrup where
  coefficient : Real

def zeroD9AbelianGhost : D9AbelianGhost := ⟨0⟩

def zeroD9AbelianAntighost : D9AbelianAntighost := ⟨0⟩

def zeroD9AbelianNakanishiLautrup : D9AbelianNakanishiLautrup := ⟨0⟩

/-- One nonminimal Abelian BRST state at a D9 symbol covector. -/
@[ext]
structure D9AbelianNonminimalBRSTState where
  potential : TangentVector3
  ghost : D9AbelianGhost
  antighost : D9AbelianAntighost
  nakanishiLautrup : D9AbelianNakanishiLautrup

def zeroD9AbelianNonminimalBRSTState :
    D9AbelianNonminimalBRSTState where
  potential := zeroTangent
  ghost := zeroD9AbelianGhost
  antighost := zeroD9AbelianAntighost
  nakanishiLautrup := zeroD9AbelianNakanishiLautrup

/-- The sign in `sA = -dc` makes both the reduced Maxwell gauge-fixing term
and the selected scalar ghost Laplacian positive with the conventions of the
existing D9 symbols. -/
def d9AbelianNonminimalBRST
    (covector : TangentVector3)
    (state : D9AbelianNonminimalBRSTState) :
    D9AbelianNonminimalBRSTState where
  potential :=
    gradientSymbol covector (-state.ghost.coefficient)
  ghost := zeroD9AbelianGhost
  antighost := ⟨state.nakanishiLautrup.coefficient⟩
  nakanishiLautrup := zeroD9AbelianNakanishiLautrup

/-- The concrete nonminimal Abelian differential is square-zero. -/
theorem d9AbelianNonminimalBRST_square_zero
    (covector : TangentVector3)
    (state : D9AbelianNonminimalBRSTState) :
    d9AbelianNonminimalBRST covector
        (d9AbelianNonminimalBRST covector state) =
      zeroD9AbelianNonminimalBRSTState := by
  apply D9AbelianNonminimalBRSTState.ext
  · ext <;>
      simp [d9AbelianNonminimalBRST, zeroD9AbelianNonminimalBRSTState,
        zeroD9AbelianGhost, gradientSymbol, scaleTangent, zeroTangent]
  · rfl
  · rfl
  · rfl

/-- Scalar coefficient of the odd quadratic gauge fermion
`cbar (div A - B/2)`. -/
def d9AbelianGaugeFermionCoefficient
    (covector : TangentVector3)
    (state : D9AbelianNonminimalBRSTState) : Real :=
  state.antighost.coefficient *
    (divergenceSymbol covector state.potential -
      (1 / 2 : Real) * state.nakanishiLautrup.coefficient)

/-- Simultaneous scaling of all four symbol coefficients. -/
def scaleD9AbelianNonminimalBRSTState
    (scalar : Real)
    (state : D9AbelianNonminimalBRSTState) :
    D9AbelianNonminimalBRSTState where
  potential := scaleTangent scalar state.potential
  ghost := ⟨scalar * state.ghost.coefficient⟩
  antighost := ⟨scalar * state.antighost.coefficient⟩
  nakanishiLautrup :=
    ⟨scalar * state.nakanishiLautrup.coefficient⟩

/-- The displayed gauge fermion is homogeneous quadratic. -/
theorem d9AbelianGaugeFermionCoefficient_scale
    (covector : TangentVector3)
    (scalar : Real)
    (state : D9AbelianNonminimalBRSTState) :
    d9AbelianGaugeFermionCoefficient covector
        (scaleD9AbelianNonminimalBRSTState scalar state) =
      scalar ^ 2 * d9AbelianGaugeFermionCoefficient covector state := by
  simp [d9AbelianGaugeFermionCoefficient,
    scaleD9AbelianNonminimalBRSTState, divergenceSymbol,
    tangentDot, scaleTangent]
  ring

/-- Graded BRST variation of the single odd gauge-fermion monomial.  The
minus sign in the second summand is the Koszul sign from the odd antighost. -/
def d9AbelianGaugeFermionBRSTVariation
    (covector : TangentVector3)
    (state : D9AbelianNonminimalBRSTState) : Real :=
  state.nakanishiLautrup.coefficient *
      (divergenceSymbol covector state.potential -
        (1 / 2 : Real) * state.nakanishiLautrup.coefficient) -
    state.antighost.coefficient *
      divergenceSymbol covector
        (d9AbelianNonminimalBRST covector state).potential

/-- Exact `s Psi` formula: auxiliary gauge fixing plus the scalar
Faddeev--Popov Laplacian. -/
theorem d9AbelianGaugeFermionBRSTVariation_formula
    (covector : TangentVector3)
    (state : D9AbelianNonminimalBRSTState) :
    d9AbelianGaugeFermionBRSTVariation covector state =
      state.nakanishiLautrup.coefficient *
          divergenceSymbol covector state.potential -
        (1 / 2 : Real) * state.nakanishiLautrup.coefficient ^ 2 +
        state.antighost.coefficient *
          (normSquared covector * state.ghost.coefficient) := by
  unfold d9AbelianGaugeFermionBRSTVariation
    d9AbelianNonminimalBRST
  rw [divergence_gradient_symbol]
  ring

/-- Off-shell bosonic auxiliary coefficient generated by `s Psi`. -/
def d9AbelianAuxiliaryGaugeFixingCoefficient
    (covector : TangentVector3)
    (state : D9AbelianNonminimalBRSTState) : Real :=
  state.nakanishiLautrup.coefficient *
      divergenceSymbol covector state.potential -
    (1 / 2 : Real) * state.nakanishiLautrup.coefficient ^ 2

/-- Mixed ghost--antighost coefficient generated by `s Psi`. -/
def d9AbelianGhostActionCoefficient
    (covector : TangentVector3)
    (state : D9AbelianNonminimalBRSTState) : Real :=
  state.antighost.coefficient *
    (normSquared covector * state.ghost.coefficient)

theorem d9AbelianGaugeFermionBRSTVariation_decomposition
    (covector : TangentVector3)
    (state : D9AbelianNonminimalBRSTState) :
    d9AbelianGaugeFermionBRSTVariation covector state =
      d9AbelianAuxiliaryGaugeFixingCoefficient covector state +
        d9AbelianGhostActionCoefficient covector state := by
  rw [d9AbelianGaugeFermionBRSTVariation_formula]
  rfl

/-- Completing the square isolates the reduced longitudinal Maxwell term. -/
theorem d9AbelianAuxiliaryGaugeFixingCoefficient_completeSquare
    (covector : TangentVector3)
    (state : D9AbelianNonminimalBRSTState) :
    d9AbelianAuxiliaryGaugeFixingCoefficient covector state =
      (1 / 2 : Real) *
          (divergenceSymbol covector state.potential) ^ 2 -
        (1 / 2 : Real) *
          (state.nakanishiLautrup.coefficient -
            divergenceSymbol covector state.potential) ^ 2 := by
  unfold d9AbelianAuxiliaryGaugeFixingCoefficient
  ring

/-- Algebraic auxiliary equation `B = div A`. -/
def d9AbelianAuxiliaryOnShell
    (covector : TangentVector3)
    (state : D9AbelianNonminimalBRSTState) :
    D9AbelianNonminimalBRSTState :=
  { state with
    nakanishiLautrup :=
      ⟨divergenceSymbol covector state.potential⟩ }

/-- After eliminating `B`, `s Psi` is exactly the longitudinal Maxwell
quadratic form plus the Faddeev--Popov ghost pairing. -/
theorem d9AbelianGaugeFermionBRSTVariation_onShell
    (covector : TangentVector3)
    (state : D9AbelianNonminimalBRSTState) :
    d9AbelianGaugeFermionBRSTVariation covector
        (d9AbelianAuxiliaryOnShell covector state) =
      (1 / 2 : Real) *
          (divergenceSymbol covector state.potential) ^ 2 +
        state.antighost.coefficient *
          (normSquared covector * state.ghost.coefficient) := by
  rw [d9AbelianGaugeFermionBRSTVariation_formula]
  simp [d9AbelianAuxiliaryOnShell]
  ring

/-- Hessian symbol of the reduced longitudinal Maxwell quadratic form. -/
def d9AbelianLongitudinalGaugeFixingSymbol
    (covector potential : TangentVector3) : TangentVector3 :=
  gradientSymbol covector
    (divergenceSymbol covector potential)

theorem d9AbelianLongitudinalGaugeFixingSymbol_pairing
    (covector first second : TangentVector3) :
    tangentDot
        (d9AbelianLongitudinalGaugeFixingSymbol covector first)
        second =
      divergenceSymbol covector first *
        divergenceSymbol covector second := by
  simp [d9AbelianLongitudinalGaugeFixingSymbol,
    gradientSymbol, divergenceSymbol, tangentDot, scaleTangent]
  ring

theorem d9AbelianLongitudinalGaugeFixingSymbol_symmetric
    (covector first second : TangentVector3) :
    tangentDot
        (d9AbelianLongitudinalGaugeFixingSymbol covector first)
        second =
      tangentDot first
        (d9AbelianLongitudinalGaugeFixingSymbol covector second) := by
  rw [d9AbelianLongitudinalGaugeFixingSymbol_pairing]
  simp [d9AbelianLongitudinalGaugeFixingSymbol,
    gradientSymbol, divergenceSymbol, tangentDot, scaleTangent]
  ring

/-- The existing Maxwell gauge-fixed symbol is the curvature symbol plus
the longitudinal Hessian generated by the gauge fermion. -/
theorem maxwellGaugeFixedSymbol_from_gaugeFermion
    (covector potential : TangentVector3) :
    maxwellGaugeFixedSymbol covector potential =
      subTangent
        (d9AbelianLongitudinalGaugeFixingSymbol covector potential)
        (crossProduct covector (crossProduct covector potential)) := by
  rfl

/-- Scalar Faddeev--Popov symbol extracted from the mixed ghost term. -/
def d9AbelianFaddeevPopovSymbol
    (covector : TangentVector3)
    (ghost : D9AbelianGhost) : D9AbelianGhost :=
  ⟨normSquared covector * ghost.coefficient⟩

theorem d9AbelianFaddeevPopovSymbol_eq_divergence_gradient
    (covector : TangentVector3)
    (ghost : D9AbelianGhost) :
    (d9AbelianFaddeevPopovSymbol covector ghost).coefficient =
      divergenceSymbol covector
        (gradientSymbol covector ghost.coefficient) := by
  exact (divergence_gradient_symbol covector ghost.coefficient).symm

/-- The mixed ghost Hessian is exactly the U(1) component of the installed
D9 ghost principal symbol. -/
theorem d9AbelianFaddeevPopovSymbol_eq_D9GhostPrincipalSymbol
    (covector : TangentVector3)
    (ghost : D9AbelianGhost) :
    (d9AbelianFaddeevPopovSymbol covector ghost).coefficient =
      (ghostPrincipalSymbol covector
        { u1Ghost := ghost.coefficient
          diffeomorphismGhost := zeroTangent }).u1Ghost := by
  rfl

end
end P0EFTJanusD9AbelianNonminimalBRSTGaugeFermion4D
end JanusFormal
