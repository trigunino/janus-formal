import Mathlib.Analysis.Normed.Operator.Bilinear
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarCompletedBoundaryTripleLaxMilgram4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarCompletedBoundaryTripleSemiboundedSpectrum4D

/-!
# The canonical shifted form on a completed scalar boundary triple

The direct shifted operator and ambient inclusion canonically determine the
bounded bilinear form

`B_lambda(u,v) = <(A-lambda)u, v>`.

Thus Lax--Milgram data do not need an independently supplied form.  Coercivity of
this canonical form, together with density of the realization, constructs the
bounded resolvent.  The same inequality implies the operator lower bound
`A >= lambda`, so one shifted-form coercivity theorem supplies both the
reference resolvent and semiboundedness.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarCompletedBoundaryTripleShiftedForm4D
end P0EFTJanusMappingTorusScalarCompletedBoundaryTripleShiftedForm4D

namespace P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleResolvent4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleLaxMilgram4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleSemiboundedSpectrum4D

universe u v w

variable {Domain : Type u} {Ambient : Type v} {Trace : Type w}
  [AddCommGroup Domain] [Module Real Domain]
  [NormedAddCommGroup Ambient] [InnerProductSpace Real Ambient]
  [CompleteSpace Ambient]
  [NormedAddCommGroup Trace] [InnerProductSpace Real Trace]
  [CompleteSpace Trace]

namespace CanonicalScalarCompletedBoundaryTripleData

variable {core : CanonicalScalarHilbertGreenCore
    (Domain := Domain) (Ambient := Ambient) (Trace := Trace)}
  {traceBound : HasCanonicalScalarHilbertGreenCoreBoundaryGraphBound core}

local instance (priority := 2000) shiftedFormDomainModule
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace) :
    Module Real (triple.lagrangianDomainSubmodule condition) :=
  (lagrangianDomainInnerProductSpace triple condition).toNormedSpace.toModule

local instance (priority := 2000) shiftedFormDomainNormedSpace
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace) :
    NormedSpace Real (triple.lagrangianDomainSubmodule condition) :=
  (lagrangianDomainInnerProductSpace triple condition).toNormedSpace

local instance (priority := 2000) shiftedFormDomainInnerProductSpace
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace) :
    InnerProductSpace Real (triple.lagrangianDomainSubmodule condition) :=
  lagrangianDomainInnerProductSpace triple condition

/-- The shifted operator repackaged with the canonical Hilbert module. -/
def lagrangianHilbertShiftedOperator
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real) :
    triple.lagrangianDomainSubmodule condition →L[Real] Ambient :=
  { toFun := fun field =>
      triple.lagrangianShiftedOperator condition spectralParameter field
    map_add' := fun first second =>
      (triple.lagrangianShiftedOperator
        condition spectralParameter).map_add first second
    map_smul' := fun scalar field =>
      (triple.lagrangianShiftedOperator
        condition spectralParameter).map_smul scalar field
    cont := (triple.lagrangianShiftedOperator
      condition spectralParameter).continuous }

/-- Algebraic shifted pairing before continuity is bundled. -/
def lagrangianShiftedPairingLinearMap
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real) :
    triple.lagrangianDomainSubmodule condition →ₗ[Real]
      triple.lagrangianDomainSubmodule condition →ₗ[Real] Real where
  toFun first :=
    { toFun := fun second =>
        inner Real
          (triple.lagrangianHilbertShiftedOperator
            condition spectralParameter first)
          (triple.lagrangianHilbertInclusion condition second)
      map_add' := by
        intro second third
        rw [map_add, inner_add_right]
      map_smul' := by
        intro scalar second
        rw [map_smul, real_inner_smul_right]
        simp }
  map_add' := by
    intro first second
    ext test
    change inner Real
        ((triple.lagrangianHilbertShiftedOperator
          condition spectralParameter) (first + second))
        (triple.lagrangianHilbertInclusion condition test) =
      inner Real
          ((triple.lagrangianHilbertShiftedOperator
            condition spectralParameter) first)
          (triple.lagrangianHilbertInclusion condition test) +
        inner Real
          ((triple.lagrangianHilbertShiftedOperator
            condition spectralParameter) second)
          (triple.lagrangianHilbertInclusion condition test)
    rw [(triple.lagrangianHilbertShiftedOperator
      condition spectralParameter).map_add, inner_add_left]
  map_smul' := by
    intro scalar first
    ext test
    change inner Real
        ((triple.lagrangianHilbertShiftedOperator
          condition spectralParameter) (scalar • first))
        (triple.lagrangianHilbertInclusion condition test) =
      scalar • inner Real
        ((triple.lagrangianHilbertShiftedOperator
          condition spectralParameter) first)
        (triple.lagrangianHilbertInclusion condition test)
    rw [(triple.lagrangianHilbertShiftedOperator
      condition spectralParameter).map_smul, real_inner_smul_left]
    simp

/-- Operator-norm constant for the canonical shifted pairing. -/
def lagrangianShiftedPairingBound
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real) : Real :=
  ‖triple.lagrangianHilbertShiftedOperator condition spectralParameter‖ *
    ‖triple.lagrangianHilbertInclusion condition‖

/-- Bilinear operator-norm estimate. -/
theorem lagrangianShiftedPairing_norm_le
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (first second : triple.lagrangianDomainSubmodule condition) :
    ‖triple.lagrangianShiftedPairingLinearMap
        condition spectralParameter first second‖ ≤
        triple.lagrangianShiftedPairingBound condition spectralParameter *
        ‖first‖ * ‖second‖ := by
  letI : NormedSpace Real (triple.lagrangianDomainSubmodule condition) :=
    shiftedFormDomainNormedSpace triple condition
  have hShifted := @ContinuousLinearMap.le_opNorm Real Real
    (triple.lagrangianDomainSubmodule condition) Ambient
    _ _ _ _ (shiftedFormDomainNormedSpace triple condition) _
    (RingHom.id Real) _
    (triple.lagrangianHilbertShiftedOperator
      condition spectralParameter) first
  have hInclusion := @ContinuousLinearMap.le_opNorm Real Real
    (triple.lagrangianDomainSubmodule condition) Ambient
    _ _ _ _ (shiftedFormDomainNormedSpace triple condition) _
    (RingHom.id Real) _
    (triple.lagrangianHilbertInclusion condition) second
  have hShiftedUpperNonnegative :
      0 ≤ ‖triple.lagrangianHilbertShiftedOperator
          condition spectralParameter‖ * ‖first‖ :=
    mul_nonneg
      (norm_nonneg (triple.lagrangianHilbertShiftedOperator
        condition spectralParameter))
      (norm_nonneg first)
  calc
    ‖triple.lagrangianShiftedPairingLinearMap
        condition spectralParameter first second‖ ≤
      ‖triple.lagrangianHilbertShiftedOperator
          condition spectralParameter first‖ *
        ‖triple.lagrangianHilbertInclusion condition second‖ :=
      norm_inner_le_norm _ _
    _ ≤
      (‖triple.lagrangianHilbertShiftedOperator
          condition spectralParameter‖ * ‖first‖) *
        (‖triple.lagrangianHilbertInclusion condition‖ * ‖second‖) :=
      mul_le_mul hShifted hInclusion (norm_nonneg _)
        hShiftedUpperNonnegative
    _ = triple.lagrangianShiftedPairingBound condition spectralParameter *
        ‖first‖ * ‖second‖ := by
      unfold lagrangianShiftedPairingBound
      ring

/-- Canonical bounded shifted bilinear form. -/
def lagrangianShiftedForm
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real) :
    triple.lagrangianDomainSubmodule condition →L[Real]
      triple.lagrangianDomainSubmodule condition →L[Real] Real :=
  by
    exact @LinearMap.mkContinuous₂ Real Real Real
      (triple.lagrangianDomainSubmodule condition)
      (triple.lagrangianDomainSubmodule condition) Real
      _ _ _ _ _ _
      (shiftedFormDomainNormedSpace triple condition)
      (shiftedFormDomainNormedSpace triple condition) _
      (RingHom.id Real) (RingHom.id Real) _
      (triple.lagrangianShiftedPairingLinearMap condition spectralParameter)
      (triple.lagrangianShiftedPairingBound condition spectralParameter)
      (triple.lagrangianShiftedPairing_norm_le condition spectralParameter)

@[simp] theorem lagrangianShiftedForm_apply
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (first second : triple.lagrangianDomainSubmodule condition) :
    triple.lagrangianShiftedForm condition spectralParameter first second =
      inner Real
        (triple.lagrangianShiftedOperator
          condition spectralParameter first)
        (triple.lagrangianInclusion condition second) :=
  by
    simp [lagrangianShiftedForm, lagrangianShiftedPairingLinearMap,
      lagrangianHilbertShiftedOperator, lagrangianHilbertInclusion]

/-- Coercivity of the canonical shifted form. -/
structure LagrangianShiftedFormCoerciveData
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real) where
  constant : Real
  constant_pos : 0 < constant
  coercive : ∀ field : triple.lagrangianDomainSubmodule condition,
    constant * ‖field‖ * ‖field‖ ≤
      triple.lagrangianShiftedForm condition spectralParameter field field

namespace LagrangianShiftedFormCoerciveData

/-- Canonical form coercivity plus domain density gives Lax--Milgram data. -/
def toLaxMilgramData
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (coercive : triple.LagrangianShiftedFormCoerciveData
      condition spectralParameter)
    (hDense : DenseRange (triple.lagrangianInclusion condition)) :
    triple.LagrangianLaxMilgramData condition spectralParameter where
  form := triple.lagrangianShiftedForm condition spectralParameter
  form_eq_pairing := triple.lagrangianShiftedForm_apply
    condition spectralParameter
  constant := coercive.constant
  constant_pos := coercive.constant_pos
  coercive := coercive.coercive
  dense := hDense

/-- Canonical shifted-form coercivity produces the direct coercive-surjective
operator package. -/
def toCoerciveSurjectiveAt
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (coercive : triple.LagrangianShiftedFormCoerciveData
      condition spectralParameter)
    (hDense : DenseRange (triple.lagrangianInclusion condition)) :
    triple.LagrangianCoerciveSurjectiveAt condition spectralParameter :=
  (coercive.toLaxMilgramData triple condition spectralParameter hDense)
    |>.toCoerciveSurjectiveAt triple condition spectralParameter

/-- Bounded direct resolvent from canonical shifted-form coercivity. -/
noncomputable def boundedResolvent
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (coercive : triple.LagrangianShiftedFormCoerciveData
      condition spectralParameter)
    (hDense : DenseRange (triple.lagrangianInclusion condition)) :
    triple.LagrangianBoundedResolventAt condition spectralParameter :=
  (coercive.toCoerciveSurjectiveAt
    triple condition spectralParameter hDense).boundedResolvent
      triple condition spectralParameter

/-- Coercivity of `A-lambda` implies the lower form bound `A >= lambda`. -/
def toSemiboundedData
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (coercive : triple.LagrangianShiftedFormCoerciveData
      condition spectralParameter) :
    triple.LagrangianSemiboundedData condition where
  lowerBound := spectralParameter
  bound := by
    intro field
    have hCoercive := coercive.coercive field
    rw [triple.lagrangianShiftedForm_apply,
      triple.lagrangianShiftedOperator_apply,
      inner_sub_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq] at hCoercive
    have hNonnegative : 0 ≤ coercive.constant * ‖field‖ * ‖field‖ :=
      mul_nonneg
        (mul_nonneg coercive.constant_pos.le (norm_nonneg _))
        (norm_nonneg _)
    linarith

/-- Shifted-form closure certificate. -/
theorem certificate
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (coercive : triple.LagrangianShiftedFormCoerciveData
      condition spectralParameter)
    (hDense : DenseRange (triple.lagrangianInclusion condition)) :
    triple.LagrangianResolventPoint condition spectralParameter ∧
      (∀ field : triple.lagrangianDomainSubmodule condition,
        spectralParameter *
            ‖triple.lagrangianInclusion condition field‖ ^ 2 ≤
          inner Real (triple.lagrangianOperator condition field)
            (triple.lagrangianInclusion condition field)) :=
  ⟨(coercive.boundedResolvent triple condition spectralParameter hDense)
      |>.resolventPoint triple condition spectralParameter,
    (coercive.toSemiboundedData triple condition spectralParameter).bound⟩

end LagrangianShiftedFormCoerciveData

end CanonicalScalarCompletedBoundaryTripleData

end
end P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D
end JanusFormal
