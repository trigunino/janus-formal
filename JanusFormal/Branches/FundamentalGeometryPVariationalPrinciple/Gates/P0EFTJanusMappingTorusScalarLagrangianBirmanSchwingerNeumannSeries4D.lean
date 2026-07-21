import Mathlib.Analysis.Normed.Algebra.OperatorNorm
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarLagrangianBirmanSchwinger4D

/-!
# Neumann-series inversion of the Birman--Schwinger factor

For a bounded ambient operator `K`, the finite alternating geometric sum

`S_N = sum_{n=0}^N (-K)^n`

satisfies

`(I+K) S_N = S_N (I+K) = I - (-K)^(N+1)`.

Thus nilpotence gives an exact finite inverse.  A separate convergence interface
records the Banach-space Neumann theorem for `‖K‖<1` and supplies the inverse
factor required by the bounded-perturbation construction.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarLagrangianBirmanSchwingerNeumannSeries4D

set_option autoImplicit false
noncomputable section

open Set Topology Module
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarOperatorGraphCompletion4D
open P0EFTJanusMappingTorusScalarClosedGraphRealization4D
open P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D
open P0EFTJanusMappingTorusScalarLagrangianResolvent4D
open P0EFTJanusMappingTorusScalarLagrangianBoundedPerturbation4D

universe u v w

variable {Domain : Type u} {Ambient : Type v} {Trace : Type w}
  [AddCommGroup Domain] [Module Real Domain]
  [NormedAddCommGroup Ambient] [InnerProductSpace Real Ambient]
  [CompleteSpace Ambient]
  [NormedAddCommGroup Trace] [InnerProductSpace Real Trace]
  [CompleteSpace Trace]

/-- Finite alternating geometric sum in the Banach algebra of continuous linear
endomorphisms. -/
def canonicalScalarBirmanSchwingerGeometricSum
    (operator : Ambient →L[Real] Ambient) (order : Nat) :
    Ambient →L[Real] Ambient :=
  ∑ exponent ∈ Finset.range (order + 1), (-operator) ^ exponent

/-- Left finite geometric identity. -/
theorem canonicalScalarBirmanSchwingerGeometricSum_left
    (operator : Ambient →L[Real] Ambient) (order : Nat) :
    (ContinuousLinearMap.id Real Ambient + operator) *
        canonicalScalarBirmanSchwingerGeometricSum operator order =
      ContinuousLinearMap.id Real Ambient - (-operator) ^ (order + 1) := by
  unfold canonicalScalarBirmanSchwingerGeometricSum
  rw [Finset.mul_sum]
  induction order with
  | zero => simp
  | succ order ih =>
      rw [Finset.sum_range_succ, mul_add, ih]
      noncomm_ring

/-- Right finite geometric identity. -/
theorem canonicalScalarBirmanSchwingerGeometricSum_right
    (operator : Ambient →L[Real] Ambient) (order : Nat) :
    canonicalScalarBirmanSchwingerGeometricSum operator order *
        (ContinuousLinearMap.id Real Ambient + operator) =
      ContinuousLinearMap.id Real Ambient - (-operator) ^ (order + 1) := by
  unfold canonicalScalarBirmanSchwingerGeometricSum
  rw [Finset.sum_mul]
  induction order with
  | zero => simp
  | succ order ih =>
      rw [Finset.sum_range_succ, add_mul, ih]
      noncomm_ring

/-- Application form of the left geometric identity. -/
theorem canonicalScalarBirmanSchwingerGeometricSum_left_apply
    (operator : Ambient →L[Real] Ambient) (order : Nat)
    (source : Ambient) :
    (ContinuousLinearMap.id Real Ambient + operator)
        (canonicalScalarBirmanSchwingerGeometricSum operator order source) =
      source - ((-operator) ^ (order + 1)) source := by
  exact DFunLike.congr_fun
    (canonicalScalarBirmanSchwingerGeometricSum_left operator order) source

/-- Exact finite inverse when the remainder is nilpotent. -/
structure CanonicalScalarNilpotentBirmanSchwingerData
    (operator : Ambient →L[Real] Ambient) where
  order : Nat
  nilpotent : (-operator) ^ (order + 1) = 0

namespace CanonicalScalarNilpotentBirmanSchwingerData

/-- Exact finite inverse. -/
def inverse
    {operator : Ambient →L[Real] Ambient}
    (nilpotent : CanonicalScalarNilpotentBirmanSchwingerData operator) :
    Ambient →L[Real] Ambient :=
  canonicalScalarBirmanSchwingerGeometricSum operator nilpotent.order

/-- Left inverse identity. -/
theorem left_inverse
    {operator : Ambient →L[Real] Ambient}
    (nilpotent : CanonicalScalarNilpotentBirmanSchwingerData operator) :
    (ContinuousLinearMap.id Real Ambient + operator) * nilpotent.inverse = 1 := by
  rw [inverse, canonicalScalarBirmanSchwingerGeometricSum_left,
    nilpotent.nilpotent]
  simp

/-- Right inverse identity. -/
theorem right_inverse
    {operator : Ambient →L[Real] Ambient}
    (nilpotent : CanonicalScalarNilpotentBirmanSchwingerData operator) :
    nilpotent.inverse * (ContinuousLinearMap.id Real Ambient + operator) = 1 := by
  rw [inverse, canonicalScalarBirmanSchwingerGeometricSum_right,
    nilpotent.nilpotent]
  simp

end CanonicalScalarNilpotentBirmanSchwingerData

/-- Analytic convergence package for the Neumann series of `I+K`. -/
structure CanonicalScalarBirmanSchwingerNeumannConvergenceData
    (operator : Ambient →L[Real] Ambient) where
  norm_lt_one : ‖operator‖ < 1
  inverse : Ambient →L[Real] Ambient
  geometric_tendsto : Tendsto
    (fun order => canonicalScalarBirmanSchwingerGeometricSum operator order)
    atTop (𝓝 inverse)
  left_inverse :
    (ContinuousLinearMap.id Real Ambient + operator) * inverse = 1
  right_inverse :
    inverse * (ContinuousLinearMap.id Real Ambient + operator) = 1

/-- Convert a Neumann convergence package into the inverse-factor interface used
by the perturbed resolvent. -/
def CanonicalScalarBirmanSchwingerNeumannConvergenceData.toFactorInverse
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (perturbation : Ambient →L[Real] Ambient)
    (spectralParameter : Real)
    (baseResolvent : CanonicalScalarClosedLagrangianBoundedResolventAt
      data hClosable traceBound condition spectralParameter)
    (neumann : CanonicalScalarBirmanSchwingerNeumannConvergenceData
      (perturbation.comp
        (baseResolvent.ambientResolvent
          data hClosable traceBound condition spectralParameter))) :
    CanonicalScalarClosedLagrangianPerturbationFactorInverseAt
      data hClosable traceBound condition perturbation spectralParameter
        baseResolvent where
  inverse := neumann.inverse
  left_inverse := by
    intro source
    exact DFunLike.congr_fun neumann.left_inverse source
  right_inverse := by
    intro source
    exact DFunLike.congr_fun neumann.right_inverse source

/-- Neumann-series perturbation certificate. -/
theorem canonicalScalarBirmanSchwingerNeumannSeries_certificate
    (operator : Ambient →L[Real] Ambient) (order : Nat) :
    (ContinuousLinearMap.id Real Ambient + operator) *
        canonicalScalarBirmanSchwingerGeometricSum operator order =
      ContinuousLinearMap.id Real Ambient - (-operator) ^ (order + 1) ∧
    canonicalScalarBirmanSchwingerGeometricSum operator order *
        (ContinuousLinearMap.id Real Ambient + operator) =
      ContinuousLinearMap.id Real Ambient - (-operator) ^ (order + 1) :=
  ⟨canonicalScalarBirmanSchwingerGeometricSum_left operator order,
    canonicalScalarBirmanSchwingerGeometricSum_right operator order⟩

end
end P0EFTJanusMappingTorusScalarLagrangianBirmanSchwingerNeumannSeries4D
end JanusFormal
