import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarGraphBoundarySpectralFlow4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarGraphMaslovIntersection4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarLagrangianFiniteMorseIndex4D

/-!
# Boundary Maslov index and Morse-index variation

For a finite regular-crossing family of symmetric Schur operators, the signed
crossing count is simultaneously the boundary spectral flow and the finite
Maslov index of the Cauchy path relative to the Robin Lagrangian.

The analytic Morse-index theorem identifies this integer with the change in the
negative spectral count between two endpoint parameters.  This file packages
that final identification while keeping endpoint nondegeneracy and the
crossing-exhaustion theorem explicit.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarGraphBoundaryMaslovMorseIndex4D

set_option autoImplicit false
noncomputable section

open Set Topology Module
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarGraphBoundaryCrossingForm4D
open P0EFTJanusMappingTorusScalarGraphBoundarySpectralFlow4D

universe w

variable {Trace : Type w}
  [NormedAddCommGroup Trace] [InnerProductSpace Real Trace]
  [CompleteSpace Trace]

/-- Finite Maslov index of a simple-crossing boundary ledger. -/
def CanonicalScalarBoundarySimpleCrossingLedger.maslovIndex
    {curve : CanonicalScalarBoundaryOperatorCurve (Trace := Trace)}
    (ledger : CanonicalScalarBoundarySimpleCrossingLedger curve) : Int :=
  ledger.spectralFlow

@[simp] theorem CanonicalScalarBoundarySimpleCrossingLedger.maslovIndex_eq_spectralFlow
    {curve : CanonicalScalarBoundaryOperatorCurve (Trace := Trace)}
    (ledger : CanonicalScalarBoundarySimpleCrossingLedger curve) :
    ledger.maslovIndex = ledger.spectralFlow :=
  rfl

/-- Endpoint Morse counts and their spectral-flow comparison theorem. -/
structure CanonicalScalarBoundaryMaslovMorseData
    (curve : CanonicalScalarBoundaryOperatorCurve (Trace := Trace))
    (ledger : CanonicalScalarBoundarySimpleCrossingLedger curve) where
  leftParameter : Real
  rightParameter : Real
  ordered : leftParameter ≤ rightParameter
  leftMorseIndex : Nat
  rightMorseIndex : Nat
  left_nondegenerate : LinearMap.ker
    (curve.operator leftParameter).toLinearMap = ⊥
  right_nondegenerate : LinearMap.ker
    (curve.operator rightParameter).toLinearMap = ⊥
  crossings_between : ∀ spectralParameter ∈ ledger.crossingParameters,
    leftParameter < spectralParameter ∧ spectralParameter < rightParameter
  morse_change_eq : (rightMorseIndex : Int) - leftMorseIndex =
    -ledger.spectralFlow

namespace CanonicalScalarBoundaryMaslovMorseData

/-- Morse change is minus the Maslov index. -/
theorem morse_change_eq_maslov
    {curve : CanonicalScalarBoundaryOperatorCurve (Trace := Trace)}
    {ledger : CanonicalScalarBoundarySimpleCrossingLedger curve}
    (data : CanonicalScalarBoundaryMaslovMorseData curve ledger) :
    (data.rightMorseIndex : Int) - data.leftMorseIndex =
      -ledger.maslovIndex :=
  data.morse_change_eq

/-- If spectral flow vanishes then the endpoint Morse indices agree. -/
theorem morseIndex_eq_of_spectralFlow_eq_zero
    {curve : CanonicalScalarBoundaryOperatorCurve (Trace := Trace)}
    {ledger : CanonicalScalarBoundarySimpleCrossingLedger curve}
    (data : CanonicalScalarBoundaryMaslovMorseData curve ledger)
    (hFlow : ledger.spectralFlow = 0) :
    data.rightMorseIndex = data.leftMorseIndex := by
  have hChange := data.morse_change_eq
  rw [hFlow] at hChange
  omega

/-- Positive spectral flow decreases the Morse index by the same amount. -/
theorem rightMorseIndex_le_left_of_nonnegative_flow
    {curve : CanonicalScalarBoundaryOperatorCurve (Trace := Trace)}
    {ledger : CanonicalScalarBoundarySimpleCrossingLedger curve}
    (data : CanonicalScalarBoundaryMaslovMorseData curve ledger)
    (hFlow : 0 ≤ ledger.spectralFlow) :
    data.rightMorseIndex ≤ data.leftMorseIndex := by
  have hChange := data.morse_change_eq
  omega

/-- Negative spectral flow increases the Morse index. -/
theorem leftMorseIndex_le_right_of_nonpositive_flow
    {curve : CanonicalScalarBoundaryOperatorCurve (Trace := Trace)}
    {ledger : CanonicalScalarBoundarySimpleCrossingLedger curve}
    (data : CanonicalScalarBoundaryMaslovMorseData curve ledger)
    (hFlow : ledger.spectralFlow ≤ 0) :
    data.leftMorseIndex ≤ data.rightMorseIndex := by
  have hChange := data.morse_change_eq
  omega

/-- Maslov/Morse certificate. -/
theorem certificate
    {curve : CanonicalScalarBoundaryOperatorCurve (Trace := Trace)}
    {ledger : CanonicalScalarBoundarySimpleCrossingLedger curve}
    (data : CanonicalScalarBoundaryMaslovMorseData curve ledger) :
    ledger.maslovIndex = ledger.spectralFlow ∧
      (data.rightMorseIndex : Int) - data.leftMorseIndex =
        -ledger.maslovIndex ∧
      LinearMap.ker (curve.operator data.leftParameter).toLinearMap = ⊥ ∧
      LinearMap.ker (curve.operator data.rightParameter).toLinearMap = ⊥ :=
  ⟨rfl, data.morse_change_eq_maslov,
    data.left_nondegenerate, data.right_nondegenerate⟩

end CanonicalScalarBoundaryMaslovMorseData

end
end P0EFTJanusMappingTorusScalarGraphBoundaryMaslovMorseIndex4D
end JanusFormal
