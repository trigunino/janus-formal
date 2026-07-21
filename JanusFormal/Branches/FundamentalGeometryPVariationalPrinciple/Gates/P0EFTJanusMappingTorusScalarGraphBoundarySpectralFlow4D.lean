import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarGraphBoundaryCrossingForm4D

/-!
# Finite boundary spectral-flow ledger

For a finite family of simple Schur crossings, the local crossing orientations
assemble into an integer spectral-flow count.  This file deliberately isolates
the finite regular-crossing theorem from the still-open analytic problem of
showing that a concrete Janus family has only finitely many regular crossings.

Every registered crossing also carries a nonzero homogeneous Robin bulk mode via
the Poisson equivalence.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarGraphBoundarySpectralFlow4D

set_option autoImplicit false
noncomputable section

open Set Topology Module
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarOperatorGraphCompletion4D
open P0EFTJanusMappingTorusScalarGraphPoissonDirichletToNeumann4D
open P0EFTJanusMappingTorusScalarGraphBoundarySpectrumReduction4D
open P0EFTJanusMappingTorusScalarGraphBoundaryCrossingForm4D

universe u v w

variable {Domain : Type u} {Ambient : Type v} {Trace : Type w}
  [AddCommGroup Domain] [Module Real Domain]
  [NormedAddCommGroup Ambient] [InnerProductSpace Real Ambient]
  [CompleteSpace Ambient]
  [NormedAddCommGroup Trace] [InnerProductSpace Real Trace]
  [CompleteSpace Trace]

/-- Finite list of simple crossing parameters for one symmetric boundary
operator curve. -/
structure CanonicalScalarBoundarySimpleCrossingLedger
    (curve : CanonicalScalarBoundaryOperatorCurve (Trace := Trace)) where
  crossingParameters : Finset Real
  crossingData : ∀ spectralParameter : Real,
    spectralParameter ∈ crossingParameters →
      CanonicalScalarBoundarySimpleCrossingData curve spectralParameter
  exhaustive : ∀ spectralParameter : Real,
    LinearMap.ker (curve.operator spectralParameter).toLinearMap ≠ ⊥ →
      spectralParameter ∈ crossingParameters

/-- Integer spectral-flow count of a finite simple-crossing ledger. -/
def CanonicalScalarBoundarySimpleCrossingLedger.spectralFlow
    {curve : CanonicalScalarBoundaryOperatorCurve (Trace := Trace)}
    (ledger : CanonicalScalarBoundarySimpleCrossingLedger curve) : Int :=
  ∑ spectralParameter ∈ ledger.crossingParameters,
    (ledger.crossingData spectralParameter ‹spectralParameter ∈ ledger.crossingParameters›).orientation

/-- Every singular parameter is registered by the ledger. -/
theorem CanonicalScalarBoundarySimpleCrossingLedger.mem_of_singular
    {curve : CanonicalScalarBoundaryOperatorCurve (Trace := Trace)}
    (ledger : CanonicalScalarBoundarySimpleCrossingLedger curve)
    (spectralParameter : Real)
    (hSingular : LinearMap.ker
      (curve.operator spectralParameter).toLinearMap ≠ ⊥) :
    spectralParameter ∈ ledger.crossingParameters :=
  ledger.exhaustive spectralParameter hSingular

/-- Every registered crossing contributes either `+1` or `-1`. -/
theorem CanonicalScalarBoundarySimpleCrossingLedger.orientation_eq_one_or_neg_one
    {curve : CanonicalScalarBoundaryOperatorCurve (Trace := Trace)}
    (ledger : CanonicalScalarBoundarySimpleCrossingLedger curve)
    (spectralParameter : Real)
    (hParameter : spectralParameter ∈ ledger.crossingParameters) :
    (ledger.crossingData spectralParameter hParameter).orientation = 1 ∨
      (ledger.crossingData spectralParameter hParameter).orientation = -1 :=
  (ledger.crossingData spectralParameter hParameter).orientation_eq_one_or_neg_one

/-- Absolute value of the finite spectral-flow count is bounded by the number
of registered crossings. -/
theorem CanonicalScalarBoundarySimpleCrossingLedger.spectralFlow_abs_le_card
    {curve : CanonicalScalarBoundaryOperatorCurve (Trace := Trace)}
    (ledger : CanonicalScalarBoundarySimpleCrossingLedger curve) :
    |ledger.spectralFlow| ≤ ledger.crossingParameters.card := by
  unfold CanonicalScalarBoundarySimpleCrossingLedger.spectralFlow
  have hTerm : ∀ spectralParameter ∈ ledger.crossingParameters,
      |(ledger.crossingData spectralParameter
        ‹spectralParameter ∈ ledger.crossingParameters›).orientation| ≤ 1 := by
    intro spectralParameter hParameter
    rcases ledger.orientation_eq_one_or_neg_one spectralParameter hParameter with h | h
    · rw [h]
      norm_num
    · rw [h]
      norm_num
  calc
    |∑ spectralParameter ∈ ledger.crossingParameters,
        (ledger.crossingData spectralParameter
          ‹spectralParameter ∈ ledger.crossingParameters›).orientation| ≤
      ∑ spectralParameter ∈ ledger.crossingParameters,
        |(ledger.crossingData spectralParameter
          ‹spectralParameter ∈ ledger.crossingParameters›).orientation| := by
        exact abs_sum_le_sum_abs _ _
    _ ≤ ∑ _spectralParameter ∈ ledger.crossingParameters, (1 : Int) := by
      gcongr with spectralParameter hParameter
      exact hTerm spectralParameter hParameter
    _ = ledger.crossingParameters.card := by simp

/-- Positive and negative crossing counts. -/
def CanonicalScalarBoundarySimpleCrossingLedger.positiveCrossingCount
    {curve : CanonicalScalarBoundaryOperatorCurve (Trace := Trace)}
    (ledger : CanonicalScalarBoundarySimpleCrossingLedger curve) : Nat :=
  (ledger.crossingParameters.filter fun spectralParameter =>
    0 < curve.crossingQuadratic spectralParameter
      (ledger.crossingData spectralParameter
        (by simp)).generator).card

/-- Negative crossing count. -/
def CanonicalScalarBoundarySimpleCrossingLedger.negativeCrossingCount
    {curve : CanonicalScalarBoundaryOperatorCurve (Trace := Trace)}
    (ledger : CanonicalScalarBoundarySimpleCrossingLedger curve) : Nat :=
  (ledger.crossingParameters.filter fun spectralParameter =>
    ¬ 0 < curve.crossingQuadratic spectralParameter
      (ledger.crossingData spectralParameter
        (by simp)).generator).card

/-- Spectral flow is positive crossings minus negative crossings. -/
theorem CanonicalScalarBoundarySimpleCrossingLedger.spectralFlow_eq_counts
    {curve : CanonicalScalarBoundaryOperatorCurve (Trace := Trace)}
    (ledger : CanonicalScalarBoundarySimpleCrossingLedger curve) :
    ledger.spectralFlow =
      (ledger.positiveCrossingCount : Int) -
        (ledger.negativeCrossingCount : Int) := by
  classical
  unfold CanonicalScalarBoundarySimpleCrossingLedger.spectralFlow
    CanonicalScalarBoundarySimpleCrossingLedger.positiveCrossingCount
    CanonicalScalarBoundarySimpleCrossingLedger.negativeCrossingCount
  rw [← Finset.sum_filter_add_sum_filter_neg_eq_sum
    (s := ledger.crossingParameters)
    (p := fun spectralParameter =>
      0 < curve.crossingQuadratic spectralParameter
        (ledger.crossingData spectralParameter (by simp)).generator)
    (f := fun spectralParameter =>
      (ledger.crossingData spectralParameter (by simp)).orientation)]
  simp only [CanonicalScalarBoundarySimpleCrossingData.orientation]
  simp [Int.ofNat_sub]

/-- A registered Schur crossing gives a nonzero homogeneous Robin bulk mode. -/
theorem canonicalScalarGraphRegisteredCrossing_has_bulkMode
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (robin : Trace →L[Real] Trace)
    (curve : CanonicalScalarGraphRobinSchurCurve data traceBound robin)
    (ledger : CanonicalScalarBoundarySimpleCrossingLedger
      curve.toBoundaryOperatorCurve)
    (spectralParameter : Real)
    (hParameter : spectralParameter ∈ ledger.crossingParameters) :
    ∃ field : canonicalScalarGraphRobinHomogeneousSolutionSubmodule
        data traceBound spectralParameter robin, field ≠ 0 := by
  let boundary := (ledger.crossingData spectralParameter hParameter).generator
  refine ⟨canonicalScalarGraphBoundaryCrossingToBulkMode
    data traceBound spectralParameter (curve.poissonData spectralParameter)
      robin boundary, ?_⟩
  exact (canonicalScalarGraphBoundaryCrossingToBulkMode_ne_zero_iff
    data traceBound spectralParameter (curve.poissonData spectralParameter)
      robin boundary).2
    (ledger.crossingData spectralParameter hParameter).generator_ne_zero

/-- Finite spectral-flow certificate. -/
theorem canonicalScalarGraphBoundarySpectralFlow_certificate
    {curve : CanonicalScalarBoundaryOperatorCurve (Trace := Trace)}
    (ledger : CanonicalScalarBoundarySimpleCrossingLedger curve) :
    |ledger.spectralFlow| ≤ ledger.crossingParameters.card ∧
      ledger.spectralFlow =
        (ledger.positiveCrossingCount : Int) -
          (ledger.negativeCrossingCount : Int) :=
  ⟨ledger.spectralFlow_abs_le_card,
    ledger.spectralFlow_eq_counts⟩

end
end P0EFTJanusMappingTorusScalarGraphBoundarySpectralFlow4D
end JanusFormal
