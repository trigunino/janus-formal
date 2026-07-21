import Mathlib

namespace JanusFormal.P0EFTJanusLLDeterminantGaugeFixingInterface

set_option autoImplicit false

/-- Finite regulated LL spectrum with its global zero modes identified. -/
structure RegulatedLLSpectrum (ι : Type) [DecidableEq ι] where
  regulatedModes : Finset ι
  zeroModes : Finset ι
  zeroModes_mem : zeroModes ⊆ regulatedModes
  eigenvalue : ι → ℝ
  zero_on_zeroModes : ∀ i ∈ zeroModes, eigenvalue i = 0
  nonzero_off_zeroModes :
    ∀ i ∈ regulatedModes, i ∉ zeroModes → eigenvalue i ≠ 0

/-- Primed determinant: multiply only the regulated nonzero modes. -/
def primedDeterminant {ι : Type} [DecidableEq ι]
    (s : RegulatedLLSpectrum ι) : ℝ :=
  ∏ i ∈ s.regulatedModes \ s.zeroModes, s.eigenvalue i

theorem primedDeterminant_ne_zero {ι : Type} [DecidableEq ι]
    (s : RegulatedLLSpectrum ι) : primedDeterminant s ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  rw [Finset.mem_sdiff] at hi
  exact s.nonzero_off_zeroModes i hi.1 hi.2

/-- Gauge choices with the same regulated physical modes and the same
eigenvalues on those modes have exactly the same primed determinant. -/
theorem primedDeterminant_gauge_invariant
    {ι : Type} [DecidableEq ι]
    (first second : RegulatedLLSpectrum ι)
    (hModes : first.regulatedModes \ first.zeroModes =
      second.regulatedModes \ second.zeroModes)
    (hEigenvalues : ∀ i ∈ first.regulatedModes \ first.zeroModes,
      first.eigenvalue i = second.eigenvalue i) :
    primedDeterminant first = primedDeterminant second := by
  unfold primedDeterminant
  rw [hModes]
  apply Finset.prod_congr rfl
  intro i hi
  rw [← hModes] at hi
  exact hEigenvalues i hi

/-- The remaining continuum/gauge data are explicit and cannot be hidden in
the finite primed-product construction. -/
structure LLDeterminantGaugeStatus where
  regulatedSpectrumConstructed : Prop
  globalZeroModesSeparated : Prop
  primedDeterminantNonzero : Prop
  bvDifferentialSquareZero : Prop
  perturbativeGaugeFermionFixed : Prop
  gaugeFixedHessianMatchesPhysicalLLAction : Prop
  regulatorRemovalAndLocalSubtractionProved : Prop
  llRGResiduesExtracted : Prop

def llDeterminantGaugeClosed (s : LLDeterminantGaugeStatus) : Prop :=
  s.regulatedSpectrumConstructed ∧
  s.globalZeroModesSeparated ∧
  s.primedDeterminantNonzero ∧
  s.bvDifferentialSquareZero ∧
  s.perturbativeGaugeFermionFixed ∧
  s.gaugeFixedHessianMatchesPhysicalLLAction ∧
  s.regulatorRemovalAndLocalSubtractionProved ∧
  s.llRGResiduesExtracted

/-- Once the finite spectral and BV certificates are supplied, closure reduces
exactly to gauge fixing, physical identification, regulator removal and RG. -/
theorem closure_iff_remaining_physical_obligations
    (gaugeFermion physicalHessian regulatorRemoval rgResidues : Prop) :
    llDeterminantGaugeClosed {
      regulatedSpectrumConstructed := True
      globalZeroModesSeparated := True
      primedDeterminantNonzero := True
      bvDifferentialSquareZero := True
      perturbativeGaugeFermionFixed := gaugeFermion
      gaugeFixedHessianMatchesPhysicalLLAction := physicalHessian
      regulatorRemovalAndLocalSubtractionProved := regulatorRemoval
      llRGResiduesExtracted := rgResidues } ↔
      gaugeFermion ∧ physicalHessian ∧ regulatorRemoval ∧ rgResidues := by
  simp [llDeterminantGaugeClosed]

end JanusFormal.P0EFTJanusLLDeterminantGaugeFixingInterface
