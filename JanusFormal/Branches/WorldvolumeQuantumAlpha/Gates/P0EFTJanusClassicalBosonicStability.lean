import Mathlib
import JanusFormal.Branches.WorldvolumeQuantumAlpha.Gates.P0EFTJanusScaleInvariantWorldvolumeAction

namespace JanusFormal.P0EFTJanusClassicalBosonicStability

set_option autoImplicit false

open P0EFTJanusScaleInvariantWorldvolumeAction

/-- Pointwise physical data for the bosonic Hamiltonian density. -/
structure BosonicHamiltonianPoint where
  action : BosonicActionData
  phi : ℝ
  scalarKineticEnergy : ℝ
  magneticInvariant : ℝ
  phiNonzero : phi ≠ 0
  scalarKineticEnergyNonnegative : 0 ≤ scalarKineticEnergy
  magneticInvariantNonnegative : 0 ≤ magneticInvariant

noncomputable def energyDensity (s : BosonicHamiltonianPoint) : ℝ :=
  s.scalarKineticEnergy + s.magneticInvariant / (4 * s.phi ^ 2) +
    sexticPotential s.action s.phi

theorem dressed_maxwell_energy_nonnegative (s : BosonicHamiltonianPoint) :
    0 ≤ s.magneticInvariant / (4 * s.phi ^ 2) := by
  have hPhiSquare : 0 < s.phi ^ 2 := sq_pos_of_ne_zero s.phiNonzero
  exact div_nonneg s.magneticInvariantNonnegative
    (le_of_lt (mul_pos (by norm_num) hPhiSquare))

/-- In a strictly nonzero magnetic sector, approaching `phi = 0` drives the
dressed Maxwell contribution above every prescribed positive energy scale. -/
theorem magnetic_flux_creates_origin_barrier
    (s : BosonicHamiltonianPoint)
    (bound : ℝ) (hBound : 0 < bound)
    (hNearOrigin : s.phi ^ 2 < s.magneticInvariant / (4 * bound)) :
    bound < s.magneticInvariant / (4 * s.phi ^ 2) := by
  have hFourBound : 0 < 4 * bound := mul_pos (by norm_num) hBound
  have hPhiSquare : 0 < s.phi ^ 2 := sq_pos_of_ne_zero s.phiNonzero
  have hRearranged : s.phi ^ 2 * (4 * bound) < s.magneticInvariant :=
    (lt_div_iff₀ hFourBound).mp hNearOrigin
  apply (lt_div_iff₀ (mul_pos (by norm_num) hPhiSquare)).2
  nlinarith

/-- The local bosonic Hamiltonian is bounded below by zero on `phi ≠ 0`. -/
theorem energy_density_nonnegative (s : BosonicHamiltonianPoint) :
    0 ≤ energyDensity s := by
  unfold energyDensity
  exact add_nonneg
    (add_nonneg s.scalarKineticEnergyNonnegative
      (dressed_maxwell_energy_nonnegative s))
    (sextic_potential_nonnegative s.action s.phi)

/-- The proof deliberately excludes `phi = 0`, where the dressed Maxwell
coefficient is singular and a quantum-domain prescription is still needed. -/
structure ClassicalStabilityStatus where
  positiveKineticSignDerived : Prop
  nonnegativeSexticCouplingDerived : Prop
  nonzeroScalarDomainDerived : Prop
  dressedMaxwellEnergyNonnegative : Prop
  nonzeroFluxOriginBarrierDerived : Prop
  llConstraintHamiltonianDerived : Prop

def classicalStabilityClosed (s : ClassicalStabilityStatus) : Prop :=
  s.positiveKineticSignDerived ∧
  s.nonnegativeSexticCouplingDerived ∧
  s.nonzeroScalarDomainDerived ∧
  s.dressedMaxwellEnergyNonnegative ∧
  s.nonzeroFluxOriginBarrierDerived ∧
  s.llConstraintHamiltonianDerived

end JanusFormal.P0EFTJanusClassicalBosonicStability
