import Mathlib

namespace JanusFormal.P0EFTJanusPhiZeroFluxZeroFrontier

set_option autoImplicit false

noncomputable def dressedFluxRatio (phi flux : ℝ) : ℝ :=
  flux ^ 2 / phi ^ 2

theorem zero_flux_ray (phi : ℝ) :
    dressedFluxRatio phi 0 = 0 := by
  simp [dressedFluxRatio]

theorem diagonal_flux_ray (phi : ℝ) (hPhi : phi ≠ 0) :
    dressedFluxRatio phi phi = 1 := by
  simp [dressedFluxRatio, hPhi]

/-- The singular Maxwell ratio has incompatible values on two punctured rays,
so `(phi,F)=(0,0)` has no path-independent algebraic extension. -/
theorem no_path_independent_origin_value :
    ¬ ∃ c : ℝ,
      (∀ phi : ℝ, phi ≠ 0 → dressedFluxRatio phi 0 = c) ∧
      (∀ phi : ℝ, phi ≠ 0 → dressedFluxRatio phi phi = c) := by
  rintro ⟨c, hZero, hDiagonal⟩
  have h0 := hZero 1 one_ne_zero
  have h1 := hDiagonal 1 one_ne_zero
  rw [zero_flux_ray] at h0
  rw [diagonal_flux_ray 1 one_ne_zero] at h1
  linarith

structure OriginSectorClosureStatus where
  puncturedFieldDomainSpecified : Prop
  nonzeroFluxBarrierDerived : Prop
  zeroFluxRaySeparated : Prop
  originBoundaryConditionOrUVCompletionFixed : Prop

def originSectorClosed (s : OriginSectorClosureStatus) : Prop :=
  s.puncturedFieldDomainSpecified ∧
  s.nonzeroFluxBarrierDerived ∧
  s.zeroFluxRaySeparated ∧
  s.originBoundaryConditionOrUVCompletionFixed

end JanusFormal.P0EFTJanusPhiZeroFluxZeroFrontier
