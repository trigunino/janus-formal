import Mathlib
import JanusFormal.Branches.WorldvolumeQuantumAlpha.Gates.P0EFTJanusScaleInvariantWorldvolumeAction

namespace JanusFormal.P0EFTJanusWorldvolumeSignatureAndEOM

set_option autoImplicit false

open P0EFTJanusScaleInvariantWorldvolumeAction

inductive WorldvolumeSignature
  | lorentzian
  | euclidean
  deriving DecidableEq

/-- The parity-even Euclidean density has positive kinetic and potential
coefficients.  The Chern--Simons term acquires the separate imaginary Wick
factor and is therefore not part of this real boundedness statement. -/
structure EuclideanBosonicCoefficients where
  scalarKinetic : ℝ
  dressedMaxwell : ℝ
  sextic : ℝ
  scalarKineticPositive : 0 < scalarKinetic
  dressedMaxwellPositive : 0 < dressedMaxwell
  sexticNonnegative : 0 ≤ sextic

theorem euclidean_parity_even_density_nonnegative
    (c : EuclideanBosonicCoefficients)
    (scalarKineticInvariant dressedMaxwellInvariant phiSix : ℝ)
    (hScalar : 0 ≤ scalarKineticInvariant)
    (hMaxwell : 0 ≤ dressedMaxwellInvariant)
    (hPhiSix : 0 ≤ phiSix) :
    0 ≤ c.scalarKinetic * scalarKineticInvariant +
      c.dressedMaxwell * dressedMaxwellInvariant + c.sextic * phiSix := by
  exact add_nonneg
    (add_nonneg
      (mul_nonneg (le_of_lt c.scalarKineticPositive) hScalar)
      (mul_nonneg (le_of_lt c.dressedMaxwellPositive) hMaxwell))
    (mul_nonneg c.sexticNonnegative hPhiSix)

/-- Homogeneous scalar Euler source for
`V(phi)=lambda6*phi^6/6 + magneticInvariant/(4*phi^2)`. -/
noncomputable def homogeneousScalarEuler
    (lambdaSix magneticInvariant phi : ℝ) : ℝ :=
  lambdaSix * phi ^ 5 - magneticInvariant / (2 * phi ^ 3)

/-- Away from the singular origin, the homogeneous scalar equation is exactly
the algebraic balance `2*lambda6*phi^8 = magneticInvariant`. -/
theorem homogeneous_scalar_equation_iff
    (lambdaSix magneticInvariant phi : ℝ) (hPhi : phi ≠ 0) :
    homogeneousScalarEuler lambdaSix magneticInvariant phi = 0 ↔
      2 * lambdaSix * phi ^ 8 = magneticInvariant := by
  have hPhiCube : phi ^ 3 ≠ 0 := pow_ne_zero 3 hPhi
  constructor
  · intro hEuler
    unfold homogeneousScalarEuler at hEuler
    field_simp [hPhiCube] at hEuler
    nlinarith
  · intro hBalance
    unfold homogeneousScalarEuler
    field_simp [hPhiCube]
    nlinarith

/-- In the zero-flux sector with positive sextic coupling there is no nonzero
homogeneous stationary scalar.  Thus flux is essential for this classical
candidate to support a nonzero saddle. -/
theorem zero_flux_has_no_nonzero_homogeneous_stationary_point
    (lambdaSix phi : ℝ) (hLambda : 0 < lambdaSix) (hPhi : phi ≠ 0) :
    homogeneousScalarEuler lambdaSix 0 phi ≠ 0 := by
  intro hEuler
  have hBalance :=
    (homogeneous_scalar_equation_iff lambdaSix 0 phi hPhi).mp hEuler
  have hPhiPower : 0 < phi ^ 8 := by
    calc
      0 < (phi ^ 4) ^ 2 := sq_pos_of_ne_zero (pow_ne_zero 4 hPhi)
      _ = phi ^ 8 := by ring
  nlinarith

end JanusFormal.P0EFTJanusWorldvolumeSignatureAndEOM
