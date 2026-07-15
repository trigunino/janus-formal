import Mathlib
import JanusFormal.Branches.WorldvolumeQuantumAlpha.Gates.P0EFTJanusScaleInvariantWorldvolumeAction

namespace JanusFormal.P0EFTJanusTruncatedPotentialCounterterms

set_option autoImplicit false

open P0EFTJanusScaleInvariantWorldvolumeAction

/-!
Local background-potential counterterms through the manifest truncation
`eta^6`. These Taylor coefficients are independent EFT data; this is not an
all-derivative counterterm basis.
-/

abbrev PotentialCountertermOrder6 := Fin 7

def scalarPower (op : PotentialCountertermOrder6) : ℕ := op.val

def coefficientDimension (op : PotentialCountertermOrder6) : MassDimension :=
  dWorldvolume - scalarPower op * scalarDimension

/-- Every coefficient has exactly the dimension needed for a local density in
2+1 dimensions. -/
theorem truncated_potential_density_dimension
    (op : PotentialCountertermOrder6) :
    coefficientDimension op + scalarPower op * scalarDimension =
      dWorldvolume := by
  unfold coefficientDimension
  ring

theorem truncated_potential_power_at_most_six
    (op : PotentialCountertermOrder6) : scalarPower op ≤ 6 := by
  exact Nat.le_of_lt_succ op.isLt

/-- The fixed-order potential basis contains the seven monomials
`1, eta, ..., eta^6`. -/
theorem truncated_potential_basis_cardinality :
    Fintype.card PotentialCountertermOrder6 = 7 := by
  simp

/-- Up to `eta^6`, all potential coefficients are relevant or marginal by
mass dimension. -/
theorem truncated_potential_coefficients_nonnegative_dimension
    (op : PotentialCountertermOrder6) : 0 ≤ coefficientDimension op := by
  have hPower := truncated_potential_power_at_most_six op
  have hPowerRat : (scalarPower op : ℚ) ≤ 6 := by exact_mod_cast hPower
  norm_num [coefficientDimension, dWorldvolume, scalarDimension]
  linarith

end JanusFormal.P0EFTJanusTruncatedPotentialCounterterms
