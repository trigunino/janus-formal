import Mathlib
import JanusFormal.Branches.WorldvolumeQuantumAlpha.Gates.P0EFTJanusScaleInvariantWorldvolumeAction

namespace JanusFormal.P0EFTJanusMCSOneLoopSchemeAudit

set_option autoImplicit false

open P0EFTJanusScaleInvariantWorldvolumeAction

def scalarMonomialDimension (power : ℕ) : MassDimension :=
  power * scalarDimension

theorem even_scalar_counterterm_dimensions :
    scalarMonomialDimension 0 = 0 ∧
    scalarMonomialDimension 2 = 1 ∧
    scalarMonomialDimension 4 = 2 ∧
    scalarMonomialDimension 6 = 3 := by
  norm_num [scalarMonomialDimension, scalarDimension]

/-- With `m_CS = |kappa|*phi^2`, a cutoff term `Lambda*m_CS^2`
has the shape `Lambda*kappa^2*phi^4` and total dimension three. -/
theorem cutoff_quartic_has_density_dimension_three :
    (1 : MassDimension) + scalarMonomialDimension 4 = dWorldvolume := by
  norm_num [scalarMonomialDimension, scalarDimension, dWorldvolume]

/-- The regulator-independent nonanalytic mass term `m_CS^3` has sextic
scalar shape and dimension three. Its finite coefficient can still be shifted
by an allowed finite sextic counterterm. -/
theorem finite_topological_mass_cube_is_sextic :
    scalarMonomialDimension 6 = dWorldvolume := by
  norm_num [scalarMonomialDimension, scalarDimension, dWorldvolume]

inductive EvenScalarCounterterm
  | vacuumEnergy
  | scalarMass
  | scalarQuartic
  | scalarSextic
  deriving DecidableEq

def evenScalarPower : EvenScalarCounterterm → ℕ
  | .vacuumEnergy => 0
  | .scalarMass => 2
  | .scalarQuartic => 4
  | .scalarSextic => 6

theorem even_scalar_basis_is_relevant_or_marginal
    (op : EvenScalarCounterterm) :
    scalarMonomialDimension (evenScalarPower op) ≤ dWorldvolume := by
  cases op <;>
    norm_num [evenScalarPower, scalarMonomialDimension, scalarDimension,
      dWorldvolume]

structure OneLoopMCSResidues where
  logarithmicSexticResidue : ℝ
  sexticBetaContribution : ℝ
  noLogarithmicPole : logarithmicSexticResidue = 0
  msBetaFromPole : sexticBetaContribution = 2 * logarithmicSexticResidue

/-- The isolated MCS determinant contributes zero to the one-loop sextic MS
beta function. This does not cover mixed multi-loop or LL diagrams. -/
theorem isolated_mcs_one_loop_sextic_beta_vanishes
    (r : OneLoopMCSResidues) : r.sexticBetaContribution = 0 := by
  rw [r.msBetaFromPole, r.noLogarithmicPole]
  norm_num

structure OneLoopSchemeClosureStatus where
  regulatorSpectrumSpecified : Prop
  vacuumCountertermFixed : Prop
  scalarMassCountertermFixed : Prop
  scalarQuarticCountertermFixed : Prop
  scalarSexticCountertermFixed : Prop
  powerDivergencesCancelled : Prop
  finiteSubtractionConditionsFixed : Prop
  logarithmicResidueSeparated : Prop

def oneLoopSchemeClosure (s : OneLoopSchemeClosureStatus) : Prop :=
  s.regulatorSpectrumSpecified ∧
  s.vacuumCountertermFixed ∧
  s.scalarMassCountertermFixed ∧
  s.scalarQuarticCountertermFixed ∧
  s.scalarSexticCountertermFixed ∧
  s.powerDivergencesCancelled ∧
  s.finiteSubtractionConditionsFixed ∧
  s.logarithmicResidueSeparated

end JanusFormal.P0EFTJanusMCSOneLoopSchemeAudit
