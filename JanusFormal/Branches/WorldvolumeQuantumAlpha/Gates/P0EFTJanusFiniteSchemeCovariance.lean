import Mathlib
import JanusFormal.Branches.WorldvolumeQuantumAlpha.Gates.P0EFTJanusScaleInvariantWorldvolumeAction

namespace JanusFormal.P0EFTJanusFiniteSchemeCovariance

set_option autoImplicit false

open P0EFTJanusScaleInvariantWorldvolumeAction

inductive CountertermOperator
  | scalarKinetic
  | scalarSextic
  | dressedMaxwell
  | gaugeChernSimons
  deriving DecidableEq

def countertermDimension : CountertermOperator → MassDimension
  | .scalarKinetic => scalarKineticDimension
  | .scalarSextic => scalarSexticDimension
  | .dressedMaxwell => dressedMaxwellDensityDimension
  | .gaugeChernSimons => chernSimonsDensityDimension

theorem minimal_counterterm_basis_is_marginal
    (op : CountertermOperator) : countertermDimension op = dWorldvolume := by
  cases op <;>
    norm_num [countertermDimension, scalarKineticDimension,
      scalarSexticDimension, dressedMaxwellDensityDimension,
      chernSimonsDensityDimension, inverseScalarSquareDimension,
      maxwellDensityDimension, fieldStrengthDimension, derivativeDimension,
      scalarDimension, csGaugeFieldDimension, dWorldvolume]

/-- Finite one-log subtraction change.  `shift` parametrizes the finite
counterterm; the logarithmic coefficient is held fixed at this order. -/
structure OneLogSchemeChange where
  coupling : ℝ
  logCoefficient : ℝ
  logCoordinate : ℝ
  shift : ℝ

def shiftedCoupling (s : OneLogSchemeChange) : ℝ :=
  s.coupling + s.logCoefficient * s.shift

def shiftedLogCoordinate (s : OneLogSchemeChange) : ℝ :=
  s.logCoordinate - s.shift

theorem one_log_effective_coefficient_scheme_invariant
    (s : OneLogSchemeChange) :
    shiftedCoupling s + s.logCoefficient * shiftedLogCoordinate s =
      s.coupling + s.logCoefficient * s.logCoordinate := by
  unfold shiftedCoupling shiftedLogCoordinate
  ring

/-- The same finite rescaling leaves `mu*exp(t)` invariant when
`mu -> mu*exp(shift)` and `t -> t-shift`. -/
theorem transmutation_mass_finite_scheme_invariant
    (mu transmutationLog shift : ℝ) :
    (mu * Real.exp shift) * Real.exp (transmutationLog - shift) =
      mu * Real.exp transmutationLog := by
  calc
    (mu * Real.exp shift) * Real.exp (transmutationLog - shift) =
        mu * (Real.exp shift * Real.exp (transmutationLog - shift)) := by ring
    _ = mu * Real.exp (shift + (transmutationLog - shift)) := by
      rw [Real.exp_add]
    _ = mu * Real.exp transmutationLog := by ring_nf

structure RenormalizationClosureStatus where
  regulatorSpecified : Prop
  brstInvariantCountertermBasisDerived : Prop
  betaFunctionsComputed : Prop
  anomalousDimensionsComputed : Prop
  callanSymanzikEquationDerived : Prop
  finiteSchemeCovarianceProved : Prop
  physicalChargeSchemeIndependent : Prop

/-- Inputs that must be fixed before a beta-function coefficient can be called
a result of the candidate theory rather than a free parameter. -/
structure MicroscopicRGSpecification where
  gaugeGroupAndNormalizationFixed : Prop
  scalarRepresentationsFixed : Prop
  fermionRepresentationsFixed : Prop
  chargeAssignmentsFixed : Prop
  llMeasureVerticesDerived : Prop
  gaugeFixingAndGhostActionFixed : Prop
  regulatorFixed : Prop
  subtractionConditionsFixed : Prop
  loopOrderFixed : Prop

def readyForMicroscopicBetaComputation
    (s : MicroscopicRGSpecification) : Prop :=
  s.gaugeGroupAndNormalizationFixed ∧
  s.scalarRepresentationsFixed ∧
  s.fermionRepresentationsFixed ∧
  s.chargeAssignmentsFixed ∧
  s.llMeasureVerticesDerived ∧
  s.gaugeFixingAndGhostActionFixed ∧
  s.regulatorFixed ∧
  s.subtractionConditionsFixed ∧
  s.loopOrderFixed

def renormalizationClosed (s : RenormalizationClosureStatus) : Prop :=
  s.regulatorSpecified ∧
  s.brstInvariantCountertermBasisDerived ∧
  s.betaFunctionsComputed ∧
  s.anomalousDimensionsComputed ∧
  s.callanSymanzikEquationDerived ∧
  s.finiteSchemeCovarianceProved ∧
  s.physicalChargeSchemeIndependent

end JanusFormal.P0EFTJanusFiniteSchemeCovariance
