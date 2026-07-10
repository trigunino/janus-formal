import Mathlib

namespace JanusFormal
namespace P0EFTJanusScaleInvariantWorldvolumeAction

set_option autoImplicit false

abbrev MassDimension := Rat

/-- World-volume spacetime dimension. -/
def dWorldvolume : MassDimension := 3

/-- Canonical scalar dimension in three spacetime dimensions. -/
def scalarDimension : MassDimension := (1 : Rat) / 2

/-- Chern--Simons scaling assigns dimension one to the compact gauge field. -/
def csGaugeFieldDimension : MassDimension := 1

/-- Derivative mass dimension. -/
def derivativeDimension : MassDimension := 1


def scalarKineticDimension : MassDimension :=
  2 * (derivativeDimension + scalarDimension)


def scalarSexticDimension : MassDimension :=
  6 * scalarDimension


def chernSimonsDensityDimension : MassDimension :=
  2 * csGaugeFieldDimension + derivativeDimension


def fieldStrengthDimension : MassDimension :=
  derivativeDimension + csGaugeFieldDimension


def maxwellDensityDimension : MassDimension :=
  2 * fieldStrengthDimension


def inverseScalarSquareDimension : MassDimension :=
  -(2 * scalarDimension)


def dressedMaxwellDensityDimension : MassDimension :=
  inverseScalarSquareDimension + maxwellDensityDimension

/-- Every proposed classical term has the required dimension three. -/
theorem candidate_terms_are_classically_marginal :
    scalarKineticDimension = dWorldvolume /\
    scalarSexticDimension = dWorldvolume /\
    chernSimonsDensityDimension = dWorldvolume /\
    dressedMaxwellDensityDimension = dWorldvolume := by
  norm_num [scalarKineticDimension, scalarSexticDimension,
    chernSimonsDensityDimension, dressedMaxwellDensityDimension,
    inverseScalarSquareDimension, maxwellDensityDimension,
    fieldStrengthDimension, derivativeDimension, scalarDimension,
    csGaugeFieldDimension, dWorldvolume]

/-- An undressed Maxwell term needs a coefficient of mass dimension minus one. -/
def ordinaryMaxwellCoefficientDimension : MassDimension :=
  dWorldvolume - maxwellDensityDimension


theorem ordinary_maxwell_term_hides_a_dimensionful_scale :
    ordinaryMaxwellCoefficientDimension = -1 := by
  norm_num [ordinaryMaxwellCoefficientDimension, dWorldvolume,
    maxwellDensityDimension, fieldStrengthDimension,
    derivativeDimension, csGaugeFieldDimension]

/-- The scalar dressing supplies exactly the missing inverse-mass dimension. -/
theorem scalar_dressing_repairs_maxwell_dimension :
    inverseScalarSquareDimension = ordinaryMaxwellCoefficientDimension := by
  norm_num [inverseScalarSquareDimension, scalarDimension,
    ordinaryMaxwellCoefficientDimension, dWorldvolume,
    maxwellDensityDimension, fieldStrengthDimension,
    derivativeDimension, csGaugeFieldDimension]

/--
Concrete candidate field content:

`S = integral sqrt(-gamma) [ (d phi)^2/2 - lambda6 phi^6/6
      - F^2/(4 phi^2) ] + k/(4*pi) integral A dA + S_LL`.

A nonzero quantum condensate gives the Maxwell scale and can normalize the LL
charge without inserting a classical mass parameter.
-/
structure ScaleInvariantWorldvolumeCandidateStatus where
  realScalarDefined : Prop
  compactU1ConnectionDefined : Prop
  scalarKineticTermDefined : Prop
  sexticPotentialDefined : Prop
  scalarDressedMaxwellTermDefined : Prop
  integerChernSimonsLevelDefined : Prop
  llMeasureSectorCoupled : Prop
  classicalWeylWeightsChecked : Prop
  gaugeInvariantRegularizationDefined : Prop
  effectivePotentialComputed : Prop
  stableNonzeroCondensateProved : Prop
  condensateToChargeNormalizationDerived : Prop
  unitarityAndNoGhostProved : Prop


def scaleInvariantCandidateClosed
    (s : ScaleInvariantWorldvolumeCandidateStatus) : Prop :=
  s.realScalarDefined /\
  s.compactU1ConnectionDefined /\
  s.scalarKineticTermDefined /\
  s.sexticPotentialDefined /\
  s.scalarDressedMaxwellTermDefined /\
  s.integerChernSimonsLevelDefined /\
  s.llMeasureSectorCoupled /\
  s.classicalWeylWeightsChecked /\
  s.gaugeInvariantRegularizationDefined /\
  s.effectivePotentialComputed /\
  s.stableNonzeroCondensateProved /\
  s.condensateToChargeNormalizationDerived /\
  s.unitarityAndNoGhostProved

end P0EFTJanusScaleInvariantWorldvolumeAction
end JanusFormal
