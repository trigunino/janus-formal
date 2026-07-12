import Mathlib
import JanusFormal.Branches.WorldvolumeQuantumAlpha.Gates.P0EFTJanusChernSimonsCriticalAlpha

namespace JanusFormal
namespace P0EFTJanusCallanSymanzikClosure

set_option autoImplicit false

open P0EFTJanusChernSimonsCriticalAlpha

/--
Leading-log Callan--Symanzik data for the composite potential

`V(σ) = σ^3 * (lambda6 + b*log(σ/mu))`.

At the subtraction point, the Callan--Symanzik equation gives

`b = beta_lambda6 - 3*gamma_sigma*lambda6`

in the convention used here.
-/
structure CompositeRGData where
  sexticCoupling : ℝ
  sexticBeta : ℝ
  compositeAnomalousDimension : ℝ
  logCoefficient : ℝ
  callanSymanzikLaw :
    logCoefficient =
      sexticBeta -
        3 * compositeAnomalousDimension * sexticCoupling

/-- The logarithmic coefficient is not an independent parameter. -/
theorem log_coefficient_is_rg_determined
    (r : CompositeRGData) :
    r.logCoefficient =
      r.sexticBeta -
        3 * r.compositeAnomalousDimension * r.sexticCoupling :=
  r.callanSymanzikLaw

/-- A sufficiently positive beta function gives a stable positive logarithmic coefficient. -/
theorem positive_log_coefficient_from_rg
    (r : CompositeRGData)
    (hRG :
      3 * r.compositeAnomalousDimension * r.sexticCoupling <
        r.sexticBeta) :
    0 < r.logCoefficient := by
  rw [r.callanSymanzikLaw]
  linarith

/-- Critical-line data with the finite-N RG correction identified. -/
structure RGClosedCriticalVacuum where
  criticalVacuum : CriticalLineAlphaVacuum
  rgData : CompositeRGData
  sameSextic :
    rgData.sexticCoupling =
      criticalVacuum.vacuum.sexticCoupling
  sameLogCoefficient :
    rgData.logCoefficient =
      criticalVacuum.vacuum.logCoefficient

/-- The hierarchy exponent equation written entirely in RG quantities. -/
theorem hierarchy_equation_from_rg_functions
    (s : RGClosedCriticalVacuum) :
    3 *
        (s.rgData.sexticBeta -
          3 * s.rgData.compositeAnomalousDimension *
            s.rgData.sexticCoupling) *
        (-s.criticalVacuum.vacuum.logRatio) =
      24 * Real.pi ^ 2 *
        (4 - s.criticalVacuum.critical.tHooftCoupling ^ 2) +
      (s.rgData.sexticBeta -
        3 * s.rgData.compositeAnomalousDimension *
          s.rgData.sexticCoupling) := by
  have hHierarchy :=
    critical_stationary_exponent_equation s.criticalVacuum
  have hLog := s.rgData.callanSymanzikLaw
  rw [← s.sameLogCoefficient, hLog] at hHierarchy
  exact hHierarchy

/--
Once the rank, level, beta function, anomalous dimension, UV mass and charge
amplitude are computed, no continuous alpha parameter remains.
-/
structure RGNoFitStatus where
  discreteRankDerived : Prop
  discreteLevelDerived : Prop
  sexticCriticalLineDerived : Prop
  finiteNSexticBetaComputed : Prop
  compositeAnomalousDimensionComputed : Prop
  positiveLogCoefficientProved : Prop
  uvMassAnchorDerived : Prop
  chargeAmplitudeDerived : Prop
  uniqueVacuumDerived : Prop
  alphaDerivedNoFit : Prop


def rgNoFitClosed (s : RGNoFitStatus) : Prop :=
  s.discreteRankDerived /\
  s.discreteLevelDerived /\
  s.sexticCriticalLineDerived /\
  s.finiteNSexticBetaComputed /\
  s.compositeAnomalousDimensionComputed /\
  s.positiveLogCoefficientProved /\
  s.uvMassAnchorDerived /\
  s.chargeAmplitudeDerived /\
  s.uniqueVacuumDerived /\
  s.alphaDerivedNoFit

end P0EFTJanusCallanSymanzikClosure
end JanusFormal
