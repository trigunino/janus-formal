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

/-- Insert the computed pure-scalar two-loop beta coefficient in repository
normalization. Gauge and LL additions are not included in this theorem. -/
theorem positive_log_coefficient_from_pure_scalar_beta
    (r : CompositeRGData)
    (hBeta :
      r.sexticBeta =
        (25 / (2 * Real.pi ^ 2)) * r.sexticCoupling ^ 2)
    (hAnomalousBound :
      3 * r.compositeAnomalousDimension * r.sexticCoupling <
        (25 / (2 * Real.pi ^ 2)) * r.sexticCoupling ^ 2) :
    0 < r.logCoefficient := by
  apply positive_log_coefficient_from_rg r
  rw [hBeta]
  exact hAnomalousBound

/-- Insert the conditional two-loop non-LL coefficient while retaining the LL
beta contribution as an explicit input. -/
theorem positive_log_coefficient_from_non_ll_beta
    (r : CompositeRGData) (betaLL : ℝ)
    (hBeta :
      r.sexticBeta =
        (475 / (32 * Real.pi ^ 2)) * r.sexticCoupling ^ 2 + betaLL)
    (hAnomalousBound :
      3 * r.compositeAnomalousDimension * r.sexticCoupling <
        (475 / (32 * Real.pi ^ 2)) * r.sexticCoupling ^ 2 + betaLL) :
    0 < r.logCoefficient := by
  apply positive_log_coefficient_from_rg r
  rw [hBeta]
  exact hAnomalousBound

/-- Exact separation of the computed non-LL beta/anomalous terms from the
still-open LL contributions. -/
theorem log_coefficient_non_ll_ll_decomposition
    (r : CompositeRGData) (betaLL gammaLL : ℝ)
    (hBeta :
      r.sexticBeta =
        (475 / (32 * Real.pi ^ 2)) * r.sexticCoupling ^ 2 + betaLL)
    (hGamma :
      r.compositeAnomalousDimension =
        (5 / (16 * Real.pi ^ 2)) * r.sexticCoupling + gammaLL) :
    r.logCoefficient =
      (445 / (32 * Real.pi ^ 2)) * r.sexticCoupling ^ 2 +
        betaLL - 3 * gammaLL * r.sexticCoupling := by
  rw [r.callanSymanzikLaw, hBeta, hGamma]
  ring

theorem positive_log_from_controlled_ll_remainder
    (r : CompositeRGData) (betaLL gammaLL : ℝ)
    (hBeta :
      r.sexticBeta =
        (475 / (32 * Real.pi ^ 2)) * r.sexticCoupling ^ 2 + betaLL)
    (hGamma :
      r.compositeAnomalousDimension =
        (5 / (16 * Real.pi ^ 2)) * r.sexticCoupling + gammaLL)
    (hLLBound :
      3 * gammaLL * r.sexticCoupling <
        (445 / (32 * Real.pi ^ 2)) * r.sexticCoupling ^ 2 + betaLL) :
    0 < r.logCoefficient := by
  rw [log_coefficient_non_ll_ll_decomposition r betaLL gammaLL hBeta hGamma]
  linarith

/-- The remaining local-stability question is now a concrete comparison of
the total anomalous-dimension term with the total beta function. -/
structure ComputedCSInputStatus where
  pureScalarBetaComputed : Prop
  mixedNonLLBetaComputed : Prop
  gaugeBetaContributionComputed : Prop
  llBetaContributionComputed : Prop
  compositeAnomalousDimensionComputed : Prop
  anomalousDimensionBoundProved : Prop
  positiveLogCoefficientDerived : Prop

def computedCSInputsClosed (s : ComputedCSInputStatus) : Prop :=
  s.pureScalarBetaComputed ∧
  s.mixedNonLLBetaComputed ∧
  s.gaugeBetaContributionComputed ∧
  s.llBetaContributionComputed ∧
  s.compositeAnomalousDimensionComputed ∧
  s.anomalousDimensionBoundProved ∧
  s.positiveLogCoefficientDerived

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
