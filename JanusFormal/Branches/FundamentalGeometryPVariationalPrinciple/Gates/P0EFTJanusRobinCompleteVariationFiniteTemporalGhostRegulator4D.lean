import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusFiniteTemporalFourierGaugeGhostCohomology4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusRobinCompleteVariationPairedLinearBRSTBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteModeCommonPhysicalGhostHeatRegulator4D

/-!
# Genuine finite temporal ghosts in the Robin-complete regulator

The symmetric nonzero Fourier cutoff is realized by genuine smooth
`U(1)^2` ghosts on the mapping torus and inserted in the ghost slot of the
Robin-complete Programme-P variation.  Its BRST potential is the intrinsic
exact potential, and the finite heat eigenvalue is the squared norm of the
same Fourier derivative multiplier.

This is only a finite temporal ghost sector.  It does not construct the ghost
Fredholm operator on a completed domain, a common continuum cutoff, or any
local or global anomaly cancellation theorem.
-/

namespace JanusFormal
namespace P0EFTJanusRobinCompleteVariationFiniteTemporalGhostRegulator4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusFiniteModeFredholmDeterminantLine
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusFiniteModeHeatKernelAnomalyRegulator
open P0EFTJanusFiniteModeCommonPhysicalGhostHeatRegulator4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusCommonPairedD9LinearBRSTBlock4D
open P0EFTJanusShiftedSobolevMappingTorusFiniteTemporalFourierBridge4D
open P0EFTJanusMappingTorusFiniteTemporalFourierGaugeGhostZeroMode4D
open P0EFTJanusMappingTorusFiniteTemporalFourierGaugeGhostCohomology4D
open P0EFTJanusRobinCompleteVariationPairedLinearBRSTBridge4D

variable (period : Real) [hPeriodPos : Fact (0 < period)]

/-- The symmetric cutoff modes, excluding the temporal zero mode. -/
abbrev TemporalGaugeGhostCutoffMode (cutoff : Nat) := CutoffMode cutoff

/-- The genuine finite Fourier coefficient carried by one cutoff mode. -/
def temporalGaugeGhostCutoffCoefficient
    {cutoff : Nat} (mode : TemporalGaugeGhostCutoffMode cutoff) :
    FiniteTemporalFourierCoefficients :=
  Finsupp.single (cutoffCircleMode mode) 1

/-- The corresponding genuine smooth `U(1)^2` ghost. -/
def temporalGaugeGhostCutoffField
    {cutoff : Nat} (mode : TemporalGaugeGhostCutoffMode cutoff) :=
  finiteTemporalFourierGaugeGhostLinearMap period
    (temporalGaugeGhostCutoffCoefficient mode)

/-- Put the genuine Fourier ghost in the first paired abelian BRST state. -/
def temporalGaugeGhostCutoffPairedBlock
    {cutoff : Nat} (mode : TemporalGaugeGhostCutoffMode cutoff) :
    CommonPairedD9LinearBRSTBlock period hPeriodPos.out.ne' :=
  { zeroCommonPairedD9LinearBRSTBlock period hPeriodPos.out.ne' with
    firstU1 :=
      { potential := 0
        ghost := temporalGaugeGhostCutoffField period mode } }

/-- The same ghost embedded in the Robin-complete Programme-P tangent. -/
def temporalGaugeGhostCutoffRobinVariation
    {cutoff : Nat} (mode : TemporalGaugeGhostCutoffMode cutoff) :=
  robinCompleteVariationPairedLinearBRSTGhosts period hPeriodPos.out.ne'
    (temporalGaugeGhostCutoffPairedBlock period mode)

@[simp]
theorem temporalGaugeGhostCutoffRobinVariation_ghosts
    {cutoff : Nat} (mode : TemporalGaugeGhostCutoffMode cutoff) :
    (temporalGaugeGhostCutoffRobinVariation period mode
      ).complete.independent.ghosts =
      (temporalGaugeGhostCutoffField period mode, 0) :=
  rfl

/-- One BRST step produces the intrinsic exact potential of this true ghost. -/
@[simp]
theorem temporalGaugeGhostCutoffPairedBlock_BRST_potential
    {cutoff : Nat} (mode : TemporalGaugeGhostCutoffMode cutoff) :
    (commonPairedD9LinearBRSTDifferential period hPeriodPos.out.ne'
      (temporalGaugeGhostCutoffPairedBlock period mode)).firstU1.potential =
      finiteTemporalFourierExactGaugeLinearMap period
        (temporalGaugeGhostCutoffCoefficient mode) :=
  rfl

/-- Finite heat spectrum of the actual temporal ghost derivative.  Chirality
is retained as explicit input rather than assumed to vanish. -/
def temporalGaugeGhostCutoffSpectrum
    (cutoff : Nat)
    (chirality : TemporalGaugeGhostCutoffMode cutoff → Real) :
    FiniteChiralSpectrum (TemporalGaugeGhostCutoffMode cutoff) where
  eigenvalueSq := fun mode =>
    Complex.normSq
      (temporalFourierDerivativeMultiplier period (cutoffCircleMode mode))
  eigenvalueSq_nonnegative := fun mode => Complex.normSq_nonneg _
  chirality := chirality

/-- The regulator eigenvalue is exactly the squared coefficient of the
intrinsic temporal derivative computed in the Fourier ghost gate. -/
theorem temporalGaugeGhostCutoffSpectrum_eigenvalueSq_eq_derivative
    (cutoff : Nat)
    (chirality : TemporalGaugeGhostCutoffMode cutoff → Real)
    (mode : TemporalGaugeGhostCutoffMode cutoff) :
    (temporalGaugeGhostCutoffSpectrum period cutoff chirality).eigenvalueSq mode =
      Complex.normSq
        (temporalFourierDerivativeCoefficients period
          (temporalGaugeGhostCutoffCoefficient mode)
          (cutoffCircleMode mode)) := by
  rw [temporalFourierDerivativeCoefficients_apply]
  simp only [temporalGaugeGhostCutoffSpectrum,
    temporalGaugeGhostCutoffCoefficient, Finsupp.single_eq_same, one_mul]

/-- PT exchanges the two nonzero frequencies without changing the squared
ghost derivative eigenvalue. -/
@[simp]
theorem temporalGaugeGhostCutoffSpectrum_eigenvalueSq_pt
    (cutoff : Nat)
    (chirality : TemporalGaugeGhostCutoffMode cutoff → Real)
    (mode : TemporalGaugeGhostCutoffMode cutoff) :
    (temporalGaugeGhostCutoffSpectrum period cutoff chirality).eigenvalueSq
        (ptMode mode) =
      (temporalGaugeGhostCutoffSpectrum period cutoff chirality).eigenvalueSq
        mode := by
  change Complex.normSq
      (temporalFourierDerivativeMultiplier period
        (cutoffCircleMode (ptMode mode))) =
    Complex.normSq
      (temporalFourierDerivativeMultiplier period (cutoffCircleMode mode))
  rw [cutoffCircleMode_pt]
  have hMultiplier :
      temporalFourierDerivativeMultiplier period
          (-cutoffCircleMode mode) =
        -temporalFourierDerivativeMultiplier period (cutoffCircleMode mode) := by
    simp [temporalFourierDerivativeMultiplier]
    ring
  rw [hMultiplier, Complex.normSq_neg]

/-- The actual finite ghost sector, with the standard ghost statistics sign,
can therefore be inserted in the existing common finite heat regulator. -/
def temporalGaugeGhostWeightedSector
    (cutoff multiplicity : Nat)
    (chirality : TemporalGaugeGhostCutoffMode cutoff → Real) :
    WeightedSector (TemporalGaugeGhostCutoffMode cutoff) where
  multiplicity := multiplicity
  statistics := .ghost
  spectrum := temporalGaugeGhostCutoffSpectrum period cutoff chirality

@[simp]
theorem temporalGaugeGhostWeightedSector_statistics
    (cutoff multiplicity : Nat)
    (chirality : TemporalGaugeGhostCutoffMode cutoff → Real) :
    (temporalGaugeGhostWeightedSector period cutoff multiplicity chirality
      ).statistics = .ghost :=
  rfl

end
end P0EFTJanusRobinCompleteVariationFiniteTemporalGhostRegulator4D
end JanusFormal
