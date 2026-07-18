import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCoDiagonalInteractionDensityFrechet
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGlobalDiagonalLorentzRoot4D

/-!
# Global two-sector Candidate-A density on the diagonal Lorentz domain

The positive scale-pair chart is the complete fixed-frame diagonal Lorentz
domain: both independent metrics have positive lapse/spatial magnitudes, with
no smallness condition around Minkowski.  This gate evaluates the genuine
Candidate-A spectral density in both metric orders, differentiates both terms
with respect to the full metric-scale pair, and proves exact exchange
invariance on the same open domain.

This is global on the simultaneously diagonal fixed-frame sector only.  It
does not claim a causal-compatible principal root for arbitrary noncommuting
Lorentz metric pairs or a curved-spacetime functional derivative.
-/

namespace JanusFormal
namespace P0EFTJanusGlobalDiagonalInteractionDensity4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusReciprocalBimetricPotential
open P0EFTJanusCoDiagonalLorentzRootFirstDerivative
open P0EFTJanusCoDiagonalInteractionDensityFrechet

abbrev Spectrum4 := Fin 4 → ℝ
abbrev ScalePair := Spectrum4 × Spectrum4

/-- Continuous exchange of the two independent diagonal metric-scale slots. -/
def scalePairExchange : ScalePair ≃L[ℝ] ScalePair :=
  ContinuousLinearEquiv.prodComm ℝ Spectrum4 Spectrum4

@[simp]
theorem scalePairExchange_apply (point : ScalePair) :
    scalePairExchange point = (point.2, point.1) :=
  rfl

@[simp]
theorem scalePairExchange_involutive (point : ScalePair) :
    scalePairExchange (scalePairExchange point) = point := by
  rcases point with ⟨plus, minus⟩
  rfl

/-- The complete positive diagonal domain is invariant under sector exchange. -/
theorem scalePairExchange_mem_domain_iff (point : ScalePair) :
    scalePairExchange point ∈ ambientPositiveScalePairDomain ↔
      point ∈ ambientPositiveScalePairDomain := by
  rcases point with ⟨plus, minus⟩
  simp [ambientPositiveScalePairDomain, scalePairExchange]
  exact and_comm

/-- Candidate-A density in the reversed metric order. -/
def exchangedDiagonalInteractionDensity
    (interactionScale : ℝ) (coefficients : PotentialCoefficients)
    (point : ScalePair) : ℝ :=
  coDiagonalInteractionDensity interactionScale coefficients
    (scalePairExchange point)

/-- Exact derivative of the reversed-order density. -/
def exchangedDiagonalInteractionDensityDerivative
    (interactionScale : ℝ) (coefficients : PotentialCoefficients)
    (point : ScalePair) : ScalePair →L[ℝ] ℝ :=
  (coDiagonalInteractionDensityDerivative interactionScale coefficients
      (scalePairExchange point)).comp
    (scalePairExchange : ScalePair →L[ℝ] ScalePair)

theorem exchangedDiagonalInteractionDensity_hasFDerivAt
    (interactionScale : ℝ) (coefficients : PotentialCoefficients)
    {point : ScalePair} (hPoint : point ∈ ambientPositiveScalePairDomain) :
    HasFDerivAt
      (exchangedDiagonalInteractionDensity interactionScale coefficients)
      (exchangedDiagonalInteractionDensityDerivative interactionScale
        coefficients point) point := by
  have hExchange :
      scalePairExchange point ∈ ambientPositiveScalePairDomain :=
    (scalePairExchange_mem_domain_iff point).2 hPoint
  exact
    (coDiagonalInteractionDensity_hasFDerivAt interactionScale coefficients
      (scalePairExchange point) hExchange).comp point
        (scalePairExchange : ScalePair →L[ℝ] ScalePair).hasFDerivAt

/-- Sum of the two genuine Candidate-A sector densities. -/
def globalDiagonalTwoSectorDensity
    (interactionScale : ℝ) (coefficients : PotentialCoefficients)
    (point : ScalePair) : ℝ :=
  coDiagonalInteractionDensity interactionScale coefficients point +
    exchangedDiagonalInteractionDensity interactionScale coefficients point

/-- Full two-metric derivative of the two-sector density. -/
def globalDiagonalTwoSectorDensityDerivative
    (interactionScale : ℝ) (coefficients : PotentialCoefficients)
    (point : ScalePair) : ScalePair →L[ℝ] ℝ :=
  coDiagonalInteractionDensityDerivative interactionScale coefficients point +
    exchangedDiagonalInteractionDensityDerivative interactionScale
      coefficients point

theorem globalDiagonalTwoSectorDensity_hasFDerivAt
    (interactionScale : ℝ) (coefficients : PotentialCoefficients)
    {point : ScalePair} (hPoint : point ∈ ambientPositiveScalePairDomain) :
    HasFDerivAt (globalDiagonalTwoSectorDensity interactionScale coefficients)
      (globalDiagonalTwoSectorDensityDerivative interactionScale coefficients
        point) point := by
  exact
    (coDiagonalInteractionDensity_hasFDerivAt interactionScale coefficients
      point hPoint).add
        (exchangedDiagonalInteractionDensity_hasFDerivAt interactionScale
          coefficients hPoint)

/-- The complete density is exactly invariant under plus/minus exchange. -/
theorem globalDiagonalTwoSectorDensity_exchange
    (interactionScale : ℝ) (coefficients : PotentialCoefficients)
    (point : ScalePair) :
    globalDiagonalTwoSectorDensity interactionScale coefficients
        (scalePairExchange point) =
      globalDiagonalTwoSectorDensity interactionScale coefficients point := by
  simp only [globalDiagonalTwoSectorDensity,
    exchangedDiagonalInteractionDensity, scalePairExchange_involutive]
  exact add_comm _ _

/-- Differentiability holds at every point of the full positive diagonal
domain, with no local-chart smallness hypothesis. -/
theorem globalDiagonalTwoSectorDensity_differentiableAt
    (interactionScale : ℝ) (coefficients : PotentialCoefficients)
    {point : ScalePair} (hPoint : point ∈ ambientPositiveScalePairDomain) :
    DifferentiableAt ℝ
      (globalDiagonalTwoSectorDensity interactionScale coefficients) point :=
  (globalDiagonalTwoSectorDensity_hasFDerivAt interactionScale coefficients
    hPoint).differentiableAt

end

end P0EFTJanusGlobalDiagonalInteractionDensity4D
end JanusFormal
