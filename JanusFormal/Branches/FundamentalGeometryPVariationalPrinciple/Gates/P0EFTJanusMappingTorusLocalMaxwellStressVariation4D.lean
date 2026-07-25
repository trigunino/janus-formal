import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicAbelianMaxwellAction4D

/-!
# Local metric/gauge split of the Maxwell first variation

This finite-index identity expands the derivative of
`-√|g| F² / 4` into the part caused by the volume and inverse metric and the
part caused by the derived gauge curvature.  No Euler coefficient is supplied.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusLocalMaxwellStressVariation4D

set_option autoImplicit false

noncomputable section

open scoped BigOperators

abbrev Index4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Index4
abbrev Matrix4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Matrix4

local instance localRealNormedAddCommGroup : NormedAddCommGroup ℝ :=
  inferInstance

local instance localRealNormedSpace : NormedSpace ℝ ℝ :=
  inferInstance

local instance localRealAddCommGroup : AddCommGroup ℝ :=
  localRealNormedAddCommGroup.toAddCommGroup

local instance (priority := 10000) localRealModule : Module ℝ ℝ :=
  localRealNormedSpace.toModule

open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusIntrinsicAbelianMaxwellAction4D

/-- The two-component Maxwell contraction at one chart point. -/
def maxwellPairingAt
    (inverse : Matrix4) (curvature : Fin 2 → Matrix4) : ℝ :=
  ∑ component : Fin 2,
    ∑ μ : Index4, ∑ ν : Index4, ∑ ρ : Index4, ∑ σ : Index4,
      inverse μ ρ * inverse ν σ *
        curvature component μ ν * curvature component ρ σ

/-- The finite-index pairing is exactly the chartwise pairing of the
intrinsically derived curvature. -/
theorem localMaxwellPairing_eq_maxwellPairingAt
    (period : ℝ) (hPeriod : period ≠ 0)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate :
      P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4) :
    localMaxwellPairing period hPeriod metric potential potential patch
        coordinate =
      maxwellPairingAt
        (localMetricMatrix period hPeriod metric patch coordinate)⁻¹
        (fun component =>
          localGaugeCurvatureMatrix period hPeriod potential component patch
            coordinate) := by
  rfl

/-- Inverse-metric contribution to the pairing velocity. -/
def maxwellMetricPairingVelocityAt
    (inverse inverseVelocity : Matrix4)
    (curvature : Fin 2 → Matrix4) : ℝ :=
  ∑ component : Fin 2,
    ∑ μ : Index4, ∑ ν : Index4, ∑ ρ : Index4, ∑ σ : Index4,
      (inverseVelocity μ ρ * inverse ν σ +
          inverse μ ρ * inverseVelocity ν σ) *
        curvature component μ ν * curvature component ρ σ

/-- Curvature contribution to the pairing velocity. -/
def maxwellGaugePairingVelocityAt
    (inverse : Matrix4)
    (curvature curvatureVelocity : Fin 2 → Matrix4) : ℝ :=
  ∑ component : Fin 2,
    ∑ μ : Index4, ∑ ν : Index4, ∑ ρ : Index4, ∑ σ : Index4,
      inverse μ ρ * inverse ν σ *
        (curvatureVelocity component μ ν * curvature component ρ σ +
          curvature component μ ν * curvatureVelocity component ρ σ)

/-- Densitized contravariant Maxwell excitation for one abelian component. -/
def maxwellExcitationAt
    (volume : ℝ) (inverse curvature : Matrix4) : Matrix4 :=
  fun first second =>
    volume *
      ∑ lowerFirst : Index4, ∑ lowerSecond : Index4,
        inverse first lowerFirst * inverse second lowerSecond *
          curvature lowerFirst lowerSecond

/-- Raising both indices and multiplying by the volume preserves the
skew-symmetry inherited from `F = dA`. -/
theorem maxwellExcitationAt_skew
    (volume : ℝ) (inverse curvature : Matrix4)
    (hCurvature : ∀ first second,
      curvature second first = -curvature first second) :
    (maxwellExcitationAt volume inverse curvature).transpose =
      -maxwellExcitationAt volume inverse curvature := by
  ext first second
  unfold maxwellExcitationAt
  simp only [Matrix.transpose_apply, Matrix.neg_apply]
  calc
    volume *
          (∑ lowerFirst : Index4, ∑ lowerSecond : Index4,
            inverse second lowerFirst * inverse first lowerSecond *
              curvature lowerFirst lowerSecond) =
        volume *
          (∑ lowerFirst : Index4, ∑ lowerSecond : Index4,
            inverse second lowerSecond * inverse first lowerFirst *
              curvature lowerSecond lowerFirst) := by
            congr 1
            rw [Finset.sum_comm]
    _ = volume *
          (∑ lowerFirst : Index4, ∑ lowerSecond : Index4,
            inverse second lowerSecond * inverse first lowerFirst *
              (-curvature lowerFirst lowerSecond)) := by
            apply congrArg (volume * ·)
            apply Finset.sum_congr rfl
            intro lowerFirst _
            apply Finset.sum_congr rfl
            intro lowerSecond _
            rw [hCurvature lowerFirst lowerSecond]
    _ = -(volume *
          (∑ lowerFirst : Index4, ∑ lowerSecond : Index4,
            inverse first lowerFirst * inverse second lowerSecond *
              curvature lowerFirst lowerSecond)) := by
            calc
              volume *
                    (∑ lowerFirst : Index4, ∑ lowerSecond : Index4,
                      inverse second lowerSecond * inverse first lowerFirst *
                        (-curvature lowerFirst lowerSecond)) =
                  volume *
                    (∑ lowerFirst : Index4, ∑ lowerSecond : Index4,
                      -(inverse first lowerFirst * inverse second lowerSecond *
                        curvature lowerFirst lowerSecond)) := by
                          apply congrArg (volume * ·)
                          apply Finset.sum_congr rfl
                          intro lowerFirst _
                          apply Finset.sum_congr rfl
                          intro lowerSecond _
                          ring
              _ = _ := by
                    simp_rw [Finset.sum_neg_distrib]
                    ring

/-- Product-rule expansion of the Maxwell pairing velocity. -/
def maxwellPairingVelocityAt
    (inverse inverseVelocity : Matrix4)
    (curvature curvatureVelocity : Fin 2 → Matrix4) : ℝ :=
  maxwellMetricPairingVelocityAt inverse inverseVelocity curvature +
    maxwellGaugePairingVelocityAt inverse curvature curvatureVelocity

/-- Metric part of `δ(-√|g| F²/4)`, including the volume velocity. -/
def localMaxwellMetricVariation
    (volume volumeVelocity : ℝ)
    (inverse inverseVelocity : Matrix4)
    (curvature : Fin 2 → Matrix4) : ℝ :=
  -(1 / 4 : ℝ) *
    (volumeVelocity * maxwellPairingAt inverse curvature +
      volume *
        maxwellMetricPairingVelocityAt inverse inverseVelocity curvature)

/-- Gauge part of `δ(-√|g| F²/4)` at fixed metric. -/
def localMaxwellGaugeVariation
    (volume : ℝ) (inverse : Matrix4)
    (curvature curvatureVelocity : Fin 2 → Matrix4) : ℝ :=
  -(1 / 4 : ℝ) * volume *
    maxwellGaugePairingVelocityAt inverse curvature curvatureVelocity

/-- Covariant metric velocity induced by a covariant variation `h`. -/
def inverseMetricVelocity
    (inverse variation : Matrix4) : Matrix4 :=
  -(inverse * variation * inverse)

/-- The metric trace entering the volume-density derivative. -/
def metricTraceVariation
    (inverse variation : Matrix4) : ℝ :=
  Matrix.trace (inverse * variation)

def matrixPairing (first second : Matrix4) : ℝ :=
  ∑ μ : Index4, ∑ ν : Index4, first μ ν * second μ ν

/-- Maxwell stress pairing derived from the action density itself.  This is
not supplied independently: it is twice the unit-volume metric derivative
with the inverse and volume velocities forced by the same covariant metric
variation. -/
def variationalMaxwellStressPairing
    (inverse : Matrix4) (curvature : Fin 2 → Matrix4)
    (variation : Matrix4) : ℝ :=
  2 *
    localMaxwellMetricVariation 1
      ((1 / 2 : ℝ) * metricTraceVariation inverse variation)
      inverse (inverseMetricVelocity inverse variation) curvature

/-- Maxwell stress paired directly with an inverse-metric velocity. -/
def variationalMaxwellInverseStressPairing
    (metric inverse : Matrix4) (curvature : Fin 2 → Matrix4)
    (inverseVelocity : Matrix4) : ℝ :=
  2 *
    localMaxwellMetricVariation 1
      (-(1 / 2 : ℝ) * matrixPairing metric inverseVelocity)
      inverse inverseVelocity curvature

theorem localMaxwellMetricVariation_eq_inverseStressPairing
    (volume : ℝ) (metric inverse : Matrix4)
    (curvature : Fin 2 → Matrix4) (inverseVelocity : Matrix4) :
    localMaxwellMetricVariation volume
        (-(volume / 2) * matrixPairing metric inverseVelocity)
        inverse inverseVelocity curvature =
      (volume / 2) *
        variationalMaxwellInverseStressPairing metric inverse curvature
          inverseVelocity := by
  simp only [variationalMaxwellInverseStressPairing,
    localMaxwellMetricVariation]
  ring

/-- The metric part of the Maxwell density is exactly one half the volume
times its derived stress pairing. -/
theorem localMaxwellMetricVariation_eq_stressPairing
    (volume : ℝ) (inverse : Matrix4) (curvature : Fin 2 → Matrix4)
    (variation : Matrix4) :
    localMaxwellMetricVariation volume
        ((volume / 2) * metricTraceVariation inverse variation)
        inverse (inverseMetricVelocity inverse variation) curvature =
      (volume / 2) *
        variationalMaxwellStressPairing inverse curvature variation := by
  simp only [variationalMaxwellStressPairing, localMaxwellMetricVariation]
  ring

theorem variationalMaxwellStressPairing_zero :
    variationalMaxwellStressPairing (0 : Matrix4)
      (fun _ => (0 : Matrix4)) (0 : Matrix4) = 0 := by
  simp [variationalMaxwellStressPairing, localMaxwellMetricVariation,
    maxwellPairingAt, maxwellMetricPairingVelocityAt,
    metricTraceVariation, inverseMetricVelocity]

/-- Exact metric/gauge decomposition of the differentiated Maxwell density. -/
theorem maxwellDensityVelocity_eq_metric_add_gauge
    (volume volumeVelocity : ℝ)
    (inverse inverseVelocity : Matrix4)
    (curvature curvatureVelocity : Fin 2 → Matrix4) :
    volumeVelocity * (-(1 / 4 : ℝ) * maxwellPairingAt inverse curvature) +
        volume * (-(1 / 4 : ℝ) *
          maxwellPairingVelocityAt inverse inverseVelocity
            curvature curvatureVelocity) =
      localMaxwellMetricVariation volume volumeVelocity inverse
          inverseVelocity curvature +
        localMaxwellGaugeVariation volume inverse curvature
          curvatureVelocity := by
  simp only [maxwellPairingVelocityAt, localMaxwellMetricVariation,
    localMaxwellGaugeVariation]
  ring

end

end P0EFTJanusMappingTorusLocalMaxwellStressVariation4D
end JanusFormal
