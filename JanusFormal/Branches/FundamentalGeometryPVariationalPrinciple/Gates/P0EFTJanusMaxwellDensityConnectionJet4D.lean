import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGlobalGaugeCurvatureHolonomicCoefficient4D

/-! # Densitized Maxwell divergence in a connection jet -/

namespace JanusFormal
namespace P0EFTJanusMaxwellDensityConnectionJet4D

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

noncomputable section

open scoped BigOperators Matrix
open P0EFTJanusMetricCoupledScalarMatterJetVariation
open P0EFTJanusMetricInducedScalarStressVariation4D
open P0EFTJanusScalarStressCoordinateConnectionJet4D
open P0EFTJanusMappingTorusLocalMaxwellStressVariation4D

abbrev Index4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Index4
abbrev Matrix4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Matrix4

/-- Pointwise derivative of the densitized twice-raised curvature obtained by
the scalar and matrix product rules. -/
def maxwellDensitizedRaisedCurvatureDerivativeAt
    (connection : MetricCompatibleTorsionFreeConnectionJet4)
    (volume : Real) (volumeDerivative : Index4 → Real)
    (curvature : Matrix4) (curvatureDerivative : Index4 → Matrix4)
    (derivative first second : Index4) : Real :=
  volumeDerivative derivative *
      (∑ lowerFirst : Index4, ∑ lowerSecond : Index4,
        connection.metric.metric⁻¹ first lowerFirst *
          connection.metric.metric⁻¹ second lowerSecond *
          curvature lowerFirst lowerSecond) +
    volume *
      (∑ lowerFirst : Index4, ∑ lowerSecond : Index4,
        (connection.inverseMetricDerivative derivative first lowerFirst *
            connection.metric.metric⁻¹ second lowerSecond *
            curvature lowerFirst lowerSecond +
          connection.metric.metric⁻¹ first lowerFirst *
            connection.inverseMetricDerivative derivative second lowerSecond *
            curvature lowerFirst lowerSecond +
          connection.metric.metric⁻¹ first lowerFirst *
            connection.metric.metric⁻¹ second lowerSecond *
            curvatureDerivative derivative lowerFirst lowerSecond))

/-- Covariant derivative of the original covariant curvature. -/
def maxwellCovariantCurvatureDerivativeAt
    (connection : MetricCompatibleTorsionFreeConnectionJet4)
    (curvature : Matrix4) (curvatureDerivative : Index4 → Matrix4)
    (derivative first second : Index4) : Real :=
  curvatureDerivative derivative first second -
    (∑ upper : Index4,
      connection.christoffel upper derivative first * curvature upper second) -
    ∑ upper : Index4,
      connection.christoffel upper derivative second * curvature first upper

/-- Coordinate divergence of the densitized twice-raised curvature. -/
def maxwellDensitizedRaisedDivergenceAt
    (connection : MetricCompatibleTorsionFreeConnectionJet4)
    (volume : Real) (volumeDerivative : Index4 → Real)
    (curvature : Matrix4) (curvatureDerivative : Index4 → Matrix4)
    (second : Index4) : Real :=
  ∑ derivative : Index4,
    maxwellDensitizedRaisedCurvatureDerivativeAt connection volume
      volumeDerivative curvature curvatureDerivative derivative derivative second

/-- The covariant divergence of the covariant curvature with its remaining
index raised. -/
def maxwellRaisedCovariantDivergenceAt
    (connection : MetricCompatibleTorsionFreeConnectionJet4)
    (curvature : Matrix4) (curvatureDerivative : Index4 → Matrix4)
    (second : Index4) : Real :=
  ∑ lowerSecond : Index4,
    connection.metric.metric⁻¹ second lowerSecond *
      ∑ derivative : Index4, ∑ lowerFirst : Index4,
        connection.metric.metric⁻¹ derivative lowerFirst *
          maxwellCovariantCurvatureDerivativeAt connection curvature
            curvatureDerivative derivative lowerFirst lowerSecond

/-- For a torsion-free metric-compatible connection, the coordinate
divergence of the densitized raised curvature is the metric volume times the
raised covariant divergence. -/
theorem maxwellDensitizedRaisedDivergence_eq_volume_mul_covariant
    (connection : MetricCompatibleTorsionFreeConnectionJet4)
    (volume : Real) (volumeDerivative : Index4 → Real)
    (curvature : Matrix4) (curvatureDerivative : Index4 → Matrix4)
    (hVolumeDerivative : ∀ derivative,
      volumeDerivative derivative = volume *
        ∑ contracted : Index4,
          connection.christoffel contracted derivative contracted)
    (hCurvatureSkew : ∀ first second,
      curvature second first = -curvature first second)
    (second : Index4) :
    maxwellDensitizedRaisedDivergenceAt connection volume volumeDerivative
        curvature curvatureDerivative second =
      volume * maxwellRaisedCovariantDivergenceAt connection curvature
        curvatureDerivative second := by
  classical
  have hInverseDerivative (derivative first second : Index4) :
      connection.inverseMetricDerivative derivative first second =
        -(∑ lower : Index4,
            connection.christoffel first derivative lower *
              connection.metric.metric⁻¹ lower second) -
          ∑ lower : Index4,
            connection.christoffel second derivative lower *
              connection.metric.metric⁻¹ first lower := by
    linarith [connection.inverseMetricCompatible derivative first second]
  have hTraceReindex :
      (∑ derivative : Index4,
          (∑ contracted : Index4,
              connection.christoffel contracted derivative contracted) *
            (∑ lowerFirst : Index4, ∑ lowerSecond : Index4,
              connection.metric.metric⁻¹ derivative lowerFirst *
                connection.metric.metric⁻¹ second lowerSecond *
                curvature lowerFirst lowerSecond)) =
        ∑ derivative : Index4, ∑ lower : Index4,
          connection.christoffel derivative derivative lower *
            (∑ lowerFirst : Index4, ∑ lowerSecond : Index4,
              connection.metric.metric⁻¹ lower lowerFirst *
                connection.metric.metric⁻¹ second lowerSecond *
                curvature lowerFirst lowerSecond) := by
    calc
      _ = ∑ derivative : Index4, ∑ contracted : Index4,
          connection.christoffel contracted derivative contracted *
            (∑ lowerFirst : Index4, ∑ lowerSecond : Index4,
              connection.metric.metric⁻¹ derivative lowerFirst *
                connection.metric.metric⁻¹ second lowerSecond *
                curvature lowerFirst lowerSecond) := by
        apply Finset.sum_congr rfl
        intro derivative _
        rw [Finset.sum_mul]
      _ = ∑ contracted : Index4, ∑ derivative : Index4,
          connection.christoffel contracted derivative contracted *
            (∑ lowerFirst : Index4, ∑ lowerSecond : Index4,
              connection.metric.metric⁻¹ derivative lowerFirst *
                connection.metric.metric⁻¹ second lowerSecond *
                curvature lowerFirst lowerSecond) := by
        rw [Finset.sum_comm]
      _ = ∑ contracted : Index4, ∑ derivative : Index4,
          connection.christoffel contracted contracted derivative *
            (∑ lowerFirst : Index4, ∑ lowerSecond : Index4,
              connection.metric.metric⁻¹ derivative lowerFirst *
                connection.metric.metric⁻¹ second lowerSecond *
                curvature lowerFirst lowerSecond) := by
        apply Finset.sum_congr rfl
        intro contracted _
        apply Finset.sum_congr rfl
        intro derivative _
        rw [connection.torsionFree]
      _ = _ := rfl
  have hExcitationSkew := maxwellExcitationAt_skew volume
    connection.metric.metric⁻¹ curvature hCurvatureSkew
  have hExcitationSkewEntry (first second : Index4) :
      maxwellExcitationAt volume connection.metric.metric⁻¹ curvature second first =
        -maxwellExcitationAt volume connection.metric.metric⁻¹ curvature first
          second := by
    exact congrFun (congrFun hExcitationSkew first) second
  have hChristoffelSkew :
      (∑ first : Index4, ∑ secondIndex : Index4,
        connection.christoffel second first secondIndex *
          maxwellExcitationAt volume connection.metric.metric⁻¹ curvature first
            secondIndex) = 0 := by
    let total := ∑ first : Index4, ∑ secondIndex : Index4,
      connection.christoffel second first secondIndex *
        maxwellExcitationAt volume connection.metric.metric⁻¹ curvature first
          secondIndex
    have hNeg : total = -total := by
      calc
        total = ∑ first : Index4, ∑ secondIndex : Index4,
            connection.christoffel second secondIndex first *
              maxwellExcitationAt volume connection.metric.metric⁻¹ curvature
                secondIndex first := by
          unfold total
          rw [Finset.sum_comm]
        _ = ∑ first : Index4, ∑ secondIndex : Index4,
            connection.christoffel second first secondIndex *
              (-maxwellExcitationAt volume connection.metric.metric⁻¹ curvature
                first secondIndex) := by
          apply Finset.sum_congr rfl
          intro first _
          apply Finset.sum_congr rfl
          intro secondIndex _
          rw [connection.torsionFree, hExcitationSkewEntry]
        _ = -total := by
          unfold total
          simp only [mul_neg, Finset.sum_neg_distrib]
    change total = 0
    linarith
  unfold maxwellDensitizedRaisedDivergenceAt
    maxwellDensitizedRaisedCurvatureDerivativeAt
    maxwellRaisedCovariantDivergenceAt
    maxwellCovariantCurvatureDerivativeAt
  simp_rw [hVolumeDerivative, hInverseDerivative]
  unfold maxwellExcitationAt at hChristoffelSkew
  simp only [Fin.sum_univ_succ] at hTraceReindex hChristoffelSkew ⊢
  ring_nf at hTraceReindex hChristoffelSkew ⊢
  linear_combination volume * hTraceReindex - hChristoffelSkew

/-- Gate marker for the finite connection-jet density/divergence identity. -/
theorem maxwell_density_connection_jet_gate
    (connection : MetricCompatibleTorsionFreeConnectionJet4)
    (volume : Real) (volumeDerivative : Index4 → Real)
    (curvature : Matrix4) (curvatureDerivative : Index4 → Matrix4)
    (hVolumeDerivative : ∀ derivative,
      volumeDerivative derivative = volume *
        ∑ contracted : Index4,
          connection.christoffel contracted derivative contracted)
    (hCurvatureSkew : ∀ first second,
      curvature second first = -curvature first second) :
    ∀ second : Index4,
      maxwellDensitizedRaisedDivergenceAt connection volume volumeDerivative
          curvature curvatureDerivative second =
        volume * maxwellRaisedCovariantDivergenceAt connection curvature
          curvatureDerivative second :=
  maxwellDensitizedRaisedDivergence_eq_volume_mul_covariant connection volume
    volumeDerivative curvature curvatureDerivative hVolumeDerivative
      hCurvatureSkew

end
end P0EFTJanusMaxwellDensityConnectionJet4D
end JanusFormal
