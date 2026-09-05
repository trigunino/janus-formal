import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularFrameCanonicalMaxwellFluxDensity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularFrameMaxwellPairingBridge4D

/-! # Raised regular-frame Maxwell pairing -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularFrameCanonicalMaxwellRaisedPairing4D

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusConformalFrameFreeMaxwellHessian4D
open P0EFTJanusProgramPRegularFrameMaxwellCurvature4D
open P0EFTJanusProgramPRegularGeneralMetricGlobalMaxwellDivergence4D
open P0EFTJanusProgramPRegularFrameGlobalMaxwellBoundaryCurrent4D
open P0EFTJanusProgramPRegularFrameMetricInverse4D
open P0EFTJanusProgramPRegularFrameCanonicalMaxwellFluxDensity4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- The regular coframe evaluated on a metric-raised coframe vector is the
inverse Gram-matrix entry. -/
theorem regularFrameDualCovector_smoothDualVector
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (row first : Fin 4) (point : EffectiveQuotient period hPeriod) :
    regularFrameDualCovector period hPeriod metric row point
        (regularFrameSmoothDualVector period hPeriod metric first point) =
      regularFrameMetricInverseMatrix period hPeriod metric first row point := by
  change
    regularFrameDualCovector period hPeriod metric row point
        (∑ column : Fin 4,
          regularFrameMetricInverseMatrix period hPeriod metric first column
              point • metric.frame column point) = _
  rw [map_sum]
  simp only [map_smul, smul_eq_mul, regularFrameDualCovector_frame]
  simp

/-- Explicit inverse-matrix expression for a raised global curvature
coefficient. -/
theorem regularFrameGlobalGaugeCurvatureRaisedCoefficient_eq_sum
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2) (first second : Fin 4)
    (point : EffectiveQuotient period hPeriod) :
    regularFrameGlobalGaugeCurvatureRaisedCoefficient period hPeriod metric
        potential component first second point =
      ∑ lowerFirst : Fin 4, ∑ lowerSecond : Fin 4,
        regularFrameMetricInverseMatrix period hPeriod metric first lowerFirst
              point *
          regularFrameMetricInverseMatrix period hPeriod metric second
              lowerSecond point *
          regularFrameGaugeCurvatureCoefficient period hPeriod metric potential
            component lowerFirst lowerSecond point := by
  change
    regularGlobalGaugeCurvatureTensor period hPeriod metric potential component
        point
          (regularFrameSmoothDualVector period hPeriod metric first point)
          (regularFrameSmoothDualVector period hPeriod metric second point) = _
  rw [regularGlobalGaugeCurvatureTensor_apply]
  simp_rw [regularFrameDualCovector_smoothDualVector period hPeriod metric]
  apply Finset.sum_congr rfl
  intro lowerFirst _
  apply Finset.sum_congr rfl
  intro lowerSecond _
  ring

/-- A four-index Maxwell contraction is the pairing of the first tensor with
the raised second tensor. -/
theorem matrixMaxwellContraction_eq_raisedSecond
    (inverse first second :
      P0EFTJanusMetricCoupledScalarMatterJetVariation.Matrix4) :
    matrixMaxwellContraction inverse first second =
      ∑ row : Fin 4, ∑ column : Fin 4,
        (∑ lowerRow : Fin 4, ∑ lowerColumn : Fin 4,
          inverse row lowerRow * inverse column lowerColumn *
            second lowerRow lowerColumn) * first row column := by
  unfold matrixMaxwellContraction
  apply Finset.sum_congr rfl
  intro row _
  apply Finset.sum_congr rfl
  intro column _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro lowerRow _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro lowerColumn _
  ring

/-- The invariant mixed Maxwell pairing is the regular-frame curvature of
the first potential paired with the raised curvature of the second. -/
theorem globalMaxwellPairing_eq_raisedRegularFrame
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (first second : SmoothAbelianGaugePotential period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate :
      P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4) :
    globalMaxwellPairing period hPeriod metric.metric first second
        (patch.coordinateMap coordinate) =
      ∑ component : Fin 2, ∑ row : Fin 4, ∑ column : Fin 4,
        regularFrameGlobalGaugeCurvatureRaisedCoefficient period hPeriod metric
              second component row column (patch.coordinateMap coordinate) *
          regularFrameGaugeCurvatureCoefficient period hPeriod metric first
            component row column (patch.coordinateMap coordinate) := by
  rw [P0EFTJanusProgramPRegularFrameMaxwellPairingBridge4D.globalMaxwellPairing_eq_regularFrameContraction]
  apply Finset.sum_congr rfl
  intro component _
  rw [matrixMaxwellContraction_eq_raisedSecond]
  apply Finset.sum_congr rfl
  intro row _
  apply Finset.sum_congr rfl
  intro column _
  rw [regularFrameGlobalGaugeCurvatureRaisedCoefficient_eq_sum]
  rfl

/-- Gate marker: the chart-free Maxwell pairing has an explicit raised
regular-frame contraction. -/
theorem regular_frame_canonical_maxwell_raised_pairing_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (first second : SmoothAbelianGaugePotential period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate :
      P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4) :
    globalMaxwellPairing period hPeriod metric.metric first second
        (patch.coordinateMap coordinate) =
      ∑ component : Fin 2, ∑ row : Fin 4, ∑ column : Fin 4,
        regularFrameGlobalGaugeCurvatureRaisedCoefficient period hPeriod metric
              second component row column (patch.coordinateMap coordinate) *
          regularFrameGaugeCurvatureCoefficient period hPeriod metric first
            component row column (patch.coordinateMap coordinate) :=
  globalMaxwellPairing_eq_raisedRegularFrame period hPeriod metric first second
    patch coordinate

end
end P0EFTJanusProgramPRegularFrameCanonicalMaxwellRaisedPairing4D
end JanusFormal
