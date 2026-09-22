import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusRegularFrameCanonicalGeneratorsDivergenceZero4D

/-! Pullback calculus for arbitrary smooth currents, using the canonical ten flows. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12CanonicalCurrentPullback4D

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusMappingTorusCanonicalTotalR4BallParametrization4D
open P0EFTJanusProgramPRegularFrameMaxwellCurvatureBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularFrameEinsteinHilbertFrameFreeActionMeasureBridge4D
open P0EFTJanusProgramPRegularFrameLocalMetricDivergence4D
open P0EFTJanusProgramPRegularFrameCanonicalDivergenceGluing4D
open P0EFTJanusProgramPRegularFrameCanonicalDivergenceLaw4D
open P0EFTJanusProgramPRegularFrameCanonicalDivergenceObstruction4D
open P0EFTJanusMappingTorusCanonicalTenFlowGeneratorDivergence4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev Index4 := Fin 4
private abbrev Vector4 := Index4 → Real

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

open P0EFTJanusProgramPRegularFrameCanonicalDivergenceLocalFormula4D
open P0EFTJanusMappingTorusCanonicalTenFlowSmoothDual4D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D

/-- The derivative of a pulled scalar against the pulled current is intrinsic. -/
theorem fderiv_comp_coordinateMap_pulledCurrent
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (vector : SmoothTangentField period hPeriod)
    (scalar : SmoothScalarField period hPeriod) (coordinate : Vector4) :
    fderiv Real (scalar.toFun ∘ patch.coordinateMap) coordinate
        (pulledRegularFrameExpansion period hPeriod metric patch vector coordinate) =
      mvfderiv coverModelWithCorners scalar.toFun (patch.coordinateMap coordinate)
        (vector (patch.coordinateMap coordinate)) := by
  unfold pulledRegularFrameExpansion
  rw [map_sum]
  simp_rw [map_smul, fderiv_comp_coordinateMap_pulledRegularFrameVector, smul_eq_mul]
  exact (regularFrameCanonicalDirectionalDerivative_reconstructs period hPeriod
    metric vector scalar (patch.coordinateMap coordinate)).symm

/-- Coordinate pullback respects the exact ten-flow decomposition of any current. -/
theorem pulledCurrent_eq_tenFlowExpansion
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (vector : SmoothTangentField period hPeriod) (coordinate : Vector4) :
    pulledRegularFrameExpansion period hPeriod metric patch vector coordinate =
      ∑ index : Fin 10,
        canonicalTenFlowDualCoefficient period hPeriod metric vector index
            (patch.coordinateMap coordinate) •
          pulledRegularFrameExpansion period hPeriod metric patch
            (canonicalTenFlowVectorField period hPeriod index) coordinate := by
  have hCoefficient (row : Fin 4) :
      regularFrameCanonicalCoefficient period hPeriod metric vector row
          (patch.coordinateMap coordinate) =
        ∑ index : Fin 10,
          canonicalTenFlowDualCoefficient period hPeriod metric vector index
              (patch.coordinateMap coordinate) *
            regularFrameCanonicalCoefficient period hPeriod metric
              (canonicalTenFlowVectorField period hPeriod index) row
              (patch.coordinateMap coordinate) := by
    change generalMetricFiniteFrameCoefficientAt period hPeriod
      (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
      metric.metric (patch.coordinateMap coordinate) row
      (vector (patch.coordinateMap coordinate)) = _
    rw [canonicalTenFlowDual_reconstructs period hPeriod metric vector]
    simp only [map_sum, map_smul, smul_eq_mul]
    rfl
  simp only [pulledRegularFrameExpansion]
  simp_rw [hCoefficient, Finset.sum_smul, mul_smul, Finset.smul_sum]
  exact Finset.sum_comm

end
end P0EFTJanusProgramPT12CanonicalCurrentPullback4D
end JanusFormal
