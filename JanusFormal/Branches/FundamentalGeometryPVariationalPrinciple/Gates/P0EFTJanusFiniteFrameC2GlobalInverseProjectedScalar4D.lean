import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameC2ProjectedInverseMetricBridge4D

/-! # Projected scalar curvature with global inverse-metric coefficients -/

namespace JanusFormal
namespace P0EFTJanusFiniteFrameC2GlobalInverseProjectedScalar4D

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open scoped Manifold ContDiff BigOperators Matrix
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D
open P0EFTJanusMappingTorusCanonicalHolonomicRiemannNaturality4D
open P0EFTJanusMappingTorusCanonicalHolonomicScalarCurvatureNaturality4D
open P0EFTJanusMappingTorusIntrinsicEinsteinHilbertCurvature4D
open P0EFTJanusProgramPGeneralMetricPositiveDualizer4D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusFiniteFrameMetricContraction4D
open P0EFTJanusFiniteFrameC2ProjectedRicciIntrinsic4D
open P0EFTJanusFiniteFrameC2ProjectedScalarIntrinsic4D
open P0EFTJanusFiniteFrameC2ProjectedInverseMetricBridge4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev CoordinateVector :=
  P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4
local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

variable (frame : SmoothD8Frame period hPeriod)
  (baseMetric metric : SmoothGeneralLorentzMetric period hPeriod)

/-- Projected Ricci contraction written with the global smooth inverse-metric coefficients. -/
def finiteFrameGlobalInverseProjectedScalarCurvatureAt
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : CoordinateVector) : Real :=
  ∑ first : Fin frame.count, ∑ second : Fin frame.count,
    finiteFrameInverseMetricCoefficient period hPeriod frame baseMetric metric first second
        (patch.coordinateMap coordinate) *
      finiteFrameProjectedRicciCoefficientAt period hPeriod frame baseMetric metric patch coordinate
        first second

/-- The global-coefficient contraction is the transported projected contraction. -/
theorem finiteFrameGlobalInverseProjectedScalarCurvatureAt_eq_projected
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : CoordinateVector) :
    finiteFrameGlobalInverseProjectedScalarCurvatureAt period hPeriod frame baseMetric metric patch
        coordinate =
      finiteFrameProjectedScalarCurvatureAt period hPeriod frame baseMetric metric patch coordinate := by
  unfold finiteFrameGlobalInverseProjectedScalarCurvatureAt finiteFrameProjectedScalarCurvatureAt
  simp_rw [← finiteFrameLocalInverseMetricCoefficientAt_eq_global period hPeriod frame baseMetric metric
    patch coordinate]

/-- The projected contraction with global inverse coefficients is intrinsic scalar curvature. -/
theorem finiteFrameGlobalInverseProjectedScalarCurvatureAt_eq_intrinsic
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : CoordinateVector) :
    finiteFrameGlobalInverseProjectedScalarCurvatureAt period hPeriod frame baseMetric metric patch
        coordinate =
      localScalarCurvature period hPeriod metric patch coordinate := by
  rw [finiteFrameGlobalInverseProjectedScalarCurvatureAt_eq_projected period hPeriod frame baseMetric
    metric patch coordinate]
  exact finiteFrameProjectedScalarCurvatureAt_eq_intrinsic period hPeriod frame baseMetric metric patch
    coordinate

end
end P0EFTJanusFiniteFrameC2GlobalInverseProjectedScalar4D
end JanusFormal
