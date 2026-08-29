import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D

namespace JanusFormal
namespace Bridge

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

open scoped Manifold ContDiff Topology
open Bundle
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothThroatEmbedding
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusNormalBundleOrientationCover
open P0EFTJanusMappingTorusOrientationDoubleCover
open P0EFTJanusMappingTorusCutThroatBoundaryDoubleCover4D
open P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D
open P0EFTJanusMappingTorusSmoothNormalVectorBundle
open P0EFTJanusD8NormalBundleD9DisplacementBridge4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusProgramPGlobalNormalDisplacementCollarGraph4D
open P0EFTJanusProgramPGlobalNormalDisplacementCollarJointSmooth4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev OrientationBoundary := CutThroatBoundary period hPeriod
private abbrev HolonomicVector4 :=
  P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D.Vector4
private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance (priority := 20000) bridgeEffectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance (priority := 20000) bridgeEffectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

theorem test_joint_base_eq_coordinatesAt
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : OrientationBoundary period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter)) :
    normalGraphCanonicalHolonomicMetricUnitNormalJointCoordinates period
        hPeriod metric displacement (boundary, parameter) patch coordinate
          (boundary, parameter) =
      normalGraphCanonicalHolonomicMetricUnitNormalCoordinatesAt period hPeriod
        metric displacement parameter hNonNull boundary patch coordinate hAt := by
  rw [normalGraphCanonicalHolonomicMetricUnitNormalJointCoordinates_base_formula
    period hPeriod metric displacement (boundary, parameter) patch coordinate]
  rw [normalGraphCanonicalMetricUnitNormalJointCoordinates_base_reconstructs
    period hPeriod metric displacement parameter hNonNull boundary]
  unfold normalGraphCanonicalHolonomicMetricUnitNormalCoordinatesAt
  let derivativeEquiv :=
    (patch.coordinateMap_isLocalDiffeomorph coordinate)
      |>.mfderivToContinuousLinearEquiv (by simp)
  have hTransport (point : EffectiveQuotient period hPeriod)
      (hPoint : patch.coordinateMap coordinate = point)
      (vector : TangentSpace coverModelWithCorners point) :
      mfderiv coverModelWithCorners
          (modelWithCornersSelf Real HolonomicVector4)
          (patch.coordinateMap_isLocalDiffeomorph coordinate).localInverse point
          vector =
        derivativeEquiv.symm (hPoint.symm ▸ vector) := by
    subst point
    rfl
  exact hTransport _ hAt _

end
end Bridge
end JanusFormal
