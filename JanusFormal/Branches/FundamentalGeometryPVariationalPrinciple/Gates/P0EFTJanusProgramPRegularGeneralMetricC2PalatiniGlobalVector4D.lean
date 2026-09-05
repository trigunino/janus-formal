import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbertCovariantDivergence4D

/-! # Global Palatini vector of the genuine C² metric variation -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2PalatiniGlobalVector4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D
open P0EFTJanusProgramPRegularFrameMaxwellCurvatureBridge4D
open P0EFTJanusProgramPRegularFrameMaxwellPairingBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2MaxwellStressDerivative4D
open P0EFTJanusProgramPRegularFrameAnholonomicPalatiniDivergence4D
open P0EFTJanusProgramPRegularGeneralMetricC2MetricCompatiblePalatiniJet4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev Index4 := Fin 4

private abbrev Vector4 :=
  P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- Regular-frame coefficients of the Palatini vector produced by the actual
smooth metric direction. -/
def regularGeneralMetricC2PalatiniFrameCoefficient
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (index : Index4) : Real :=
  regularFramePalatiniVector
    (regularGeneralMetricC2MetricCompatiblePalatiniJetAt
      period hPeriod metric
      (regularGeneralMetricC2SmoothDirection period hPeriod metric tensor)
      point) index

/-- The Palatini current reconstructed as an intrinsic tangent vector. -/
def regularGeneralMetricC2PalatiniVectorAt
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    TangentSpace coverModelWithCorners point :=
  ∑ index : Index4,
    regularGeneralMetricC2PalatiniFrameCoefficient
        period hPeriod metric tensor point index •
      metric.frame index point

/-- Holonomic-coordinate representative of the same Palatini current. -/
def regularGeneralMetricC2PalatiniVectorLocal
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) : Vector4 :=
  ∑ index : Index4,
    regularGeneralMetricC2PalatiniFrameCoefficient period hPeriod metric tensor
        (patch.coordinateMap coordinate) index •
      pulledRegularFrameVector period hPeriod metric patch index coordinate

/-- The pulled regular basis reads off exactly the intrinsic Palatini
coefficients. -/
theorem regularGeneralMetricC2PalatiniVectorLocal_repr
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) (index : Index4) :
    (pulledRegularFrameBasis period hPeriod metric patch coordinate).repr
        (regularGeneralMetricC2PalatiniVectorLocal
          period hPeriod metric tensor patch coordinate) index =
      regularGeneralMetricC2PalatiniFrameCoefficient period hPeriod metric
        tensor (patch.coordinateMap coordinate) index := by
  let basis := pulledRegularFrameBasis period hPeriod metric patch coordinate
  let coefficient : Index4 → Real := fun current =>
    regularGeneralMetricC2PalatiniFrameCoefficient period hPeriod metric tensor
      (patch.coordinateMap coordinate) current
  change basis.repr
      (∑ current : Index4, coefficient current •
        pulledRegularFrameVector period hPeriod metric patch current coordinate)
        index = coefficient index
  have hBasis (current : Index4) :
      pulledRegularFrameVector period hPeriod metric patch current coordinate =
        basis current :=
    (pulledRegularFrameBasis_apply period hPeriod metric patch coordinate
      current).symm
  simp_rw [hBasis]
  exact congrFun (basis.repr_sum_self coefficient) index

set_option backward.isDefEq.respectTransparency false in
/-- Pushing the local representative through the chart recovers the global
tangent vector exactly. -/
theorem coordinateMap_mfderiv_regularGeneralMetricC2PalatiniVectorLocal
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners
        patch.coordinateMap coordinate
        (regularGeneralMetricC2PalatiniVectorLocal
          period hPeriod metric tensor patch coordinate) =
      regularGeneralMetricC2PalatiniVectorAt period hPeriod metric tensor
        (patch.coordinateMap coordinate) := by
  unfold regularGeneralMetricC2PalatiniVectorLocal
    regularGeneralMetricC2PalatiniVectorAt
  rw [map_sum]
  simp_rw [map_smul, coordinateMap_mfderiv_pulledRegularFrameVector]

set_option backward.isDefEq.respectTransparency false in
/-- The holonomic representative is unique because every atlas chart is a
local diffeomorphism. -/
theorem regularGeneralMetricC2PalatiniVectorLocal_unique
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate vector : Vector4)
    (hVector :
      mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners
          patch.coordinateMap coordinate vector =
        regularGeneralMetricC2PalatiniVectorAt period hPeriod metric tensor
          (patch.coordinateMap coordinate)) :
    vector = regularGeneralMetricC2PalatiniVectorLocal
      period hPeriod metric tensor patch coordinate := by
  let derivative := patch.coordinateMap_isLocalDiffeomorph
    |>.mfderivToContinuousLinearEquiv (by simp) coordinate
  apply derivative.injective
  change mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners
      patch.coordinateMap coordinate vector =
    mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners
      patch.coordinateMap coordinate
        (regularGeneralMetricC2PalatiniVectorLocal
          period hPeriod metric tensor patch coordinate)
  rw [hVector,
    coordinateMap_mfderiv_regularGeneralMetricC2PalatiniVectorLocal]

/-- Gate marker: the pointwise Palatini current is a genuine intrinsic vector
with unique representatives in every canonical holonomic chart. -/
theorem regular_general_metric_c2_palatini_global_vector_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners
        patch.coordinateMap coordinate
        (regularGeneralMetricC2PalatiniVectorLocal
          period hPeriod metric tensor patch coordinate) =
      regularGeneralMetricC2PalatiniVectorAt period hPeriod metric tensor
        (patch.coordinateMap coordinate) :=
  coordinateMap_mfderiv_regularGeneralMetricC2PalatiniVectorLocal
    period hPeriod metric tensor patch coordinate

end
end P0EFTJanusProgramPRegularGeneralMetricC2PalatiniGlobalVector4D
end JanusFormal
