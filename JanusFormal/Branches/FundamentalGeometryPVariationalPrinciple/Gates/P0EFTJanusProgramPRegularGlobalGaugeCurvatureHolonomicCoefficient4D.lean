import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusLocalMaxwellChristoffelSkewCancellation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricGlobalMaxwellDivergence4D

/-! # Holonomic coefficients of the reconstructed global gauge curvature -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGlobalGaugeCurvatureHolonomicCoefficient4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff Matrix
open P0EFTJanusMetricCoupledScalarMatterJetVariation
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGeneralMetricSymmetricTensorCovariantDerivative4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusIntrinsicAbelianMaxwellCurvature4D
open P0EFTJanusMappingTorusIntrinsicAbelianMaxwellAction4D
open P0EFTJanusMappingTorusConformalFrameFreeMaxwellHessian4D
open P0EFTJanusProgramPRegularFrameMaxwellCurvatureBridge4D
open P0EFTJanusProgramPRegularFrameMaxwellPairingBridge4D
open P0EFTJanusProgramPRegularGeneralMetricGlobalMaxwellDivergence4D

variable (period : Real) (hPeriod : period ≠ 0)

abbrev Index4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Index4
abbrev Vector4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- The reconstructed global curvature and the genuine local exterior
derivative define the same bilinear form in every holonomic chart. -/
theorem regularGlobalGaugeCurvatureTensor_localCoordinateForm
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    localSymmetricTensorCoordinateForm period hPeriod
        (regularGlobalGaugeCurvatureTensor period hPeriod metric potential
          component)
        patch coordinate =
      alternatingTwoFormToBilin
        (localGaugeCurvature period hPeriod potential component patch
          coordinate) := by
  let basis := pulledRegularFrameBasis period hPeriod metric patch coordinate
  apply LinearMap.ext_basis basis basis
  intro regularFirst regularSecond
  rw [show basis regularFirst =
        pulledRegularFrameVector period hPeriod metric patch regularFirst
          coordinate by
      exact pulledRegularFrameBasis_apply period hPeriod metric patch coordinate
        regularFirst,
    show basis regularSecond =
        pulledRegularFrameVector period hPeriod metric patch regularSecond
          coordinate by
      exact pulledRegularFrameBasis_apply period hPeriod metric patch coordinate
        regularSecond]
  rw [localSymmetricTensorCoordinateForm_apply,
    coordinateMap_mfderiv_pulledRegularFrameVector,
    coordinateMap_mfderiv_pulledRegularFrameVector,
    alternatingTwoFormToBilin_apply]
  exact regularGlobalGaugeCurvatureTensor_eq_localGaugeCurvature
    period hPeriod metric potential component patch coordinate regularFirst
      regularSecond

/-- Hence the complete holonomic matrix of the reconstructed global tensor is
the implemented local `dA` matrix. -/
theorem regularGlobalGaugeCurvatureTensor_localMatrix
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    localSymmetricTensorMatrix period hPeriod
        (regularGlobalGaugeCurvatureTensor period hPeriod metric potential
          component)
        patch coordinate =
      localGaugeCurvatureMatrix period hPeriod potential component patch
        coordinate := by
  have hForms := congrArg
    (fun form : LinearMap.BilinForm Real Vector4 =>
      LinearMap.BilinForm.toMatrix (Pi.basisFun Real (Fin 4)) form)
    (regularGlobalGaugeCurvatureTensor_localCoordinateForm period hPeriod
      metric potential component patch coordinate)
  have hGlobalMatrix :
      LinearMap.BilinForm.toMatrix (Pi.basisFun Real (Fin 4))
          (localSymmetricTensorCoordinateForm period hPeriod
            (regularGlobalGaugeCurvatureTensor period hPeriod metric potential
              component)
            patch coordinate) =
        localSymmetricTensorMatrix period hPeriod
          (regularGlobalGaugeCurvatureTensor period hPeriod metric potential
            component)
          patch coordinate := by
    change LinearMap.BilinForm.toMatrix'
      (Matrix.toBilin'
        (localSymmetricTensorMatrix period hPeriod
          (regularGlobalGaugeCurvatureTensor period hPeriod metric potential
            component)
          patch coordinate)) = _
    exact LinearMap.BilinForm.toMatrix'_toBilin' _
  rw [hGlobalMatrix,
    ← localGaugeCurvatureMatrix_eq_toMatrix period hPeriod potential component
      patch coordinate] at hForms
  exact hForms

/-- Entrywise version of the matrix identity. -/
theorem regularGlobalGaugeCurvatureTensor_localCoefficient
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) (first second : Index4) :
    localSymmetricTensorCoefficient period hPeriod
        (regularGlobalGaugeCurvatureTensor period hPeriod metric potential
          component)
        patch first second coordinate =
      localGaugeCurvatureMatrix period hPeriod potential component patch
        coordinate first second := by
  exact congrFun (congrFun
    (regularGlobalGaugeCurvatureTensor_localMatrix period hPeriod metric
      potential component patch coordinate) first) second

/-- The coordinate derivative used by the intrinsic divergence is therefore
the ordinary derivative of the implemented local curvature matrix. -/
theorem regularGlobalGaugeCurvatureTensor_localDerivative
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) (derivative first second : Index4) :
    localSymmetricTensorDerivative period hPeriod
        (regularGlobalGaugeCurvatureTensor period hPeriod metric potential
          component)
        patch coordinate derivative first second =
      fderiv Real
        (fun current =>
          localGaugeCurvatureMatrix period hPeriod potential component patch
            current first second)
        coordinate (Pi.single derivative 1) := by
  unfold localSymmetricTensorDerivative
  rw [show localSymmetricTensorCoefficient period hPeriod
        (regularGlobalGaugeCurvatureTensor period hPeriod metric potential
          component)
        patch first second =
      fun current =>
        localGaugeCurvatureMatrix period hPeriod potential component patch
          current first second by
    funext current
    exact regularGlobalGaugeCurvatureTensor_localCoefficient period hPeriod
      metric potential component patch current first second]

/-- Gate marker for the intrinsic/local curvature-coefficient bridge. -/
theorem regular_global_gauge_curvature_holonomic_coefficient_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    ∀ (component : Fin 2)
        (patch : SmoothHolonomicFrameChart4 period hPeriod)
        (coordinate : Vector4) (first second : Index4),
      localSymmetricTensorCoefficient period hPeriod
          (regularGlobalGaugeCurvatureTensor period hPeriod metric potential
            component)
          patch first second coordinate =
        localGaugeCurvatureMatrix period hPeriod potential component patch
          coordinate first second :=
  regularGlobalGaugeCurvatureTensor_localCoefficient period hPeriod metric
    potential

end
end P0EFTJanusProgramPRegularGlobalGaugeCurvatureHolonomicCoefficient4D
end JanusFormal
