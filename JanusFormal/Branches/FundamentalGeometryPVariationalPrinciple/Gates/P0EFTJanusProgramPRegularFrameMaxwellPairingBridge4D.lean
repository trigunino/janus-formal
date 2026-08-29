import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularFrameMetricInverse4D

/-!
# Frame-free Maxwell pairing in the genuine regular frame

The stored regular frame and every holonomic coordinate frame are related by
an invertible change-of-basis matrix.  The existing tensorial Maxwell
congruence therefore identifies the global chart-free pairing with the exact
regular-frame contraction used by the general-metric `C²` chart.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularFrameMaxwellPairingBridge4D

set_option autoImplicit false
set_option maxHeartbeats 5000000

noncomputable section

open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusIntrinsicAbelianMaxwellCurvature4D
open P0EFTJanusMappingTorusIntrinsicAbelianMaxwellAction4D
open P0EFTJanusMappingTorusConformalFrameFreeMaxwellHessian4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPRegularFrameMaxwellCurvature4D
open P0EFTJanusProgramPRegularFrameMaxwellCurvatureBridge4D
open P0EFTJanusProgramPRegularFrameMetricInverse4D

variable (period : Real) (hPeriod : period ≠ 0)

abbrev Vector4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4
abbrev Matrix4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Matrix4

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- The regular tangent basis pulled back through a holonomic chart. -/
def pulledRegularFrameBasis
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) : Module.Basis (Fin 4) Real Vector4 :=
  (Pi.basisFun Real (Fin 4)).map
    (((metric.frameEquiv (patch.coordinateMap coordinate)).trans
      ((patch.coordinateMap_isLocalDiffeomorph
        |>.mfderivToContinuousLinearEquiv (by simp) coordinate).symm))
      |>.toLinearEquiv)

theorem pulledRegularFrameBasis_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) (index : Fin 4) :
    pulledRegularFrameBasis period hPeriod metric patch coordinate index =
      pulledRegularFrameVector period hPeriod metric patch index coordinate := by
  let derivative := patch.coordinateMap_isLocalDiffeomorph
    |>.mfderivToContinuousLinearEquiv (by simp) coordinate
  apply derivative.injective
  calc
    derivative
        (pulledRegularFrameBasis period hPeriod metric patch coordinate index) =
        metric.frame index (patch.coordinateMap coordinate) := by
      rw [show pulledRegularFrameBasis period hPeriod metric patch coordinate
            index =
          derivative.symm
            (metric.frameEquiv (patch.coordinateMap coordinate)
              ((Pi.basisFun Real (Fin 4)) index)) by
        rfl]
      rw [derivative.apply_symm_apply]
      exact (RegularGeneralLorentzMetric.frame_eq_basisFun
        period hPeriod metric (patch.coordinateMap coordinate) index).symm
    _ = derivative
        (pulledRegularFrameVector period hPeriod metric patch index
          coordinate) := by
      change metric.frame index (patch.coordinateMap coordinate) =
        mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners
          patch.coordinateMap coordinate
          (pulledRegularFrameVector period hPeriod metric patch index coordinate)
      exact (coordinateMap_mfderiv_pulledRegularFrameVector period hPeriod
        metric patch coordinate index).symm

/-- Change from regular-frame coefficients to holonomic coefficients. -/
def regularFrameChangeMatrix
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) : Matrix4 :=
  (Pi.basisFun Real (Fin 4)).toMatrix
    (pulledRegularFrameBasis period hPeriod metric patch coordinate)

theorem regularFrameChangeMatrix_isUnit
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    IsUnit (regularFrameChangeMatrix period hPeriod metric patch coordinate) := by
  letI : Invertible
      ((Pi.basisFun Real (Fin 4)).toMatrix
        (pulledRegularFrameBasis period hPeriod metric patch coordinate)) :=
    Module.Basis.invertibleToMatrix
      (Pi.basisFun Real (Fin 4))
      (pulledRegularFrameBasis period hPeriod metric patch coordinate)
  change IsUnit
    ((Pi.basisFun Real (Fin 4)).toMatrix
      (pulledRegularFrameBasis period hPeriod metric patch coordinate))
  exact isUnit_of_invertible _

/-- The genuine metric matrix obeys the same basis congruence as the local
holonomic metric matrix. -/
theorem regularFrameMetricMatrix_congruence
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    regularFrameMetricMatrixMap period hPeriod metric
        (patch.coordinateMap coordinate) =
      (regularFrameChangeMatrix period hPeriod metric patch coordinate).transpose *
        localMetricMatrix period hPeriod metric.metric patch coordinate *
        regularFrameChangeMatrix period hPeriod metric patch coordinate := by
  let basis := pulledRegularFrameBasis period hPeriod metric patch coordinate
  let form := localMetricCoordinateForm period hPeriod metric.metric patch coordinate
  have hCongruence :=
    LinearMap.BilinForm.toMatrix_mul_basis_toMatrix
      (b := Pi.basisFun Real (Fin 4)) basis form
  have hLocal :
      LinearMap.BilinForm.toMatrix (Pi.basisFun Real (Fin 4)) form =
        localMetricMatrix period hPeriod metric.metric patch coordinate := by
    change LinearMap.BilinForm.toMatrix'
        (Matrix.toBilin'
          (localMetricMatrix period hPeriod metric.metric patch coordinate)) = _
    exact LinearMap.BilinForm.toMatrix'_toBilin'
      (localMetricMatrix period hPeriod metric.metric patch coordinate)
  have hMatrix :
      LinearMap.BilinForm.toMatrix basis form =
        regularFrameMetricMatrixMap period hPeriod metric
          (patch.coordinateMap coordinate) := by
    ext first second
    rw [LinearMap.BilinForm.toMatrix_apply]
    rw [show basis first = pulledRegularFrameVector period hPeriod metric patch
        first coordinate by
      exact pulledRegularFrameBasis_apply period hPeriod metric patch coordinate first]
    rw [show basis second = pulledRegularFrameVector period hPeriod metric patch
        second coordinate by
      exact pulledRegularFrameBasis_apply period hPeriod metric patch coordinate second]
    rw [localMetricCoordinateForm_apply,
      coordinateMap_mfderiv_pulledRegularFrameVector,
      coordinateMap_mfderiv_pulledRegularFrameVector]
    rfl
  rw [hLocal, hMatrix] at hCongruence
  change regularFrameMetricMatrixMap period hPeriod metric
      (patch.coordinateMap coordinate) =
    ((Pi.basisFun Real (Fin 4)).toMatrix basis).transpose *
      localMetricMatrix period hPeriod metric.metric patch coordinate *
      (Pi.basisFun Real (Fin 4)).toMatrix basis
  exact hCongruence.symm

/-- Each genuine regular-frame curvature matrix is the corresponding
holonomic `dA` matrix under the same basis congruence. -/
theorem regularFrameGaugeCurvatureMatrix_congruence
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    (fun first second =>
      regularFrameGaugeCurvatureCoefficient period hPeriod metric potential
        component first second (patch.coordinateMap coordinate)) =
      (regularFrameChangeMatrix period hPeriod metric patch coordinate).transpose *
        localGaugeCurvatureMatrix period hPeriod potential component patch
          coordinate *
        regularFrameChangeMatrix period hPeriod metric patch coordinate := by
  let basis := pulledRegularFrameBasis period hPeriod metric patch coordinate
  let form := alternatingTwoFormToBilin
    (localGaugeCurvature period hPeriod potential component patch coordinate)
  have hCongruence :=
    LinearMap.BilinForm.toMatrix_mul_basis_toMatrix
      (b := Pi.basisFun Real (Fin 4)) basis form
  have hLocal :
      LinearMap.BilinForm.toMatrix (Pi.basisFun Real (Fin 4)) form =
        localGaugeCurvatureMatrix period hPeriod potential component patch
          coordinate := by
    exact (localGaugeCurvatureMatrix_eq_toMatrix period hPeriod potential
      component patch coordinate).symm
  have hMatrix :
      LinearMap.BilinForm.toMatrix basis form =
        fun first second =>
          regularFrameGaugeCurvatureCoefficient period hPeriod metric potential
            component first second (patch.coordinateMap coordinate) := by
    ext first second
    rw [LinearMap.BilinForm.toMatrix_apply]
    rw [show basis first = pulledRegularFrameVector period hPeriod metric patch
        first coordinate by
      exact pulledRegularFrameBasis_apply period hPeriod metric patch coordinate first]
    rw [show basis second = pulledRegularFrameVector period hPeriod metric patch
        second coordinate by
      exact pulledRegularFrameBasis_apply period hPeriod metric patch coordinate second]
    rw [alternatingTwoFormToBilin_apply]
    exact (regularFrameGaugeCurvatureCoefficient_eq_localGaugeCurvature
      period hPeriod metric potential component patch coordinate first second).symm
  rw [hLocal, hMatrix] at hCongruence
  change (fun first second =>
      regularFrameGaugeCurvatureCoefficient period hPeriod metric potential
        component first second (patch.coordinateMap coordinate)) =
    ((Pi.basisFun Real (Fin 4)).toMatrix basis).transpose *
      localGaugeCurvatureMatrix period hPeriod potential component patch coordinate *
      (Pi.basisFun Real (Fin 4)).toMatrix basis
  exact hCongruence.symm

/-- The chart-free Maxwell pairing is exactly its genuine regular-frame
matrix contraction. -/
theorem globalMaxwellPairing_eq_regularFrameContraction
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (first second : SmoothAbelianGaugePotential period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    globalMaxwellPairing period hPeriod metric.metric first second
        (patch.coordinateMap coordinate) =
      ∑ component : Fin 2,
        matrixMaxwellContraction
          (regularFrameMetricMatrixMap period hPeriod metric
            (patch.coordinateMap coordinate))⁻¹
          (fun row column =>
            regularFrameGaugeCurvatureCoefficient period hPeriod metric first
              component row column (patch.coordinateMap coordinate))
          (fun row column =>
            regularFrameGaugeCurvatureCoefficient period hPeriod metric second
              component row column (patch.coordinateMap coordinate)) := by
  rw [globalMaxwellPairing_eq_local]
  change
    (∑ component : Fin 2,
      matrixMaxwellContraction
        (localMetricMatrix period hPeriod metric.metric patch coordinate)⁻¹
        (localGaugeCurvatureMatrix period hPeriod first component patch coordinate)
        (localGaugeCurvatureMatrix period hPeriod second component patch coordinate)) = _
  apply Finset.sum_congr rfl
  intro component _
  have hInvariant := matrixMaxwellContraction_congruence
    (regularFrameChangeMatrix period hPeriod metric patch coordinate)
    (localMetricMatrix period hPeriod metric.metric patch coordinate)
    (localGaugeCurvatureMatrix period hPeriod first component patch coordinate)
    (localGaugeCurvatureMatrix period hPeriod second component patch coordinate)
    (regularFrameChangeMatrix_isUnit period hPeriod metric patch coordinate)
  rw [← regularFrameMetricMatrix_congruence period hPeriod metric patch coordinate,
    ← regularFrameGaugeCurvatureMatrix_congruence period hPeriod metric first
      component patch coordinate,
    ← regularFrameGaugeCurvatureMatrix_congruence period hPeriod metric second
      component patch coordinate] at hInvariant
  exact hInvariant.symm

/-- Summary gate for the exact regular-frame/global Maxwell identification. -/
theorem regular_frame_maxwell_pairing_bridge_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (first second : SmoothAbelianGaugePotential period hPeriod) :
    ∀ (patch : SmoothHolonomicFrameChart4 period hPeriod)
        (coordinate : Vector4),
      globalMaxwellPairing period hPeriod metric.metric first second
          (patch.coordinateMap coordinate) =
        ∑ component : Fin 2,
          matrixMaxwellContraction
            (regularFrameMetricMatrixMap period hPeriod metric
              (patch.coordinateMap coordinate))⁻¹
            (fun row column =>
              regularFrameGaugeCurvatureCoefficient period hPeriod metric first
                component row column (patch.coordinateMap coordinate))
            (fun row column =>
              regularFrameGaugeCurvatureCoefficient period hPeriod metric second
                component row column (patch.coordinateMap coordinate)) :=
  globalMaxwellPairing_eq_regularFrameContraction period hPeriod metric first second

end

end P0EFTJanusProgramPRegularFrameMaxwellPairingBridge4D
end JanusFormal
