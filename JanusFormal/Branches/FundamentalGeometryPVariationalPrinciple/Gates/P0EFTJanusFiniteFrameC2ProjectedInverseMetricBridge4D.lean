import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameC2ProjectedScalarIntrinsic4D

/-! # Bridge from transported to global inverse-metric coefficients -/

namespace JanusFormal
namespace P0EFTJanusFiniteFrameC2ProjectedInverseMetricBridge4D

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
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D
open P0EFTJanusProgramPGeneralMetricPositiveDualizer4D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusFiniteFrameMetricContraction4D
open P0EFTJanusFiniteFrameC2ProjectedRicciIntrinsic4D
open P0EFTJanusFiniteFrameC2ProjectedScalarIntrinsic4D

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

/-- Coordinate vector obtained by raising a transported redundant dual covector. -/
def finiteFrameLocalRaisedCoefficientVector
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : CoordinateVector)
    (index : Fin frame.count) : CoordinateVector :=
  Matrix.mulVec (localMetricMatrix period hPeriod metric patch coordinate)⁻¹
    (fun lower => finiteFrameLocalCoefficientAt period hPeriod frame baseMetric patch coordinate index
      (Pi.single lower 1))

private theorem localMetricCoordinateForm_raisedCoefficient_basis
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : CoordinateVector)
    (dualIndex : Fin frame.count) (index : Fin 4) :
    localMetricCoordinateForm period hPeriod metric patch coordinate (Pi.single index 1)
        (finiteFrameLocalRaisedCoefficientVector period hPeriod frame baseMetric metric patch coordinate
          dualIndex) =
      finiteFrameLocalCoefficientAt period hPeriod frame baseMetric patch coordinate dualIndex
        (Pi.single index 1) := by
  rw [localMetricCoordinateForm_apply_basis_left]
  change ((localMetricMatrix period hPeriod metric patch coordinate) *ᵥ
    ((localMetricMatrix period hPeriod metric patch coordinate)⁻¹ *ᵥ fun lower =>
      finiteFrameLocalCoefficientAt period hPeriod frame baseMetric patch coordinate dualIndex
        (Pi.single lower 1))) index = _
  rw [Matrix.mulVec_mulVec]
  have hDet : IsUnit (localMetricMatrix period hPeriod metric patch coordinate).det :=
    isUnit_iff_ne_zero.mpr
      (localMetricMatrix_det_ne_zero period hPeriod metric patch coordinate)
  rw [Matrix.mul_nonsing_inv _ hDet, Matrix.one_mulVec]

/-- Raising in local coordinates and raising intrinsically give the same tangent vector. -/
theorem coordinateMap_mfderiv_finiteFrameLocalRaisedCoefficientVector
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : CoordinateVector)
    (index : Fin frame.count) :
    mfderiv (modelWithCornersSelf Real CoordinateVector) coverModelWithCorners
        patch.coordinateMap coordinate
        (finiteFrameLocalRaisedCoefficientVector period hPeriod frame baseMetric metric patch coordinate
          index) =
      inverseMetricSharp period hPeriod metric (patch.coordinateMap coordinate)
        (generalMetricFiniteFrameCoefficientAt period hPeriod frame baseMetric
          (patch.coordinateMap coordinate) index) := by
  apply (metric.musical (patch.coordinateMap coordinate)).injective
  rw [metric_flat_inverseMetricSharp]
  apply ContinuousLinearMap.ext
  intro tangent
  let frameEquiv :=
    (Pi.basisFun Real (Fin 4)).equiv (patch.frame coordinate) (Equiv.refl (Fin 4))
  obtain ⟨vector, rfl⟩ := frameEquiv.surjective tangent
  have hMusical := metric.musical_eq_tensor (patch.coordinateMap coordinate)
  rw [coordinateMap_mfderiv_eq_frameEquiv period hPeriod]
  have hFlat :
      metric.musical (patch.coordinateMap coordinate)
          (frameEquiv (finiteFrameLocalRaisedCoefficientVector period hPeriod frame baseMetric metric
            patch coordinate index)) =
        metric.tensor.tensor (patch.coordinateMap coordinate)
          (frameEquiv (finiteFrameLocalRaisedCoefficientVector period hPeriod frame baseMetric metric
            patch coordinate index)) := DFunLike.congr_fun hMusical _
  rw [hFlat]
  rw [metric.tensor.symmetric]
  have hForm := localMetricCoordinateForm_apply period hPeriod metric patch coordinate vector
    (finiteFrameLocalRaisedCoefficientVector period hPeriod frame baseMetric metric patch coordinate
      index)
  rw [coordinateMap_mfderiv_eq_frameEquiv period hPeriod,
    coordinateMap_mfderiv_eq_frameEquiv period hPeriod] at hForm
  rw [← hForm]
  have hExpansion : vector = ∑ basisIndex : Fin 4,
      vector basisIndex • Pi.single basisIndex 1 := by
    ext basisIndex
    simp [Pi.single_apply]
  rw [hExpansion, map_sum, map_sum, map_sum]
  simp_rw [map_smul]
  rw [LinearMap.sum_apply Finset.univ
    (fun basisIndex : Fin 4 => vector basisIndex •
      localMetricCoordinateForm period hPeriod metric patch coordinate
        (Pi.single basisIndex 1))
    (finiteFrameLocalRaisedCoefficientVector period hPeriod frame baseMetric metric patch coordinate
      index)]
  simp only [LinearMap.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro basisIndex _
  rw [localMetricCoordinateForm_raisedCoefficient_basis period hPeriod frame baseMetric metric patch
    coordinate index basisIndex]
  have hBasis : frameEquiv (Pi.single basisIndex 1) = patch.frame coordinate basisIndex := by
    have hBasis' :
        ((Pi.basisFun Real (Fin 4)).equiv (patch.frame coordinate) (Equiv.refl (Fin 4)))
            ((Pi.basisFun Real (Fin 4)) basisIndex) = patch.frame coordinate basisIndex :=
      Module.Basis.equiv_apply _ _ _ _
    simpa only [frameEquiv, Pi.basisFun_apply] using hBasis'
  change vector basisIndex *
      generalMetricFiniteFrameCoefficientAt period hPeriod frame baseMetric
        (patch.coordinateMap coordinate) index (frameEquiv (Pi.single basisIndex 1)) = _
  rw [hBasis]

/-- The transported inverse coefficient is the existing global smooth inverse coefficient. -/
theorem finiteFrameLocalInverseMetricCoefficientAt_eq_global
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : CoordinateVector)
    (first second : Fin frame.count) :
    finiteFrameLocalInverseMetricCoefficientAt period hPeriod frame baseMetric metric patch coordinate
        first second =
      finiteFrameInverseMetricCoefficient period hPeriod frame baseMetric metric first second
        (patch.coordinateMap coordinate) := by
  rw [finiteFrameInverseMetricCoefficient_apply]
  unfold inverseMetricContraction
  rw [← coordinateMap_mfderiv_finiteFrameLocalRaisedCoefficientVector period hPeriod frame baseMetric
    metric patch coordinate second]
  rw [coordinateMap_mfderiv_eq_frameEquiv period hPeriod]
  change finiteFrameLocalInverseMetricCoefficientAt period hPeriod frame baseMetric metric patch
      coordinate first second =
    finiteFrameLocalCoefficientAt period hPeriod frame baseMetric patch coordinate first
      (finiteFrameLocalRaisedCoefficientVector period hPeriod frame baseMetric metric patch coordinate
        second)
  symm
  have hExpansion :
      finiteFrameLocalRaisedCoefficientVector period hPeriod frame baseMetric metric patch coordinate
          second =
        ∑ row : Fin 4,
          finiteFrameLocalRaisedCoefficientVector period hPeriod frame baseMetric metric patch coordinate
              second row • Pi.single row 1 := by
    ext row
    simp [Pi.single_apply]
  rw [hExpansion, map_sum]
  simp only [map_smul, smul_eq_mul]
  unfold finiteFrameLocalRaisedCoefficientVector finiteFrameLocalInverseMetricCoefficientAt
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro row _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro column _
  ring

end
end P0EFTJanusFiniteFrameC2ProjectedInverseMetricBridge4D
end JanusFormal
