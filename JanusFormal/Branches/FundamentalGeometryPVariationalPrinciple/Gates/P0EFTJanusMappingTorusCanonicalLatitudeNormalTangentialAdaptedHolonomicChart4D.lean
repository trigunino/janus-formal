import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeNormalAdaptedHolonomicChart4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeScalarStressEnergyCurrent4D

/-!
# Normal-and-tangential adapted holonomic charts
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalLatitudeNormalTangentialAdaptedHolonomicChart4D

set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalLatitudeScalarNormalCurrent4D
open P0EFTJanusMappingTorusCanonicalLatitudeScalarStressEnergyCurrent4D
open P0EFTJanusMappingTorusCanonicalLatitudeNormalAdaptedHolonomicChart4D
open P0EFTJanusMappingTorusCanonicalHolonomicChartBallRealization4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D

variable (period : Real) (hPeriod : period ≠ 0)

abbrev Vector4 := Fin 4 → Real
private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

private def firstCoordinate : Vector4 →L[Real] Real :=
  ContinuousLinearMap.proj 0

private def firstBasisVector : Vector4 :=
  Pi.single 0 1

/-- Rank-one correction which preserves the first axis and makes a covector
equal to the first coordinate after precomposition. -/
private def normalKernelCorrection
    (covector : Vector4 →L[Real] Real) : Vector4 →L[Real] Vector4 :=
  ContinuousLinearMap.id Real Vector4 +
    (firstCoordinate - covector).smulRight firstBasisVector

private theorem normalKernelCorrection_covector
    (covector : Vector4 →L[Real] Real)
    (hFirst : covector firstBasisVector = 1) (vector : Vector4) :
    covector (normalKernelCorrection covector vector) = firstCoordinate vector := by
  simp only [normalKernelCorrection, add_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply,
    sub_apply, map_add, map_smul, hFirst, smul_eq_mul]
  ring

private theorem normalKernelCorrection_first
    (covector : Vector4 →L[Real] Real)
    (hFirst : covector firstBasisVector = 1) :
    normalKernelCorrection covector firstBasisVector = firstBasisVector := by
  simp only [normalKernelCorrection, add_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply,
    sub_apply]
  rw [hFirst]
  simp [firstCoordinate, firstBasisVector]

private theorem normalKernelCorrection_injective
    (covector : Vector4 →L[Real] Real)
    (hFirst : covector firstBasisVector = 1) :
    Function.Injective (normalKernelCorrection covector) := by
  intro first second hEqual
  suffices first - second = 0 by exact sub_eq_zero.mp this
  let difference := first - second
  have hDifference : normalKernelCorrection covector difference = 0 := by
    rw [map_sub, hEqual, sub_self]
  have hCoordinate : firstCoordinate difference = 0 := by
    rw [← normalKernelCorrection_covector covector hFirst difference,
      hDifference, map_zero]
  have hFormula :
      difference - covector difference • firstBasisVector = 0 := by
    simpa [normalKernelCorrection, hCoordinate, sub_eq_add_neg] using hDifference
  have hDifferenceEq :
      difference = covector difference • firstBasisVector :=
    sub_eq_zero.mp hFormula
  have hCovector : covector difference = 0 := by
    calc
      covector difference = firstCoordinate
          (covector difference • firstBasisVector) := by
        simp [firstCoordinate, firstBasisVector]
      _ = firstCoordinate difference := congrArg firstCoordinate hDifferenceEq.symm
      _ = 0 := hCoordinate
  change difference = 0
  rw [hDifferenceEq, hCovector, zero_smul]

private def normalKernelCorrectionEquiv
    (covector : Vector4 →L[Real] Real)
    (hFirst : covector firstBasisVector = 1) : Vector4 ≃L[Real] Vector4 :=
  (LinearEquiv.ofBijective (normalKernelCorrection covector).toLinearMap
    ⟨normalKernelCorrection_injective covector hFirst,
      LinearMap.surjective_of_injective
        (normalKernelCorrection_injective covector hFirst)⟩).toContinuousLinearEquiv

private theorem normalKernelCorrectionEquiv_apply
    (covector : Vector4 →L[Real] Real)
    (hFirst : covector firstBasisVector = 1) (vector : Vector4) :
    normalKernelCorrectionEquiv covector hFirst vector =
      normalKernelCorrection covector vector :=
  rfl

private theorem normalKernelCorrectionEquiv_first
    (covector : Vector4 →L[Real] Real)
    (hFirst : covector firstBasisVector = 1) :
    normalKernelCorrectionEquiv covector hFirst firstBasisVector = firstBasisVector := by
  rw [normalKernelCorrectionEquiv_apply,
    normalKernelCorrection_first covector hFirst]

private theorem normalKernelCorrectionEquiv_tangential
    (covector : Vector4 →L[Real] Real)
    (hFirst : covector firstBasisVector = 1)
    (index : Fin 4) (hIndex : index ≠ 0) :
    covector (normalKernelCorrectionEquiv covector hFirst (Pi.single index 1)) = 0 := by
  rw [normalKernelCorrectionEquiv_apply,
    normalKernelCorrection_covector covector hFirst]
  simp [firstCoordinate, hIndex]

private theorem continuousLinearEquiv_mfderiv
    (equivalence : Vector4 ≃L[Real] Vector4) (coordinate : Vector4) :
    mfderiv (modelWithCornersSelf Real Vector4)
      (modelWithCornersSelf Real Vector4) equivalence coordinate =
        equivalence.toContinuousLinearMap := by
  rw [mfderiv_eq_fderiv]
  exact equivalence.toContinuousLinearMap.hasFDerivAt.fderiv

/-- A genuine holonomic chart whose zeroth frame vector is the canonical
normal and whose remaining frame vectors lie in the kernel of its metric
normal covector. -/
structure NormalTangentialAdaptedHolonomicChart
    (base : CanonicalLatitudeBase) (normal : Real) where
  coordinateMap : Vector4 → EffectiveQuotient period hPeriod
  isLocalDiffeomorph :
    IsLocalDiffeomorph (modelWithCornersSelf Real Vector4)
      coverModelWithCorners ∞ coordinateMap
  at_zero : coordinateMap 0 =
    quotientNormalLatitude period hPeriod
      (canonicalLatitudeAnchor period hPeriod base) normal
  derivative_normal :
    mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners
      coordinateMap 0 (Pi.single 0 1) =
        canonicalLatitudeNormalVector period hPeriod base normal
  derivative_tangential : ∀ index : Fin 4, index ≠ 0 →
    canonicalLatitudeNormalCovector period hPeriod base normal
      (mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners
        coordinateMap 0 (Pi.single index 1)) = 0

def NormalTangentialAdaptedHolonomicChart.toSmoothHolonomicFrameChart4
    {base : CanonicalLatitudeBase} {normal : Real}
    (chart : NormalTangentialAdaptedHolonomicChart period hPeriod base normal) :
    SmoothHolonomicFrameChart4 period hPeriod :=
  smoothHolonomicFrameChart4OfLocalDiffeomorph period hPeriod
    chart.coordinateMap chart.isLocalDiffeomorph

theorem NormalTangentialAdaptedHolonomicChart.frame_zero_normal
    {base : CanonicalLatitudeBase} {normal : Real}
    (chart : NormalTangentialAdaptedHolonomicChart period hPeriod base normal) :
    (chart.toSmoothHolonomicFrameChart4 period hPeriod).frame 0 0 =
      canonicalLatitudeNormalVector period hPeriod base normal := by
  rw [SmoothHolonomicFrameChart4.frame_eq_coordinateDerivative]
  exact chart.derivative_normal

theorem NormalTangentialAdaptedHolonomicChart.frame_tangential
    {base : CanonicalLatitudeBase} {normal : Real}
    (chart : NormalTangentialAdaptedHolonomicChart period hPeriod base normal)
    (index : Fin 4) (hIndex : index ≠ 0) :
    canonicalLatitudeNormalCovector period hPeriod base normal
      ((chart.toSmoothHolonomicFrameChart4 period hPeriod).frame 0 index) = 0 := by
  rw [SmoothHolonomicFrameChart4.frame_eq_coordinateDerivative]
  exact chart.derivative_tangential index hIndex

/-- Every canonical collar point admits a total holonomic chart with the
complete pointwise normal/tangential frame split. -/
theorem normalTangentialAdaptedHolonomicChart_exists
    (base : CanonicalLatitudeBase) (normal : Real) :
    Nonempty
      (NormalTangentialAdaptedHolonomicChart period hPeriod base normal) := by
  let chart := Classical.choice
    (normalAdaptedHolonomicChart_exists period hPeriod base normal)
  let normalCovector := canonicalLatitudeNormalCovector period hPeriod base normal
  let pulledCovector : Vector4 →L[Real] Real :=
    normalCovector.comp
      (mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners
        chart.coordinateMap 0)
  have hPulledFirst : pulledCovector firstBasisVector = 1 := by
    change normalCovector
      (mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners
        chart.coordinateMap 0 (Pi.single 0 1)) = 1
    rw [chart.derivative_normal]
    exact canonicalLatitudeNormalCovector_apply_normal period hPeriod base normal
  let correction := normalKernelCorrectionEquiv pulledCovector hPulledFirst
  let coordinateMap := chart.coordinateMap ∘ correction
  have hCorrection : IsLocalDiffeomorph
      (modelWithCornersSelf Real Vector4)
      (modelWithCornersSelf Real Vector4) ∞ correction :=
    correction.toDiffeomorph.isLocalDiffeomorph
  have hCoordinateMap : IsLocalDiffeomorph
      (modelWithCornersSelf Real Vector4) coverModelWithCorners ∞ coordinateMap :=
    fun coordinate => IsLocalDiffeomorphAt.comp
      (I := modelWithCornersSelf Real Vector4)
      (J := modelWithCornersSelf Real Vector4)
      (K := coverModelWithCorners)
      (M := Vector4) (N := Vector4)
      (P := EffectiveQuotient period hPeriod) (n := ∞)
      (hCorrection coordinate) (chart.isLocalDiffeomorph (correction coordinate))
  have hChain (index : Fin 4) := mfderiv_comp_apply_of_eq
    (I := modelWithCornersSelf Real Vector4)
    (I' := modelWithCornersSelf Real Vector4)
    (I'' := coverModelWithCorners)
    (f := correction) (g := chart.coordinateMap)
    (x := (0 : Vector4)) (y := (0 : Vector4))
    (chart.isLocalDiffeomorph.mdifferentiable (by simp) 0)
    (hCorrection.mdifferentiable (by simp) 0)
    (map_zero correction) (Pi.single index 1 : Vector4)
  have hCorrectionDerivative (index : Fin 4) :
      mfderiv (modelWithCornersSelf Real Vector4)
          (modelWithCornersSelf Real Vector4) correction 0
            (Pi.single index 1 : Vector4) = correction (Pi.single index 1) := by
    rw [continuousLinearEquiv_mfderiv]
    rfl
  have hCorrectionFirst : correction (Pi.single 0 1 : Vector4) =
      (Pi.single 0 1 : Vector4) := by
    dsimp [correction]
    exact normalKernelCorrectionEquiv_first pulledCovector hPulledFirst
  have hBaseNormal :
      mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners
          chart.coordinateMap 0 (correction (Pi.single 0 1 : Vector4)) =
        canonicalLatitudeNormalVector period hPeriod base normal := by
    rw [hCorrectionFirst]
    exact chart.derivative_normal
  refine ⟨{
    coordinateMap := coordinateMap
    isLocalDiffeomorph := hCoordinateMap
    at_zero := ?_
    derivative_normal := ?_
    derivative_tangential := ?_ }⟩
  · change chart.coordinateMap (correction 0) = _
    rw [map_zero]
    exact chart.at_zero
  · change mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners
      coordinateMap 0 (Pi.single 0 1) = _
    rw [hChain 0, hCorrectionDerivative 0]
    exact hBaseNormal
  · intro index hIndex
    change normalCovector
      (mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners
        coordinateMap 0 (Pi.single index 1)) = 0
    rw [hChain index, hCorrectionDerivative index]
    change pulledCovector (correction (Pi.single index 1)) = 0
    exact normalKernelCorrectionEquiv_tangential
      pulledCovector hPulledFirst index hIndex

end
end P0EFTJanusMappingTorusCanonicalLatitudeNormalTangentialAdaptedHolonomicChart4D
end JanusFormal
