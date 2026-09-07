import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameCovariantTensorDivergence4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusSmoothDiffeomorphismGhostLieBracket4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D

/-! # Smooth Koszul coefficients in a redundant finite generating family

The bracket coefficients use the reconstructed dual of a fixed reference.
The independent metric supplies its genuine Levi--Civita connection and musical
inverse. No inverse of the redundant Gram matrix is used.
-/

namespace JanusFormal
namespace P0EFTJanusFiniteFrameKoszulCoefficients4D

set_option autoImplicit false

noncomputable section
open scoped Manifold ContDiff BigOperators Matrix Matrix.Norms.Frobenius
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusSmoothDiffeomorphismGhostLieBracket4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusProgramPGeneralMetricPositiveDualizer4D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusFiniteFrameMetricContraction4D
open P0EFTJanusFiniteFrameCovariantTensorDivergence4D
open P0EFTJanusRegularFrameMetricTensorTrace4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev Vector4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4
local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

private abbrev TangentFiber (point : EffectiveQuotient period hPeriod) :=
  TangentSpace coverModelWithCorners point

/-- The genuine bracket of two smooth generators, with its canonical redundant coefficients. -/
def finiteFrameStructureCoefficient
    (frame : SmoothD8Frame period hPeriod)
    (reference : SmoothGeneralLorentzMetric period hPeriod)
    (first second upper : Fin frame.count) : SmoothScalarField period hPeriod :=
  generalMetricFiniteFrameCoefficient period hPeriod frame reference
    (smoothGhostLieBracket period hPeriod
      (smoothFrameVectorSection period hPeriod frame first)
      (smoothFrameVectorSection period hPeriod frame second)) upper

@[simp] theorem finiteFrameStructureCoefficient_apply
    (frame : SmoothD8Frame period hPeriod)
    (reference : SmoothGeneralLorentzMetric period hPeriod)
    (first second upper : Fin frame.count) (point : EffectiveQuotient period hPeriod) :
    finiteFrameStructureCoefficient period hPeriod frame reference first second upper point =
      generalMetricFiniteFrameCoefficientAt period hPeriod frame reference point upper
        (smoothGhostLieBracket period hPeriod
          (smoothFrameVectorSection period hPeriod frame first)
          (smoothFrameVectorSection period hPeriod frame second) point) := rfl

theorem finiteFrameStructureCoefficient_reconstructs
    (frame : SmoothD8Frame period hPeriod)
    (reference : SmoothGeneralLorentzMetric period hPeriod)
    (first second : Fin frame.count) (point : EffectiveQuotient period hPeriod) :
    smoothGhostLieBracket period hPeriod
        (smoothFrameVectorSection period hPeriod frame first)
        (smoothFrameVectorSection period hPeriod frame second) point =
      ∑ upper : Fin frame.count,
        finiteFrameStructureCoefficient period hPeriod frame reference first second upper point •
          frame.vectorAt point upper :=
  generalMetricFiniteFrame_reconstructs period hPeriod frame reference _ point

private theorem coordinateDerivative_isInvertible
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : Vector4) :
    (mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners
      patch.coordinateMap coordinate).IsInvertible :=
  ⟨patch.coordinateMap_isLocalDiffeomorph.mfderivToContinuousLinearEquiv (by simp) coordinate, rfl⟩

theorem coordinateMap_mfderiv_lieBracket_finiteFramePulledVector
    (frame : SmoothD8Frame period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : Vector4)
    (first second : Fin frame.count) :
    mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners patch.coordinateMap coordinate
        (VectorField.lieBracket (E := Vector4) Real (finiteFramePulledVector period hPeriod frame patch first)
          (finiteFramePulledVector period hPeriod frame patch second) coordinate) =
      smoothGhostLieBracket period hPeriod
        (smoothFrameVectorSection period hPeriod frame first)
        (smoothFrameVectorSection period hPeriod frame second) (patch.coordinateMap coordinate) := by
  let firstField := smoothFrameVectorSection period hPeriod frame first
  let secondField := smoothFrameVectorSection period hPeriod frame second
  have hNatural := VectorField.mpullback_mlieBracket
    (x₀ := coordinate) (f := patch.coordinateMap)
    (V := fun point => firstField point) (W := fun point => secondField point)
    (firstField.contMDiff.mdifferentiableAt (by simp))
    (secondField.contMDiff.mdifferentiableAt (by simp))
    patch.coordinateMap_contMDiff.contMDiffAt (by
      rw [minSmoothness_of_isRCLikeNormedField]
      exact WithTop.coe_le_coe.mpr le_top)
  have hEuclidean : VectorField.mlieBracket (modelWithCornersSelf Real Vector4)
      (finiteFramePulledVector period hPeriod frame patch first)
      (finiteFramePulledVector period hPeriod frame patch second) coordinate =
      VectorField.lieBracket (E := Vector4) Real (finiteFramePulledVector period hPeriod frame patch first)
        (finiteFramePulledVector period hPeriod frame patch second) coordinate := by
    rw [← VectorField.mlieBracketWithin_univ,
      VectorField.mlieBracketWithin_eq_lieBracketWithin, VectorField.lieBracketWithin_univ]
  have hApplied := congrArg
    (fun vector : Vector4 => mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners
      patch.coordinateMap coordinate vector) hNatural
  rw [VectorField.mpullback_apply,
    (coordinateDerivative_isInvertible period hPeriod patch coordinate).self_apply_inverse] at hApplied
  dsimp [firstField, secondField, smoothFrameVectorSection] at hApplied
  dsimp [finiteFramePulledVector] at hEuclidean
  rw [hEuclidean] at hApplied
  simpa only [finiteFramePulledVector, smoothGhostLieBracket_apply, smoothFrameVectorSection,
    ContMDiffSection.coeFn_mk] using
    hApplied.symm

theorem finiteFrameLocalLieBracket_eq_sum
    (frame : SmoothD8Frame period hPeriod)
    (reference : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : Vector4)
    (first second : Fin frame.count) :
    VectorField.lieBracket (E := Vector4) Real (finiteFramePulledVector period hPeriod frame patch first)
        (finiteFramePulledVector period hPeriod frame patch second) coordinate =
      ∑ upper : Fin frame.count,
        finiteFrameStructureCoefficient period hPeriod frame reference first second upper
            (patch.coordinateMap coordinate) •
          finiteFramePulledVector period hPeriod frame patch upper coordinate := by
  let e := (Pi.basisFun Real (Fin 4)).equiv (patch.frame coordinate) (Equiv.refl (Fin 4))
  have hVector (upper : Fin frame.count) :
      e (finiteFramePulledVector period hPeriod frame patch upper coordinate) =
        frame.vectorAt (patch.coordinateMap coordinate) upper :=
    (coordinateMap_mfderiv_eq_frameEquiv period hPeriod patch coordinate _).symm.trans
      (coordinateMap_mfderiv_finiteFramePulledVector period hPeriod frame patch coordinate upper)
  have hBracket :
      e (VectorField.lieBracket (E := Vector4) Real
        (finiteFramePulledVector period hPeriod frame patch first)
        (finiteFramePulledVector period hPeriod frame patch second) coordinate) =
      smoothGhostLieBracket period hPeriod
        (smoothFrameVectorSection period hPeriod frame first)
        (smoothFrameVectorSection period hPeriod frame second) (patch.coordinateMap coordinate) :=
    (coordinateMap_mfderiv_eq_frameEquiv period hPeriod patch coordinate _).symm.trans
      (coordinateMap_mfderiv_lieBracket_finiteFramePulledVector period hPeriod frame patch coordinate first second)
  apply e.injective
  rw [map_sum]
  simp_rw [map_smul, hVector]
  exact hBracket.trans
    (finiteFrameStructureCoefficient_reconstructs period hPeriod frame reference first second _)

private theorem metricForm_frame
    (frame : SmoothD8Frame period hPeriod) (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : Vector4)
    (first second : Fin frame.count) :
    localMetricCoordinateForm period hPeriod metric patch coordinate
        (finiteFramePulledVector period hPeriod frame patch first coordinate)
        (finiteFramePulledVector period hPeriod frame patch second coordinate) =
      generalMetricFrameCoefficient period hPeriod frame metric.tensor first second
        (patch.coordinateMap coordinate) := by
  rw [localMetricCoordinateForm_apply, coordinateMap_mfderiv_finiteFramePulledVector,
    coordinateMap_mfderiv_finiteFramePulledVector]
  rfl

private theorem metricForm_symmetric
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate first second : Vector4) :
    localMetricCoordinateForm period hPeriod metric patch coordinate first second =
      localMetricCoordinateForm period hPeriod metric patch coordinate second first := by
  rw [localMetricCoordinateForm_apply, localMetricCoordinateForm_apply]
  exact metric.tensor.symmetric _ _ _

theorem finiteFrameLocalCovariantDerivative_metricCompatible
    (frame : SmoothD8Frame period hPeriod) (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : Vector4)
    (derivative first second : Fin frame.count) :
    frameDerivative period hPeriod Real frame
        (generalMetricFrameCoefficient period hPeriod frame metric.tensor first second)
        (patch.coordinateMap coordinate) derivative =
      localMetricCoordinateForm period hPeriod metric patch coordinate
          (finiteFrameLocalCovariantDerivativeVector period hPeriod frame metric patch coordinate
            derivative first) (finiteFramePulledVector period hPeriod frame patch second coordinate) +
        localMetricCoordinateForm period hPeriod metric patch coordinate
          (finiteFramePulledVector period hPeriod frame patch first coordinate)
          (finiteFrameLocalCovariantDerivativeVector period hPeriod frame metric patch coordinate
            derivative second) := by
  have hProduct := fderiv_matrix_toBilin_dynamic_apply
    (localMetricMatrix period hPeriod metric patch)
    (finiteFramePulledVector period hPeriod frame patch first)
    (finiteFramePulledVector period hPeriod frame patch second) coordinate
    (finiteFramePulledVector period hPeriod frame patch derivative coordinate)
    ((localMetricMatrix_contDiff period hPeriod metric patch).differentiable (by simp) coordinate)
    ((finiteFramePulledVector_contDiff period hPeriod frame patch first).differentiable (by simp) coordinate)
    ((finiteFramePulledVector_contDiff period hPeriod frame patch second).differentiable (by simp) coordinate)
  change fderiv Real (fun current => localMetricCoordinateForm period hPeriod metric patch current
      (finiteFramePulledVector period hPeriod frame patch first current)
      (finiteFramePulledVector period hPeriod frame patch second current)) coordinate
      (finiteFramePulledVector period hPeriod frame patch derivative coordinate) = _ at hProduct
  have hFunction : (fun current => localMetricCoordinateForm period hPeriod metric patch current
      (finiteFramePulledVector period hPeriod frame patch first current)
      (finiteFramePulledVector period hPeriod frame patch second current)) =
      (generalMetricFrameCoefficient period hPeriod frame metric.tensor first second).toFun ∘
        patch.coordinateMap := by
    funext current
    exact metricForm_frame period hPeriod frame metric patch current first second
  rw [hFunction, fderiv_comp_coordinateMap_finiteFramePulledVector] at hProduct
  have hCompatibility := congrArg
    (fun form => form (finiteFramePulledVector period hPeriod frame patch derivative coordinate)
      (finiteFramePulledVector period hPeriod frame patch first coordinate)
      (finiteFramePulledVector period hPeriod frame patch second coordinate))
    (localMetricDerivativeTrilinearForm_eq_leviCivita period hPeriod metric patch coordinate)
  change localMetricDerivativeTrilinearForm period hPeriod metric patch coordinate
      (finiteFramePulledVector period hPeriod frame patch derivative coordinate)
      (finiteFramePulledVector period hPeriod frame patch first coordinate)
      (finiteFramePulledVector period hPeriod frame patch second coordinate) = _ at hCompatibility
  rw [hProduct]
  change localMetricCoordinateForm period hPeriod metric patch coordinate
      (fderiv Real (finiteFramePulledVector period hPeriod frame patch first) coordinate
        (finiteFramePulledVector period hPeriod frame patch derivative coordinate))
      (finiteFramePulledVector period hPeriod frame patch second coordinate) +
    localMetricDerivativeTrilinearForm period hPeriod metric patch coordinate
      (finiteFramePulledVector period hPeriod frame patch derivative coordinate)
      (finiteFramePulledVector period hPeriod frame patch first coordinate)
      (finiteFramePulledVector period hPeriod frame patch second coordinate) +
    localMetricCoordinateForm period hPeriod metric patch coordinate
      (finiteFramePulledVector period hPeriod frame patch first coordinate)
      (fderiv Real (finiteFramePulledVector period hPeriod frame patch second) coordinate
        (finiteFramePulledVector period hPeriod frame patch derivative coordinate)) = _
  rw [hCompatibility]
  simp only [localLeviCivitaMetricCompatibilityForm_apply,
    localLeviCivitaChristoffelBilinearMap_apply, finiteFrameLocalCovariantDerivativeVector,
    map_add, LinearMap.add_apply]
  abel

theorem finiteFrameLocalCovariantDerivative_torsion
    (frame : SmoothD8Frame period hPeriod) (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : Vector4)
    (first second : Fin frame.count) :
    finiteFrameLocalCovariantDerivativeVector period hPeriod frame metric patch coordinate first second -
        finiteFrameLocalCovariantDerivativeVector period hPeriod frame metric patch coordinate second first =
      VectorField.lieBracket Real (finiteFramePulledVector period hPeriod frame patch first)
        (finiteFramePulledVector period hPeriod frame patch second) coordinate := by
  unfold finiteFrameLocalCovariantDerivativeVector VectorField.lieBracket
  rw [localLeviCivitaChristoffelApply_symmetric period hPeriod metric patch coordinate
    (finiteFramePulledVector period hPeriod frame patch second coordinate)
    (finiteFramePulledVector period hPeriod frame patch first coordinate)]
  abel

private def finiteFrameBracketMetricCoefficient
    (frame : SmoothD8Frame period hPeriod) (reference metric : SmoothGeneralLorentzMetric period hPeriod)
    (row first second : Fin frame.count) : SmoothScalarField period hPeriod where
  toFun point := ∑ upper : Fin frame.count,
    finiteFrameStructureCoefficient period hPeriod frame reference first second upper point *
      generalMetricFrameCoefficient period hPeriod frame metric.tensor row upper point
  contMDiff_toFun := ContMDiff.sum fun upper _ =>
    (finiteFrameStructureCoefficient period hPeriod frame reference first second upper).contMDiff_toFun.mul
      (generalMetricFrameCoefficient period hPeriod frame metric.tensor row upper).contMDiff_toFun

private theorem finiteFrameBracketMetricCoefficient_eq_local
    (frame : SmoothD8Frame period hPeriod) (reference metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : Vector4)
    (row first second : Fin frame.count) :
    finiteFrameBracketMetricCoefficient period hPeriod frame reference metric row first second
        (patch.coordinateMap coordinate) =
      localMetricCoordinateForm period hPeriod metric patch coordinate
        (finiteFramePulledVector period hPeriod frame patch row coordinate)
        (VectorField.lieBracket Real (finiteFramePulledVector period hPeriod frame patch first)
          (finiteFramePulledVector period hPeriod frame patch second) coordinate) := by
  rw [finiteFrameLocalLieBracket_eq_sum period hPeriod frame reference patch coordinate]
  rw [map_sum]
  change (∑ upper : Fin frame.count,
    finiteFrameStructureCoefficient period hPeriod frame reference first second upper
        (patch.coordinateMap coordinate) *
      generalMetricFrameCoefficient period hPeriod frame metric.tensor row upper
        (patch.coordinateMap coordinate)) = _
  apply Finset.sum_congr rfl
  intro upper _
  rw [map_smul, metricForm_frame]
  rfl

/-- Smooth lower Koszul expression; the bracket terms retain nonholonomicity. -/
def finiteFrameKoszulLowerCoefficient
    (frame : SmoothD8Frame period hPeriod) (reference metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second lower : Fin frame.count) : SmoothScalarField period hPeriod :=
  (1 / 2 : Real) •
    (frameDerivativeComponentField period hPeriod frame
        (generalMetricFrameCoefficient period hPeriod frame metric.tensor second lower) first +
      frameDerivativeComponentField period hPeriod frame
        (generalMetricFrameCoefficient period hPeriod frame metric.tensor first lower) second -
      frameDerivativeComponentField period hPeriod frame
        (generalMetricFrameCoefficient period hPeriod frame metric.tensor first second) lower -
      finiteFrameBracketMetricCoefficient period hPeriod frame reference metric first second lower +
      finiteFrameBracketMetricCoefficient period hPeriod frame reference metric second lower first +
      finiteFrameBracketMetricCoefficient period hPeriod frame reference metric lower first second)

@[simp] theorem finiteFrameKoszulLowerCoefficient_apply
    (frame : SmoothD8Frame period hPeriod) (reference metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second lower : Fin frame.count) (point : EffectiveQuotient period hPeriod) :
    finiteFrameKoszulLowerCoefficient period hPeriod frame reference metric first second lower point =
      (1 / 2 : Real) *
        (frameDerivative period hPeriod Real frame
            (generalMetricFrameCoefficient period hPeriod frame metric.tensor second lower) point first +
          frameDerivative period hPeriod Real frame
            (generalMetricFrameCoefficient period hPeriod frame metric.tensor first lower) point second -
          frameDerivative period hPeriod Real frame
            (generalMetricFrameCoefficient period hPeriod frame metric.tensor first second) point lower -
          (∑ upper : Fin frame.count,
            finiteFrameStructureCoefficient period hPeriod frame reference second lower upper point *
              generalMetricFrameCoefficient period hPeriod frame metric.tensor first upper point) +
          (∑ upper : Fin frame.count,
            finiteFrameStructureCoefficient period hPeriod frame reference lower first upper point *
              generalMetricFrameCoefficient period hPeriod frame metric.tensor second upper point) +
          ∑ upper : Fin frame.count,
            finiteFrameStructureCoefficient period hPeriod frame reference first second upper point *
              generalMetricFrameCoefficient period hPeriod frame metric.tensor lower upper point) := rfl

theorem finiteFrameKoszulLowerCoefficient_eq_local
    (frame : SmoothD8Frame period hPeriod) (reference metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : Vector4)
    (first second lower : Fin frame.count) :
    finiteFrameKoszulLowerCoefficient period hPeriod frame reference metric first second lower
        (patch.coordinateMap coordinate) =
      localMetricCoordinateForm period hPeriod metric patch coordinate
        (finiteFrameLocalCovariantDerivativeVector period hPeriod frame metric patch coordinate first second)
        (finiteFramePulledVector period hPeriod frame patch lower coordinate) := by
  change (1 / 2 : Real) *
      (frameDerivative period hPeriod Real frame
          (generalMetricFrameCoefficient period hPeriod frame metric.tensor second lower)
          (patch.coordinateMap coordinate) first +
        frameDerivative period hPeriod Real frame
          (generalMetricFrameCoefficient period hPeriod frame metric.tensor first lower)
          (patch.coordinateMap coordinate) second -
        frameDerivative period hPeriod Real frame
          (generalMetricFrameCoefficient period hPeriod frame metric.tensor first second)
          (patch.coordinateMap coordinate) lower -
        finiteFrameBracketMetricCoefficient period hPeriod frame reference metric first second lower
          (patch.coordinateMap coordinate) +
        finiteFrameBracketMetricCoefficient period hPeriod frame reference metric second lower first
          (patch.coordinateMap coordinate) +
        finiteFrameBracketMetricCoefficient period hPeriod frame reference metric lower first second
          (patch.coordinateMap coordinate)) = _
  rw [finiteFrameBracketMetricCoefficient_eq_local,
    finiteFrameBracketMetricCoefficient_eq_local, finiteFrameBracketMetricCoefficient_eq_local,
    finiteFrameLocalCovariantDerivative_metricCompatible,
    finiteFrameLocalCovariantDerivative_metricCompatible,
    finiteFrameLocalCovariantDerivative_metricCompatible,
    ← finiteFrameLocalCovariantDerivative_torsion period hPeriod frame metric patch coordinate second lower,
    ← finiteFrameLocalCovariantDerivative_torsion period hPeriod frame metric patch coordinate lower first,
    ← finiteFrameLocalCovariantDerivative_torsion period hPeriod frame metric patch coordinate first second]
  simp only [map_sub]
  rw [metricForm_symmetric period hPeriod metric patch coordinate
      (finiteFrameLocalCovariantDerivativeVector period hPeriod frame metric patch coordinate lower first)
      (finiteFramePulledVector period hPeriod frame patch second coordinate),
    metricForm_symmetric period hPeriod metric patch coordinate
      (finiteFrameLocalCovariantDerivativeVector period hPeriod frame metric patch coordinate second first)
      (finiteFramePulledVector period hPeriod frame patch lower coordinate),
    metricForm_symmetric period hPeriod metric patch coordinate
      (finiteFramePulledVector period hPeriod frame patch lower coordinate)
      (finiteFrameLocalCovariantDerivativeVector period hPeriod frame metric patch coordinate first second)]
  ring

/-- Raising the lower coefficient uses the true musical inverse on the reconstructed dual. -/
def finiteFrameKoszulChristoffelCoefficient
    (frame : SmoothD8Frame period hPeriod) (reference metric : SmoothGeneralLorentzMetric period hPeriod)
    (upper first second : Fin frame.count) : SmoothScalarField period hPeriod where
  toFun point := ∑ lower : Fin frame.count,
    finiteFrameInverseMetricCoefficient period hPeriod frame reference metric upper lower point *
      finiteFrameKoszulLowerCoefficient period hPeriod frame reference metric first second lower point
  contMDiff_toFun := ContMDiff.sum fun lower _ =>
    (finiteFrameInverseMetricCoefficient period hPeriod frame reference metric upper lower).contMDiff_toFun.mul
      (finiteFrameKoszulLowerCoefficient period hPeriod frame reference metric first second lower).contMDiff_toFun

@[simp] theorem finiteFrameKoszulChristoffelCoefficient_apply
    (frame : SmoothD8Frame period hPeriod) (reference metric : SmoothGeneralLorentzMetric period hPeriod)
    (upper first second : Fin frame.count) (point : EffectiveQuotient period hPeriod) :
    finiteFrameKoszulChristoffelCoefficient period hPeriod frame reference metric upper first second point =
      ∑ lower : Fin frame.count,
        finiteFrameInverseMetricCoefficient period hPeriod frame reference metric upper lower point *
          finiteFrameKoszulLowerCoefficient period hPeriod frame reference metric first second lower point := rfl

private theorem finiteFrameCoefficientAt_eq_raised_metric
    (frame : SmoothD8Frame period hPeriod) (reference metric : SmoothGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod) (upper : Fin frame.count)
    (vector : TangentFiber period hPeriod point) :
    generalMetricFiniteFrameCoefficientAt period hPeriod frame reference point upper vector =
      ∑ lower : Fin frame.count,
        finiteFrameInverseMetricCoefficient period hPeriod frame reference metric upper lower point *
          metric.tensor.tensor point vector (frame.vectorAt point lower) := by
  have h := congrArg
    (fun covector : TangentFiber period hPeriod point →L[Real] Real =>
      generalMetricFiniteFrameCoefficientAt period hPeriod frame reference point upper
        (inverseMetricSharp period hPeriod metric point covector))
    (finiteFrameCovector_reconstructs period hPeriod frame reference point (metric.musical point vector))
  rw [inverseMetricSharp_metric_flat] at h
  simp only [map_sum, map_smul, smul_eq_mul] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro lower _
  have hFlat : (metric.musical point vector) (frame.vectorAt point lower) =
      metric.tensor.tensor point vector (frame.vectorAt point lower) := by
    change ((metric.musical point).toContinuousLinearMap vector) (frame.vectorAt point lower) = _
    rw [metric.musical_eq_tensor point]
  rw [finiteFrameInverseMetricCoefficient_apply, hFlat]
  exact mul_comm _ _

/-- The explicit smooth Koszul coefficients are precisely the coefficients of
the actual local Levi--Civita connection used by the intrinsic divergence. -/
theorem finiteFrameKoszulChristoffelCoefficient_eq_local
    (frame : SmoothD8Frame period hPeriod) (reference metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : Vector4)
    (upper first second : Fin frame.count) :
    finiteFrameKoszulChristoffelCoefficient period hPeriod frame reference metric upper first second
        (patch.coordinateMap coordinate) =
      finiteFrameTensorChristoffelCoefficient period hPeriod frame reference metric patch coordinate
        upper first second := by
  unfold finiteFrameTensorChristoffelCoefficient
  rw [finiteFrameCoefficientAt_eq_raised_metric, finiteFrameKoszulChristoffelCoefficient_apply]
  apply Finset.sum_congr rfl
  intro lower _
  rw [finiteFrameKoszulLowerCoefficient_eq_local, localMetricCoordinateForm_apply,
    coordinateMap_mfderiv_finiteFramePulledVector]

end
end P0EFTJanusFiniteFrameKoszulCoefficients4D
end JanusFormal
