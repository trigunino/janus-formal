import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGlobalGeneralMetricAbelianLorenzCodifferential4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameKoszulCoefficients4D

/-! # Intrinsic Lorenz trace in a redundant finite generating family

The potential coefficients and their connection correction are genuine smooth
geometric quantities. Reconstruction computes the trace with the inverse-metric
dual coefficients, without choosing a global tangent basis.
-/

namespace JanusFormal
namespace P0EFTJanusFiniteFrameLorenzCovariantTrace4D

set_option autoImplicit false

noncomputable section
open scoped Manifold ContDiff Matrix Matrix.Norms.Frobenius BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D
open P0EFTJanusMappingTorusCanonicalTotalR4BallParametrization4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusLocalAbelianLorenzCodifferential4D
open P0EFTJanusMappingTorusAbelianLorenzCodifferentialTransition4D
open P0EFTJanusMappingTorusGlobalGeneralMetricAbelianLorenzCodifferential4D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusFiniteFrameMetricContraction4D
open P0EFTJanusFiniteFrameMetricTensorTrace4D
open P0EFTJanusFiniteFrameCovariantTensorDivergence4D
open P0EFTJanusFiniteFrameKoszulCoefficients4D

private abbrev Vector4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4
variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance (point : EffectiveQuotient period hPeriod) :
    FiniteDimensional Real (TangentSpace coverModelWithCorners point) := by
  change FiniteDimensional Real CoverCoordinates
  infer_instance

private abbrev TangentFiber (point : EffectiveQuotient period hPeriod) :=
  TangentSpace coverModelWithCorners point

/-- The actual smooth coefficient `A_component(e_index)`. -/
def finiteFramePotentialCoefficient
    (frame : SmoothD8Frame period hPeriod) (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2) (index : Fin frame.count) : SmoothScalarField period hPeriod where
  toFun := fun point => potential.toFun component point (frame.vectorAt point index)
  contMDiff_toFun := (potential.contMDiff_eval component).comp (frame.contMDiff_vector index)

@[simp] theorem finiteFramePotentialCoefficient_apply
    (frame : SmoothD8Frame period hPeriod) (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2) (index : Fin frame.count) (point : EffectiveQuotient period hPeriod) :
    finiteFramePotentialCoefficient period hPeriod frame potential component index point =
      potential.toFun component point (frame.vectorAt point index) := rfl

private theorem endomorphism_trace_eq_finiteFrameMetricPairing
    (frame : SmoothD8Frame period hPeriod) (reference metric : SmoothGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (operator : TangentFiber period hPeriod point →ₗ[Real] TangentFiber period hPeriod point) :
    LinearMap.trace Real (TangentFiber period hPeriod point) operator =
      ∑ first : Fin frame.count, ∑ second : Fin frame.count,
        finiteFrameInverseMetricCoefficient period hPeriod frame reference metric first second point *
          metric.tensor.tensor point (operator (frame.vectorAt point first)) (frame.vectorAt point second) := by
  refine (finiteFrame_endomorphism_trace period hPeriod frame reference point operator).trans ?_
  apply Finset.sum_congr rfl
  intro first _
  have hCovector := congrArg
    (fun value : TangentFiber period hPeriod point →L[Real] Real =>
      generalMetricFiniteFrameCoefficientAt period hPeriod frame reference point first
        (inverseMetricSharp period hPeriod metric point value))
    (finiteFrameCovector_reconstructs period hPeriod frame reference point
      (metric.tensor.tensor point (operator (frame.vectorAt point first))))
  simp only [map_sum, map_smul, smul_eq_mul] at hCovector
  have hFlat : inverseMetricSharp period hPeriod metric point
      (metric.tensor.tensor point (operator (frame.vectorAt point first))) =
      operator (frame.vectorAt point first) := by
    rw [← metric.musical_eq_tensor]
    exact inverseMetricSharp_metric_flat period hPeriod metric point _
  refine (congrArg (generalMetricFiniteFrameCoefficientAt period hPeriod frame reference point first)
    hFlat.symm).trans (hCovector.trans ?_)
  apply Finset.sum_congr rfl
  intro second _
  rw [finiteFrameInverseMetricCoefficient_apply]
  exact mul_comm _ _

private theorem localMetricCoordinateForm_raised_frame
    (frame : SmoothD8Frame period hPeriod) (metric : SmoothGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod) (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : Vector4) (index : Fin frame.count) :
    localMetricCoordinateForm period hPeriod metric patch coordinate
      (localRaisedAbelianGaugePotential period hPeriod metric potential component patch coordinate)
      (finiteFramePulledVector period hPeriod frame patch index coordinate) =
    finiteFramePotentialCoefficient period hPeriod frame potential component index (patch.coordinateMap coordinate) := by
  rw [localMetricCoordinateForm_apply, coordinateMap_mfderiv_localRaisedAbelianGaugePotential,
    coordinateMap_mfderiv_finiteFramePulledVector, ← metric.musical_eq_tensor]
  exact congrArg (fun covector : TangentFiber period hPeriod (patch.coordinateMap coordinate) →L[Real] Real =>
    covector (frame.vectorAt (patch.coordinateMap coordinate) index))
    (metric_flat_inverseMetricSharp period hPeriod metric (patch.coordinateMap coordinate)
      (potential.toFun component (patch.coordinateMap coordinate)))

/-- Metric compatibility gives the actual coefficient derivative and connection correction. -/
theorem finiteFrameLorenz_covariantPairing_eq_coefficientDerivative
    (frame : SmoothD8Frame period hPeriod) (reference metric : SmoothGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod) (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : Vector4) (first second : Fin frame.count) :
    localMetricCoordinateForm period hPeriod metric patch coordinate
      (localAbelianLorenzCovariantDerivative period hPeriod metric potential component patch coordinate
        (finiteFramePulledVector period hPeriod frame patch first coordinate))
      (finiteFramePulledVector period hPeriod frame patch second coordinate) =
    frameDerivative period hPeriod Real frame
      (finiteFramePotentialCoefficient period hPeriod frame potential component second) (patch.coordinateMap coordinate) first -
      ∑ index : Fin frame.count,
        finiteFrameTensorChristoffelCoefficient period hPeriod frame reference metric patch coordinate index first second *
          finiteFramePotentialCoefficient period hPeriod frame potential component index (patch.coordinateMap coordinate) := by
  let raised := localRaisedAbelianGaugePotential period hPeriod metric potential component patch
  let vector := finiteFramePulledVector period hPeriod frame patch second
  let direction := finiteFramePulledVector period hPeriod frame patch first coordinate
  let form := localMetricCoordinateForm period hPeriod metric patch coordinate
  let connection := finiteFrameLocalCovariantDerivativeVector period hPeriod frame metric patch coordinate first second
  have hProduct : fderiv Real (fun current => localMetricCoordinateForm period hPeriod metric patch current
      (raised current) (vector current)) coordinate direction =
      form (fderiv Real raised coordinate direction) (vector coordinate) +
        localMetricDerivativeTrilinearForm period hPeriod metric patch coordinate direction (raised coordinate) (vector coordinate) +
        form (raised coordinate) (fderiv Real vector coordinate direction) := by
    simpa only [form, localMetricCoordinateForm, localMetricDerivativeTrilinearForm_apply] using
      fderiv_matrix_toBilin_dynamic_apply (localMetricMatrix period hPeriod metric patch) raised vector coordinate direction
        ((localMetricMatrix_contDiff period hPeriod metric patch).differentiable (by simp) coordinate)
        ((localRaisedAbelianGaugePotential_contDiff period hPeriod metric potential component patch).differentiable
          (by simp) coordinate)
        ((finiteFramePulledVector_contDiff period hPeriod frame patch second).differentiable (by simp) coordinate)
  have hFunction : (fun current => localMetricCoordinateForm period hPeriod metric patch current
      (raised current) (vector current)) =
      (finiteFramePotentialCoefficient period hPeriod frame potential component second).toFun ∘ patch.coordinateMap := by
    funext current
    exact localMetricCoordinateForm_raised_frame period hPeriod frame metric potential component patch current second
  rw [hFunction, fderiv_comp_coordinateMap_finiteFramePulledVector,
    localMetricDerivativeTrilinearForm_eq_leviCivita] at hProduct
  simp only [localLeviCivitaMetricCompatibilityForm_apply] at hProduct
  have hConnection : form (raised coordinate) connection = ∑ index : Fin frame.count,
      finiteFrameTensorChristoffelCoefficient period hPeriod frame reference metric patch coordinate index first second *
        finiteFramePotentialCoefficient period hPeriod frame potential component index (patch.coordinateMap coordinate) := by
    rw [show connection = _ from finiteFrameLocalCovariantDerivativeVector_reconstructs
      period hPeriod frame reference metric patch coordinate first second]
    simp only [map_sum, map_smul, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro index _
    exact congrArg (fun value : Real =>
      finiteFrameTensorChristoffelCoefficient period hPeriod frame reference metric patch coordinate index first second * value)
      (localMetricCoordinateForm_raised_frame period hPeriod frame metric potential component patch coordinate index)
  rw [← hConnection]
  change form (fderiv Real raised coordinate direction +
    localLeviCivitaChristoffelBilinearMap period hPeriod metric patch coordinate direction (raised coordinate))
      (vector coordinate) = _
  have hConnectionExpand : form (raised coordinate) connection =
      form (raised coordinate) (fderiv Real vector coordinate direction) +
        form (raised coordinate)
          (localLeviCivitaChristoffelBilinearMap period hPeriod metric patch coordinate direction (vector coordinate)) :=
    map_add (form (raised coordinate)) _ _
  rw [hConnectionExpand, map_add, LinearMap.add_apply]
  dsimp only [form, raised, vector, direction] at hProduct ⊢
  linarith [hProduct]

/-- The intrinsic Lorenz value in any holonomic chart, using the genuine local connection. -/
theorem globalGeneralMetricAbelianLorenzCodifferential_eq_finiteFrameCovariantTrace_local
    (frame : SmoothD8Frame period hPeriod) (reference metric : SmoothGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod) (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : Vector4) :
    globalGeneralMetricAbelianLorenzCodifferential period hPeriod metric potential (patch.coordinateMap coordinate) component =
      ∑ first : Fin frame.count, ∑ second : Fin frame.count,
        finiteFrameInverseMetricCoefficient period hPeriod frame reference metric first second (patch.coordinateMap coordinate) *
          (frameDerivative period hPeriod Real frame
            (finiteFramePotentialCoefficient period hPeriod frame potential component second) (patch.coordinateMap coordinate) first -
            ∑ index : Fin frame.count,
              finiteFrameTensorChristoffelCoefficient period hPeriod frame reference metric patch coordinate index first second *
                finiteFramePotentialCoefficient period hPeriod frame potential component index (patch.coordinateMap coordinate)) := by
  let e := (Pi.basisFun Real (Fin 4)).equiv (patch.frame coordinate) (Equiv.refl (Fin 4))
  let operator := localAbelianLorenzCovariantDerivative period hPeriod metric potential component patch coordinate
  have hPush (index : Fin frame.count) : e (finiteFramePulledVector period hPeriod frame patch index coordinate) =
      frame.vectorAt (patch.coordinateMap coordinate) index :=
    (coordinateMap_mfderiv_eq_frameEquiv period hPeriod patch coordinate _).symm.trans
      (coordinateMap_mfderiv_finiteFramePulledVector period hPeriod frame patch coordinate index)
  have hPull (index : Fin frame.count) : e.symm (frame.vectorAt (patch.coordinateMap coordinate) index) =
      finiteFramePulledVector period hPeriod frame patch index coordinate := by
    apply e.injective
    exact (e.apply_symm_apply _).trans (hPush index).symm
  have hForm (first second : Vector4) :
      metric.tensor.tensor (patch.coordinateMap coordinate) (e first) (e second) =
        localMetricCoordinateForm period hPeriod metric patch coordinate first second := by
    rw [localMetricCoordinateForm_apply, coordinateMap_mfderiv_eq_frameEquiv, coordinateMap_mfderiv_eq_frameEquiv]
  have hPairing (first second : Fin frame.count) :
      metric.tensor.tensor (patch.coordinateMap coordinate)
        (e.conj operator (frame.vectorAt (patch.coordinateMap coordinate) first))
        (frame.vectorAt (patch.coordinateMap coordinate) second) =
      localMetricCoordinateForm period hPeriod metric patch coordinate
        (operator (finiteFramePulledVector period hPeriod frame patch first coordinate))
        (finiteFramePulledVector period hPeriod frame patch second coordinate) := by
    change metric.tensor.tensor (patch.coordinateMap coordinate)
      (e (operator (e.symm (frame.vectorAt (patch.coordinateMap coordinate) first))))
      (frame.vectorAt (patch.coordinateMap coordinate) second) = _
    rw [hPull, ← hPush second]
    exact hForm _ _
  rw [globalGeneralMetricAbelianLorenzCodifferential_apply, globalGeneralMetricAbelianLorenzValue_eq_local,
    localAbelianLorenzDivergence_eq_trace]
  refine (LinearMap.trace_conj' operator e).symm.trans
    ((endomorphism_trace_eq_finiteFrameMetricPairing period hPeriod frame reference metric
      (patch.coordinateMap coordinate) (e.conj operator)).trans ?_)
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  apply congrArg (fun value : Real =>
    finiteFrameInverseMetricCoefficient period hPeriod frame reference metric first second (patch.coordinateMap coordinate) * value)
  exact (hPairing first second).trans (finiteFrameLorenz_covariantPairing_eq_coefficientDerivative
    period hPeriod frame reference metric potential component patch coordinate first second)

/-- Global agreement, with the smooth Koszul coefficients of the same metric. -/
theorem globalGeneralMetricAbelianLorenzCodifferential_eq_finiteFrameCovariantTrace
    (frame : SmoothD8Frame period hPeriod) (reference metric : SmoothGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod) (component : Fin 2)
    (point : EffectiveQuotient period hPeriod) :
    globalGeneralMetricAbelianLorenzCodifferential period hPeriod metric potential point component =
      ∑ first : Fin frame.count, ∑ second : Fin frame.count,
        finiteFrameInverseMetricCoefficient period hPeriod frame reference metric first second point *
          (frameDerivative period hPeriod Real frame
            (finiteFramePotentialCoefficient period hPeriod frame potential component second) point first -
            ∑ index : Fin frame.count,
              finiteFrameKoszulChristoffelCoefficient period hPeriod frame reference metric index first second point *
                finiteFramePotentialCoefficient period hPeriod frame potential component index point) := by
  rcases canonicalHolonomicChartThroughEveryPoint period hPeriod point with ⟨patch, coordinate, hPoint⟩
  rw [← hPoint]
  simp only [finiteFrameKoszulChristoffelCoefficient_eq_local]
  exact globalGeneralMetricAbelianLorenzCodifferential_eq_finiteFrameCovariantTrace_local
    period hPeriod frame reference metric potential component patch coordinate

end
end P0EFTJanusFiniteFrameLorenzCovariantTrace4D
end JanusFormal
