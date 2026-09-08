import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameC2RiemannActualDerivative4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D

/-! # Intrinsic reconstruction of finite-frame Riemann curvature -/

namespace JanusFormal
namespace P0EFTJanusFiniteFrameC2RiemannIntrinsicReconstruction4D

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D
open P0EFTJanusMappingTorusCanonicalHolonomicRiemannNaturality4D
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMetricCoupledScalarMatterJetVariation
open P0EFTJanusProgramPGeneralMetricPositiveDualizer4D
open P0EFTJanusFiniteFrameCovariantTensorDivergence4D
open P0EFTJanusFiniteFrameKoszulCoefficients4D
open P0EFTJanusFiniteFrameC2ScalarCurvatureSmoothCoefficients4D
open P0EFTJanusFiniteFrameC2ConnectionActualDerivative4D
open P0EFTJanusFiniteFrameC2RiemannActualDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D

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

/-- The smooth Christoffel coefficients reconstruct the actual local connection vector. -/
theorem finiteFrameSmoothChristoffel_reconstructs
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : CoordinateVector)
    (first second : Fin frame.count) :
    (∑ upper : Fin frame.count,
      finiteFrameKoszulChristoffelCoefficient period hPeriod frame baseMetric metric
          upper first second (patch.coordinateMap coordinate) •
        finiteFramePulledVector period hPeriod frame patch upper coordinate) =
      finiteFrameLocalCovariantDerivativeVector period hPeriod frame metric patch coordinate
        first second := by
  rw [finiteFrameLocalCovariantDerivativeVector_reconstructs period hPeriod frame baseMetric]
  apply Finset.sum_congr rfl
  intro upper _
  rw [finiteFrameKoszulChristoffelCoefficient_eq_local]

private theorem fderiv_finiteFrameLocalCovariantDerivative_reconstruction
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : CoordinateVector)
    (derivative first second : Fin frame.count) :
    fderiv Real
        (fun current => finiteFrameLocalCovariantDerivativeVector period hPeriod frame metric patch
          current first second)
        coordinate (finiteFramePulledVector period hPeriod frame patch derivative coordinate) =
      (∑ upper : Fin frame.count,
        frameDerivative period hPeriod Real frame
            (finiteFrameKoszulChristoffelCoefficient period hPeriod frame baseMetric metric
              upper first second)
            (patch.coordinateMap coordinate) derivative •
          finiteFramePulledVector period hPeriod frame patch upper coordinate) +
        ∑ upper : Fin frame.count,
          finiteFrameKoszulChristoffelCoefficient period hPeriod frame baseMetric metric
              upper first second (patch.coordinateMap coordinate) •
            fderiv Real (finiteFramePulledVector period hPeriod frame patch upper) coordinate
              (finiteFramePulledVector period hPeriod frame patch derivative coordinate) := by
  let coefficient (upper : Fin frame.count) : CoordinateVector → Real := fun current =>
    finiteFrameKoszulChristoffelCoefficient period hPeriod frame baseMetric metric
      upper first second (patch.coordinateMap current)
  let localFrame (upper : Fin frame.count) : CoordinateVector → CoordinateVector :=
    finiteFramePulledVector period hPeriod frame patch upper
  let term (upper : Fin frame.count) : CoordinateVector → CoordinateVector := fun current =>
    coefficient upper current • localFrame upper current
  have hCoefficient (upper : Fin frame.count) : DifferentiableAt Real (coefficient upper) coordinate :=
    ((finiteFrameKoszulChristoffelCoefficient period hPeriod frame baseMetric metric
      upper first second).contMDiff_toFun.comp patch.coordinateMap_contMDiff).contDiff.differentiable
        (by simp) coordinate
  have hFrame (upper : Fin frame.count) : DifferentiableAt Real (localFrame upper) coordinate :=
    (finiteFramePulledVector_contDiff period hPeriod frame patch upper).differentiable (by simp) coordinate
  have hTerm (upper : Fin frame.count) : DifferentiableAt Real (term upper) coordinate :=
    (hCoefficient upper).smul (hFrame upper)
  have hTermDerivative (upper : Fin frame.count) :
      fderiv Real (term upper) coordinate
          (finiteFramePulledVector period hPeriod frame patch derivative coordinate) =
        coefficient upper coordinate •
            fderiv Real (localFrame upper) coordinate
              (finiteFramePulledVector period hPeriod frame patch derivative coordinate) +
          fderiv Real (coefficient upper) coordinate
              (finiteFramePulledVector period hPeriod frame patch derivative coordinate) •
            localFrame upper coordinate := by
    have hProduct := fderiv_smul (hCoefficient upper) (hFrame upper)
    have hApplied := congrArg
      (fun derivativeMap : CoordinateVector →L[Real] CoordinateVector =>
        derivativeMap (finiteFramePulledVector period hPeriod frame patch derivative coordinate))
      hProduct
    change fderiv Real (coefficient upper • localFrame upper) coordinate _ = _
    rw [hApplied]
    simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply]
  have hFunction :
      (fun current => finiteFrameLocalCovariantDerivativeVector period hPeriod frame metric patch
        current first second) = fun current => ∑ upper : Fin frame.count, term upper current := by
    funext current
    exact (finiteFrameSmoothChristoffel_reconstructs period hPeriod frame baseMetric metric patch
      current first second).symm
  rw [hFunction]
  have hSum := fderiv_fun_sum (u := Finset.univ) (fun upper _ => hTerm upper)
  have hApplied := congrArg
    (fun derivativeMap : CoordinateVector →L[Real] CoordinateVector =>
      derivativeMap (finiteFramePulledVector period hPeriod frame patch derivative coordinate)) hSum
  rw [hApplied]
  simp only [sum_apply]
  calc
    (∑ upper : Fin frame.count,
      fderiv Real (term upper) coordinate
        (finiteFramePulledVector period hPeriod frame patch derivative coordinate)) =
        ∑ upper : Fin frame.count,
          (coefficient upper coordinate •
              fderiv Real (localFrame upper) coordinate
                (finiteFramePulledVector period hPeriod frame patch derivative coordinate) +
            fderiv Real (coefficient upper) coordinate
                (finiteFramePulledVector period hPeriod frame patch derivative coordinate) •
              localFrame upper coordinate) := by
      apply Finset.sum_congr rfl
      intro upper _
      exact hTermDerivative upper
    _ = _ := by
      rw [Finset.sum_add_distrib]
      simp_rw [show ∀ upper : Fin frame.count,
          fderiv Real (coefficient upper) coordinate
              (finiteFramePulledVector period hPeriod frame patch derivative coordinate) =
            frameDerivative period hPeriod Real frame
              (finiteFrameKoszulChristoffelCoefficient period hPeriod frame baseMetric metric
                upper first second) (patch.coordinateMap coordinate) derivative by
        intro upper
        exact fderiv_comp_coordinateMap_finiteFramePulledVector period hPeriod frame
          (finiteFrameKoszulChristoffelCoefficient period hPeriod frame baseMetric metric
            upper first second) patch coordinate derivative]
      dsimp only [coefficient, localFrame]
      abel

private theorem finiteFrameSmoothChristoffelProduct_reconstructs
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : CoordinateVector)
    (derivative first second : Fin frame.count) :
    (∑ upper : Fin frame.count,
        (∑ contracted : Fin frame.count,
          finiteFrameKoszulChristoffelCoefficient period hPeriod frame baseMetric metric
                contracted first second (patch.coordinateMap coordinate) *
            finiteFrameKoszulChristoffelCoefficient period hPeriod frame baseMetric metric
                upper derivative contracted (patch.coordinateMap coordinate)) •
          finiteFramePulledVector period hPeriod frame patch upper coordinate) =
      ∑ contracted : Fin frame.count,
        finiteFrameKoszulChristoffelCoefficient period hPeriod frame baseMetric metric
              contracted first second (patch.coordinateMap coordinate) •
          finiteFrameLocalCovariantDerivativeVector period hPeriod frame metric patch coordinate
            derivative contracted := by
  simp_rw [← finiteFrameSmoothChristoffel_reconstructs period hPeriod frame baseMetric metric patch
    coordinate derivative]
  simp only [Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]

private theorem finiteFrameSmoothSecondCovariantDerivative_reconstructs
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : CoordinateVector)
    (derivative first second : Fin frame.count) :
    (∑ upper : Fin frame.count,
        frameDerivative period hPeriod Real frame
            (finiteFrameKoszulChristoffelCoefficient period hPeriod frame baseMetric metric
              upper first second) (patch.coordinateMap coordinate) derivative •
          finiteFramePulledVector period hPeriod frame patch upper coordinate) +
      (∑ upper : Fin frame.count,
        (∑ contracted : Fin frame.count,
          finiteFrameKoszulChristoffelCoefficient period hPeriod frame baseMetric metric
                contracted first second (patch.coordinateMap coordinate) *
            finiteFrameKoszulChristoffelCoefficient period hPeriod frame baseMetric metric
                upper derivative contracted (patch.coordinateMap coordinate)) •
          finiteFramePulledVector period hPeriod frame patch upper coordinate) =
      localCovariantDerivativeVectorField period hPeriod metric patch
        (finiteFramePulledVector period hPeriod frame patch derivative)
        (fun current => finiteFrameLocalCovariantDerivativeVector period hPeriod frame metric patch
          current first second) coordinate := by
  unfold localCovariantDerivativeVectorField
  rw [fderiv_finiteFrameLocalCovariantDerivative_reconstruction period hPeriod frame baseMetric metric
    patch coordinate derivative first second]
  rw [finiteFrameSmoothChristoffelProduct_reconstructs period hPeriod frame baseMetric metric patch
    coordinate derivative first second]
  change _ = _ + _ +
    localLeviCivitaChristoffelBilinearMap period hPeriod metric patch coordinate
      (finiteFramePulledVector period hPeriod frame patch derivative coordinate)
      (finiteFrameLocalCovariantDerivativeVector period hPeriod frame metric patch coordinate
        first second)
  rw [← finiteFrameSmoothChristoffel_reconstructs period hPeriod frame baseMetric metric patch
    coordinate first second]
  change _ = _ + _ +
    localLeviCivitaChristoffelBilinearMap period hPeriod metric patch coordinate
      (finiteFramePulledVector period hPeriod frame patch derivative coordinate)
      (∑ contracted : Fin frame.count,
        finiteFrameKoszulChristoffelCoefficient period hPeriod frame baseMetric metric
              contracted first second (patch.coordinateMap coordinate) •
          finiteFramePulledVector period hPeriod frame patch contracted coordinate)
  rw [map_sum]
  simp_rw [map_smul]
  simp_rw [finiteFrameLocalCovariantDerivativeVector, smul_add]
  rw [Finset.sum_add_distrib]
  abel

private theorem finiteFrameSmoothStructureChristoffelProduct_reconstructs
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : CoordinateVector)
    (first second lower : Fin frame.count) :
    (∑ upper : Fin frame.count,
        (∑ contracted : Fin frame.count,
          finiteFrameStructureCoefficient period hPeriod frame baseMetric first second contracted
                (patch.coordinateMap coordinate) *
            finiteFrameKoszulChristoffelCoefficient period hPeriod frame baseMetric metric
                upper contracted lower (patch.coordinateMap coordinate)) •
          finiteFramePulledVector period hPeriod frame patch upper coordinate) =
      ∑ contracted : Fin frame.count,
        finiteFrameStructureCoefficient period hPeriod frame baseMetric first second contracted
              (patch.coordinateMap coordinate) •
          finiteFrameLocalCovariantDerivativeVector period hPeriod frame metric patch coordinate
            contracted lower := by
  simp_rw [← finiteFrameSmoothChristoffel_reconstructs period hPeriod frame baseMetric metric patch
    coordinate]
  simp only [Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]

private theorem finiteFrameSmoothBracketCovariantDerivative_reconstructs
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : CoordinateVector)
    (first second lower : Fin frame.count) :
    (∑ upper : Fin frame.count,
        (∑ contracted : Fin frame.count,
          finiteFrameStructureCoefficient period hPeriod frame baseMetric first second contracted
                (patch.coordinateMap coordinate) *
            finiteFrameKoszulChristoffelCoefficient period hPeriod frame baseMetric metric
                upper contracted lower (patch.coordinateMap coordinate)) •
          finiteFramePulledVector period hPeriod frame patch upper coordinate) =
      localCovariantDerivativeVectorField period hPeriod metric patch
        (VectorField.lieBracket Real
          (finiteFramePulledVector period hPeriod frame patch first)
          (finiteFramePulledVector period hPeriod frame patch second))
        (finiteFramePulledVector period hPeriod frame patch lower) coordinate := by
  rw [finiteFrameSmoothStructureChristoffelProduct_reconstructs period hPeriod frame baseMetric
    metric patch coordinate first second lower]
  unfold localCovariantDerivativeVectorField
  rw [finiteFrameLocalLieBracket_eq_sum period hPeriod frame baseMetric patch coordinate]
  rw [map_sum]
  change _ = _ +
    localLeviCivitaChristoffelBilinearMap period hPeriod metric patch coordinate
      (∑ contracted : Fin frame.count,
        finiteFrameStructureCoefficient period hPeriod frame baseMetric first second contracted
              (patch.coordinateMap coordinate) •
          finiteFramePulledVector period hPeriod frame patch contracted coordinate)
      (finiteFramePulledVector period hPeriod frame patch lower coordinate)
  rw [map_sum]
  simp_rw [map_smul]
  rw [LinearMap.sum_apply]
  change (∑ contracted : Fin frame.count,
      finiteFrameStructureCoefficient period hPeriod frame baseMetric first second contracted
            (patch.coordinateMap coordinate) •
        finiteFrameLocalCovariantDerivativeVector period hPeriod frame metric patch coordinate
          contracted lower) =
    (∑ contracted : Fin frame.count,
      finiteFrameStructureCoefficient period hPeriod frame baseMetric first second contracted
            (patch.coordinateMap coordinate) •
        fderiv Real (finiteFramePulledVector period hPeriod frame patch lower) coordinate
          (finiteFramePulledVector period hPeriod frame patch contracted coordinate)) +
      ∑ contracted : Fin frame.count,
        (finiteFrameStructureCoefficient period hPeriod frame baseMetric first second contracted
              (patch.coordinateMap coordinate) •
          localLeviCivitaChristoffelBilinearMap period hPeriod metric patch coordinate
            (finiteFramePulledVector period hPeriod frame patch contracted coordinate))
          (finiteFramePulledVector period hPeriod frame patch lower coordinate)
  simp_rw [finiteFrameLocalCovariantDerivativeVector, smul_add]
  rw [Finset.sum_add_distrib]
  rfl

/-- The smooth redundant-frame Riemann coefficients reconstruct the intrinsic Riemann vector. -/
theorem finiteFrameSmoothRiemann_reconstructs
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : CoordinateVector)
    (lower first second : Fin frame.count) :
    (∑ upper : Fin frame.count,
      finiteFrameSmoothRiemannCoefficient period hPeriod frame baseMetric metric
            upper lower first second (patch.coordinateMap coordinate) •
        finiteFramePulledVector period hPeriod frame patch upper coordinate) =
      localLeviCivitaRiemannVector period hPeriod metric patch coordinate
        (finiteFramePulledVector period hPeriod frame patch first coordinate)
        (finiteFramePulledVector period hPeriod frame patch second coordinate)
        (finiteFramePulledVector period hPeriod frame patch lower coordinate) := by
  let localFrame (upper : Fin frame.count) :=
    finiteFramePulledVector period hPeriod frame patch upper coordinate
  let firstDerivative := ∑ upper : Fin frame.count,
    frameDerivative period hPeriod Real frame
        (finiteFrameKoszulChristoffelCoefficient period hPeriod frame baseMetric metric
          upper second lower) (patch.coordinateMap coordinate) first • localFrame upper
  let secondDerivative := ∑ upper : Fin frame.count,
    frameDerivative period hPeriod Real frame
        (finiteFrameKoszulChristoffelCoefficient period hPeriod frame baseMetric metric
          upper first lower) (patch.coordinateMap coordinate) second • localFrame upper
  let firstProduct := ∑ upper : Fin frame.count,
    (∑ contracted : Fin frame.count,
      finiteFrameKoszulChristoffelCoefficient period hPeriod frame baseMetric metric
            contracted second lower (patch.coordinateMap coordinate) *
        finiteFrameKoszulChristoffelCoefficient period hPeriod frame baseMetric metric
            upper first contracted (patch.coordinateMap coordinate)) • localFrame upper
  let secondProduct := ∑ upper : Fin frame.count,
    (∑ contracted : Fin frame.count,
      finiteFrameKoszulChristoffelCoefficient period hPeriod frame baseMetric metric
            contracted first lower (patch.coordinateMap coordinate) *
        finiteFrameKoszulChristoffelCoefficient period hPeriod frame baseMetric metric
            upper second contracted (patch.coordinateMap coordinate)) • localFrame upper
  let bracketProduct := ∑ upper : Fin frame.count,
    (∑ contracted : Fin frame.count,
      finiteFrameStructureCoefficient period hPeriod frame baseMetric first second contracted
            (patch.coordinateMap coordinate) *
        finiteFrameKoszulChristoffelCoefficient period hPeriod frame baseMetric metric
            upper contracted lower (patch.coordinateMap coordinate)) • localFrame upper
  have hExpansion :
      (∑ upper : Fin frame.count,
        finiteFrameSmoothRiemannCoefficient period hPeriod frame baseMetric metric
              upper lower first second (patch.coordinateMap coordinate) • localFrame upper) =
        (firstDerivative + firstProduct) - (secondDerivative + secondProduct) - bracketProduct := by
    simp_rw [finiteFrameSmoothRiemannCoefficient_eq_actual]
    unfold finiteFrameActualRiemannCoefficient
    dsimp only [firstDerivative, secondDerivative, firstProduct, secondProduct, bracketProduct]
    simp only [smoothScalarFieldSub_apply, smoothScalarFieldAdd_apply,
      P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0FiniteMatrixProduct4D.smoothScalarFieldFinsetSum_apply,
      smoothScalarFieldMul_apply, sub_smul, add_smul, Finset.sum_sub_distrib,
      Finset.sum_add_distrib, Finset.sum_smul]
    unfold frameDerivativeComponentField
    abel
  rw [hExpansion]
  rw [finiteFrameSmoothSecondCovariantDerivative_reconstructs period hPeriod frame baseMetric metric
      patch coordinate first second lower]
  rw [finiteFrameSmoothSecondCovariantDerivative_reconstructs period hPeriod frame baseMetric metric
      patch coordinate second first lower]
  dsimp only [bracketProduct]
  rw [finiteFrameSmoothBracketCovariantDerivative_reconstructs period hPeriod frame baseMetric metric
    patch coordinate first second lower]
  exact localCovariantDerivativeVectorField_curvature period hPeriod metric patch coordinate
    (finiteFramePulledVector period hPeriod frame patch first)
    (finiteFramePulledVector period hPeriod frame patch second)
    (finiteFramePulledVector period hPeriod frame patch lower)
    ((finiteFramePulledVector_contDiff period hPeriod frame patch first).differentiable (by simp) coordinate)
    ((finiteFramePulledVector_contDiff period hPeriod frame patch second).differentiable (by simp) coordinate)
    (finiteFramePulledVector_contDiff period hPeriod frame patch lower)

end
end P0EFTJanusFiniteFrameC2RiemannIntrinsicReconstruction4D
end JanusFormal
