import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGaugeC2AbelianOffShellGraphBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusLorenzSmoothScalarLeibniz4D

/-! # Genuine Lorenz feature from completed C² frame coefficients -/

namespace JanusFormal
namespace P0EFTJanusRegularFrameC2LorenzFeature4D

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

noncomputable section
open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusIntrinsicAbelianMaxwellCurvature4D
open P0EFTJanusMappingTorusLocalAbelianLorenzCodifferential4D
open P0EFTJanusMappingTorusGlobalGeneralMetricAbelianLorenzCodifferential4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0Space4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarSmoothL2Density4D
open P0EFTJanusProgramPRegularFrameMetricInverse4D
open P0EFTJanusProgramPRegularFrameMaxwellCurvatureBridge4D
open P0EFTJanusProgramPRegularFrameGaugePotentialReconstruction4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalMetricGaugeCoreProjection4D
open P0EFTJanusProgramPRegularFrameGaugeCurvatureC0FromC2Coefficients4D
open P0EFTJanusLorenzSmoothScalarLeibniz4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev C0Scalar := C(EffectiveQuotient period hPeriod, Real)
private abbrev C2Scalar := CanonicalPhysicalScalarC2JetCore period hPeriod
private abbrev GaugeC2Core := RegularGeneralMetricC2GaugeCoefficientCore period hPeriod

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance : NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (C2Scalar period hPeriod) := inferInstance

/-- One dual-frame one-form, repeated in both Abelian components. -/
def regularFrameLorenzBasisPotential
    (metric : RegularGeneralLorentzMetric period hPeriod) (index : Fin 4) :
    SmoothAbelianGaugePotential period hPeriod :=
  regularFrameGaugePotentialFromCoefficients period hPeriod metric
    (constantSmoothField period hPeriod GaugeFiber
      ((EuclideanSpace.equiv (Fin 4 × Fin 2) Real).symm
        (fun entry => if entry.1 = index then 1 else 0)))

theorem regularFrameLorenzBasisPotential_covector
    (metric : RegularGeneralLorentzMetric period hPeriod) (index : Fin 4)
    (component : Fin 2) (point : EffectiveQuotient period hPeriod) :
    (regularFrameLorenzBasisPotential period hPeriod metric index).toFun component point =
      ∑ column : Fin 4,
        regularFrameMetricInverseMatrix period hPeriod metric index column point •
          metric.metric.tensor.tensor point (metric.frame column point) := by
  classical
  change (∑ row : Fin 4, ∑ column : Fin 4,
    ((if row = index then 1 else 0) *
      regularFrameMetricInverseMatrix period hPeriod metric row column point) •
        metric.metric.tensor.tensor point (metric.frame column point)) = _
  simp only [ite_mul, one_mul, zero_mul, ite_smul, zero_smul]
  simp

theorem regularFrameLorenzBasisPotential_sharp
    (metric : RegularGeneralLorentzMetric period hPeriod) (index : Fin 4)
    (component : Fin 2) (point : EffectiveQuotient period hPeriod) :
    inverseMetricSharp period hPeriod metric.metric point
        ((regularFrameLorenzBasisPotential period hPeriod metric index).toFun
          component point) =
      ∑ column : Fin 4,
        regularFrameMetricInverseMatrix period hPeriod metric index column point •
          metric.frame column point := by
  rw [regularFrameLorenzBasisPotential_covector, map_sum]
  apply Finset.sum_congr rfl
  intro column _
  rw [map_smul, ← metric.metric.musical_eq_tensor point]
  exact congrArg
    (regularFrameMetricInverseMatrix period hPeriod metric index column point • ·)
    (inverseMetricSharp_metric_flat period hPeriod metric.metric point
      (metric.frame column point))

private theorem reconstructed_component_expansion
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (coefficients : SmoothQuotientField period hPeriod GaugeFiber)
    (component : Fin 2) (point : EffectiveQuotient period hPeriod) :
    (regularFrameGaugePotentialFromCoefficients period hPeriod metric coefficients).toFun
        component point =
      (∑ index : Fin 4, smoothScalarMulGaugePotential period hPeriod
        (regularFrameGaugeCoefficient period hPeriod coefficients (index, component))
        (regularFrameLorenzBasisPotential period hPeriod metric index)).toFun
          component point := by
  let evaluation : SmoothAbelianGaugePotential period hPeriod →+
      (TangentSpace coverModelWithCorners point →L[Real] Real) :=
    { toFun := fun potential => potential.toFun component point
      map_zero' := rfl
      map_add' := by intros; rfl }
  change _ = evaluation (∑ index : Fin 4,
    smoothScalarMulGaugePotential period hPeriod
      (regularFrameGaugeCoefficient period hPeriod coefficients (index, component))
      (regularFrameLorenzBasisPotential period hPeriod metric index))
  rw [map_sum]
  change (∑ row : Fin 4, ∑ column : Fin 4,
      (coefficients point (row, component) *
        regularFrameMetricInverseMatrix period hPeriod metric row column point) •
        metric.metric.tensor.tensor point (metric.frame column point)) =
    ∑ row : Fin 4, coefficients point (row, component) •
      (regularFrameLorenzBasisPotential period hPeriod metric row).toFun component point
  simp_rw [regularFrameLorenzBasisPotential_covector, Finset.smul_sum, smul_smul]

private theorem lorenz_component_congr
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (hEqual : ∀ point, first.toFun component point = second.toFun component point)
    (point : EffectiveQuotient period hPeriod) :
    globalGeneralMetricAbelianLorenzCodifferential period hPeriod metric first point component =
      globalGeneralMetricAbelianLorenzCodifferential period hPeriod metric second point component := by
  have hRaised : ∀ patch coordinate,
      localRaisedAbelianGaugePotential period hPeriod metric first component patch coordinate =
        localRaisedAbelianGaugePotential period hPeriod metric second component patch coordinate := by
    intro patch coordinate
    unfold localRaisedAbelianGaugePotential
    congr 1
    funext index
    unfold localGaugeCoefficient
    rw [hEqual]
  simp only [globalGeneralMetricAbelianLorenzCodifferential_apply,
    globalGeneralMetricAbelianLorenzValue, localAbelianLorenzDivergence]
  simp_rw [hRaised]

/-- The lower-order Lorenz coefficient is the actual Lorenz field of a fixed
smooth dual-frame potential. -/
def regularFrameLorenzZerothCoefficient
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (index : Fin 4) (component : Fin 2) : SmoothScalarField period hPeriod :=
  ghostComponent period hPeriod
    (globalGeneralMetricAbelianLorenzCodifferential period hPeriod metric.metric
      (regularFrameLorenzBasisPotential period hPeriod metric index)) component

/-- Exact first-order regular-frame expansion of the genuine global Lorenz operator. -/
theorem regularFrameLorenz_reconstructed
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (coefficients : SmoothQuotientField period hPeriod GaugeFiber)
    (component : Fin 2) (point : EffectiveQuotient period hPeriod) :
    globalGeneralMetricAbelianLorenzCodifferential period hPeriod metric.metric
        (regularFrameGaugePotentialFromCoefficients period hPeriod metric coefficients)
        point component =
      ∑ index : Fin 4,
        (coefficients point (index, component) *
            regularFrameLorenzZerothCoefficient period hPeriod metric index component point +
          ∑ column : Fin 4,
            regularFrameMetricInverseMatrix period hPeriod metric index column point *
              frameDerivative period hPeriod Real
                (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
                (regularFrameGaugeCoefficient period hPeriod coefficients (index, component))
                point column) := by
  rw [lorenz_component_congr period hPeriod metric.metric _ _ component
    (reconstructed_component_expansion period hPeriod metric coefficients component)]
  let evaluation : SmoothAbelianGaugePotential period hPeriod →ₗ[Real] Real :=
    { toFun := fun potential => globalGeneralMetricAbelianLorenzCodifferential
        period hPeriod metric.metric potential point component
      map_add' first second := by
        rw [globalGeneralMetricAbelianLorenzCodifferential_add]
        rfl
      map_smul' scalar potential := by
        rw [globalGeneralMetricAbelianLorenzCodifferential_smul]
        rfl }
  change evaluation (∑ index : Fin 4,
    smoothScalarMulGaugePotential period hPeriod
      (regularFrameGaugeCoefficient period hPeriod coefficients (index, component))
      (regularFrameLorenzBasisPotential period hPeriod metric index)) = _
  rw [map_sum]
  change (∑ index : Fin 4,
    globalGeneralMetricAbelianLorenzCodifferential period hPeriod metric.metric
      (smoothScalarMulGaugePotential period hPeriod
        (regularFrameGaugeCoefficient period hPeriod coefficients (index, component))
        (regularFrameLorenzBasisPotential period hPeriod metric index)) point component) = _
  simp_rw [globalGeneralMetricAbelianLorenzCodifferential_smoothScalarMul_apply,
    regularFrameLorenzBasisPotential_sharp, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro index _
  congr 1

/-- The existing regular-frame derivative, bundled as a bounded linear map. -/
def regularFrameC2FirstDerivativeCLM
    (metric : RegularGeneralLorentzMetric period hPeriod) (index : Fin 4) :
    C2Scalar period hPeriod →L[Real] C0Scalar period hPeriod where
  toFun := regularFrameC2FirstDerivative period hPeriod metric index
  map_add' := regularFrameC2FirstDerivative_add period hPeriod metric index
  map_smul' scalar jet := by
    unfold regularFrameC2FirstDerivative
    simp only [map_smul, mul_smul_comm, Finset.smul_sum, RingHom.id_apply]
  cont := (regularFrameC2FirstDerivative_contDiff period hPeriod metric index).continuous

/-- Genuine Lorenz component on the completed coefficient core. -/
def regularFrameC2LorenzComponent
    (metric : RegularGeneralLorentzMetric period hPeriod) (component : Fin 2) :
    GaugeC2Core period hPeriod →L[Real] C0Scalar period hPeriod :=
  ∑ index : Fin 4,
    ((ContinuousLinearMap.mul Real (C0Scalar period hPeriod)
      (smoothToCanonicalPhysicalContinuousScalar period hPeriod
        (regularFrameLorenzZerothCoefficient period hPeriod metric index component))).comp
      (canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod) +
      ∑ column : Fin 4,
        (ContinuousLinearMap.mul Real (C0Scalar period hPeriod)
          (smoothToCanonicalPhysicalContinuousScalar period hPeriod
            (regularFrameMetricInverseMatrix period hPeriod metric index column))).comp
          (regularFrameC2FirstDerivativeCLM period hPeriod metric column)).comp
      (gaugeCoefficientC2CoreComponentCLM period hPeriod index component)

theorem regularFrameC2LorenzComponent_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (coefficients : SmoothQuotientField period hPeriod GaugeFiber) (component : Fin 2) :
    regularFrameC2LorenzComponent period hPeriod metric component
        (smoothGaugeCoefficientC2CoreLinearMap period hPeriod coefficients) =
      smoothToCanonicalPhysicalContinuousScalar period hPeriod
        (ghostComponent period hPeriod
          (globalGeneralMetricAbelianLorenzCodifferential period hPeriod metric.metric
            (regularFrameGaugePotentialFromCoefficients period hPeriod metric coefficients))
          component) := by
  apply ContinuousMap.ext
  intro point
  simp only [regularFrameC2LorenzComponent, sum_apply, add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply',
    gaugeCoefficientC2CoreComponentCLM, ContinuousLinearMap.proj_apply,
    smoothGaugeCoefficientC2CoreLinearMap_apply,
    canonicalPhysicalScalarC2JetCoreToContinuous_smooth,
    ContinuousMap.sum_apply, ContinuousMap.add_apply, ContinuousMap.mul_apply]
  change (∑ index : Fin 4,
      (regularFrameLorenzZerothCoefficient period hPeriod metric index component point *
          coefficients point (index, component) +
        ∑ column : Fin 4,
          regularFrameMetricInverseMatrix period hPeriod metric index column point *
            regularFrameC2FirstDerivative period hPeriod metric column
              (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
                (regularFrameGaugeCoefficient period hPeriod coefficients (index, component)))
              point)) = _
  simp_rw [regularFrameC2FirstDerivative_smooth]
  change (∑ index : Fin 4,
      (regularFrameLorenzZerothCoefficient period hPeriod metric index component point *
          coefficients point (index, component) +
        ∑ column : Fin 4,
          regularFrameMetricInverseMatrix period hPeriod metric index column point *
            frameDerivative period hPeriod Real
              (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
              (regularFrameGaugeCoefficient period hPeriod coefficients (index, component))
              point column)) =
    globalGeneralMetricAbelianLorenzCodifferential period hPeriod metric.metric
      (regularFrameGaugePotentialFromCoefficients period hPeriod metric coefficients)
      point component
  rw [regularFrameLorenz_reconstructed]
  apply Finset.sum_congr rfl
  intro index _
  rw [mul_comm (regularFrameLorenzZerothCoefficient period hPeriod metric index component point)]

/-- Bounded physical L² Lorenz feature. -/
def regularFrameC2LorenzComponentL2
    (metric : RegularGeneralLorentzMetric period hPeriod) (component : Fin 2) :
    GaugeC2Core period hPeriod →L[Real] CanonicalPhysicalBulkL2 period hPeriod :=
  (continuousToCanonicalPhysicalBulkL2 period hPeriod).comp
    (regularFrameC2LorenzComponent period hPeriod metric component)

theorem regularFrameC2LorenzComponentL2_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (coefficients : SmoothQuotientField period hPeriod GaugeFiber) (component : Fin 2) :
    regularFrameC2LorenzComponentL2 period hPeriod metric component
        (smoothGaugeCoefficientC2CoreLinearMap period hPeriod coefficients) =
      smoothToCanonicalPhysicalBulkL2 period hPeriod
        (ghostComponent period hPeriod
          (globalGeneralMetricAbelianLorenzCodifferential period hPeriod metric.metric
            (regularFrameGaugePotentialFromCoefficients period hPeriod metric coefficients))
          component) := by
  change continuousToCanonicalPhysicalBulkL2 period hPeriod
    (regularFrameC2LorenzComponent period hPeriod metric component
      (smoothGaugeCoefficientC2CoreLinearMap period hPeriod coefficients)) = _
  rw [regularFrameC2LorenzComponent_smooth,
    continuousToCanonicalPhysicalBulkL2_agrees_on_smooth]

end
end P0EFTJanusRegularFrameC2LorenzFeature4D
end JanusFormal
