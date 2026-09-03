import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularFrameGaugeCurvatureC0FromC2Coefficients4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootJetRigidity4D

/-! # Gauge-coefficient transport from the varied frame to the base frame -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2GaugeCoefficientFrameTransport4D

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 1200000

noncomputable section

open Set
open scoped Manifold ContDiff BigOperators Matrix.Norms.Frobenius
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0LocalRootBranch4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2LocalRootBranch4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2IdentityRootBranch4D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusProgramPGlobalGaugeTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootLift4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootSmoothLift4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootJetRigidity4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartRegularMetric4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalMetricGaugeCoreProjection4D
open P0EFTJanusProgramPRegularFrameGaugePotentialReconstruction4D
open P0EFTJanusProgramPRegularFrameGaugeCurvatureC0FromC2Coefficients4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev Matrix4 :=
  P0EFTJanusPositiveRawSplitCharpolyContDiffLocalRootBranch4D.Matrix4

private abbrev C2Scalar :=
  CanonicalPhysicalScalarC2JetCore period hPeriod

private abbrev C2Matrix := C2FiniteMatrix period hPeriod 4

private abbrev GaugeC2Core :=
  RegularGeneralMetricC2GaugeCoefficientCore period hPeriod

@[reducible] local instance canonicalMatrixNormedAddCommGroup :
    NormedAddCommGroup Matrix4 :=
  NonUnitalNormedRing.toNormedAddCommGroup

local instance canonicalMatrixAddCommGroup : AddCommGroup Matrix4 :=
  canonicalMatrixNormedAddCommGroup.toAddCommGroup

local instance canonicalMatrixPseudoMetricSpace : PseudoMetricSpace Matrix4 :=
  canonicalMatrixNormedAddCommGroup.toPseudoMetricSpace

local instance canonicalMatrixUniformSpace : UniformSpace Matrix4 :=
  canonicalMatrixPseudoMetricSpace.toUniformSpace

local instance canonicalMatrixTopologicalSpace : TopologicalSpace Matrix4 :=
  canonicalMatrixUniformSpace.toTopologicalSpace

@[reducible] local instance canonicalMatrixNormedSpace :
    NormedSpace Real Matrix4 :=
  NormedAlgebra.toNormedSpace Matrix4

local instance canonicalMatrixModule : Module Real Matrix4 :=
  canonicalMatrixNormedSpace.toModule

local instance canonicalMatrixCompleteSpace : CompleteSpace Matrix4 :=
  FiniteDimensional.complete Real Matrix4

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance c2ScalarNormedAddCommGroup :
    NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule
    period hPeriod).normedAddCommGroup

local instance c2ScalarNormedSpace :
    NormedSpace Real (C2Scalar period hPeriod) :=
  inferInstance

/-- One entry of a completed C² root matrix. -/
def gaugeFrameTransportC2MatrixEntryCLM
    (row column : Fin 4) :
    C2Matrix period hPeriod →L[Real] C2Scalar period hPeriod :=
  (ContinuousLinearMap.proj column :
      (Fin 4 → C2Scalar period hPeriod) →L[Real]
        C2Scalar period hPeriod).comp
    (ContinuousLinearMap.proj row :
      C2Matrix period hPeriod →L[Real]
        (Fin 4 → C2Scalar period hPeriod))

/-- The root transpose sends moving-frame gauge coefficients to coefficients
in the fixed base frame. -/
def gaugeCoefficientC2CoreFrameTransport
    (root : C2Matrix period hPeriod)
    (coefficients : GaugeC2Core period hPeriod) :
    GaugeC2Core period hPeriod :=
  fun baseIndex component =>
    ∑ movingIndex : Fin 4,
      canonicalPhysicalScalarC2JetCoreProduct period hPeriod
        (root movingIndex baseIndex) (coefficients movingIndex component)

/-- The finite completed transport is jointly smooth. -/
theorem gaugeCoefficientC2CoreFrameTransport_contDiff :
    ContDiff Real ∞
      (fun input : C2Matrix period hPeriod × GaugeC2Core period hPeriod =>
        gaugeCoefficientC2CoreFrameTransport period hPeriod input.1 input.2) := by
  rw [contDiff_pi]
  intro baseIndex
  rw [contDiff_pi]
  intro component
  apply ContDiff.sum
  intro movingIndex _
  exact (canonicalPhysicalScalarC2JetCoreProduct_contDiff
      period hPeriod).comp
    (((gaugeFrameTransportC2MatrixEntryCLM period hPeriod movingIndex
        baseIndex).comp
      (ContinuousLinearMap.fst Real (C2Matrix period hPeriod)
        (GaugeC2Core period hPeriod))).prod
      ((gaugeCoefficientC2CoreComponentCLM period hPeriod movingIndex
          component).comp
        (ContinuousLinearMap.snd Real (C2Matrix period hPeriod)
          (GaugeC2Core period hPeriod)))).contDiff

private def matrix4EntryCLM (row column : Fin 4) : Matrix4 →L[Real] Real :=
  LinearMap.toContinuousLinearMap
    { toFun := fun matrix => matrix row column
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

private def gaugeFiberEntryCLM (index : Fin 4 × Fin 2) :
    GaugeFiber →L[Real] Real :=
  LinearMap.toContinuousLinearMap
    { toFun := fun value => value index
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

/-- Smooth scalar coefficient produced by the same finite transport. -/
def smoothGaugeCoefficientFrameTransportEntry
    (root : SmoothQuotientField period hPeriod Matrix4)
    (coefficients : SmoothQuotientField period hPeriod GaugeFiber)
    (baseIndex : Fin 4) (component : Fin 2) :
    SmoothQuotientField period hPeriod Real :=
  ∑ movingIndex : Fin 4,
    smoothScalarFieldMul period hPeriod
      (smoothMatrixFieldCoefficients period hPeriod root movingIndex baseIndex)
      (regularFrameGaugeCoefficient period hPeriod coefficients
        (movingIndex, component))

/-- Smooth packet obtained by transporting all gauge coefficients. -/
def smoothGaugeCoefficientFrameTransport
    (root : SmoothQuotientField period hPeriod Matrix4)
    (coefficients : SmoothQuotientField period hPeriod GaugeFiber) :
    SmoothQuotientField period hPeriod GaugeFiber where
  toFun := fun point =>
    (EuclideanSpace.equiv (Fin 4 × Fin 2) Real).symm
      (fun index => smoothGaugeCoefficientFrameTransportEntry period hPeriod
        root coefficients index.1 index.2 point)
  contMDiff_toFun := by
    apply
      (EuclideanSpace.equiv (Fin 4 × Fin 2) Real).symm.toContinuousLinearMap
        |>.contMDiff.comp
    rw [contMDiff_pi_space]
    intro index
    exact (smoothGaugeCoefficientFrameTransportEntry period hPeriod root
      coefficients index.1 index.2).contMDiff_toFun

@[simp]
theorem smoothGaugeCoefficientFrameTransport_apply
    (root : SmoothQuotientField period hPeriod Matrix4)
    (coefficients : SmoothQuotientField period hPeriod GaugeFiber)
    (point : EffectiveQuotient period hPeriod)
    (baseIndex : Fin 4) (component : Fin 2) :
    smoothGaugeCoefficientFrameTransport period hPeriod root coefficients
        point (baseIndex, component) =
      smoothGaugeCoefficientFrameTransportEntry period hPeriod root
        coefficients baseIndex component point :=
  rfl

theorem regularFrameGaugeCoefficient_smoothFrameTransport
    (root : SmoothQuotientField period hPeriod Matrix4)
    (coefficients : SmoothQuotientField period hPeriod GaugeFiber)
    (baseIndex : Fin 4) (component : Fin 2) :
    regularFrameGaugeCoefficient period hPeriod
        (smoothGaugeCoefficientFrameTransport period hPeriod root coefficients)
        (baseIndex, component) =
      smoothGaugeCoefficientFrameTransportEntry period hPeriod root
        coefficients baseIndex component := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  rfl

@[simp]
theorem gaugeFrameTransport_smoothMatrixFieldToC2_entry
    (root : SmoothQuotientField period hPeriod Matrix4)
    (row column : Fin 4) :
    smoothMatrixFieldToC2 period hPeriod root row column =
      smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
        (smoothMatrixFieldCoefficients period hPeriod root row column) :=
  rfl

/-- The completed transport agrees exactly with smooth multiplication. -/
theorem gaugeCoefficientC2CoreFrameTransport_smooth
    (root : SmoothQuotientField period hPeriod Matrix4)
    (coefficients : SmoothQuotientField period hPeriod GaugeFiber) :
    gaugeCoefficientC2CoreFrameTransport period hPeriod
        (smoothMatrixFieldToC2 period hPeriod root)
        (smoothGaugeCoefficientC2CoreLinearMap period hPeriod coefficients) =
      smoothGaugeCoefficientC2CoreLinearMap period hPeriod
        (smoothGaugeCoefficientFrameTransport period hPeriod root
          coefficients) := by
  funext baseIndex component
  unfold gaugeCoefficientC2CoreFrameTransport
  rw [smoothGaugeCoefficientC2CoreLinearMap_apply,
    regularFrameGaugeCoefficient_smoothFrameTransport]
  unfold smoothGaugeCoefficientFrameTransportEntry
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro movingIndex _
  rw [gaugeFrameTransport_smoothMatrixFieldToC2_entry,
    smoothGaugeCoefficientC2CoreLinearMap_apply,
    canonicalPhysicalScalarC2JetCoreProduct_smooth]

/-- The root transpose transport is exactly change of coefficients from the
Lorentz-chart frame back to the fixed regular frame. -/
theorem smoothGaugeCoefficientFrameTransport_lorentzChart
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation : regularGeneralMetricSmoothC2Variation
        period hPeriod metric tensor ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric)
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    let hRoot :=
      (regularGeneralMetricC2LorentzChartDomain_matrix_mem_root
        period hPeriod metric hVariation).1
    smoothGaugeCoefficientFrameTransport period hPeriod
        (regularGeneralMetricC2IdentityRootMatrixField
          period hPeriod metric tensor hRoot)
        (gaugePotentialFrameCoefficients period hPeriod
          (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod
            metric tensor hVariation) potential) =
      gaugePotentialFrameCoefficients period hPeriod metric potential := by
  let hRoot :=
    (regularGeneralMetricC2LorentzChartDomain_matrix_mem_root
      period hPeriod metric hVariation).1
  let varied := regularGeneralMetricC2LorentzChartRegularMetric period hPeriod
    metric tensor hVariation
  let root := regularGeneralMetricC2IdentityRootMatrixField period hPeriod
    metric tensor hRoot
  apply SmoothQuotientField.ext period hPeriod GaugeFiber
  intro point
  apply (EuclideanSpace.equiv (Fin 4 × Fin 2) Real).injective
  funext index
  change
    (∑ movingIndex : Fin 4,
      root point movingIndex index.1 *
        potential.toFun index.2 point (varied.frame movingIndex point)) =
      potential.toFun index.2 point (metric.frame index.1 point)
  have hCoordinates :
      (varied.frameEquiv point).symm (metric.frame index.1 point) =
        fun movingIndex => root point movingIndex index.1 := by
    dsimp only [varied]
    rw [regularGeneralMetricC2LorentzChartRegularMetric_frameEquiv_symm_apply,
      regularGeneralMetricC2IdentityRootAt_apply]
    ext movingIndex
    simp [root, regularGeneralMetricC2IdentityRootMatrixField,
      RegularGeneralLorentzMetric.frame_eq_basisFun, Pi.basisFun_apply]
  have hFrame :
      metric.frame index.1 point =
        ∑ movingIndex : Fin 4,
          root point movingIndex index.1 • varied.frame movingIndex point := by
    let coordinates : Fin 4 → Real :=
      fun movingIndex => root point movingIndex index.1
    have hExpansion :
        varied.frameEquiv point coordinates =
          ∑ movingIndex : Fin 4,
            coordinates movingIndex • varied.frame movingIndex point := by
      calc
        varied.frameEquiv point coordinates =
            varied.frameEquiv point
              (∑ movingIndex : Fin 4,
                coordinates movingIndex •
                  (Pi.basisFun Real (Fin 4)) movingIndex) := by
          congr 1
          exact ((Pi.basisFun Real (Fin 4)).sum_repr coordinates).symm
        _ = ∑ movingIndex : Fin 4,
            coordinates movingIndex •
              varied.frameEquiv point
                ((Pi.basisFun Real (Fin 4)) movingIndex) := by
          simp only [map_sum, map_smul]
        _ = ∑ movingIndex : Fin 4,
            coordinates movingIndex • varied.frame movingIndex point := by
          apply Finset.sum_congr rfl
          intro movingIndex _
          rw [RegularGeneralLorentzMetric.frame_eq_basisFun]
    calc
      metric.frame index.1 point =
          varied.frameEquiv point
            ((varied.frameEquiv point).symm
              (metric.frame index.1 point)) :=
        ((varied.frameEquiv point).apply_symm_apply
          (metric.frame index.1 point)).symm
      _ = varied.frameEquiv point coordinates := by
        exact congrArg (varied.frameEquiv point) hCoordinates
      _ = _ := hExpansion
  rw [hFrame, map_sum]
  apply Finset.sum_congr rfl
  intro movingIndex _
  rw [map_smul]
  rfl

/-- Exact completed form of the geometric frame-change identity. -/
theorem gaugeCoefficientC2CoreFrameTransport_lorentzChart
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation : regularGeneralMetricSmoothC2Variation
        period hPeriod metric tensor ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric)
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    gaugeCoefficientC2CoreFrameTransport period hPeriod
        (c2IdentityRootBranch period hPeriod
          (regularGeneralMetricC2VariationMatrix
            period hPeriod metric tensor))
        (smoothGaugeCoefficientC2CoreLinearMap period hPeriod
          (gaugePotentialFrameCoefficients period hPeriod
            (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod
              metric tensor hVariation) potential)) =
      smoothGaugeCoefficientC2CoreLinearMap period hPeriod
        (gaugePotentialFrameCoefficients period hPeriod metric potential) := by
  let hRoot :=
    (regularGeneralMetricC2LorentzChartDomain_matrix_mem_root
      period hPeriod metric hVariation).1
  rw [regularGeneralMetricC2IdentityRoot_eq_smoothMatrixFieldToC2
    period hPeriod metric tensor hRoot]
  rw [gaugeCoefficientC2CoreFrameTransport_smooth]
  rw [smoothGaugeCoefficientFrameTransport_lorentzChart
    period hPeriod metric tensor hVariation potential]

/-- Reconstruction is also a left inverse of frame evaluation. -/
@[simp]
theorem regularFrameGaugePotentialFromCoefficients_frameCoefficients
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    regularFrameGaugePotentialFromCoefficients period hPeriod metric
        (gaugePotentialFrameCoefficients period hPeriod metric potential) =
      potential := by
  apply gaugePotentialFrameCoefficientsLinearMap_injective
    period hPeriod metric
  exact gaugePotentialFrameCoefficients_reconstructed period hPeriod metric
    (gaugePotentialFrameCoefficients period hPeriod metric potential)

/-- Gate marker: the completed gauge packet can be transported jointly and
recovers the exact fixed-frame coefficients on every smooth chart input. -/
theorem regular_general_metric_c2_gauge_coefficient_frame_transport_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation : regularGeneralMetricSmoothC2Variation
        period hPeriod metric tensor ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric)
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    ContDiff Real ∞
        (fun input : C2Matrix period hPeriod × GaugeC2Core period hPeriod =>
          gaugeCoefficientC2CoreFrameTransport period hPeriod input.1
            input.2) ∧
      gaugeCoefficientC2CoreFrameTransport period hPeriod
          (c2IdentityRootBranch period hPeriod
            (regularGeneralMetricC2VariationMatrix
              period hPeriod metric tensor))
          (smoothGaugeCoefficientC2CoreLinearMap period hPeriod
            (gaugePotentialFrameCoefficients period hPeriod
              (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod
                metric tensor hVariation) potential)) =
        smoothGaugeCoefficientC2CoreLinearMap period hPeriod
          (gaugePotentialFrameCoefficients period hPeriod metric potential) := by
  exact ⟨gaugeCoefficientC2CoreFrameTransport_contDiff period hPeriod,
    gaugeCoefficientC2CoreFrameTransport_lorentzChart period hPeriod metric
      tensor hVariation potential⟩

end

end P0EFTJanusProgramPRegularGeneralMetricC2GaugeCoefficientFrameTransport4D
end JanusFormal
