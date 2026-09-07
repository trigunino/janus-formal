import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusStrongMaxwellMetricCenterFirstVariation4D

/-! # Smooth intrinsic representative of the metric-induced gauge velocity

The transpose-root velocity is represented by an actual smooth potential.
Its completed frame coefficients are exactly the velocity in the mobile
Maxwell derivative, with the positive factor one half retained.
-/
namespace JanusFormal
namespace P0EFTJanusMetricInducedSmoothGaugeVelocity4D
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 600000
noncomputable section
open scoped Manifold ContDiff BigOperators
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
open P0EFTJanusProgramPGlobalGaugeTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPGeneralMetricC2RelativeEndomorphism4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2MaxwellStressDerivative4D
open P0EFTJanusProgramPRegularFrameGaugePotentialReconstruction4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalMetricGaugeCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2GaugeCoefficientFrameTransport4D
open P0EFTJanusProgramPRegularGeneralMetricC2GaugeCoefficientMaxwellAction4D
open P0EFTJanusStrongMaxwellMetricCenterFirstVariation4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev C2Scalar := CanonicalPhysicalScalarC2JetCore period hPeriod
local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance : NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (C2Scalar period hPeriod) := inferInstance

def metricInducedGaugeCoefficientEntry
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (baseIndex : Fin 4) (component : Fin 2) : SmoothQuotientField period hPeriod Real :=
  (1 / 2 : Real) • ∑ row : Fin 4,
    smoothScalarFieldMul period hPeriod
      (smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
        metric.metric tensor row baseIndex)
      (regularFrameGaugeCoefficient period hPeriod
        (gaugePotentialFrameCoefficients period hPeriod metric potential) (row, component))

def metricInducedGaugeCoefficients
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    SmoothQuotientField period hPeriod GaugeFiber where
  toFun := fun point => (EuclideanSpace.equiv (Fin 4 × Fin 2) Real).symm
    (fun index => metricInducedGaugeCoefficientEntry period hPeriod metric tensor potential
      index.1 index.2 point)
  contMDiff_toFun := by
    apply (EuclideanSpace.equiv (Fin 4 × Fin 2) Real).symm.toContinuousLinearMap.contMDiff.comp
    rw [contMDiff_pi_space]
    intro index
    exact (metricInducedGaugeCoefficientEntry period hPeriod metric tensor potential
      index.1 index.2).contMDiff_toFun

theorem metricInducedGaugeCoefficient_represented
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (row : Fin 4) (component : Fin 2) :
    regularFrameGaugeCoefficient period hPeriod
        (metricInducedGaugeCoefficients period hPeriod metric tensor potential) (row, component) =
      metricInducedGaugeCoefficientEntry period hPeriod metric tensor potential row component := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  rfl

/-- The smooth packet has exactly the completed velocity already derived
from the mobile frame; no additional tangent is postulated. -/
theorem metricInducedGaugeCoefficients_toC2
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    smoothGaugeCoefficientC2CoreLinearMap period hPeriod
        (metricInducedGaugeCoefficients period hPeriod metric tensor potential) =
      (1 / 2 : Real) • gaugeCoefficientC2CoreFrameTransport period hPeriod
        (regularGeneralMetricC2GaugeCoefficientMetricMatrixCLM period hPeriod metric
          (regularGeneralMetricC2SmoothDirection period hPeriod metric tensor))
        (smoothGaugeCoefficientC2CoreLinearMap period hPeriod
          (gaugePotentialFrameCoefficients period hPeriod metric potential)) := by
  funext baseIndex component
  rw [smoothGaugeCoefficientC2CoreLinearMap_apply, metricInducedGaugeCoefficient_represented]
  rw [metricInducedGaugeCoefficientEntry, map_smul, map_sum]
  change (1 / 2 : Real) • (_ : C2Scalar period hPeriod) =
    (1 / 2 : Real) • (_ : C2Scalar period hPeriod)
  apply congrArg (fun value : C2Scalar period hPeriod => (1 / 2 : Real) • value)
  apply Finset.sum_congr rfl
  intro row _
  exact (canonicalPhysicalScalarC2JetCoreProduct_smooth period hPeriod _ _).symm

def metricInducedGaugePotential
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    SmoothAbelianGaugePotential period hPeriod :=
  regularFrameGaugePotentialFromCoefficients period hPeriod metric
    (metricInducedGaugeCoefficients period hPeriod metric tensor potential)

theorem metricInducedGaugePotential_frame
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2) (point : EffectiveQuotient period hPeriod) (row : Fin 4) :
    (metricInducedGaugePotential period hPeriod metric tensor potential).toFun
        component point (metric.frame row point) =
      metricInducedGaugeCoefficientEntry period hPeriod metric tensor potential row component point :=
  regularFrameGaugeCovectorFromCoefficients_frame period hPeriod metric
    (metricInducedGaugeCoefficients period hPeriod metric tensor potential) component point row

theorem metricInducedGaugePotential_toC2
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    smoothGaugeCoefficientC2CoreLinearMap period hPeriod
        (gaugePotentialFrameCoefficients period hPeriod metric
          (metricInducedGaugePotential period hPeriod metric tensor potential)) =
      regularGeneralMetricC2InducedGaugeVelocityCLM period hPeriod metric
        (smoothGaugeCoefficientC2CoreLinearMap period hPeriod
          (gaugePotentialFrameCoefficients period hPeriod metric potential))
        (regularGeneralMetricC2SmoothDirection period hPeriod metric tensor) := by
  rw [metricInducedGaugePotential, gaugePotentialFrameCoefficients_reconstructed,
    regularGeneralMetricC2InducedGaugeVelocityCLM_apply]
  exact metricInducedGaugeCoefficients_toC2 period hPeriod metric tensor potential

end
end P0EFTJanusMetricInducedSmoothGaugeVelocity4D
end JanusFormal
