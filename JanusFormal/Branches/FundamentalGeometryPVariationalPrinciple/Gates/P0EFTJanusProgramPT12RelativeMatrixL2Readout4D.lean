import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12RelativeTensorFirstJetL24D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12RegularTensorCovectorL24D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12RegularTensorL2Bridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusRegularFrameCanonicalFormalAdjoint4D

/-! Concrete L2 representatives and estimates for smooth regular-frame metric covectors. -/
namespace JanusFormal.P0EFTJanusProgramPT12RelativeMatrixL2Readout4D
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 600000
noncomputable section
open MeasureTheory
open scoped Manifold ContDiff ENNReal
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusL2PTFunctionalSpace4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceStokes4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceWeakStokes4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceLeibniz4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _
local instance : BorelSpace (EffectiveQuotient period hPeriod) where measurable_eq := rfl
local instance : IsFiniteMeasure (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

open scoped BigOperators
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusMappingTorusSmoothDiffeomorphismGhostLieBracket4D
open P0EFTJanusMappingTorusMetricCartanGlobalAction4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D
open P0EFTJanusRegularFrameSymmetricTensorDivergence4D
open P0EFTJanusRegularFrameMetricCartanCoefficients4D
open P0EFTJanusProgramPT12CanonicalFrameDerivativeAdjoint4D
open P0EFTJanusProgramPT12CanonicalFirstOrderColumn4D

open P0EFTJanusProgramPT12SmoothMatrixL24D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusProgramPGeneralMetricPositiveDualizer4D
open Set

open P0EFTJanusProgramPT12FrameTensorL2Transport4D

open P0EFTJanusProgramPT12FrameTensorL2Equiv4D
open P0EFTJanusProgramPT12RegularFrameCartanClosed4D
open P0EFTJanusProgramPT12PairedRegularFrameCartan4D
open P0EFTJanusProgramPT12PairedRegularFrameCartanCore4D
open P0EFTJanusProgramPGlobalGeneralMetricDeDonderGraphCore4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusD9D10ExactFieldContentBridge4D

variable (reference : RegularGeneralLorentzMetric period hPeriod)

open scoped InnerProductSpace
open P0EFTJanusRegularFrameCanonicalFormalAdjoint4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFirstLevel4D
open P0EFTJanusProgramPT12RegularTensorL2Bridge4D

open P0EFTJanusMappingTorusCanonicalPhysicalScalarSmoothL2Density4D

open P0EFTJanusProgramPT12RelativeTensorFirstJetL24D
open P0EFTJanusProgramPT12NativeMaxwellSpatialSmooth4D
open P0EFTJanusProgramPRegularFrameMetricInverse4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0FiniteMatrixProduct4D

/-- Each component of g⁻¹h, continuously read from the actual tensor L2 space. -/
def relativeMatrixComponentL2 (row column : Fin 4) :
    GlobalGeneralMetricTensorFrameL2 period hPeriod →L[Real] CanonicalPhysicalBulkL2 period hPeriod :=
  ∑ middle : Fin 4, (canonicalSmoothMultiplier period hPeriod
    (regularFrameMetricInverseMatrix period hPeriod reference row middle)).comp
      ((PiLp.proj 2 (fun _ : Fin 4 × Fin 4 => CanonicalPhysicalBulkL2 period hPeriod) (middle, column)).comp
        (regularTensorL2Recovery period hPeriod reference))

theorem relativeMatrixComponentL2_smooth
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) (row column : Fin 4) :
    relativeMatrixComponentL2 period hPeriod reference row column
      (globalGeneralMetricTensorFrameL2LinearMap period hPeriod tensor) =
    smoothToCanonicalPhysicalBulkL2 period hPeriod (nativeRelativeMatrixField period hPeriod reference tensor row column) := by
  simp only [relativeMatrixComponentL2, sum_apply, ContinuousLinearMap.comp_apply, regularTensorL2Recovery_smooth]
  change (∑ middle : Fin 4, canonicalSmoothMultiplier period hPeriod
    (regularFrameMetricInverseMatrix period hPeriod reference row middle)
    (smoothToCanonicalPhysicalBulkL2 period hPeriod (generalMetricFrameCoefficient period hPeriod
      (regularGeneralLorentzMetricSmoothD8Frame period hPeriod reference) tensor middle column))) = _
  simp_rw [canonicalSmoothMultiplier_smooth]
  rw [← map_sum]
  apply congrArg (smoothToCanonicalPhysicalBulkL2 period hPeriod)
  ext point
  rw [nativeRelativeMatrixField_apply]
  simp only [smoothScalarFieldFinsetSum_apply]
  rfl

end
end JanusFormal.P0EFTJanusProgramPT12RelativeMatrixL2Readout4D
