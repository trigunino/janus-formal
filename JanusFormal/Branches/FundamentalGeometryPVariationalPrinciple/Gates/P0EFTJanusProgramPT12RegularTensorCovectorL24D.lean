import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12RegularTensorL2Bridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusRegularFrameCanonicalFormalAdjoint4D

/-! Concrete L2 representatives and estimates for smooth regular-frame metric covectors. -/
namespace JanusFormal.P0EFTJanusProgramPT12RegularTensorCovectorL24D
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

/-- The sixteen real L2 coefficients of a metric covector. -/
def regularTensorCovectorL2 (coefficients : Fin 4 → Fin 4 → SmoothScalarField period hPeriod) :
    CartanTensorL2 period hPeriod :=
  WithLp.toLp 2 fun row => smoothToCanonicalPhysicalBulkL2 period hPeriod (coefficients row.1 row.2)

theorem regularTensorCovectorL2_pairing
    (coefficients : Fin 4 → Fin 4 → SmoothScalarField period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    inner Real (regularTensorCovectorL2 period hPeriod coefficients)
      (regularTensorL2 period hPeriod reference tensor) =
    ∫ point, generalMetricTensorPairingAt period hPeriod reference.metric
      (regularFrameCovariantCoefficientTensor period hPeriod reference coefficients) tensor point
      ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod := by
  have hInt : ∀ row : Fin 4 × Fin 4, Integrable (fun point => coefficients row.1 row.2 point *
      generalMetricFrameCoefficient period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod reference) tensor row.1 row.2 point)
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
    intro row
    exact ((coefficients row.1 row.2).contMDiff_toFun.continuous.mul
      (generalMetricFrameCoefficient period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod reference) tensor row.1 row.2).contMDiff_toFun.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [PiLp.inner_apply]
  change (∑ row : Fin 4 × Fin 4, inner Real
    (smoothToCanonicalPhysicalBulkL2 period hPeriod (coefficients row.1 row.2))
    (smoothToCanonicalPhysicalBulkL2 period hPeriod
      (generalMetricFrameCoefficient period hPeriod (regularGeneralLorentzMetricSmoothD8Frame period hPeriod reference) tensor row.1 row.2))) = _
  simp_rw [canonicalScalarL2_inner]
  rw [← integral_finsetSum Finset.univ (fun row _ => hInt row)]
  apply integral_congr_ae
  filter_upwards [] with point
  rw [regularFrameCovariantCoefficientTensor_pairing, Fintype.sum_prod_type]
  rfl

/-- A covector on the actual tensor L2 coordinates, not on a stronger graph norm. -/
def regularTensorCovectorActualL2 (coefficients : Fin 4 → Fin 4 → SmoothScalarField period hPeriod) :
    GlobalGeneralMetricTensorFrameL2 period hPeriod :=
  (regularTensorL2Recovery period hPeriod reference).adjoint (regularTensorCovectorL2 period hPeriod coefficients)

theorem regularTensorCovectorActualL2_pairing
    (coefficients : Fin 4 → Fin 4 → SmoothScalarField period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    inner Real (regularTensorCovectorActualL2 period hPeriod reference coefficients)
      (globalGeneralMetricTensorFrameL2LinearMap period hPeriod tensor) =
    ∫ point, generalMetricTensorPairingAt period hPeriod reference.metric
      (regularFrameCovariantCoefficientTensor period hPeriod reference coefficients) tensor point
      ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod := by
  unfold regularTensorCovectorActualL2
  rw [ContinuousLinearMap.adjoint_inner_left, regularTensorL2Recovery_smooth,
    regularTensorCovectorL2_pairing]

theorem regularTensorCovectorActualL2_bound
    (coefficients : Fin 4 → Fin 4 → SmoothScalarField period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    ‖∫ point, generalMetricTensorPairingAt period hPeriod reference.metric
      (regularFrameCovariantCoefficientTensor period hPeriod reference coefficients) tensor point
      ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod‖ ≤
    ‖regularTensorCovectorActualL2 period hPeriod reference coefficients‖ *
      ‖globalGeneralMetricTensorFrameL2LinearMap period hPeriod tensor‖ := by
  rw [← regularTensorCovectorActualL2_pairing]
  exact norm_inner_le_norm _ _

end
end JanusFormal.P0EFTJanusProgramPT12RegularTensorCovectorL24D
