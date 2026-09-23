import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12RegularGhostL2Transport4D

/-! Bounded changes of finite generating-frame coordinates for actual covectors. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameCovectorL2Transport4D
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

open P0EFTJanusEffectiveD8SmoothCovectorFieldFunctor4D
open P0EFTJanusMappingTorusGlobalGeneralMetricSymmetricTensorDivergence4D

variable (source target : SmoothD8Frame period hPeriod)
variable (reference : SmoothGeneralLorentzMetric period hPeriod)

abbrev ActualSmoothCovector := EffectiveD8SmoothCovectorField (generalMetricDivergenceBackground period hPeriod)
abbrev FrameCovectorL2 (frame : SmoothD8Frame period hPeriod) :=
  PiLp 2 (fun _ : Fin frame.count => CanonicalPhysicalBulkL2 period hPeriod)

def frameCovectorCoefficient (frame : SmoothD8Frame period hPeriod)
    (covector : ActualSmoothCovector period hPeriod) (row : Fin frame.count) : SmoothScalarField period hPeriod where
  toFun point := covector point (frame.vectorAt point row)
  contMDiff_toFun := by
    have hApplied := covector.contMDiff.clm_bundle_apply (frame.contMDiff_vector row)
    intro point
    have hAppliedAt := hApplied point
    rw [Bundle.contMDiffAt_section] at hAppliedAt
    simpa using hAppliedAt

def frameCovectorCoefficientLinearMap (frame : SmoothD8Frame period hPeriod) (row : Fin frame.count) :
    ActualSmoothCovector period hPeriod →ₗ[Real] SmoothScalarField period hPeriod where
  toFun covector := frameCovectorCoefficient period hPeriod frame covector row
  map_add' _ _ := by apply SmoothQuotientField.ext period hPeriod Real; intro point; rfl
  map_smul' _ _ := by apply SmoothQuotientField.ext period hPeriod Real; intro point; rfl

def frameCovectorL2 (frame : SmoothD8Frame period hPeriod) :
    ActualSmoothCovector period hPeriod →ₗ[Real] FrameCovectorL2 period hPeriod frame where
  toFun covector := WithLp.toLp 2 fun row => smoothToCanonicalPhysicalBulkL2 period hPeriod
    (frameCovectorCoefficientLinearMap period hPeriod frame row covector)
  map_add' first second := by
    apply PiLp.ext
    intro row
    exact ((smoothToCanonicalPhysicalBulkL2 period hPeriod).comp
      (frameCovectorCoefficientLinearMap period hPeriod frame row)).map_add first second
  map_smul' scalar field := by
    apply PiLp.ext
    intro row
    exact ((smoothToCanonicalPhysicalBulkL2 period hPeriod).comp
      (frameCovectorCoefficientLinearMap period hPeriod frame row)).map_smul scalar field

def frameCovectorChangeMatrix : Fin target.count → Fin source.count → SmoothScalarField period hPeriod :=
  fun row column => generalMetricFiniteFrameCoefficient period hPeriod source reference
    (frameTangentField period hPeriod target row) column

theorem frameCovectorChangeMatrix_smooth (covector : ActualSmoothCovector period hPeriod)
    (row : Fin target.count) :
    frameCovectorCoefficient period hPeriod target covector row =
      ∑ column, canonicalScalarMul period hPeriod
        (frameCovectorChangeMatrix period hPeriod source target reference row column)
        (frameCovectorCoefficient period hPeriod source covector column) := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  rw [canonicalScalar_sum_apply]
  change covector point (target.vectorAt point row) =
    ∑ column, generalMetricFiniteFrameCoefficientAt period hPeriod source reference point column
      (target.vectorAt point row) * covector point (source.vectorAt point column)
  calc
    _ = covector point (∑ column, generalMetricFiniteFrameCoefficientAt period hPeriod source reference point column
          (target.vectorAt point row) • source.vectorAt point column) :=
      congrArg (covector point) (generalMetricFiniteFrameCoefficientAt_reconstructs period hPeriod source reference point _)
    _ = _ := by simp only [map_sum, map_smul, smul_eq_mul]

def frameCovectorL2Transport : FrameCovectorL2 period hPeriod source →L[Real] FrameCovectorL2 period hPeriod target :=
  canonicalSmoothMatrixL2 period hPeriod (frameCovectorChangeMatrix period hPeriod source target reference)

theorem frameCovectorL2Transport_smooth (covector : ActualSmoothCovector period hPeriod) :
    frameCovectorL2Transport period hPeriod source target reference (frameCovectorL2 period hPeriod source covector) =
      frameCovectorL2 period hPeriod target covector := by
  apply PiLp.ext
  intro row
  exact (canonicalSmoothMatrixL2_smooth period hPeriod
    (frameCovectorChangeMatrix period hPeriod source target reference)
    (fun column => frameCovectorCoefficient period hPeriod source covector column) row).trans
    (congrArg (smoothToCanonicalPhysicalBulkL2 period hPeriod)
      (frameCovectorChangeMatrix_smooth period hPeriod source target reference covector row).symm)

end
end JanusFormal.P0EFTJanusProgramPT12FrameCovectorL2Transport4D
