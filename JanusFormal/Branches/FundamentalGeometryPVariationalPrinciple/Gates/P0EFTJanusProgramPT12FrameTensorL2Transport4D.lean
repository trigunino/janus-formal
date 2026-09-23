import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12RegularGhostL2Transport4D

/-! Bounded changes of finite generating-frame coordinates for actual symmetric tensors. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameTensorL2Transport4D
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

variable (source target : SmoothD8Frame period hPeriod)
variable (reference : SmoothGeneralLorentzMetric period hPeriod)

abbrev FrameTensorL2 (frame : SmoothD8Frame period hPeriod) :=
  PiLp 2 (fun _ : Fin frame.count × Fin frame.count => CanonicalPhysicalBulkL2 period hPeriod)

def frameTensorCoefficientLinearMap (frame : SmoothD8Frame period hPeriod)
    (row : Fin frame.count × Fin frame.count) :
    SmoothSymmetricCovariantTwoTensor period hPeriod →ₗ[Real] SmoothScalarField period hPeriod where
  toFun tensor := generalMetricFrameCoefficient period hPeriod frame tensor row.1 row.2
  map_add' _ _ := by apply SmoothQuotientField.ext period hPeriod Real; intro point; rfl
  map_smul' _ _ := by apply SmoothQuotientField.ext period hPeriod Real; intro point; rfl

def frameTensorL2 (frame : SmoothD8Frame period hPeriod) :
    SmoothSymmetricCovariantTwoTensor period hPeriod →ₗ[Real] FrameTensorL2 period hPeriod frame where
  toFun tensor := WithLp.toLp 2 fun row => smoothToCanonicalPhysicalBulkL2 period hPeriod
    (frameTensorCoefficientLinearMap period hPeriod frame row tensor)
  map_add' first second := by
    apply PiLp.ext
    intro row
    exact ((smoothToCanonicalPhysicalBulkL2 period hPeriod).comp
      (frameTensorCoefficientLinearMap period hPeriod frame row)).map_add first second
  map_smul' scalar tensor := by
    apply PiLp.ext
    intro row
    exact ((smoothToCanonicalPhysicalBulkL2 period hPeriod).comp
      (frameTensorCoefficientLinearMap period hPeriod frame row)).map_smul scalar tensor

def frameTensorChangeMatrix :
    (Fin target.count × Fin target.count) → (Fin source.count × Fin source.count) →
      SmoothScalarField period hPeriod :=
  fun row column => canonicalScalarMul period hPeriod
    (generalMetricFiniteFrameCoefficient period hPeriod source reference
      (frameTangentField period hPeriod target row.1) column.1)
    (generalMetricFiniteFrameCoefficient period hPeriod source reference
      (frameTangentField period hPeriod target row.2) column.2)

theorem frameTensorChangeMatrix_smooth (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (row : Fin target.count × Fin target.count) :
    generalMetricFrameCoefficient period hPeriod target tensor row.1 row.2 =
      ∑ column, canonicalScalarMul period hPeriod
        (frameTensorChangeMatrix period hPeriod source target reference row column)
        (generalMetricFrameCoefficient period hPeriod source tensor column.1 column.2) := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  rw [canonicalScalar_sum_apply]
  change tensor.tensor point (target.vectorAt point row.1) (target.vectorAt point row.2) =
    ∑ column : Fin source.count × Fin source.count,
      (generalMetricFiniteFrameCoefficientAt period hPeriod source reference point column.1
        (target.vectorAt point row.1) *
      generalMetricFiniteFrameCoefficientAt period hPeriod source reference point column.2
        (target.vectorAt point row.2)) *
      tensor.tensor point (source.vectorAt point column.1) (source.vectorAt point column.2)
  rw [Fintype.sum_prod_type]
  calc
    _ = tensor.tensor point
        (∑ first, generalMetricFiniteFrameCoefficientAt period hPeriod source reference point first
          (target.vectorAt point row.1) • source.vectorAt point first)
        (∑ second, generalMetricFiniteFrameCoefficientAt period hPeriod source reference point second
          (target.vectorAt point row.2) • source.vectorAt point second) :=
      congrArg₂ (fun first second => tensor.tensor point first second)
        (generalMetricFiniteFrameCoefficientAt_reconstructs period hPeriod source reference point _)
        (generalMetricFiniteFrameCoefficientAt_reconstructs period hPeriod source reference point _)
    _ = _ := by
      simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul,
        Finset.mul_sum]
      conv_lhs => rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro first _
      apply Finset.sum_congr rfl
      intro second _
      ring

def frameTensorL2Transport : FrameTensorL2 period hPeriod source →L[Real] FrameTensorL2 period hPeriod target :=
  canonicalSmoothMatrixL2 period hPeriod (frameTensorChangeMatrix period hPeriod source target reference)

theorem frameTensorL2Transport_smooth (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    frameTensorL2Transport period hPeriod source target reference (frameTensorL2 period hPeriod source tensor) =
      frameTensorL2 period hPeriod target tensor := by
  apply PiLp.ext
  intro row
  exact (canonicalSmoothMatrixL2_smooth period hPeriod
    (frameTensorChangeMatrix period hPeriod source target reference)
    (fun column => generalMetricFrameCoefficient period hPeriod source tensor column.1 column.2) row).trans
    (congrArg (smoothToCanonicalPhysicalBulkL2 period hPeriod)
      (frameTensorChangeMatrix_smooth period hPeriod source target reference tensor row).symm)

end
end JanusFormal.P0EFTJanusProgramPT12FrameTensorL2Transport4D
