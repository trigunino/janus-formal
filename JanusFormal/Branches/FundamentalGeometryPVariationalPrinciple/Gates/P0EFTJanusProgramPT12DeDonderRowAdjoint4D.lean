import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DeDonderSmoothCoefficients4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameTensorL2Transport4D

/-! Explicit canonical-volume adjoint tests for the complete de Donder rows. -/
namespace JanusFormal.P0EFTJanusProgramPT12DeDonderRowAdjoint4D
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
open P0EFTJanusProgramPT12CanonicalFrameDerivativeAdjoint4D
open P0EFTJanusProgramPT12CanonicalFirstOrderColumn4D


open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusProgramPGeneralMetricPositiveDualizer4D
open Set

open P0EFTJanusFiniteFrameMetricContraction4D
open P0EFTJanusFiniteFrameMetricTensorTrace4D
open P0EFTJanusFiniteFrameKoszulCoefficients4D
open P0EFTJanusFiniteFrameC2DeDonder4D
open P0EFTJanusFiniteFrameC2KoszulConnection4D
open P0EFTJanusFiniteFrameC2InverseMetricCoefficients4D
open P0EFTJanusFiniteFrameC2MetricTensorTrace4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusMappingTorusGlobalGeneralMetricDeDonder4D
open P0EFTJanusMappingTorusGeneralMetricSmoothTrace4D

open P0EFTJanusProgramPT12DeDonderSmoothCoefficients4D
open P0EFTJanusProgramPT12FrameTensorL2Transport4D

variable (frame : SmoothD8Frame period hPeriod) (metric : SmoothGeneralLorentzMetric period hPeriod)
variable (reference : RegularGeneralLorentzMetric period hPeriod)

def tensorCoefficientsL2 (field : TensorCoefficients period hPeriod frame) : FrameTensorL2 period hPeriod frame :=
  WithLp.toLp 2 fun index => smoothToCanonicalPhysicalBulkL2 period hPeriod (field index.1 index.2)

def tensorSingleTest (row column : Fin frame.count) (test : SmoothScalarField period hPeriod) : FrameTensorL2 period hPeriod frame :=
  PiLp.single 2 (row, column) (smoothToCanonicalPhysicalBulkL2 period hPeriod test)

theorem tensorSingleTest_pairing (field : TensorCoefficients period hPeriod frame)
    (row column : Fin frame.count) (test : SmoothScalarField period hPeriod) :
    inner Real (tensorCoefficientsL2 period hPeriod frame field) (tensorSingleTest period hPeriod frame row column test) =
      inner Real (smoothToCanonicalPhysicalBulkL2 period hPeriod (field row column)) (smoothToCanonicalPhysicalBulkL2 period hPeriod test) := by
  simp [tensorSingleTest, PiLp.inner_apply, PiLp.single_apply, tensorCoefficientsL2, apply_ite]

def deDonderTraceAdjoint (test : SmoothScalarField period hPeriod) : FrameTensorL2 period hPeriod frame :=
  ∑ row, ∑ column, tensorSingleTest period hPeriod frame column row
    (canonicalScalarMul period hPeriod (finiteFrameInverseMetricCoefficient period hPeriod frame metric metric row column) test)

def deDonderCovariantRowAdjoint (derivative first last : Fin frame.count)
    (test : SmoothScalarField period hPeriod) : FrameTensorL2 period hPeriod frame :=
  tensorSingleTest period hPeriod frame first last (canonicalFrameDerivativeAdjoint period hPeriod reference frame derivative test) -
    (∑ index, tensorSingleTest period hPeriod frame index last (canonicalScalarMul period hPeriod
      (finiteFrameKoszulChristoffelCoefficient period hPeriod frame metric metric index derivative first) test)) -
    ∑ index, tensorSingleTest period hPeriod frame first index (canonicalScalarMul period hPeriod
      (finiteFrameKoszulChristoffelCoefficient period hPeriod frame metric metric index derivative last) test)

def deDonderRowAdjoint (last : Fin frame.count) (test : SmoothScalarField period hPeriod) : FrameTensorL2 period hPeriod frame :=
  (∑ derivative, ∑ first, deDonderCovariantRowAdjoint period hPeriod frame metric reference derivative first last
    (canonicalScalarMul period hPeriod (finiteFrameInverseMetricCoefficient period hPeriod frame metric metric derivative first) test)) -
    (1 / 2 : Real) • deDonderTraceAdjoint period hPeriod frame metric (canonicalFrameDerivativeAdjoint period hPeriod reference frame last test)

theorem deDonderTrace_pairing (field : TensorCoefficients period hPeriod frame) (test : SmoothScalarField period hPeriod) :
    inner Real (smoothToCanonicalPhysicalBulkL2 period hPeriod (deDonderTrace period hPeriod frame metric field))
      (smoothToCanonicalPhysicalBulkL2 period hPeriod test) =
      inner Real (tensorCoefficientsL2 period hPeriod frame field) (deDonderTraceAdjoint period hPeriod frame metric test) := by
  simp only [deDonderTrace, deDonderTraceAdjoint, map_sum, sum_inner, inner_sum, tensorSingleTest_pairing]
  apply Finset.sum_congr rfl
  intro row _
  apply Finset.sum_congr rfl
  intro column _
  exact canonicalScalarMul_pairing period hPeriod _ _ _

theorem deDonderCovariantRow_pairing (field : TensorCoefficients period hPeriod frame)
    (derivative first last : Fin frame.count) (test : SmoothScalarField period hPeriod) :
    inner Real (smoothToCanonicalPhysicalBulkL2 period hPeriod
      (deDonderCovariantRow period hPeriod frame metric field derivative first last)) (smoothToCanonicalPhysicalBulkL2 period hPeriod test) =
      inner Real (tensorCoefficientsL2 period hPeriod frame field)
        (deDonderCovariantRowAdjoint period hPeriod frame metric reference derivative first last test) := by
  simp only [deDonderCovariantRow, deDonderCovariantRowAdjoint, map_sub, map_sum,
    inner_sub_left, inner_sub_right, sum_inner, inner_sum, tensorSingleTest_pairing]
  have hDerivative := canonicalFrameDerivativeAdjoint_pairing period hPeriod reference frame derivative (field first last) test
  simp only [canonicalFrameDerivativeL2, LinearMap.comp_apply] at hDerivative
  rw [hDerivative]
  simp_rw [canonicalScalarMul_pairing]

theorem deDonderRow_pairing (field : TensorCoefficients period hPeriod frame)
    (last : Fin frame.count) (test : SmoothScalarField period hPeriod) :
    inner Real (smoothToCanonicalPhysicalBulkL2 period hPeriod (deDonderRow period hPeriod frame metric field last))
      (smoothToCanonicalPhysicalBulkL2 period hPeriod test) =
      inner Real (tensorCoefficientsL2 period hPeriod frame field) (deDonderRowAdjoint period hPeriod frame metric reference last test) := by
  simp only [deDonderRow, deDonderRowAdjoint, map_sub, map_sum, map_smul,
    inner_sub_left, inner_sub_right, sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
  have hDerivative := canonicalFrameDerivativeAdjoint_pairing period hPeriod reference frame last
    (deDonderTrace period hPeriod frame metric field) test
  simp only [canonicalFrameDerivativeL2, LinearMap.comp_apply] at hDerivative
  rw [hDerivative, deDonderTrace_pairing]
  apply congrArg₂ (· - ·) _ rfl
  apply Finset.sum_congr rfl
  intro derivative _
  apply Finset.sum_congr rfl
  intro first _
  exact (canonicalScalarMul_pairing period hPeriod _ _ _).trans
    (deDonderCovariantRow_pairing period hPeriod frame metric reference field derivative first last _)

end
end JanusFormal.P0EFTJanusProgramPT12DeDonderRowAdjoint4D
