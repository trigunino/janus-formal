import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameC2ProjectedRicciCompletion4D

/-! # C² completion of projected finite-frame scalar curvature -/

namespace JanusFormal
namespace P0EFTJanusFiniteFrameC2ProjectedScalarCompletion4D

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0Space4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D
open P0EFTJanusMappingTorusCanonicalHolonomicScalarCurvatureNaturality4D
open P0EFTJanusMappingTorusIntrinsicEinsteinHilbertCurvature4D
open P0EFTJanusProgramPGeneralMetricPositiveDualizer4D
open P0EFTJanusProgramPGeneralMetricC2VariationCore4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusFiniteFrameMetricContraction4D
open P0EFTJanusFiniteFrameC2InverseMetricCoefficients4D
open P0EFTJanusFiniteFrameC2GlobalInverseProjectedScalar4D
open P0EFTJanusFiniteFrameC2ProjectedRicciCompletion4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev CoordinateVector :=
  P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4
private abbrev C2Scalar := CanonicalPhysicalScalarC2JetCore period hPeriod
private abbrev C0Scalar := C(EffectiveQuotient period hPeriod, Real)
local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance : NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (C2Scalar period hPeriod) := inferInstance
local instance : CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod

variable (frame : SmoothD8Frame period hPeriod)
  (baseMetric : SmoothGeneralLorentzMetric period hPeriod)
local notation "Model" => GeneralMetricRelativeC2Core period hPeriod frame baseMetric
local notation "Domain" => generalMetricRelativeC2OpenDomain period hPeriod frame baseMetric

/-- Smooth scalar curvature formed from global inverse coefficients and projected Ricci. -/
def finiteFrameSmoothProjectedScalarCurvature
    (metric : SmoothGeneralLorentzMetric period hPeriod) : SmoothScalarField period hPeriod :=
  ∑ first : Fin frame.count, ∑ second : Fin frame.count,
    smoothScalarFieldMul period hPeriod
      (finiteFrameInverseMetricCoefficient period hPeriod frame baseMetric metric first second)
      (finiteFrameSmoothProjectedRicciCoefficient period hPeriod frame baseMetric metric first second)

/-- C⁰ realization of projected scalar curvature on the completed C² chart. -/
def finiteFrameProjectedScalarCurvatureC0 (variation : Model) : C0Scalar period hPeriod :=
  ∑ first : Fin frame.count, ∑ second : Fin frame.count,
    finiteFrameInverseMetricC0Coefficient period hPeriod frame baseMetric first second variation *
      finiteFrameProjectedRicciC0Coefficient period hPeriod frame baseMetric first second variation

theorem finiteFrameProjectedScalarCurvatureC0_contDiffOn_two :
    ContDiffOn Real 2
      (finiteFrameProjectedScalarCurvatureC0 period hPeriod frame baseMetric) Domain := by
  apply ContDiffOn.sum
  intro first _
  apply ContDiffOn.sum
  intro second _
  exact ((finiteFrameInverseMetricC0Coefficient_contDiffOn period hPeriod frame baseMetric
    first second).of_le (WithTop.coe_le_coe.mpr le_top)).mul
    ((finiteFrameProjectedRicciC0Coefficient_contDiffOn period hPeriod frame baseMetric
      first second).of_le (WithTop.coe_le_coe.mpr le_top))

/-- Smooth inputs evaluate to the global smooth projected scalar curvature. -/
theorem finiteFrameProjectedScalarCurvatureC0_smooth
    (variation : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (hMetric : metric.tensor = baseMetric.tensor + variation)
    (hVariation : smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric variation ∈ Domain) :
    finiteFrameProjectedScalarCurvatureC0 period hPeriod frame baseMetric
        (smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric variation) =
      smoothToCanonicalPhysicalContinuousScalar period hPeriod
        (finiteFrameSmoothProjectedScalarCurvature period hPeriod frame baseMetric metric) := by
  apply ContinuousMap.ext
  intro point
  change finiteFrameProjectedScalarCurvatureC0 period hPeriod frame baseMetric
      (smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric variation) point =
    finiteFrameSmoothProjectedScalarCurvature period hPeriod frame baseMetric metric point
  simp only [finiteFrameProjectedScalarCurvatureC0, finiteFrameSmoothProjectedScalarCurvature,
    ContinuousMap.sum_apply, ContinuousMap.mul_apply, smoothScalarFieldMul_apply,
    P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0FiniteMatrixProduct4D.smoothScalarFieldFinsetSum_apply]
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  rw [finiteFrameInverseMetricC0Coefficient_smooth period hPeriod frame baseMetric variation metric
      hMetric hVariation,
    finiteFrameProjectedRicciC0Coefficient_smooth period hPeriod frame baseMetric variation metric
      hMetric hVariation]
  rfl

/-- The global smooth projected scalar has the local global-inverse contraction value. -/
theorem finiteFrameSmoothProjectedScalarCurvature_eq_local
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : CoordinateVector) :
    finiteFrameSmoothProjectedScalarCurvature period hPeriod frame baseMetric metric
        (patch.coordinateMap coordinate) =
      finiteFrameGlobalInverseProjectedScalarCurvatureAt period hPeriod frame baseMetric metric patch
        coordinate := by
  unfold finiteFrameSmoothProjectedScalarCurvature
    finiteFrameGlobalInverseProjectedScalarCurvatureAt
  simp only [P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0FiniteMatrixProduct4D.smoothScalarFieldFinsetSum_apply,
    smoothScalarFieldMul_apply]
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  rw [finiteFrameSmoothProjectedRicciCoefficient_eq_local period hPeriod frame baseMetric metric patch
    coordinate first second]

/-- The completed smooth scalar curvature is intrinsically the Levi-Civita scalar curvature. -/
theorem finiteFrameSmoothProjectedScalarCurvature_eq_intrinsic
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : CoordinateVector) :
    finiteFrameSmoothProjectedScalarCurvature period hPeriod frame baseMetric metric
        (patch.coordinateMap coordinate) =
      localScalarCurvature period hPeriod metric patch coordinate := by
  rw [finiteFrameSmoothProjectedScalarCurvature_eq_local period hPeriod frame baseMetric metric patch
    coordinate]
  exact finiteFrameGlobalInverseProjectedScalarCurvatureAt_eq_intrinsic period hPeriod frame baseMetric
    metric patch coordinate

end
end P0EFTJanusFiniteFrameC2ProjectedScalarCompletion4D
end JanusFormal
