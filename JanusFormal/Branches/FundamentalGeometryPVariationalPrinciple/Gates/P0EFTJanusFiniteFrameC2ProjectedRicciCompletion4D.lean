import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameC2GlobalInverseProjectedScalar4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameCovectorC2Projection4D

/-! # C² completion of the projected finite-frame Ricci coefficients -/

namespace JanusFormal
namespace P0EFTJanusFiniteFrameC2ProjectedRicciCompletion4D

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
open P0EFTJanusProgramPGeneralMetricPositiveDualizer4D
open P0EFTJanusProgramPGeneralMetricC2VariationCore4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusFiniteFrameCovariantTensorDivergence4D
open P0EFTJanusFiniteFrameCovectorC2Projection4D
open P0EFTJanusFiniteFrameC2ScalarCurvature4D
open P0EFTJanusFiniteFrameC2ScalarCurvatureSmoothCoefficients4D
open P0EFTJanusFiniteFrameC2ProjectedRicciIntrinsic4D

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

/-- Smooth projected Ricci coefficient obtained by inserting the canonical dual projection. -/
def finiteFrameSmoothProjectedRicciCoefficient
    (metric : SmoothGeneralLorentzMetric period hPeriod) (first second : Fin frame.count) :
    SmoothScalarField period hPeriod :=
  ∑ traced : Fin frame.count, ∑ upper : Fin frame.count,
    smoothScalarFieldMul period hPeriod
      (finiteFrameCovectorProjectionCoefficient period hPeriod frame baseMetric upper traced)
      (finiteFrameSmoothRiemannCoefficient period hPeriod frame baseMetric metric
        upper first traced second)

/-- C⁰ realization of the projected Ricci coefficient on the completed C² chart. -/
def finiteFrameProjectedRicciC0Coefficient (first second : Fin frame.count)
    (variation : Model) : C0Scalar period hPeriod :=
  ∑ traced : Fin frame.count, ∑ upper : Fin frame.count,
    smoothToCanonicalPhysicalContinuousScalar period hPeriod
        (finiteFrameCovectorProjectionCoefficient period hPeriod frame baseMetric upper traced) *
      finiteFrameRiemannC0Coefficient period hPeriod frame baseMetric
        upper first traced second variation

theorem finiteFrameProjectedRicciC0Coefficient_contDiffOn
    (first second : Fin frame.count) :
    ContDiffOn Real ∞
      (finiteFrameProjectedRicciC0Coefficient period hPeriod frame baseMetric first second) Domain := by
  apply ContDiffOn.sum
  intro traced _
  apply ContDiffOn.sum
  intro upper _
  exact contDiffOn_const.mul
    (finiteFrameRiemannC0Coefficient_contDiffOn period hPeriod frame baseMetric
      upper first traced second)

/-- On smooth metrics, the completed projected coefficient is the smooth projected coefficient. -/
theorem finiteFrameProjectedRicciC0Coefficient_smooth
    (variation : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (hMetric : metric.tensor = baseMetric.tensor + variation)
    (hVariation : smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric variation ∈ Domain)
    (first second : Fin frame.count) :
    finiteFrameProjectedRicciC0Coefficient period hPeriod frame baseMetric first second
        (smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric variation) =
      smoothToCanonicalPhysicalContinuousScalar period hPeriod
        (finiteFrameSmoothProjectedRicciCoefficient period hPeriod frame baseMetric metric first second) := by
  apply ContinuousMap.ext
  intro point
  change finiteFrameProjectedRicciC0Coefficient period hPeriod frame baseMetric first second
      (smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric variation) point =
    finiteFrameSmoothProjectedRicciCoefficient period hPeriod frame baseMetric metric first second point
  simp only [finiteFrameProjectedRicciC0Coefficient,
    finiteFrameSmoothProjectedRicciCoefficient, ContinuousMap.sum_apply,
    ContinuousMap.mul_apply,
    P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0FiniteMatrixProduct4D.smoothScalarFieldFinsetSum_apply,
    smoothScalarFieldMul_apply]
  apply Finset.sum_congr rfl
  intro traced _
  apply Finset.sum_congr rfl
  intro upper _
  rw [finiteFrameRiemannC0Coefficient_smooth period hPeriod frame baseMetric variation metric
    hMetric hVariation upper first traced second]
  rfl

private theorem finiteFrameLocalCoefficientAt_pulledVector
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : CoordinateVector)
    (dualIndex vectorIndex : Fin frame.count) :
    finiteFrameLocalCoefficientAt period hPeriod frame baseMetric patch coordinate dualIndex
        (finiteFramePulledVector period hPeriod frame patch vectorIndex coordinate) =
      finiteFrameCovectorProjectionCoefficient period hPeriod frame baseMetric vectorIndex dualIndex
        (patch.coordinateMap coordinate) := by
  unfold finiteFrameLocalCoefficientAt
  change generalMetricFiniteFrameCoefficientAt period hPeriod frame baseMetric
      (patch.coordinateMap coordinate) dualIndex
      (((Pi.basisFun Real (Fin 4)).equiv (patch.frame coordinate) (Equiv.refl (Fin 4)))
        (finiteFramePulledVector period hPeriod frame patch vectorIndex coordinate)) = _
  rw [← coordinateMap_mfderiv_eq_frameEquiv period hPeriod,
    coordinateMap_mfderiv_finiteFramePulledVector period hPeriod frame patch coordinate vectorIndex]
  rfl

/-- The global smooth projection has the chart-local projected Ricci value. -/
theorem finiteFrameSmoothProjectedRicciCoefficient_eq_local
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : CoordinateVector)
    (first second : Fin frame.count) :
    finiteFrameSmoothProjectedRicciCoefficient period hPeriod frame baseMetric metric first second
        (patch.coordinateMap coordinate) =
      finiteFrameProjectedRicciCoefficientAt period hPeriod frame baseMetric metric patch coordinate
        first second := by
  unfold finiteFrameSmoothProjectedRicciCoefficient finiteFrameProjectedRicciCoefficientAt
  simp only [P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0FiniteMatrixProduct4D.smoothScalarFieldFinsetSum_apply,
    smoothScalarFieldMul_apply, map_sum, map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro traced _
  apply Finset.sum_congr rfl
  intro upper _
  rw [finiteFrameLocalCoefficientAt_pulledVector period hPeriod frame baseMetric patch coordinate
    traced upper]
  ring

end
end P0EFTJanusFiniteFrameC2ProjectedRicciCompletion4D
end JanusFormal
