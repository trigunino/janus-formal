import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameC2MaxwellCurvature4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameC2InverseMetricCoefficients4D

/-! # Maxwell pairing on the redundant finite C² frame -/

namespace JanusFormal
namespace P0EFTJanusFiniteFrameC2MaxwellPairing4D

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
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0Space4D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusProgramPGeneralMetricC2RelativeEndomorphism4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusFiniteFrameMetricContraction4D
open P0EFTJanusFiniteFrameC2AbelianOperators4D
open P0EFTJanusFiniteFrameC2InverseMetricCoefficients4D
open P0EFTJanusFiniteFrameC2MaxwellCurvature4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
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

private theorem smoothScalarSum_apply
    {ι : Type*} [Fintype ι]
    (fields : ι → SmoothScalarField period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    (∑ index, fields index) point = ∑ index, fields index point := by
  let evaluation : SmoothScalarField period hPeriod →ₗ[Real] Real :=
    { toFun := fun field => field point
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  exact map_sum evaluation fields Finset.univ

private theorem smoothToContinuous_apply
    (field : SmoothScalarField period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    smoothToCanonicalPhysicalContinuousScalar period hPeriod field point = field point := rfl

variable (frame : SmoothD8Frame period hPeriod)
  (baseMetric : SmoothGeneralLorentzMetric period hPeriod)

local notation "MetricCore" =>
  GeneralMetricRelativeC2Core period hPeriod frame baseMetric
local notation "GaugeCore" => FiniteFrameAbelianGaugeC2Core period hPeriod frame
local notation "Input" => MetricCore × GaugeCore

/-- The open metric domain, with unrestricted completed gauge coefficients. -/
def finiteFrameC2MaxwellDomain : Set Input :=
  generalMetricRelativeC2OpenDomain period hPeriod frame baseMetric ×ˢ Set.univ

theorem finiteFrameC2MaxwellDomain_isOpen :
    IsOpen (finiteFrameC2MaxwellDomain period hPeriod frame baseMetric) :=
  (generalMetricRelativeC2OpenDomain_isOpen period hPeriod frame baseMetric).prod isOpen_univ

/-- Double inverse-metric contraction of the projected Cartan curvature. -/
def finiteFrameMaxwellPairingC0 (variation : MetricCore) (potential : GaugeCore) :
    C0Scalar period hPeriod :=
  ∑ component : Fin 2,
    ∑ first : Fin frame.count, ∑ second : Fin frame.count,
      ∑ raisedFirst : Fin frame.count, ∑ raisedSecond : Fin frame.count,
        finiteFrameInverseMetricC0Coefficient period hPeriod frame baseMetric
            first raisedFirst variation *
          finiteFrameInverseMetricC0Coefficient period hPeriod frame baseMetric
            second raisedSecond variation *
          finiteFrameProjectedGaugeCurvatureC0Coefficient period hPeriod frame baseMetric
            potential component first second *
          finiteFrameProjectedGaugeCurvatureC0Coefficient period hPeriod frame baseMetric
            potential component raisedFirst raisedSecond

/-- The completed Maxwell pairing is smooth on the genuine open metric domain. -/
theorem finiteFrameMaxwellPairingC0_contDiffOn :
    ContDiffOn Real ∞
      (fun input : Input =>
        finiteFrameMaxwellPairingC0 period hPeriod frame baseMetric input.1 input.2)
      (finiteFrameC2MaxwellDomain period hPeriod frame baseMetric) := by
  have hInverse (first second : Fin frame.count) : ContDiffOn Real ∞
      (fun input : Input =>
        finiteFrameInverseMetricC0Coefficient period hPeriod frame baseMetric
          first second input.1)
      (finiteFrameC2MaxwellDomain period hPeriod frame baseMetric) :=
    (finiteFrameInverseMetricC0Coefficient_contDiffOn period hPeriod frame baseMetric
      first second).comp contDiff_fst.contDiffOn (fun _ h => h.1)
  have hCurvature (component : Fin 2) (first second : Fin frame.count) :
      ContDiffOn Real ∞
        (fun input : Input =>
          finiteFrameProjectedGaugeCurvatureC0Coefficient period hPeriod frame baseMetric
            input.2 component first second)
        (finiteFrameC2MaxwellDomain period hPeriod frame baseMetric) :=
    (finiteFrameProjectedGaugeCurvatureC0Coefficient_contDiff period hPeriod frame
      baseMetric component first second).comp contDiff_snd |>.contDiffOn
  apply ContDiffOn.sum
  intro component _
  apply ContDiffOn.sum
  intro first _
  apply ContDiffOn.sum
  intro second _
  apply ContDiffOn.sum
  intro raisedFirst _
  apply ContDiffOn.sum
  intro raisedSecond _
  exact (((hInverse first raisedFirst).mul (hInverse second raisedSecond)).mul
    (hCurvature component first second)).mul
      (hCurvature component raisedFirst raisedSecond)

@[simp] theorem finiteFrameProjectedGaugeCurvatureC0Coefficient_zero
    (component : Fin 2) (first second : Fin frame.count) :
    finiteFrameProjectedGaugeCurvatureC0Coefficient period hPeriod frame baseMetric
        0 component first second = 0 := by
  unfold finiteFrameProjectedGaugeCurvatureC0Coefficient
    finiteFrameGaugeCurvatureC0Coefficient
  simp

theorem finiteFrameProjectedGaugeCurvatureC0Coefficient_neg
    (potential : GaugeCore) (component : Fin 2)
    (first second : Fin frame.count) :
    finiteFrameProjectedGaugeCurvatureC0Coefficient period hPeriod frame baseMetric
        (-potential) component first second =
      -finiteFrameProjectedGaugeCurvatureC0Coefficient period hPeriod frame baseMetric
        potential component first second := by
  unfold finiteFrameProjectedGaugeCurvatureC0Coefficient
    finiteFrameGaugeCurvatureC0Coefficient
  simp only [map_neg, Pi.neg_apply, neg_sub]
  apply ContinuousMap.ext
  intro point
  simp only [ContinuousMap.sub_apply, ContinuousMap.neg_apply,
    ContinuousMap.sum_apply, ContinuousMap.mul_apply]
  simp_rw [mul_neg]
  rw [Finset.sum_neg_distrib]
  ring_nf

@[simp] theorem finiteFrameMaxwellPairingC0_zero (variation : MetricCore) :
    finiteFrameMaxwellPairingC0 period hPeriod frame baseMetric variation 0 = 0 := by
  unfold finiteFrameMaxwellPairingC0
  simp

theorem finiteFrameMaxwellPairingC0_neg
    (variation : MetricCore) (potential : GaugeCore) :
    finiteFrameMaxwellPairingC0 period hPeriod frame baseMetric variation (-potential) =
      finiteFrameMaxwellPairingC0 period hPeriod frame baseMetric variation potential := by
  unfold finiteFrameMaxwellPairingC0
  simp_rw [finiteFrameProjectedGaugeCurvatureC0Coefficient_neg]
  apply ContinuousMap.ext
  intro point
  simp only [ContinuousMap.sum_apply, ContinuousMap.mul_apply, ContinuousMap.neg_apply]
  ring_nf

/-- Smooth finite-frame contraction before completion. -/
def finiteFrameSmoothMaxwellPairing
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    SmoothScalarField period hPeriod :=
  ∑ component : Fin 2,
    ∑ first : Fin frame.count, ∑ second : Fin frame.count,
      ∑ raisedFirst : Fin frame.count, ∑ raisedSecond : Fin frame.count,
        smoothScalarFieldMul period hPeriod
          (finiteFrameInverseMetricCoefficient period hPeriod frame baseMetric metric
            first raisedFirst)
          (smoothScalarFieldMul period hPeriod
            (finiteFrameInverseMetricCoefficient period hPeriod frame baseMetric metric
              second raisedSecond)
            (smoothScalarFieldMul period hPeriod
              (finiteFrameSmoothGaugeCurvatureCoefficient period hPeriod frame potential
                component first second)
              (finiteFrameSmoothGaugeCurvatureCoefficient period hPeriod frame potential
                component raisedFirst raisedSecond)))

/-- Smooth inputs recover exactly the same finite-frame contraction. -/
theorem finiteFrameMaxwellPairingC0_smooth
    (variation : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (hMetric : metric.tensor = baseMetric.tensor + variation)
    (hVariation :
      smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric variation ∈
        generalMetricRelativeC2OpenDomain period hPeriod frame baseMetric)
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    finiteFrameMaxwellPairingC0 period hPeriod frame baseMetric
        (smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric variation)
        (finiteFrameSmoothAbelianGaugeC2Coefficients period hPeriod frame potential) =
      smoothToCanonicalPhysicalContinuousScalar period hPeriod
        (finiteFrameSmoothMaxwellPairing period hPeriod frame baseMetric metric potential) := by
  apply ContinuousMap.ext
  intro point
  simp only [finiteFrameMaxwellPairingC0, finiteFrameSmoothMaxwellPairing,
    ContinuousMap.sum_apply, ContinuousMap.mul_apply,
    finiteFrameInverseMetricC0Coefficient_smooth period hPeriod frame baseMetric
      variation metric hMetric hVariation,
    finiteFrameProjectedGaugeCurvatureC0Coefficient_smooth,
    smoothToContinuous_apply, smoothScalarSum_apply, smoothScalarFieldMul_apply]
  ring_nf

end
end P0EFTJanusFiniteFrameC2MaxwellPairing4D
end JanusFormal
