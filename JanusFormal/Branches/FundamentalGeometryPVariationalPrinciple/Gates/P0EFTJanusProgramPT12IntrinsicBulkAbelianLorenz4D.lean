import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicBulkAbelianBRestriction4D

/-! The frozen, projected Lorenz operator and the actual bounded B--A pairing. -/
namespace JanusFormal.P0EFTJanusProgramPT12IntrinsicBulkAbelianLorenz4D
set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0Space4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGlobalGeneralMetricAbelianLorenzCodifferential4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusFiniteFrameScalarC2Derivatives4D P0EFTJanusFiniteFrameC2InverseMetricCoefficients4D
open P0EFTJanusFiniteFrameC2KoszulConnection4D P0EFTJanusFiniteFrameCovectorC2Projection4D
open P0EFTJanusFiniteFrameC2AbelianOperators4D P0EFTJanusFiniteFrameC2AbelianBRSTAction4D
open P0EFTJanusFiniteFrameDiffeomorphismBRSTSmoothFeatures4D
open P0EFTJanusProgramPT12IntrinsicBulkGeometry4D P0EFTJanusProgramPT12IntrinsicBulkAbelianBRestriction4D
open P0EFTJanusProgramPGlobalCandidateAGeometry4D
attribute [local instance 2000]
  NonUnitalNormedRing.toNormedAddCommGroup NormedAlgebra.toNormedSpace

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev Q := MappingTorus (reflectedSphereData period hPeriod)
local instance : ChartedSpace CoverModel (Q period hPeriod) := reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (Q period hPeriod) := reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (Q period hPeriod) := reflectedSphereQuotientCompactSpace period hPeriod
local instance : NormedAddCommGroup (CanonicalPhysicalScalarC2JetCore period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (CanonicalPhysicalScalarC2JetCore period hPeriod) := inferInstance
local notation "frame" => finiteSmoothTangentFrame period hPeriod
local notation "metric" => GlobalCandidateAGeometry.plusMetric (intrinsicBulkGeometry period hPeriod)
local notation "Gauge" => FiniteFrameAbelianGaugeC2Core period hPeriod frame
local notation "Ghost" => FiniteFrameAbelianGhostC2Core period hPeriod
local notation "C0" => C(Q period hPeriod, Real)

abbrev IntrinsicBulkAbelianACore := Gauge × Gauge
local notation "ACore" => IntrinsicBulkAbelianACore period hPeriod
local notation "BCore" => IntrinsicBulkAbelianBCore period hPeriod

private def projectedCoefficient (component : Fin 2)
    (index : Fin (finiteSmoothTangentFrame period hPeriod).count) :
    Gauge →L[Real] CanonicalPhysicalScalarC2JetCore period hPeriod :=
  (ContinuousLinearMap.proj index).comp ((ContinuousLinearMap.proj component).comp
    (finiteFrameGaugeC2Projection period hPeriod frame metric))

def intrinsicBulkAbelianLorenzComponent (component : Fin 2) : Gauge →L[Real] C0 :=
  ∑ first : Fin (finiteSmoothTangentFrame period hPeriod).count,
    ∑ second : Fin (finiteSmoothTangentFrame period hPeriod).count,
    (ContinuousLinearMap.mul Real C0
      (finiteFrameInverseMetricC0Coefficient period hPeriod frame metric first second 0)).comp
    ((finiteFrameScalarC2FirstDerivative period hPeriod metric frame first).comp
        (projectedCoefficient period hPeriod component second) -
      ∑ upper : Fin (finiteSmoothTangentFrame period hPeriod).count,
        (ContinuousLinearMap.mul Real C0
          (finiteFrameChristoffelC0Coefficient period hPeriod frame metric upper first second 0)).comp
        ((canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod).comp
          (projectedCoefficient period hPeriod component upper)))

theorem intrinsicBulkAbelianLorenzComponent_apply (component : Fin 2) (potential : Gauge) :
    intrinsicBulkAbelianLorenzComponent period hPeriod component potential =
      finiteFrameC2AbelianLorenzComponentExpression period hPeriod frame metric 0
        (finiteFrameGaugeC2Projection period hPeriod frame metric potential) component := by
  simp only [intrinsicBulkAbelianLorenzComponent, projectedCoefficient,
    finiteFrameC2AbelianLorenzComponentExpression, finiteFrameC2AbelianLorenzExpression,
    sum_apply, ContinuousLinearMap.comp_apply,
    sub_apply, ContinuousLinearMap.mul_apply', ContinuousLinearMap.proj_apply]

theorem intrinsicBulkAbelianLorenzComponent_smooth
    (potential : SmoothAbelianGaugePotential period hPeriod) (component : Fin 2) :
    intrinsicBulkAbelianLorenzComponent period hPeriod component
      (finiteFrameSmoothAbelianGaugeC2Coefficients period hPeriod frame potential) =
      smoothToCanonicalPhysicalContinuousScalar period hPeriod
        (ghostComponent period hPeriod
          (globalGeneralMetricAbelianLorenzCodifferential period hPeriod metric potential) component) := by
  rw [intrinsicBulkAbelianLorenzComponent_apply,
    finiteFrameSmoothAbelianGaugeC2Coefficients_projected]
  simpa only [map_zero] using finiteFrameC2AbelianLorenzComponentExpression_smooth period hPeriod frame metric 0 metric
    (by simp) (by simpa only [map_zero] using
      zero_mem_generalMetricRelativeC2OpenDomain period hPeriod frame metric) potential component

def intrinsicBulkAbelianSectorBAPairingDensity : Ghost →L[Real] Gauge →L[Real] C0 :=
  ∑ component : Fin 2, (ContinuousLinearMap.mul Real C0).bilinearComp
    (finiteFrameAbelianScalarC2Readout period hPeriod component)
    (intrinsicBulkAbelianLorenzComponent period hPeriod component)

def intrinsicBulkAbelianBAPairingDensity : BCore →L[Real] ACore →L[Real] C0 :=
  (intrinsicBulkAbelianSectorBAPairingDensity period hPeriod).bilinearComp
      (ContinuousLinearMap.fst Real Ghost Ghost) (ContinuousLinearMap.fst Real Gauge Gauge) +
    (intrinsicBulkAbelianSectorBAPairingDensity period hPeriod).bilinearComp
      (ContinuousLinearMap.snd Real Ghost Ghost) (ContinuousLinearMap.snd Real Gauge Gauge)

def intrinsicBulkAbelianBAPairing : BCore →L[Real] ACore →L[Real] Real :=
  (ContinuousLinearMap.compL Real ACore C0 Real (finiteFrameBRSTCanonicalIntegralCLM period hPeriod)).comp
    (intrinsicBulkAbelianBAPairingDensity period hPeriod)

end
end JanusFormal.P0EFTJanusProgramPT12IntrinsicBulkAbelianLorenz4D
