import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusRegularFrameCanonicalFormalAdjoint4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2SmoothPalatiniDivergence4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularFramePalatiniCanonicalDivergenceReduction4D

/-! # Stored-volume Palatini remainder as weighted current coefficients

Canonical integration by parts transfers the frame derivatives from the
Palatini coefficients to their weights. No volume gauge is imposed.
-/

namespace JanusFormal
namespace P0EFTJanusStoredVolumePalatiniCurrentWeight4D

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 600000
noncomputable section
open MeasureTheory
open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0FiniteMatrixProduct4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothPalatiniCurrent4D
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothPalatiniDivergence4D
open P0EFTJanusProgramPRegularFramePalatiniCanonicalDivergenceReduction4D
open P0EFTJanusRegularFrameCanonicalFormalAdjoint4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

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

/-- Separate the actual frame derivatives from the Levi--Civita trace. -/
theorem regularFrameSmoothPalatiniCovariantDivergence_eq_frameCurrentSum
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    regularFrameSmoothPalatiniCovariantDivergence period hPeriod metric tensor =
      ∑ vector : Fin 4,
        (frameDerivativeComponentField period hPeriod
          (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
          (regularFrameSmoothPalatiniCoefficient period hPeriod metric tensor vector) vector +
        smoothScalarFieldMul period hPeriod
          (regularFrameLeviCivitaTrace period hPeriod metric vector)
          (regularFrameSmoothPalatiniCoefficient period hPeriod metric tensor vector)) := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  simp only [regularFrameSmoothPalatiniCovariantDivergence,
    regularFrameSmoothPalatiniCoefficient_frameDerivative, regularFrameLeviCivitaTrace,
    smoothScalarFieldFinsetSum_apply, smoothScalarFieldAdd_apply, smoothScalarFieldMul_apply,
    Finset.sum_add_distrib, Finset.sum_mul]
  congr 1
  exact Finset.sum_comm

private theorem coefficient_mul_palatiniDivergence
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (coefficient : SmoothScalarField period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    smoothScalarFieldMul period hPeriod coefficient
        (regularFrameSmoothPalatiniCovariantDivergence period hPeriod metric tensor) =
      ∑ vector : Fin 4,
        (smoothScalarFieldMul period hPeriod coefficient
          (frameDerivativeComponentField period hPeriod
            (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
            (regularFrameSmoothPalatiniCoefficient period hPeriod metric tensor vector) vector) +
        smoothScalarFieldMul period hPeriod
          (smoothScalarFieldMul period hPeriod coefficient
            (regularFrameLeviCivitaTrace period hPeriod metric vector))
          (regularFrameSmoothPalatiniCoefficient period hPeriod metric tensor vector)) := by
  rw [regularFrameSmoothPalatiniCovariantDivergence_eq_frameCurrentSum]
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  simp only [smoothScalarFieldMul_apply, smoothScalarFieldFinsetSum_apply,
    smoothScalarFieldAdd_apply, Finset.mul_sum, mul_add, mul_assoc]

/-- Integration by parts for any smooth scalar weight on the Palatini current. -/
theorem canonicalSmoothScalarIntegral_mul_palatiniDivergence
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (coefficient : SmoothScalarField period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    canonicalSmoothScalarIntegral period hPeriod
        (smoothScalarFieldMul period hPeriod coefficient
          (regularFrameSmoothPalatiniCovariantDivergence period hPeriod metric tensor)) =
      canonicalSmoothScalarIntegral period hPeriod
        (∑ vector : Fin 4, smoothScalarFieldMul period hPeriod
          (smoothScalarFieldMul period hPeriod coefficient
              (regularFrameLeviCivitaTrace period hPeriod metric vector) +
            regularFrameCanonicalFormalAdjoint period hPeriod metric coefficient vector)
          (regularFrameSmoothPalatiniCoefficient period hPeriod metric tensor vector)) := by
  rw [coefficient_mul_palatiniDivergence, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro vector _
  rw [map_add, regularFrameCanonicalFormalAdjoint_smoothIntegral]
  have hWeight :
      smoothScalarFieldMul period hPeriod
          (smoothScalarFieldMul period hPeriod coefficient
              (regularFrameLeviCivitaTrace period hPeriod metric vector) +
            regularFrameCanonicalFormalAdjoint period hPeriod metric coefficient vector)
          (regularFrameSmoothPalatiniCoefficient period hPeriod metric tensor vector) =
      smoothScalarFieldMul period hPeriod
          (regularFrameCanonicalFormalAdjoint period hPeriod metric coefficient vector)
          (regularFrameSmoothPalatiniCoefficient period hPeriod metric tensor vector) +
        smoothScalarFieldMul period hPeriod
          (smoothScalarFieldMul period hPeriod coefficient
            (regularFrameLeviCivitaTrace period hPeriod metric vector))
          (regularFrameSmoothPalatiniCoefficient period hPeriod metric tensor vector) := by
    apply SmoothQuotientField.ext period hPeriod Real
    intro point
    simp only [smoothScalarFieldMul_apply, smoothScalarFieldAdd_apply]
    ring
  rw [hWeight, map_add]

/-- Weight after removing the frame derivative from each Palatini coefficient. -/
def storedVolumePalatiniCurrentWeight
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (gravitationalCoupling : Real) (vector : Fin 4) : SmoothScalarField period hPeriod :=
  let coefficient := (1 / (2 * gravitationalCoupling) : Real) • metric.volume
  smoothScalarFieldMul period hPeriod coefficient
      (regularFrameLeviCivitaTrace period hPeriod metric vector) +
    regularFrameCanonicalFormalAdjoint period hPeriod metric coefficient vector

/-- Exact stored-volume Palatini remainder, with no gauge or coupling restriction. -/
theorem storedVolumePalatiniRemainder_eq_weightedCurrent
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (gravitationalCoupling : Real)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    (∫ point, metric.volume point / (2 * gravitationalCoupling) *
      regularFrameSmoothPalatiniCovariantDivergence period hPeriod metric tensor point
      ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod) =
      canonicalSmoothScalarIntegral period hPeriod
        (∑ vector : Fin 4, smoothScalarFieldMul period hPeriod
          (storedVolumePalatiniCurrentWeight period hPeriod metric gravitationalCoupling vector)
          (regularFrameSmoothPalatiniCoefficient period hPeriod metric tensor vector)) := by
  let coefficient := (1 / (2 * gravitationalCoupling) : Real) • metric.volume
  calc
    _ = canonicalSmoothScalarIntegral period hPeriod
        (smoothScalarFieldMul period hPeriod coefficient
          (regularFrameSmoothPalatiniCovariantDivergence period hPeriod metric tensor)) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun point => by
        change metric.volume point / (2 * gravitationalCoupling) *
            regularFrameSmoothPalatiniCovariantDivergence period hPeriod metric tensor point =
          ((1 / (2 * gravitationalCoupling) : Real) * metric.volume point) *
            regularFrameSmoothPalatiniCovariantDivergence period hPeriod metric tensor point
        ring
    _ = _ := by
      simpa only [storedVolumePalatiniCurrentWeight, coefficient] using
        canonicalSmoothScalarIntegral_mul_palatiniDivergence
          period hPeriod metric coefficient tensor

end
end P0EFTJanusStoredVolumePalatiniCurrentWeight4D
end JanusFormal
