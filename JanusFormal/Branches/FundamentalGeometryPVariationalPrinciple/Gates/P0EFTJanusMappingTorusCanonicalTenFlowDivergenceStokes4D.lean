import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalTenFlowSmoothDual4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D

/-! # Global Stokes theorem for the canonical ten-flow divergence -/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalTenFlowDivergenceStokes4D

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalTenFlowIPP4D
open P0EFTJanusMappingTorusCanonicalTenFlowFrame4D
open P0EFTJanusMappingTorusCanonicalTenFlowSmoothDual4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance intrinsicCanonicalLorentzVolumeMeasureIsFinite :
    IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

/-- Divergence induced by reconstructing a tangent current in the ten global
volume-preserving flow directions. -/
def canonicalTenFlowDivergence
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (vector : SmoothTangentField period hPeriod) :
    SmoothQuotientField period hPeriod Real where
  toFun := fun point =>
    ∑ index : Fin 10,
      frameDerivative period hPeriod Real
        (canonicalTenFlowFrame period hPeriod)
        (canonicalTenFlowDualCoefficient period hPeriod metric vector index)
        point index
  contMDiff_toFun := by
    apply ContMDiff.sum
    intro index _
    exact (contMDiff_pi_space.mp
      (frameDerivative_contMDiff period hPeriod Real
        (canonicalTenFlowFrame period hPeriod)
        (canonicalTenFlowDualCoefficient period hPeriod metric vector index)))
      index

@[simp]
theorem canonicalTenFlowDivergence_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (vector : SmoothTangentField period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    canonicalTenFlowDivergence period hPeriod metric vector point =
      ∑ index : Fin 10,
        frameDerivative period hPeriod Real
          (canonicalTenFlowFrame period hPeriod)
          (canonicalTenFlowDualCoefficient period hPeriod metric vector index)
          point index :=
  rfl

theorem canonicalTenFlowDivergence_integrable
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (vector : SmoothTangentField period hPeriod) :
    Integrable (canonicalTenFlowDivergence period hPeriod metric vector)
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  (canonicalTenFlowDivergence period hPeriod metric vector).contMDiff_toFun
    |>.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

private theorem canonicalTenFlowCoefficientDerivative_integrable
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (vector : SmoothTangentField period hPeriod) (index : Fin 10) :
    Integrable
      (fun point =>
        frameDerivative period hPeriod Real
          (canonicalTenFlowFrame period hPeriod)
          (canonicalTenFlowDualCoefficient period hPeriod metric vector index)
          point index)
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
  exact ((contMDiff_pi_space.mp
      (frameDerivative_contMDiff period hPeriod Real
        (canonicalTenFlowFrame period hPeriod)
        (canonicalTenFlowDualCoefficient period hPeriod metric vector index)))
      index).continuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)

private theorem canonicalTenFlowCoefficientDerivative_integral_eq_zero
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (vector : SmoothTangentField period hPeriod) (index : Fin 10) :
    (∫ point,
      frameDerivative period hPeriod Real
        (canonicalTenFlowFrame period hPeriod)
        (canonicalTenFlowDualCoefficient period hPeriod metric vector index)
        point index
      ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod)) = 0 := by
  have hIPP := canonicalTenFlowFrame_integral_inner_derivative_eq_neg
    period hPeriod index
    (constantSmoothField period hPeriod Real 1)
    (canonicalTenFlowDualCoefficient period hPeriod metric vector index)
  simpa [frameDerivative_eq_mfderiv, constantSmoothField, mvfderiv_const] using hIPP

/-- Boundaryless global Stokes theorem for every smooth tangent current. -/
theorem canonicalTenFlowDivergence_integral_eq_zero
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (vector : SmoothTangentField period hPeriod) :
    (∫ point, canonicalTenFlowDivergence period hPeriod metric vector point
      ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod)) = 0 := by
  change (∫ point, (∑ index : Fin 10,
    frameDerivative period hPeriod Real
      (canonicalTenFlowFrame period hPeriod)
      (canonicalTenFlowDualCoefficient period hPeriod metric vector index)
      point index) ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod)) = 0
  rw [integral_finsetSum Finset.univ (fun index _ =>
    canonicalTenFlowCoefficientDerivative_integrable period hPeriod
      metric vector index)]
  exact Finset.sum_eq_zero fun index _ =>
    canonicalTenFlowCoefficientDerivative_integral_eq_zero period hPeriod
      metric vector index

/-- Gate marker: smooth reconstruction yields an integrable global divergence
whose canonical-volume integral vanishes. -/
theorem canonical_ten_flow_divergence_stokes_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (vector : SmoothTangentField period hPeriod) :
    (∀ point : EffectiveQuotient period hPeriod,
      vector point =
        ∑ index : Fin 10,
          canonicalTenFlowDualCoefficient period hPeriod metric vector index
              point •
            canonicalTenFlowGeneratorAt period hPeriod point
              ((canonicalFlowIndexEquivFinTen).symm index)) ∧
      Integrable (canonicalTenFlowDivergence period hPeriod metric vector)
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) ∧
      (∫ point, canonicalTenFlowDivergence period hPeriod metric vector point
        ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod)) = 0 := by
  exact ⟨canonicalTenFlowDual_reconstructs period hPeriod metric vector,
    canonicalTenFlowDivergence_integrable period hPeriod metric vector,
    canonicalTenFlowDivergence_integral_eq_zero period hPeriod metric vector⟩

end
end P0EFTJanusMappingTorusCanonicalTenFlowDivergenceStokes4D
end JanusFormal
