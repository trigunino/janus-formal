import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalTenFlowDivergenceStokes4D

/-! # Weak characterization of the canonical ten-flow divergence -/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalTenFlowDivergenceWeakStokes4D

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
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalTenFlowFrame4D
open P0EFTJanusMappingTorusCanonicalTenFlowSmoothDual4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceStokes4D

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

/-- The ten dual coefficients reconstruct the directional derivative of every
smooth scalar exactly. -/
theorem canonicalTenFlowDirectionalDerivative_reconstructs
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (vector : SmoothTangentField period hPeriod)
    (test : SmoothQuotientField period hPeriod Real)
    (point : EffectiveQuotient period hPeriod) :
    mvfderiv coverModelWithCorners test.toFun point (vector point) =
      ∑ index : Fin 10,
        canonicalTenFlowDualCoefficient period hPeriod metric vector index
            point *
          frameDerivative period hPeriod Real
            (canonicalTenFlowFrame period hPeriod) test point index := by
  rw [canonicalTenFlowDual_reconstructs period hPeriod metric vector point]
  simp only [map_sum, map_smul, smul_eq_mul, frameDerivative_eq_mfderiv]
  apply Finset.sum_congr rfl
  intro index _
  rfl

private theorem leftSummand_integrable
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (vector : SmoothTangentField period hPeriod)
    (test : SmoothQuotientField period hPeriod Real) (index : Fin 10) :
    Integrable
      (fun point => test point *
        frameDerivative period hPeriod Real
          (canonicalTenFlowFrame period hPeriod)
          (canonicalTenFlowDualCoefficient period hPeriod metric vector index)
          point index)
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
  exact (test.contMDiff_toFun.continuous.mul
    ((contMDiff_pi_space.mp
      (frameDerivative_contMDiff period hPeriod Real
        (canonicalTenFlowFrame period hPeriod)
        (canonicalTenFlowDualCoefficient period hPeriod metric vector index)))
      index).continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)

private theorem rightSummand_integrable
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (vector : SmoothTangentField period hPeriod)
    (test : SmoothQuotientField period hPeriod Real) (index : Fin 10) :
    Integrable
      (fun point =>
        frameDerivative period hPeriod Real
            (canonicalTenFlowFrame period hPeriod) test point index *
          canonicalTenFlowDualCoefficient period hPeriod metric vector index
            point)
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
  exact (((contMDiff_pi_space.mp
      (frameDerivative_contMDiff period hPeriod Real
        (canonicalTenFlowFrame period hPeriod) test)) index).continuous.mul
    (canonicalTenFlowDualCoefficient period hPeriod metric vector index
      ).contMDiff_toFun.continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)

/-- Intrinsic weak Stokes identity for the divergence of every smooth tangent
current and every smooth scalar test. -/
theorem canonicalTenFlowDivergence_weak_stokes
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (vector : SmoothTangentField period hPeriod)
    (test : SmoothQuotientField period hPeriod Real) :
    (∫ point,
        test point * canonicalTenFlowDivergence period hPeriod metric vector point
      ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod)) =
      -∫ point,
        mvfderiv coverModelWithCorners test.toFun point (vector point)
      ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
  let measure := intrinsicCanonicalLorentzVolumeMeasure period hPeriod
  let coefficient := canonicalTenFlowDualCoefficient period hPeriod metric vector
  let derivative := fun (field : SmoothQuotientField period hPeriod Real)
      (point : EffectiveQuotient period hPeriod) (index : Fin 10) =>
    frameDerivative period hPeriod Real
      (canonicalTenFlowFrame period hPeriod) field point index
  have hIPP (index : Fin 10) :
      (∫ point, test point * derivative (coefficient index) point index ∂measure) =
        -∫ point, derivative test point index * coefficient index point ∂measure := by
    simpa only [measure, coefficient, derivative, RCLike.inner_apply,
      conj_trivial, mul_comm] using
      canonicalTenFlowFrame_integral_inner_derivative_eq_neg period hPeriod
        index test (coefficient index)
  calc
    (∫ point,
        test point * canonicalTenFlowDivergence period hPeriod metric vector point
      ∂measure) =
        ∑ index : Fin 10,
          ∫ point, test point * derivative (coefficient index) point index
            ∂measure := by
      rw [← integral_finsetSum Finset.univ (fun index _ =>
        leftSummand_integrable period hPeriod metric vector test index)]
      apply integral_congr_ae
      filter_upwards [] with point
      simp only [canonicalTenFlowDivergence_apply, Finset.mul_sum]
    _ = ∑ index : Fin 10,
        -∫ point, derivative test point index * coefficient index point
          ∂measure := by
      apply Finset.sum_congr rfl
      intro index _
      exact hIPP index
    _ = -∫ point,
        ∑ index : Fin 10,
          derivative test point index * coefficient index point ∂measure := by
      rw [Finset.sum_neg_distrib,
        integral_finsetSum Finset.univ (fun index _ =>
          rightSummand_integrable period hPeriod metric vector test index)]
    _ = -∫ point,
        mvfderiv coverModelWithCorners test.toFun point (vector point)
          ∂measure := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with point
      rw [canonicalTenFlowDirectionalDerivative_reconstructs period hPeriod
        metric vector test point]
      apply Finset.sum_congr rfl
      intro index _
      ring

/-- Gate marker: the constructed divergence is the distributional divergence
for the canonical volume, not merely a zero-integral scalar. -/
theorem canonical_ten_flow_divergence_weak_stokes_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (vector : SmoothTangentField period hPeriod) :
    (∀ test : SmoothQuotientField period hPeriod Real,
      (∫ point,
          test point *
            canonicalTenFlowDivergence period hPeriod metric vector point
        ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod)) =
        -∫ point,
          mvfderiv coverModelWithCorners test.toFun point (vector point)
        ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod)) ∧
      (∫ point, canonicalTenFlowDivergence period hPeriod metric vector point
        ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod)) = 0 := by
  exact ⟨canonicalTenFlowDivergence_weak_stokes period hPeriod metric vector,
    canonicalTenFlowDivergence_integral_eq_zero period hPeriod metric vector⟩

end
end P0EFTJanusMappingTorusCanonicalTenFlowDivergenceWeakStokes4D
end JanusFormal
