import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularFrameCanonicalMaxwellRaisedPairing4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartMaxwell4D

/-! # Authentic Maxwell first variation in the regular frame -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularFrameCanonicalMaxwellFirstVariationCurvature4D

set_option autoImplicit false
set_option maxHeartbeats 1800000

noncomputable section

open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusIntrinsicAbelianMaxwellAction4D
open P0EFTJanusMappingTorusConformalFrameFreeMaxwellHessian4D
open P0EFTJanusProgramPRegularFrameMaxwellCurvature4D
open P0EFTJanusProgramPRegularFrameMetricInverse4D
open P0EFTJanusProgramPRegularFrameMaxwellPairingBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartMaxwell4D
open P0EFTJanusProgramPRegularFrameCanonicalMaxwellElementaryFlux4D
open P0EFTJanusProgramPRegularFrameCanonicalMaxwellFluxDensity4D
open P0EFTJanusProgramPRegularFrameCanonicalMaxwellRaisedPairing4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

private theorem sum_four_swap_pairs
    (function : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Real) :
    (∑ first : Fin 4, ∑ second : Fin 4,
      ∑ third : Fin 4, ∑ fourth : Fin 4,
        function first second third fourth) =
      ∑ third : Fin 4, ∑ fourth : Fin 4,
        ∑ first : Fin 4, ∑ second : Fin 4,
          function first second third fourth := by
  have hGroup (summand : Fin 4 → Fin 4 → Real) :
      (∑ first : Fin 4, ∑ second : Fin 4, summand first second) =
        ∑ pair : Fin 4 × Fin 4, summand pair.1 pair.2 :=
    (Fintype.sum_prod_type' summand).symm
  calc
    _ = ∑ firstSecond : Fin 4 × Fin 4,
          ∑ third : Fin 4, ∑ fourth : Fin 4,
            function firstSecond.1 firstSecond.2 third fourth := hGroup _
    _ = ∑ firstSecond : Fin 4 × Fin 4,
          ∑ thirdFourth : Fin 4 × Fin 4,
            function firstSecond.1 firstSecond.2 thirdFourth.1 thirdFourth.2 := by
      apply Finset.sum_congr rfl
      intro firstSecond _
      exact hGroup _
    _ = ∑ thirdFourth : Fin 4 × Fin 4,
          ∑ firstSecond : Fin 4 × Fin 4,
            function firstSecond.1 firstSecond.2 thirdFourth.1 thirdFourth.2 :=
      Finset.sum_comm
    _ = ∑ thirdFourth : Fin 4 × Fin 4,
          ∑ first : Fin 4, ∑ second : Fin 4,
            function first second thirdFourth.1 thirdFourth.2 := by
      apply Finset.sum_congr rfl
      intro thirdFourth _
      exact (hGroup (fun first second =>
        function first second thirdFourth.1 thirdFourth.2)).symm
    _ = _ :=
      (hGroup (fun third fourth =>
        ∑ first : Fin 4, ∑ second : Fin 4,
          function first second third fourth)).symm

theorem regularFrameMetricInverseMatrixMap_symmetric
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod) (first second : Fin 4) :
    (regularFrameMetricMatrixMap period hPeriod metric point)⁻¹ first second =
      (regularFrameMetricMatrixMap period hPeriod metric point)⁻¹ second first := by
  have hMetric :
      (regularFrameMetricMatrixMap period hPeriod metric point).transpose =
        regularFrameMetricMatrixMap period hPeriod metric point := by
    ext row column
    exact metric.metric.tensor.symmetric point _ _
  have hInverse := Matrix.transpose_nonsing_inv
    (A := regularFrameMetricMatrixMap period hPeriod metric point)
  rw [hMetric] at hInverse
  exact congrFun (congrFun hInverse second) first

theorem matrixMaxwellContraction_comm_of_symmetric
    (inverse first second :
      P0EFTJanusMetricCoupledScalarMatterJetVariation.Matrix4)
    (hInverse : ∀ row column, inverse row column = inverse column row) :
    matrixMaxwellContraction inverse first second =
      matrixMaxwellContraction inverse second first := by
  unfold matrixMaxwellContraction
  rw [sum_four_swap_pairs]
  apply Finset.sum_congr rfl
  intro third _
  apply Finset.sum_congr rfl
  intro fourth _
  apply Finset.sum_congr rfl
  intro firstIndex _
  apply Finset.sum_congr rfl
  intro secondIndex _
  rw [hInverse firstIndex third, hInverse secondIndex fourth]
  ring

theorem globalMaxwellPairing_comm_regularFrame
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (first second : SmoothAbelianGaugePotential period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate :
      P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4) :
    globalMaxwellPairing period hPeriod metric.metric first second
        (patch.coordinateMap coordinate) =
      globalMaxwellPairing period hPeriod metric.metric second first
        (patch.coordinateMap coordinate) := by
  rw [globalMaxwellPairing_eq_regularFrameContraction,
    globalMaxwellPairing_eq_regularFrameContraction]
  apply Finset.sum_congr rfl
  intro component _
  apply matrixMaxwellContraction_comm_of_symmetric
  exact regularFrameMetricInverseMatrixMap_symmetric period hPeriod metric
    (patch.coordinateMap coordinate)

/-- The genuine first variation is `-1/2` times the densitized raised base
curvature contracted with the Cartan curvature of the variation. -/
theorem regularMaxwellFirstVariationField_eq_flux_curvature
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate :
      P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4) :
    regularMaxwellFirstVariationField period hPeriod metric
        (regularIntrinsicMaxwellLineOfPotentials period hPeriod metric
          potential variation)
        (patch.coordinateMap coordinate) =
      -(1 / 2 : Real) *
        ∑ component : Fin 2, ∑ first : Fin 4, ∑ second : Fin 4,
          regularFrameCanonicalMaxwellFluxCoefficient period hPeriod metric
                potential component first second
                (patch.coordinateMap coordinate) *
            regularFrameGaugeCurvatureCoefficient period hPeriod metric
              variation component first second
              (patch.coordinateMap coordinate) := by
  let point := patch.coordinateMap coordinate
  let contraction :=
    ∑ component : Fin 2, ∑ first : Fin 4, ∑ second : Fin 4,
      regularFrameGlobalGaugeCurvatureRaisedCoefficient period hPeriod metric
            potential component first second point *
        regularFrameGaugeCurvatureCoefficient period hPeriod metric variation
          component first second point
  have hFlux :
      (∑ component : Fin 2, ∑ first : Fin 4, ∑ second : Fin 4,
        regularFrameCanonicalMaxwellFluxCoefficient period hPeriod metric
              potential component first second point *
          regularFrameGaugeCurvatureCoefficient period hPeriod metric variation
            component first second point) =
        metric.volume point * contraction := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro component _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro first _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro second _
    rw [regularFrameCanonicalMaxwellFluxCoefficient_eq_volume_mul]
    ring
  change metric.volume point *
      (-(1 / 4 : Real) *
        (globalMaxwellPairing period hPeriod metric.metric variation potential
            point +
          globalMaxwellPairing period hPeriod metric.metric potential variation
            point)) = _
  rw [← globalMaxwellPairing_comm_regularFrame period hPeriod metric variation
    potential patch coordinate]
  rw [globalMaxwellPairing_eq_raisedRegularFrame period hPeriod metric variation
    potential patch coordinate]
  change metric.volume point * (-(1 / 4 : Real) *
      (contraction + contraction)) = _
  rw [hFlux]
  ring

/-- Gate marker for the authentic global-density Maxwell variation in an
arbitrary smooth regular frame. -/
theorem regular_frame_canonical_maxwell_first_variation_curvature_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod) :
    ∀ (patch : SmoothHolonomicFrameChart4 period hPeriod)
        (coordinate :
          P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4),
      regularMaxwellFirstVariationField period hPeriod metric
          (regularIntrinsicMaxwellLineOfPotentials period hPeriod metric
            potential variation)
          (patch.coordinateMap coordinate) =
        -(1 / 2 : Real) *
          ∑ component : Fin 2, ∑ first : Fin 4, ∑ second : Fin 4,
            regularFrameCanonicalMaxwellFluxCoefficient period hPeriod metric
                  potential component first second
                  (patch.coordinateMap coordinate) *
              regularFrameGaugeCurvatureCoefficient period hPeriod metric
                variation component first second
                (patch.coordinateMap coordinate) :=
  regularMaxwellFirstVariationField_eq_flux_curvature period hPeriod metric
    potential variation

end
end P0EFTJanusProgramPRegularFrameCanonicalMaxwellFirstVariationCurvature4D
end JanusFormal
