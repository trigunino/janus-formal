import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularFrameMaxwellWeightedEulerBoundary4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2SmoothMaxwellLocalBoxStokes4D

/-! # Local Maxwell weak--strong reduction on a Dirichlet box -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2SmoothMaxwellLocalBoxWeakStrong4D

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusIntrinsicAbelianMaxwellAction4D
open P0EFTJanusMappingTorusLocalMaxwellEulerBoundary4D
open P0EFTJanusMappingTorusLocalPalatiniBoxStokes4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartMaxwell4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongMaxwellLocalEulerBoundary4D
open P0EFTJanusProgramPRegularFrameMaxwellWeightedEulerBoundary4D
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothMaxwellLocalBoxStokes4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev Index4 := Fin 4

private abbrev Vector4 :=
  P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- Each coefficient in the local Maxwell Euler pairing is continuous. -/
theorem regularIntrinsicMaxwellLocalEulerCoefficient_continuous
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (second : Index4) :
    Continuous (fun coordinate =>
      maxwellEulerCoefficient
        (regularIntrinsicMaxwellLocalExcitationField period hPeriod metric
          potential patch component)
        coordinate second) := by
  unfold maxwellEulerCoefficient coordinatePartial
  apply continuous_finsetSum
  intro first _
  exact
    ((regularIntrinsicMaxwellLocalExcitationField_entry_contDiff period hPeriod
      metric potential component patch first second).continuous_fderiv
        (by simp)).clm_apply continuous_const

/-- The local Maxwell Euler pairing with a smooth test potential is
continuous. -/
theorem regularIntrinsicMaxwellLocalEulerPairing_continuous
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) :
    Continuous (fun coordinate =>
      maxwellEulerPairing
        (regularIntrinsicMaxwellLocalExcitationField period hPeriod metric
          potential patch component)
        (regularIntrinsicMaxwellLocalPotentialCoordinates period hPeriod
          variation component patch)
        coordinate) := by
  unfold maxwellEulerPairing
  apply continuous_finsetSum
  intro second _
  exact
    (regularIntrinsicMaxwellLocalEulerCoefficient_continuous period hPeriod
      metric potential component patch second).mul
      (regularIntrinsicMaxwellLocalPotentialCoordinates_entry_contDiff period
        hPeriod variation component patch second).continuous

/-- The weighted strong pairing selected by the action is integrable on every
compact coordinate box. -/
theorem regularFrameMaxwellStrongPairing_integrableOn
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (box : CompactCoordinateBox4) :
    IntegrableOn
      (regularFrameMaxwellStrongPairing period hPeriod metric potential
        variation component patch) (Icc box.lower box.upper) := by
  have hEquality :
      regularFrameMaxwellStrongPairing period hPeriod metric potential
          variation component patch =
        fun coordinate =>
          maxwellEulerPairing
            (regularIntrinsicMaxwellLocalExcitationField period hPeriod metric
              potential patch component)
            (regularIntrinsicMaxwellLocalPotentialCoordinates period hPeriod
              variation component patch)
            coordinate := by
    funext coordinate
    exact (regularIntrinsicMaxwellEulerPairing_eq_weightedStrongPairing period
      hPeriod metric potential variation component patch coordinate).symm
  rw [hEquality]
  exact
    (regularIntrinsicMaxwellLocalEulerPairing_continuous period hPeriod metric
      potential variation component patch).continuousOn.integrableOn_compact
      isCompact_Icc

/-- Pointwise weighted weak--strong split using the analytic divergence from
the concrete Stokes theorem. -/
theorem regularMaxwellFirstVariationField_eq_strong_sub_analyticDivergence
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    regularMaxwellFirstVariationField period hPeriod metric
        (regularIntrinsicMaxwellLineOfPotentials period hPeriod metric
          potential variation)
        (patch.coordinateMap coordinate) =
      ∑ component : Fin 2,
        (regularFrameMaxwellStrongPairing period hPeriod metric potential
            variation component patch coordinate -
          regularIntrinsicMaxwellLocalBoundaryDivergence period hPeriod metric
            potential variation component patch coordinate) := by
  rw [regularMaxwellFirstVariationField_eq_weightedStrongPairing_sub_boundary]
  apply Finset.sum_congr rfl
  intro component _
  rw [regularIntrinsicMaxwellLocalBoundaryDivergence_eq]

/-- On a compact box with Dirichlet test data, the integrated intrinsic
Maxwell first-variation density is exactly the integrated weighted strong
residual pairing, with no assumed Stokes contract. -/
theorem integral_regularMaxwellFirstVariationField_eq_integral_strong_of_dirichlet
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (box : CompactCoordinateBox4)
    (boundary : RegularIntrinsicMaxwellLocalBoxDirichlet period hPeriod
      variation patch box) :
    (∫ coordinate in Icc box.lower box.upper,
      regularMaxwellFirstVariationField period hPeriod metric
        (regularIntrinsicMaxwellLineOfPotentials period hPeriod metric
          potential variation)
        (patch.coordinateMap coordinate)) =
      ∫ coordinate in Icc box.lower box.upper,
        ∑ component : Fin 2,
          regularFrameMaxwellStrongPairing period hPeriod metric potential
            variation component patch coordinate := by
  rw [integral_congr_ae (Filter.Eventually.of_forall fun coordinate =>
    regularMaxwellFirstVariationField_eq_strong_sub_analyticDivergence period
      hPeriod metric potential variation patch coordinate)]
  calc
    (∫ coordinate in Icc box.lower box.upper,
      ∑ component : Fin 2,
        (regularFrameMaxwellStrongPairing period hPeriod metric potential
            variation component patch coordinate -
          regularIntrinsicMaxwellLocalBoundaryDivergence period hPeriod metric
            potential variation component patch coordinate)) =
        ∑ component : Fin 2,
          ∫ coordinate in Icc box.lower box.upper,
            (regularFrameMaxwellStrongPairing period hPeriod metric potential
                variation component patch coordinate -
              regularIntrinsicMaxwellLocalBoundaryDivergence period hPeriod
                metric potential variation component patch coordinate) := by
      rw [integral_finsetSum]
      intro component _
      exact
        (regularFrameMaxwellStrongPairing_integrableOn period hPeriod metric
          potential variation component patch box).sub
          (regularIntrinsicMaxwellLocalBoundaryDivergence_integrableOn period
            hPeriod metric potential variation component patch box)
    _ = ∑ component : Fin 2,
          ((∫ coordinate in Icc box.lower box.upper,
              regularFrameMaxwellStrongPairing period hPeriod metric potential
                variation component patch coordinate) -
            ∫ coordinate in Icc box.lower box.upper,
              regularIntrinsicMaxwellLocalBoundaryDivergence period hPeriod
                metric potential variation component patch coordinate) := by
      apply Finset.sum_congr rfl
      intro component _
      rw [integral_sub
        (regularFrameMaxwellStrongPairing_integrableOn period hPeriod metric
          potential variation component patch box)
        (regularIntrinsicMaxwellLocalBoundaryDivergence_integrableOn period
          hPeriod metric potential variation component patch box)]
    _ = ∑ component : Fin 2,
          ∫ coordinate in Icc box.lower box.upper,
            regularFrameMaxwellStrongPairing period hPeriod metric potential
              variation component patch coordinate := by
      apply Finset.sum_congr rfl
      intro component _
      rw [integral_regularIntrinsicMaxwellLocalBoundaryDivergence_eq_zero_of_dirichlet
        period hPeriod metric potential variation patch box boundary component,
        sub_zero]
    _ = ∫ coordinate in Icc box.lower box.upper,
          ∑ component : Fin 2,
            regularFrameMaxwellStrongPairing period hPeriod metric potential
              variation component patch coordinate := by
      symm
      rw [integral_finsetSum]
      intro component _
      exact regularFrameMaxwellStrongPairing_integrableOn period hPeriod metric
        potential variation component patch box

/-- Gate marker for the unconditional local Maxwell weak--strong reduction. -/
theorem regular_general_metric_c2_smooth_maxwell_local_box_weak_strong_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (box : CompactCoordinateBox4)
    (boundary : RegularIntrinsicMaxwellLocalBoxDirichlet period hPeriod
      variation patch box) :
    (∫ coordinate in Icc box.lower box.upper,
      regularMaxwellFirstVariationField period hPeriod metric
        (regularIntrinsicMaxwellLineOfPotentials period hPeriod metric
          potential variation)
        (patch.coordinateMap coordinate)) =
      ∫ coordinate in Icc box.lower box.upper,
        ∑ component : Fin 2,
          regularFrameMaxwellStrongPairing period hPeriod metric potential
            variation component patch coordinate :=
  integral_regularMaxwellFirstVariationField_eq_integral_strong_of_dirichlet
    period hPeriod metric potential variation patch box boundary

end
end P0EFTJanusProgramPRegularGeneralMetricC2SmoothMaxwellLocalBoxWeakStrong4D
end JanusFormal
