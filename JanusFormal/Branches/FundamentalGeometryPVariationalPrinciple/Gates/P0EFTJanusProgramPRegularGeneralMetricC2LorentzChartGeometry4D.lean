import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootSmoothOperator4D

/-!
# Global Candidate-A geometry on the regular Lorentz chart

The completed identity root, its smooth action and the genuine affine Lorentz
metric are assembled into the intrinsic `GlobalCandidateAGeometry` package.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartGeometry4D

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 600000

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootLift4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootSmoothOperator4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- The intrinsic relative endomorphism of the varied chart metric is the
affine target already squared by the completed identity root. -/
theorem regularGeneralMetricC2LorentzChartMetric_relativeEndomorphismAt
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation : regularGeneralMetricSmoothC2Variation
        period hPeriod metric tensor ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric)
    (point : EffectiveQuotient period hPeriod) :
    relativeEndomorphismAt period hPeriod metric.metric
        (regularGeneralMetricC2LorentzChartMetric
          period hPeriod metric tensor hVariation) point =
      regularGeneralMetricAffineRelativeEndomorphismAt
        period hPeriod metric tensor point := by
  apply ContinuousLinearMap.ext
  intro vector
  change (metric.metric.musical point).symm
      ((regularGeneralMetricC2LorentzChartMetric
        period hPeriod metric tensor hVariation).musical point vector) =
    vector + (metric.metric.musical point).symm
      (tensor.tensor point vector)
  have hVariedMusical :
      (regularGeneralMetricC2LorentzChartMetric
          period hPeriod metric tensor hVariation).musical point vector =
        (regularGeneralMetricC2LorentzChartMetric
          period hPeriod metric tensor hVariation).tensor.tensor point
            vector := by
    exact DFunLike.congr_fun
      ((regularGeneralMetricC2LorentzChartMetric
        period hPeriod metric tensor hVariation).musical_eq_tensor point)
      vector
  rw [hVariedMusical, regularGeneralMetricC2LorentzChartMetric_tensor]
  change (metric.metric.musical point).symm
      (metric.metric.tensor.tensor point vector + tensor.tensor point vector) = _
  rw [← DFunLike.congr_fun (metric.metric.musical_eq_tensor point) vector,
    map_add]
  congr 1
  exact (metric.metric.musical point).symm_apply_apply vector

/-- Canonical intrinsic Candidate-A geometry selected by one admissible
variation in the unified regular C² Lorentz chart. -/
def regularGeneralMetricC2LorentzChartGeometry
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation : regularGeneralMetricSmoothC2Variation
        period hPeriod metric tensor ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric) :
    GlobalCandidateAGeometry period hPeriod :=
  let hRoot : RegularGeneralMetricC2IdentityRootAdmissible
      period hPeriod metric tensor :=
    (regularGeneralMetricC2LorentzChartDomain_matrix_mem_root
      period hPeriod metric hVariation).1
  { plusMetric := metric.metric
    minusMetric := regularGeneralMetricC2LorentzChartMetric
      period hPeriod metric tensor hVariation
    rootAt := regularGeneralMetricC2IdentityRootAt
      period hPeriod metric tensor
    rootOperator := regularGeneralMetricC2IdentityRootOperator
      period hPeriod metric tensor hRoot
    rootOperator_apply :=
      regularGeneralMetricC2IdentityRootOperator_apply
        period hPeriod metric tensor hRoot
    root_square := by
      intro point
      exact (regularGeneralMetricC2IdentityRootAt_square
        period hPeriod metric tensor hRoot point).trans
          (regularGeneralMetricC2LorentzChartMetric_relativeEndomorphismAt
            period hPeriod metric tensor hVariation point).symm }

@[simp]
theorem regularGeneralMetricC2LorentzChartGeometry_plusMetric
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation : regularGeneralMetricSmoothC2Variation
        period hPeriod metric tensor ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric) :
    (regularGeneralMetricC2LorentzChartGeometry
      period hPeriod metric tensor hVariation).plusMetric = metric.metric :=
  rfl

@[simp]
theorem regularGeneralMetricC2LorentzChartGeometry_minusMetric
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation : regularGeneralMetricSmoothC2Variation
        period hPeriod metric tensor ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric) :
    (regularGeneralMetricC2LorentzChartGeometry
      period hPeriod metric tensor hVariation).minusMetric =
        regularGeneralMetricC2LorentzChartMetric
          period hPeriod metric tensor hVariation :=
  rfl

@[simp]
theorem regularGeneralMetricC2LorentzChartGeometry_rootAt
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation : regularGeneralMetricSmoothC2Variation
        period hPeriod metric tensor ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric) :
    (regularGeneralMetricC2LorentzChartGeometry
      period hPeriod metric tensor hVariation).rootAt =
        regularGeneralMetricC2IdentityRootAt
          period hPeriod metric tensor :=
  rfl

@[simp]
theorem regularGeneralMetricC2LorentzChartGeometry_rootOperator
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation : regularGeneralMetricSmoothC2Variation
        period hPeriod metric tensor ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric) :
    (regularGeneralMetricC2LorentzChartGeometry
      period hPeriod metric tensor hVariation).rootOperator =
        regularGeneralMetricC2IdentityRootOperator period hPeriod metric tensor
          (regularGeneralMetricC2LorentzChartDomain_matrix_mem_root
            period hPeriod metric hVariation).1 :=
  rfl

/-- Gate marker: the unified Lorentz chart now lands in the genuine global
Candidate-A geometry domain. -/
theorem regular_general_metric_c2_lorentz_chart_geometry_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation : regularGeneralMetricSmoothC2Variation
        period hPeriod metric tensor ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric) :
    ∃ geometry : GlobalCandidateAGeometry period hPeriod,
      geometry.plusMetric = metric.metric ∧
        geometry.minusMetric = regularGeneralMetricC2LorentzChartMetric
          period hPeriod metric tensor hVariation :=
  ⟨regularGeneralMetricC2LorentzChartGeometry
      period hPeriod metric tensor hVariation, rfl, rfl⟩

end

end P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartGeometry4D
end JanusFormal
