import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2SelfAdjointRootDomain4D

/-!
# Unified regular general-metric C² Lorentz chart domain

This intersects the existing inverse/positive-volume chart with the
self-adjoint identity-root chart.  A single open zero-neighbourhood in the
completed relative metric core then supplies every hypothesis needed to turn a
genuine smooth variation into the Lorentz metric `g + h`.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartDomain4D

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 300000

noncomputable section

open scoped Manifold ContDiff Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootLift4D
open P0EFTJanusProgramPRegularGeneralMetricC2SelfAdjointRootDomain4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev C2Scalar :=
  CanonicalPhysicalScalarC2JetCore period hPeriod

private abbrev RegularFrame
    (metric : RegularGeneralLorentzMetric period hPeriod) :=
  regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance c2ScalarNormedAddCommGroup :
    NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule
    period hPeriod).normedAddCommGroup

local instance c2ScalarNormedSpace :
    NormedSpace Real (C2Scalar period hPeriod) :=
  inferInstance

local instance c2ScalarCompleteSpace :
    CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod

/-- One operational chart domain carrying inverse, positive volume and the
self-adjoint local identity root. -/
def regularGeneralMetricC2LorentzChartDomain
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    Set (RegularGeneralMetricC2Core period hPeriod metric) :=
  regularGeneralMetricC2Domain period hPeriod metric ∩
    (generalMetricRelativeC2CoreToMatrix period hPeriod
      (RegularFrame period hPeriod metric) metric.metric) ⁻¹'
      regularGeneralMetricC2SelfAdjointRootDomain
        period hPeriod metric

theorem regularGeneralMetricC2LorentzChartDomain_isOpen
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    IsOpen (regularGeneralMetricC2LorentzChartDomain
      period hPeriod metric) := by
  exact (regularGeneralMetricC2Domain_isOpen period hPeriod metric).inter
    ((regularGeneralMetricC2SelfAdjointRootDomain_isOpen
      period hPeriod metric).preimage
        (generalMetricRelativeC2CoreToMatrix period hPeriod
          (RegularFrame period hPeriod metric) metric.metric).continuous)

theorem zero_mem_regularGeneralMetricC2LorentzChartDomain
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    (0 : RegularGeneralMetricC2Core period hPeriod metric) ∈
      regularGeneralMetricC2LorentzChartDomain
        period hPeriod metric := by
  constructor
  · exact zero_mem_regularGeneralMetricC2Domain period hPeriod metric
  · change generalMetricRelativeC2CoreToMatrix period hPeriod
        (RegularFrame period hPeriod metric) metric.metric 0 ∈
      regularGeneralMetricC2SelfAdjointRootDomain period hPeriod metric
    rw [map_zero]
    exact zero_mem_regularGeneralMetricC2SelfAdjointRootDomain
      period hPeriod metric

theorem regularGeneralMetricC2LorentzChartDomain_mem_nondegenerate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    {variation : RegularGeneralMetricC2Core period hPeriod metric}
    (hVariation : variation ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric) :
    variation ∈ generalMetricRelativeC2OpenDomain period hPeriod
      (RegularFrame period hPeriod metric) metric.metric := by
  exact hVariation.1.1

theorem regularGeneralMetricC2LorentzChartDomain_matrix_mem_root
    (metric : RegularGeneralLorentzMetric period hPeriod)
    {variation : RegularGeneralMetricC2Core period hPeriod metric}
    (hVariation : variation ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod metric) :
    variation.1 ∈ regularGeneralMetricC2SelfAdjointRootDomain
      period hPeriod metric := by
  exact hVariation.2

theorem regularGeneralMetricSmoothC2Variation_zero_mem_lorentzChartDomain
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    regularGeneralMetricSmoothC2Variation period hPeriod metric 0 ∈
      regularGeneralMetricC2LorentzChartDomain
        period hPeriod metric := by
  change smoothToGeneralMetricRelativeC2Core period hPeriod
      (RegularFrame period hPeriod metric) metric.metric 0 ∈ _
  rw [map_zero]
  exact zero_mem_regularGeneralMetricC2LorentzChartDomain
    period hPeriod metric

/-- Direct chart constructor for the genuine Lorentz metric `g + h`. -/
def regularGeneralMetricC2LorentzChartMetric
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation : regularGeneralMetricSmoothC2Variation
        period hPeriod metric tensor ∈
      regularGeneralMetricC2LorentzChartDomain
        period hPeriod metric) :
    SmoothGeneralLorentzMetric period hPeriod :=
  regularGeneralMetricC2SelfAdjointAffineLorentzMetric
    period hPeriod metric tensor
      (regularGeneralMetricC2LorentzChartDomain_matrix_mem_root
        period hPeriod metric hVariation)
      (regularGeneralMetricC2LorentzChartDomain_mem_nondegenerate
        period hPeriod metric hVariation)

@[simp]
theorem regularGeneralMetricC2LorentzChartMetric_tensor
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation : regularGeneralMetricSmoothC2Variation
        period hPeriod metric tensor ∈
      regularGeneralMetricC2LorentzChartDomain
        period hPeriod metric) :
    (regularGeneralMetricC2LorentzChartMetric period hPeriod metric tensor
      hVariation).tensor = metric.metric.tensor + tensor :=
  rfl

/-- Gate marker: all metric admissibility data are now carried by one open
zero-neighbourhood in the regular completed C² chart. -/
theorem regular_general_metric_c2_lorentz_chart_domain_gate
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    IsOpen (regularGeneralMetricC2LorentzChartDomain
      period hPeriod metric) ∧
      (0 : RegularGeneralMetricC2Core period hPeriod metric) ∈
        regularGeneralMetricC2LorentzChartDomain period hPeriod metric ∧
      ∀ (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
        (hVariation : regularGeneralMetricSmoothC2Variation
          period hPeriod metric tensor ∈
            regularGeneralMetricC2LorentzChartDomain period hPeriod metric),
        (regularGeneralMetricC2LorentzChartMetric period hPeriod metric tensor
          hVariation).tensor = metric.metric.tensor + tensor := by
  exact ⟨regularGeneralMetricC2LorentzChartDomain_isOpen
      period hPeriod metric,
    zero_mem_regularGeneralMetricC2LorentzChartDomain
      period hPeriod metric,
    fun tensor hVariation =>
      regularGeneralMetricC2LorentzChartMetric_tensor
        period hPeriod metric tensor hVariation⟩

end

end P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartDomain4D
end JanusFormal
