import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartGramTransport4D

/-!
# Fixed ambient matrix domain for the completed Lorentz chart

The dependent chart core is replaced by an equivalent open subset of the
ambient `4 × 4` completed `C²` matrix algebra.  Its only metric-dependent
condition is the self-adjoint root domain, already invariant under chart
transport by Gate 374.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartMatrixDomain4D

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 600000

noncomputable section

open scoped Manifold ContDiff Topology BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2LocalRoot4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixDeterminant4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixInverse4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPGeneralMetricC2VolumeDensity4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2SelfAdjointRootDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartRegularMetric4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartGramTransport4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev C2Scalar :=
  CanonicalPhysicalScalarC2JetCore period hPeriod

private abbrev C2Matrix :=
  C2FiniteMatrix period hPeriod 4

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

/-- Fixed ambient matrix version of the Lorentz-chart domain. -/
def regularGeneralMetricC2LorentzChartMatrixDomain
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    Set (C2Matrix period hPeriod) :=
  (((fun matrix => c2FiniteMatrixIdentity period hPeriod 4 + matrix) ⁻¹'
      c2FiniteMatrixUnitSet period hPeriod 4) ∩
    ((fun matrix => c2FiniteMatrixDeterminant period hPeriod 4
        (c2FiniteMatrixIdentity period hPeriod 4 + matrix)) ⁻¹'
      c2ScalarLocalRootTarget period hPeriod)) ∩
    regularGeneralMetricC2SelfAdjointRootDomain period hPeriod metric

theorem regularGeneralMetricC2LorentzChartMatrixDomain_isOpen
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    IsOpen (regularGeneralMetricC2LorentzChartMatrixDomain
      period hPeriod metric) := by
  have hExtended : Continuous
      (fun matrix : C2Matrix period hPeriod =>
        c2FiniteMatrixIdentity period hPeriod 4 + matrix) :=
    continuous_const.add continuous_id
  have hDeterminant : Continuous
      (fun matrix : C2Matrix period hPeriod =>
        c2FiniteMatrixDeterminant period hPeriod 4
          (c2FiniteMatrixIdentity period hPeriod 4 + matrix)) :=
    (c2FiniteMatrixDeterminant_contDiff period hPeriod 4).continuous.comp
      hExtended
  exact (((c2FiniteMatrixUnitSet_isOpen period hPeriod 4).preimage
      hExtended).inter
    ((c2ScalarLocalRootTarget_isOpen period hPeriod).preimage
      hDeterminant)).inter
    (regularGeneralMetricC2SelfAdjointRootDomain_isOpen
      period hPeriod metric)

theorem zero_mem_regularGeneralMetricC2LorentzChartMatrixDomain
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    (0 : C2Matrix period hPeriod) ∈
      regularGeneralMetricC2LorentzChartMatrixDomain
        period hPeriod metric := by
  refine ⟨⟨?_, ?_⟩, zero_mem_regularGeneralMetricC2SelfAdjointRootDomain
    period hPeriod metric⟩
  · simpa using c2FiniteMatrixIdentity_mem_unitSet period hPeriod 4
  · change c2FiniteMatrixDeterminant period hPeriod 4
        (c2FiniteMatrixIdentity period hPeriod 4 + 0) ∈
      c2ScalarLocalRootTarget period hPeriod
    rw [add_zero, c2FiniteMatrixDeterminant_identity]
    exact c2ScalarOne_mem_localRootTarget period hPeriod

/-- Membership of the original dependent core is exactly ambient matrix
membership of its underlying completed matrix. -/
theorem regularGeneralMetricC2LorentzChartDomain_mem_iff_matrixDomain
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variation : RegularGeneralMetricC2Core period hPeriod metric) :
    variation ∈ regularGeneralMetricC2LorentzChartDomain
        period hPeriod metric ↔
      variation.1 ∈ regularGeneralMetricC2LorentzChartMatrixDomain
        period hPeriod metric := by
  rfl

/-- Chart transport leaves the fixed ambient domain unchanged. -/
theorem regularGeneralMetricC2LorentzChartMatrixDomain_transport_eq
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hVariation :
      P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D.regularGeneralMetricSmoothC2Variation
          period hPeriod metric tensor ∈
        regularGeneralMetricC2LorentzChartDomain period hPeriod metric) :
    regularGeneralMetricC2LorentzChartMatrixDomain period hPeriod
        (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod
          metric tensor hVariation) =
      regularGeneralMetricC2LorentzChartMatrixDomain
        period hPeriod metric := by
  unfold regularGeneralMetricC2LorentzChartMatrixDomain
  rw [regularGeneralMetricC2LorentzChart_selfAdjointRootDomain_eq
    period hPeriod metric tensor hVariation]

/-- Gate marker for openness, zero membership, and exact core membership. -/
theorem regular_general_metric_c2_lorentz_chart_matrix_domain_gate
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    IsOpen (regularGeneralMetricC2LorentzChartMatrixDomain
        period hPeriod metric) ∧
      (0 : C2Matrix period hPeriod) ∈
        regularGeneralMetricC2LorentzChartMatrixDomain period hPeriod metric ∧
      ∀ variation : RegularGeneralMetricC2Core period hPeriod metric,
        variation ∈ regularGeneralMetricC2LorentzChartDomain
            period hPeriod metric ↔
          variation.1 ∈ regularGeneralMetricC2LorentzChartMatrixDomain
            period hPeriod metric := by
  exact ⟨regularGeneralMetricC2LorentzChartMatrixDomain_isOpen
      period hPeriod metric,
    zero_mem_regularGeneralMetricC2LorentzChartMatrixDomain
      period hPeriod metric,
    regularGeneralMetricC2LorentzChartDomain_mem_iff_matrixDomain
      period hPeriod metric⟩

end

end P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartMatrixDomain4D
end JanusFormal
