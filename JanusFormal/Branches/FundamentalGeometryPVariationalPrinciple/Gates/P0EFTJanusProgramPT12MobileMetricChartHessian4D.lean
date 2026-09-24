import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12GraphHessian4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12MobileGaugeTransportHessian4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusStrongMaxwellMetricCenterFirstVariation4D
namespace JanusFormal
namespace P0EFTJanusProgramPT12MobileMetricChartHessian4D

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 600000

noncomputable section
open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixInverse4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2IdentityRootBranch4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2IdentityRootDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalMetricGaugeCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2GaugeCoefficientFrameTransport4D
open P0EFTJanusProgramPRegularGeneralMetricC2GaugeCoefficientMaxwellAction4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev C2Scalar := CanonicalPhysicalScalarC2JetCore period hPeriod
private abbrev C2Matrix := C2FiniteMatrix period hPeriod 4
private abbrev GaugeC2Core := RegularGeneralMetricC2GaugeCoefficientCore period hPeriod

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

open Filter
open scoped Topology
open P0EFTJanusPairedStrongMaxwellMetricTransportDerivative4D
open P0EFTJanusProgramPT12BilinearHessian4D

open P0EFTJanusProgramPT12C2RootHessian4D
open P0EFTJanusProgramPT12VectorHessianPullback4D

open P0EFTJanusProgramPT12MobileGaugeTransportHessian4D
open P0EFTJanusStrongMaxwellMetricCenterFirstVariation4D
open P0EFTJanusProgramPT12GraphHessian4D
variable (metric : RegularGeneralLorentzMetric period hPeriod)
  (coefficients : GaugeC2Core period hPeriod)

/-- The actual moving-frame metric chart with independent gauge coordinates fixed. -/
def mobileMetricChart (variation : RegularGeneralMetricC2Core period hPeriod metric) :
    RegularGeneralMetricC2Core period hPeriod metric × GaugeC2Core period hPeriod :=
  (variation, regularGeneralMetricC2MobileGaugeCoefficientTransport period hPeriod metric variation coefficients)

@[simp]
theorem mobileMetricChart_zero : mobileMetricChart period hPeriod metric coefficients 0 = (0, coefficients) := by
  simp only [mobileMetricChart, regularGeneralMetricC2MobileGaugeCoefficientTransport_zero]

theorem mobileMetricChart_contDiffAt_zero :
    ContDiffAt Real 2 (mobileMetricChart period hPeriod metric coefficients) 0 := by
  let linear := gaugeCoefficientC2CoreFrameTransportLeftCLM period hPeriod coefficients
  let projection := regularGeneralMetricC2GaugeCoefficientMetricMatrixCLM period hPeriod metric
  have hRoot : ContDiffAt Real 2 (c2IdentityRootBranch period hPeriod) (projection 0) := by
    rw [map_zero]
    exact (c2IdentityRootBranch_contDiffOn period hPeriod).contDiffAt
      ((c2IdentityRootPerturbationDomain_isOpen period hPeriod).mem_nhds
        (zero_mem_c2IdentityRootPerturbationDomain period hPeriod))
  exact contDiffAt_id.prodMk
    (linear.contDiff.contDiffAt.comp 0 (hRoot.comp 0 projection.contDiff.contDiffAt))

theorem mobileMetricChart_fderiv_zero (direction : RegularGeneralMetricC2Core period hPeriod metric) :
    fderiv Real (mobileMetricChart period hPeriod metric coefficients) 0 direction =
      (direction, (1 / 2 : Real) • gaugeCoefficientC2CoreFrameTransport period hPeriod direction.1 coefficients) := by
  unfold mobileMetricChart
  rw [graph_fderiv _ 0 direction
    (regularGeneralMetricC2MobileGaugeCoefficientTransport_hasFDerivAt_zero
      period hPeriod metric coefficients).differentiableAt,
    regularGeneralMetricC2MobileGaugeCoefficientTransport_fderiv_zero_apply]
  rfl
theorem mobileMetricChart_hessian_zero (first second : RegularGeneralMetricC2Core period hPeriod metric) :
    let product := c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) 4
    fderiv Real (fderiv Real (mobileMetricChart period hPeriod metric coefficients)) 0 first second =
      (0, (-(1 / 8 : Real)) • gaugeCoefficientC2CoreFrameTransport period hPeriod
        (product first.1 second.1 + product second.1 first.1) coefficients) := by
  have hC2 := (mobileMetricChart_contDiffAt_zero period hPeriod metric coefficients).snd
  have h := graph_hessian (fun variation => regularGeneralMetricC2MobileGaugeCoefficientTransport
    period hPeriod metric variation coefficients) 0 first second hC2
  exact h.trans (congrArg (fun acceleration =>
    ((0 : RegularGeneralMetricC2Core period hPeriod metric), acceleration))
      (mobileGaugeTransport_hessian_zero period hPeriod metric coefficients first second))

end
end P0EFTJanusProgramPT12MobileMetricChartHessian4D
end JanusFormal
