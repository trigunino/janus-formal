import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12C2RootHessian4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12VectorHessianPullback4D
namespace JanusFormal
namespace P0EFTJanusProgramPT12MobileGaugeTransportHessian4D

set_option autoImplicit false
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

/-- The coefficient packet is fixed; its acceleration comes from the actual root. -/
theorem identityGaugeTransport_hessian_zero (coefficients : GaugeC2Core period hPeriod)
    (first second : C2Matrix period hPeriod) :
    let product := c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) 4
    fderiv Real (fderiv Real (fun variation => gaugeCoefficientC2CoreFrameTransport
      period hPeriod (c2IdentityRootBranch period hPeriod variation) coefficients))
      0 first second =
      (-(1 / 8 : Real)) • gaugeCoefficientC2CoreFrameTransport period hPeriod
        (product first second + product second first) coefficients := by
  let linear := gaugeCoefficientC2CoreFrameTransportLeftCLM period hPeriod coefficients
  have hC2 : ContDiffAt Real 2 (c2IdentityRootBranch period hPeriod) 0 :=
    (c2IdentityRootBranch_contDiffOn period hPeriod).contDiffAt
      ((c2IdentityRootPerturbationDomain_isOpen period hPeriod).mem_nhds
        (zero_mem_c2IdentityRootPerturbationDomain period hPeriod))
  change fderiv Real (fderiv Real (linear ∘ c2IdentityRootBranch period hPeriod)) 0 first second = _
  rw [linearPostHessian linear _ 0 first second hC2, c2IdentityRootBranch_hessian_zero, map_smul]
  rfl

/-- Exact second derivative on the completed native metric core. -/
theorem mobileGaugeTransport_hessian_zero (metric : RegularGeneralLorentzMetric period hPeriod)
    (coefficients : GaugeC2Core period hPeriod)
    (first second : RegularGeneralMetricC2Core period hPeriod metric) :
    let product := c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) 4
    fderiv Real (fderiv Real (fun variation => regularGeneralMetricC2MobileGaugeCoefficientTransport
      period hPeriod metric variation coefficients)) 0 first second =
      (-(1 / 8 : Real)) • gaugeCoefficientC2CoreFrameTransport period hPeriod
        (product first.1 second.1 + product second.1 first.1) coefficients := by
  let linear := gaugeCoefficientC2CoreFrameTransportLeftCLM period hPeriod coefficients
  let projection := regularGeneralMetricC2GaugeCoefficientMetricMatrixCLM period hPeriod metric
  let field := linear ∘ c2IdentityRootBranch period hPeriod
  have hRoot : ContDiffAt Real 2 (c2IdentityRootBranch period hPeriod) 0 :=
    (c2IdentityRootBranch_contDiffOn period hPeriod).contDiffAt
      ((c2IdentityRootPerturbationDomain_isOpen period hPeriod).mem_nhds
        (zero_mem_c2IdentityRootPerturbationDomain period hPeriod))
  have hC2 : ContDiffAt Real 2 field 0 := linear.contDiff.contDiffAt.comp 0 hRoot
  have h := affineHessian field 0 projection hC2 first second
  simp only [zero_add] at h
  exact h.trans (identityGaugeTransport_hessian_zero period hPeriod coefficients first.1 second.1)

end
end P0EFTJanusProgramPT12MobileGaugeTransportHessian4D
end JanusFormal
