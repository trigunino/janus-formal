import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPairedStrongMaxwellMetricTransportDerivative4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12BilinearHessian4D
namespace JanusFormal
namespace P0EFTJanusProgramPT12C2RootHessian4D

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

/-- The genuine root acceleration, including both noncommuting products. -/
theorem c2IdentityRootBranch_hessian_zero (first second : C2Matrix period hPeriod) :
    let product := c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) 4
    fderiv Real (fderiv Real (c2IdentityRootBranch period hPeriod)) 0 first second =
      (-(1 / 8 : Real)) • (product first second + product second first) := by
  let root := c2IdentityRootBranch period hPeriod
  let product := c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) 4
  have hC2 : ContDiffAt Real 2 root 0 :=
    (c2IdentityRootBranch_contDiffOn period hPeriod).contDiffAt
      ((c2IdentityRootPerturbationDomain_isOpen period hPeriod).mem_nhds
        (zero_mem_c2IdentityRootPerturbationDomain period hPeriod))
  have hNear : (fun current => product (root current) (root current)) =ᶠ[𝓝 0]
      (fun current => c2FiniteMatrixIdentity period hPeriod 4 + current) := by
    filter_upwards [(c2IdentityRootPerturbationDomain_isOpen period hPeriod).mem_nhds
      (zero_mem_c2IdentityRootPerturbationDomain period hPeriod)] with current hCurrent
    exact c2IdentityRootBranch_square period hPeriod hCurrent
  have hAffine (current : C2Matrix period hPeriod) :
      fderiv Real (fun value => c2FiniteMatrixIdentity period hPeriod 4 + value) current =
        ContinuousLinearMap.id Real (C2Matrix period hPeriod) := by
    simpa only [Pi.add_def, zero_add, ContinuousLinearMap.id_apply] using
      ((hasFDerivAt_const (c2FiniteMatrixIdentity period hPeriod 4) current).add
        (ContinuousLinearMap.id Real (C2Matrix period hPeriod)).hasFDerivAt).fderiv
  have hZero : fderiv Real (fderiv Real (fun current => product (root current) (root current)))
      0 first second = 0 := by
    rw [hNear.fderiv.fderiv_eq]
    rw [show fderiv Real (fun current : C2Matrix period hPeriod =>
      c2FiniteMatrixIdentity period hPeriod 4 + current) =
        (fun _ => ContinuousLinearMap.id Real (C2Matrix period hPeriod)) from funext hAffine]
    simp only [fderiv_const_apply, zero_apply]
  rw [bilinearHessian product root root 0 first second hC2 hC2] at hZero
  have hRoot := (c2IdentityRootBranch_hasFDerivAt_zero period hPeriod).fderiv
  simp only [root, c2IdentityRootBranch_zero, hRoot, smul_apply,
    ContinuousLinearMap.id_apply, product, c2FiniteMatrixProduct_identity_left,
    c2FiniteMatrixProduct_identity_right, map_smul, smul_smul] at hZero
  let acceleration := fderiv Real (fderiv Real (c2IdentityRootBranch period hPeriod)) 0 first second
  change acceleration + (1 / 2 * (1 / 2) : Real) • product first second +
    (acceleration + (1 / 2 * (1 / 2) : Real) • product second first) = 0 at hZero
  change acceleration = _
  calc
    acceleration = acceleration - (1 / 2 : Real) •
        (acceleration + (1 / 2 * (1 / 2) : Real) • product first second +
          (acceleration + (1 / 2 * (1 / 2) : Real) • product second first)) := by
      rw [hZero, smul_zero, sub_zero]
    _ = _ := by module

end
end P0EFTJanusProgramPT12C2RootHessian4D
end JanusFormal
