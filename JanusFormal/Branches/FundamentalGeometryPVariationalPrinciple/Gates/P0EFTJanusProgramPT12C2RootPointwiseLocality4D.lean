import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12C2RootHessian4D
namespace JanusFormal
namespace P0EFTJanusProgramPT12C2RootPointwiseLocality4D

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

open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
private abbrev Matrix4 := Matrix (Fin 4) (Fin 4) Real

private def finiteSylvester (root : Matrix4) : Matrix4 →ₗ[Real] Matrix4 where
  toFun direction := root * direction + direction * root
  map_add' first second := by simp only [Matrix.mul_add, Matrix.add_mul]; abel
  map_smul' scalar direction := by simp only [Matrix.mul_smul, Matrix.smul_mul, smul_add, RingHom.id_apply]

def constantC2Matrix (matrix : Matrix4) : C2Matrix period hPeriod :=
  fun row column => smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
    (⟨fun _ => matrix row column, contMDiff_const⟩ : SmoothScalarField period hPeriod)

theorem constantC2Matrix_valueAt (matrix : Matrix4) (point : EffectiveQuotient period hPeriod) :
    c2FiniteMatrixValueAt period hPeriod 4 (constantC2Matrix period hPeriod matrix) point = matrix := rfl

theorem c2IdentityRootDerivative_sylvester_valueAt
    (variation : C2Matrix period hPeriod) (hVariation : variation ∈ c2IdentityRootPerturbationDomain period hPeriod)
    (direction : C2Matrix period hPeriod) (point : EffectiveQuotient period hPeriod) :
    let root := c2FiniteMatrixValueAt period hPeriod 4 (c2IdentityRootBranch period hPeriod variation) point
    let velocity := c2FiniteMatrixValueAt period hPeriod 4 (c2IdentityRootDerivative period hPeriod variation hVariation direction) point
    root * velocity + velocity * root = c2FiniteMatrixValueAt period hPeriod 4 direction point := by
  have h := congrArg (fun matrix => c2FiniteMatrixValueAt period hPeriod 4 matrix point)
    (c2IdentityRootDerivative_sylvester period hPeriod variation hVariation direction)
  simpa only [c2FiniteMatrixSylvester, add_apply, ContinuousLinearMap.flip_apply,
    c2FiniteMatrixValueAt_add, c2FiniteMatrixValueAt_product] using h

/-- Surjectivity of the actual C2 derivative forces pointwise finite Sylvester invertibility. -/
theorem c2IdentityRoot_pointwise_sylvester_injective
    (variation : C2Matrix period hPeriod) (hVariation : variation ∈ c2IdentityRootPerturbationDomain period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    Function.Injective (fun direction : Matrix4 =>
      c2FiniteMatrixValueAt period hPeriod 4 (c2IdentityRootBranch period hPeriod variation) point * direction +
        direction * c2FiniteMatrixValueAt period hPeriod 4 (c2IdentityRootBranch period hPeriod variation) point) := by
  let root := c2FiniteMatrixValueAt period hPeriod 4 (c2IdentityRootBranch period hPeriod variation) point
  change Function.Injective (finiteSylvester root)
  apply (LinearMap.injective_iff_surjective).2
  intro target
  refine ⟨c2FiniteMatrixValueAt period hPeriod 4
    (c2IdentityRootDerivative period hPeriod variation hVariation (constantC2Matrix period hPeriod target)) point, ?_⟩
  exact c2IdentityRootDerivative_sylvester_valueAt period hPeriod variation hVariation _ point

theorem c2IdentityRootDerivative_valueAt_zero
    (variation : C2Matrix period hPeriod) (hVariation : variation ∈ c2IdentityRootPerturbationDomain period hPeriod)
    (direction : C2Matrix period hPeriod) (point : EffectiveQuotient period hPeriod)
    (hDirection : c2FiniteMatrixValueAt period hPeriod 4 direction point = 0) :
    c2FiniteMatrixValueAt period hPeriod 4 (c2IdentityRootDerivative period hPeriod variation hVariation direction) point = 0 := by
  apply c2IdentityRoot_pointwise_sylvester_injective period hPeriod variation hVariation point
  dsimp only
  rw [c2IdentityRootDerivative_sylvester_valueAt, hDirection, mul_zero, zero_mul, add_zero]

end
end P0EFTJanusProgramPT12C2RootPointwiseLocality4D
end JanusFormal
