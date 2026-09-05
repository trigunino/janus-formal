import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricInvariantMaxwellStressVariation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarC2LocalRoot4D

/-! # Exact derivative of the scalar C² root at the unit -/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarC2LocalRootDerivative4D

set_option autoImplicit false
set_option maxHeartbeats 600000

noncomputable section

open scoped Manifold ContDiff Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2LocalRoot4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev C2Scalar :=
  CanonicalPhysicalScalarC2JetCore period hPeriod

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

/-- Multiplication by one half on the completed scalar C² core. -/
def c2ScalarHalfIdentity :
    C2Scalar period hPeriod →L[Real] C2Scalar period hPeriod :=
  (1 / 2 : Real) • ContinuousLinearMap.id Real (C2Scalar period hPeriod)

@[simp]
theorem c2ScalarHalfIdentity_apply (field : C2Scalar period hPeriod) :
    c2ScalarHalfIdentity period hPeriod field = (1 / 2 : Real) • field :=
  rfl

/-- The selected positive scalar root has derivative `½ id` at the unit. -/
theorem c2ScalarLocalRootBranch_hasFDerivAt_one :
    HasFDerivAt (c2ScalarLocalRootBranch period hPeriod)
      (c2ScalarHalfIdentity period hPeriod)
      (c2ScalarOne period hPeriod) := by
  let chart := c2ScalarLocalSquareChart period hPeriod
  let one := c2ScalarOne period hPeriod
  have hSelected : chart.symm one = one := by
    exact c2ScalarLocalRootBranch_at_one period hPeriod
  have hForward : HasFDerivAt chart
      (c2ScalarDoubleEquiv period hPeriod :
        C2Scalar period hPeriod →L[Real] C2Scalar period hPeriod)
      (chart.symm one) := by
    rw [hSelected]
    exact (c2ScalarSquare_hasFDerivAt period hPeriod one).congr_fderiv
      (c2ScalarDoubleEquiv_forward_eq period hPeriod).symm
  have hInverse := chart.hasFDerivAt_symm
    (c2ScalarOne_mem_localRootTarget period hPeriod) hForward
  exact hInverse.congr_fderiv (by
    apply ContinuousLinearMap.ext
    intro field
    rfl)

/-- Gate marker for the exact first derivative of the positive scalar root. -/
theorem canonical_physical_scalar_c2_local_root_derivative_gate :
    HasFDerivAt (c2ScalarLocalRootBranch period hPeriod)
      (c2ScalarHalfIdentity period hPeriod)
      (c2ScalarOne period hPeriod) :=
  c2ScalarLocalRootBranch_hasFDerivAt_one period hPeriod

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarC2LocalRootDerivative4D
end JanusFormal
