import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalC2IdentityRootDerivative4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2GaugeCoefficientMaxwellAction4D

/-! # Centre derivative of the moving-frame Maxwell coefficient transport

The identity-root derivative is half the metric-relative direction. The
transpose root transport consequently induces the gauge velocity
`δa = (1/2) Hᵀa`, even when the independent gauge coefficients are fixed.
-/

namespace JanusFormal
namespace P0EFTJanusPairedStrongMaxwellMetricTransportDerivative4D

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 1200000
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

/-- At the identity, the Sylvester equation is `D + D = H`. -/
theorem c2IdentityRootDerivative_zero_apply (direction : C2Matrix period hPeriod) :
    c2IdentityRootDerivative period hPeriod 0
        (zero_mem_c2IdentityRootPerturbationDomain period hPeriod) direction =
      (1 / 2 : Real) • direction := by
  let derivative := c2IdentityRootDerivative period hPeriod 0
    (zero_mem_c2IdentityRootPerturbationDomain period hPeriod) direction
  have hSylvester := c2IdentityRootDerivative_sylvester period hPeriod 0
    (zero_mem_c2IdentityRootPerturbationDomain period hPeriod) direction
  rw [c2IdentityRootBranch_zero] at hSylvester
  change
    c2FiniteMatrixProduct period hPeriod 4 (c2FiniteMatrixIdentity period hPeriod 4) derivative +
      c2FiniteMatrixProduct period hPeriod 4 derivative (c2FiniteMatrixIdentity period hPeriod 4) =
        direction at hSylvester
  rw [c2FiniteMatrixProduct_identity_left, c2FiniteMatrixProduct_identity_right] at hSylvester
  have hHalf := congrArg (fun value : C2Matrix period hPeriod => (1 / 2 : Real) • value)
    hSylvester
  simpa only [smul_add, ← add_smul, show (1 / 2 : Real) + 1 / 2 = 1 by norm_num,
    one_smul] using hHalf

theorem c2IdentityRootDerivative_zero :
    c2IdentityRootDerivative period hPeriod 0
        (zero_mem_c2IdentityRootPerturbationDomain period hPeriod) =
      (1 / 2 : Real) • ContinuousLinearMap.id Real (C2Matrix period hPeriod) := by
  apply ContinuousLinearMap.ext
  intro direction
  exact c2IdentityRootDerivative_zero_apply period hPeriod direction

theorem c2IdentityRootBranch_hasFDerivAt_zero :
    HasFDerivAt (c2IdentityRootBranch period hPeriod)
      ((1 / 2 : Real) • ContinuousLinearMap.id Real (C2Matrix period hPeriod)) 0 := by
  have hDerivative := c2IdentityRootBranch_hasFDerivAt period hPeriod 0
    (zero_mem_c2IdentityRootPerturbationDomain period hPeriod)
  rw [c2IdentityRootDerivative_zero] at hDerivative
  exact hDerivative

/-- Continuous linear dependence of the transport on its root matrix,
with the coefficient packet fixed. -/
def gaugeCoefficientC2CoreFrameTransportLeftCLM (coefficients : GaugeC2Core period hPeriod) :
    C2Matrix period hPeriod →L[Real] GaugeC2Core period hPeriod :=
  ContinuousLinearMap.pi fun baseIndex =>
    ContinuousLinearMap.pi fun component =>
      ∑ movingIndex : Fin 4,
        ((canonicalPhysicalScalarC2JetCoreProduct period hPeriod).flip
          (coefficients movingIndex component)).comp
          (gaugeFrameTransportC2MatrixEntryCLM period hPeriod movingIndex baseIndex)

@[simp]
theorem gaugeCoefficientC2CoreFrameTransportLeftCLM_apply
    (coefficients : GaugeC2Core period hPeriod) (root : C2Matrix period hPeriod) :
    gaugeCoefficientC2CoreFrameTransportLeftCLM period hPeriod coefficients root =
      gaugeCoefficientC2CoreFrameTransport period hPeriod root coefficients := by
  funext baseIndex component
  simp only [gaugeCoefficientC2CoreFrameTransportLeftCLM, ContinuousLinearMap.pi_apply,
    sum_apply, ContinuousLinearMap.comp_apply]
  rfl

/-- Exact root-induced coefficient derivative, with no independent gauge
variation. The factor one half comes from the proved Sylvester equation. -/
theorem c2IdentityGaugeCoefficientTransport_hasFDerivAt_zero
    (coefficients : GaugeC2Core period hPeriod) :
    HasFDerivAt
      (fun variation => gaugeCoefficientC2CoreFrameTransport period hPeriod
        (c2IdentityRootBranch period hPeriod variation) coefficients)
      ((1 / 2 : Real) •
        gaugeCoefficientC2CoreFrameTransportLeftCLM period hPeriod coefficients) 0 := by
  have hDerivative :=
    (gaugeCoefficientC2CoreFrameTransportLeftCLM period hPeriod coefficients).hasFDerivAt.comp 0
      (c2IdentityRootBranch_hasFDerivAt_zero period hPeriod)
  simpa only [Function.comp_def, gaugeCoefficientC2CoreFrameTransportLeftCLM_apply,
    ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_id] using hDerivative

theorem c2IdentityGaugeCoefficientTransport_fderiv_zero_apply
    (coefficients : GaugeC2Core period hPeriod) (direction : C2Matrix period hPeriod) :
    fderiv Real
        (fun variation => gaugeCoefficientC2CoreFrameTransport period hPeriod
          (c2IdentityRootBranch period hPeriod variation) coefficients) 0 direction =
      (1 / 2 : Real) •
        gaugeCoefficientC2CoreFrameTransport period hPeriod direction coefficients := by
  simpa only [smul_apply,
    gaugeCoefficientC2CoreFrameTransportLeftCLM_apply] using
    congrArg (fun derivative => derivative direction)
      (c2IdentityGaugeCoefficientTransport_hasFDerivAt_zero period hPeriod coefficients).fderiv

/-- The same derivative on the native completed metric core. -/
theorem regularGeneralMetricC2MobileGaugeCoefficientTransport_hasFDerivAt_zero
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (coefficients : GaugeC2Core period hPeriod) :
    HasFDerivAt
      (fun variation => regularGeneralMetricC2MobileGaugeCoefficientTransport
        period hPeriod metric variation coefficients)
      ((1 / 2 : Real) •
        (gaugeCoefficientC2CoreFrameTransportLeftCLM period hPeriod coefficients).comp
          (regularGeneralMetricC2GaugeCoefficientMetricMatrixCLM period hPeriod metric)) 0 := by
  have hDerivative :=
    (c2IdentityGaugeCoefficientTransport_hasFDerivAt_zero period hPeriod coefficients).comp
      (0 : RegularGeneralMetricC2Core period hPeriod metric)
      (regularGeneralMetricC2GaugeCoefficientMetricMatrixCLM period hPeriod metric).hasFDerivAt
  simpa only [Function.comp_def, regularGeneralMetricC2MobileGaugeCoefficientTransport,
    ContinuousLinearMap.smul_comp] using hDerivative

/-- In components this is `δa(j,c) = (1/2) Σᵢ H(i,j) a(i,c)`. -/
theorem regularGeneralMetricC2MobileGaugeCoefficientTransport_fderiv_zero_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (coefficients : GaugeC2Core period hPeriod)
    (direction : RegularGeneralMetricC2Core period hPeriod metric) :
    fderiv Real
        (fun variation => regularGeneralMetricC2MobileGaugeCoefficientTransport
          period hPeriod metric variation coefficients) 0 direction =
      (1 / 2 : Real) • gaugeCoefficientC2CoreFrameTransport period hPeriod
        (regularGeneralMetricC2GaugeCoefficientMetricMatrixCLM period hPeriod metric direction)
        coefficients := by
  simpa only [smul_apply, ContinuousLinearMap.comp_apply,
    gaugeCoefficientC2CoreFrameTransportLeftCLM_apply] using
    congrArg (fun derivative => derivative direction)
      (regularGeneralMetricC2MobileGaugeCoefficientTransport_hasFDerivAt_zero
        period hPeriod metric coefficients).fderiv

end
end P0EFTJanusPairedStrongMaxwellMetricTransportDerivative4D
end JanusFormal
