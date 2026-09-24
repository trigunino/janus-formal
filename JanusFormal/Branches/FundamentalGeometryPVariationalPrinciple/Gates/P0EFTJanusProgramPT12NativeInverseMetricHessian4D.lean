import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12C2InverseHessian4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12VectorHessianPullback4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGeneralMetricC2VolumeDerivative4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixInverseDerivative4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2Maxwell4D

/-! # Exact second derivative of the native inverse metric -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12NativeInverseMetricHessian4D

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

noncomputable section

open Filter
open scoped Manifold ContDiff Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixInverse4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixInverseDerivative4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPGeneralMetricC2VolumeDerivative4D
open P0EFTJanusProgramPRegularFrameMetricInverse4D
open P0EFTJanusProgramPRegularGeneralMetricC2Maxwell4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

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

open P0EFTJanusProgramPT12C2InverseHessian4D
open P0EFTJanusProgramPT12VectorHessianPullback4D

theorem nativeRelativeInverse_hessian (metric : RegularGeneralLorentzMetric period hPeriod)
    (first second : RegularGeneralMetricC2Core period hPeriod metric) :
    let frame := regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric
    let product := c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) 4
    fderiv Real (fderiv Real (generalMetricRelativeC2InverseMatrix
        period hPeriod frame metric.metric)) 0 first second =
      product second.1 first.1 + product first.1 second.1 := by
  let frame := regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric
  let projection : RegularGeneralMetricC2Core period hPeriod metric →L[Real]
      C2FiniteMatrix period hPeriod 4 :=
    generalMetricRelativeC2CoreToMatrix period hPeriod frame metric.metric
  have hC2 : ContDiffAt Real 2 (c2FiniteMatrixInverse period hPeriod 4)
      (c2FiniteMatrixIdentity period hPeriod 4) :=
    ((c2FiniteMatrixInverse_contDiffOn period hPeriod 4).contDiffAt
      ((c2FiniteMatrixUnitSet_isOpen period hPeriod 4).mem_nhds
        (c2FiniteMatrixIdentity_mem_unitSet period hPeriod 4))).of_le (by decide)
  change fderiv Real (fderiv Real (fun variation => c2FiniteMatrixInverse period hPeriod 4
    (c2FiniteMatrixIdentity period hPeriod 4 + projection variation))) 0 first second = _
  rw [affineHessian _ _ projection hC2]
  exact c2Inverse_hessian_identity period hPeriod 4 first.1 second.1

theorem nativeInverseMetric_hessian (metric : RegularGeneralLorentzMetric period hPeriod)
    (first second : RegularGeneralMetricC2Core period hPeriod metric) :
    let product := c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) 4
    fderiv Real (fderiv Real (regularGeneralMetricC2InverseMetricMatrix
        period hPeriod metric)) 0 first second =
      product (product second.1 first.1 + product first.1 second.1)
        (regularFrameMetricInverseC2Matrix period hPeriod metric) := by
  let frame := regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric
  let inverse : RegularGeneralMetricC2Core period hPeriod metric → C2FiniteMatrix period hPeriod 4 :=
    generalMetricRelativeC2InverseMatrix period hPeriod frame metric.metric
  let linear := (c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) 4).flip
    (regularFrameMetricInverseC2Matrix period hPeriod metric)
  have hC2 : ContDiffAt Real 2 inverse 0 :=
    ((generalMetricRelativeC2InverseMatrix_contDiffOn period hPeriod frame metric.metric).contDiffAt
      ((generalMetricRelativeC2OpenDomain_isOpen period hPeriod frame metric.metric).mem_nhds
        (zero_mem_generalMetricRelativeC2OpenDomain period hPeriod frame metric.metric))).of_le
      (by decide)
  change fderiv Real (fderiv Real (linear ∘ inverse)) 0 first second = _
  rw [linearPostHessian linear inverse 0 first second hC2]
  exact congrArg linear (nativeRelativeInverse_hessian period hPeriod metric first second)

end
end P0EFTJanusProgramPT12NativeInverseMetricHessian4D
end JanusFormal
