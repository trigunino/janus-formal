import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12C2InverseHessian4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12VectorHessianPullback4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGeneralMetricC2VolumeDerivative4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixInverseDerivative4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2Maxwell4D

/-! # Vanishing parameter acceleration of the native affine metric jets -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12MetricJetAcceleration4D

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

open P0EFTJanusProgramPT12VectorHessianPullback4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D

private abbrev C0Scalar := C(EffectiveQuotient period hPeriod, Real)

private def entryCLM (row column : Fin 4) :
    C2FiniteMatrix period hPeriod 4 →L[Real] C2Scalar period hPeriod :=
  (ContinuousLinearMap.proj column :
    (Fin 4 → C2Scalar period hPeriod) →L[Real] C2Scalar period hPeriod).comp
      (ContinuousLinearMap.proj row :
        C2FiniteMatrix period hPeriod 4 →L[Real] (Fin 4 → C2Scalar period hPeriod))

private def firstJetCLM (metric : RegularGeneralLorentzMetric period hPeriod) (direction : Fin 4) :
    C2Scalar period hPeriod →L[Real] C0Scalar period hPeriod :=
  ∑ index, (ContinuousLinearMap.mul Real (C0Scalar period hPeriod)
    (regularFrameFromPhysicalCoefficientContinuous period hPeriod metric direction index)).comp
      (canonicalPhysicalScalarC2FirstComponent period hPeriod index)

private theorem firstJetCLM_apply (metric : RegularGeneralLorentzMetric period hPeriod)
    (direction : Fin 4) (jet : C2Scalar period hPeriod) :
    firstJetCLM period hPeriod metric direction jet =
      regularFrameC2FirstDerivative period hPeriod metric direction jet := by
  simp only [firstJetCLM, sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.mul_apply', regularFrameC2FirstDerivative]

private def secondJetCLM (metric : RegularGeneralLorentzMetric period hPeriod) (outer inner : Fin 4) :
    C2Scalar period hPeriod →L[Real] C0Scalar period hPeriod :=
  ∑ physicalOuter, (ContinuousLinearMap.mul Real (C0Scalar period hPeriod)
    (regularFrameFromPhysicalCoefficientContinuous period hPeriod metric outer physicalOuter)).comp
      (∑ physicalInner, (
        (ContinuousLinearMap.mul Real (C0Scalar period hPeriod)
          (regularFrameFromPhysicalCoefficientDerivativeContinuous period hPeriod metric
            inner physicalInner physicalOuter)).comp
            (canonicalPhysicalScalarC2FirstComponent period hPeriod physicalInner) +
        (ContinuousLinearMap.mul Real (C0Scalar period hPeriod)
          (regularFrameFromPhysicalCoefficientContinuous period hPeriod metric inner physicalInner)).comp
            (canonicalPhysicalScalarC2SecondComponent period hPeriod physicalOuter physicalInner)))

private theorem secondJetCLM_apply (metric : RegularGeneralLorentzMetric period hPeriod)
    (outer inner : Fin 4) (jet : C2Scalar period hPeriod) :
    secondJetCLM period hPeriod metric outer inner jet =
      regularFrameC2SecondDerivative period hPeriod metric outer inner jet := by
  simp only [secondJetCLM, sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.mul_apply', add_apply, regularFrameC2SecondDerivative]

private theorem metricReadout_hessian_zero (metric : RegularGeneralLorentzMetric period hPeriod)
    (linear : C2FiniteMatrix period hPeriod 4 →L[Real] C0Scalar period hPeriod)
    (first second : RegularGeneralMetricC2Core period hPeriod metric) :
    fderiv Real (fderiv Real (linear ∘ regularGeneralMetricC2MetricMatrix period hPeriod metric))
      0 first second = 0 := by
  let product := c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) 4
    (regularFrameMetricC2Matrix period hPeriod metric)
  let projection : RegularGeneralMetricC2Core period hPeriod metric →L[Real]
      C2FiniteMatrix period hPeriod 4 := generalMetricRelativeC2CoreToMatrix period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric) metric.metric
  change fderiv Real (fderiv Real (fun variation => (linear.comp product)
    (c2FiniteMatrixIdentity period hPeriod 4 + projection variation))) 0 first second = 0
  rw [affineHessian _ _ projection (linear.comp product).contDiff.contDiffAt]
  have hDerivative : fderiv Real (linear.comp product) = fun _ => linear.comp product :=
    funext fun _ => (linear.comp product).fderiv
  simp only [hDerivative, fderiv_const_apply, zero_apply]

theorem nativeMetricCoefficient_hessian_zero
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (first second : RegularGeneralMetricC2Core period hPeriod metric) (row column : Fin 4) :
    fderiv Real (fderiv Real (fun variation => regularGeneralMetricC0MetricCoefficient
      period hPeriod metric variation row column)) 0 first second = 0 :=
  metricReadout_hessian_zero period hPeriod metric
    ((canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod).comp
      (entryCLM period hPeriod row column)) first second

theorem nativeMetricFirstJet_hessian_zero
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (first second : RegularGeneralMetricC2Core period hPeriod metric) (direction row column : Fin 4) :
    fderiv Real (fderiv Real (fun variation => regularGeneralMetricC0MetricFirstDerivative
      period hPeriod metric variation direction row column)) 0 first second = 0 := by
  let linear := (firstJetCLM period hPeriod metric direction).comp (entryCLM period hPeriod row column)
  have hEq : (fun variation => regularGeneralMetricC0MetricFirstDerivative
      period hPeriod metric variation direction row column) =
      linear ∘ regularGeneralMetricC2MetricMatrix period hPeriod metric := by
    funext variation
    exact (firstJetCLM_apply period hPeriod metric direction _).symm
  rw [hEq]
  exact metricReadout_hessian_zero period hPeriod metric linear first second

theorem nativeMetricSecondJet_hessian_zero
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (first second : RegularGeneralMetricC2Core period hPeriod metric) (outer inner row column : Fin 4) :
    fderiv Real (fderiv Real (fun variation => regularGeneralMetricC0MetricSecondDerivative
      period hPeriod metric variation outer inner row column)) 0 first second = 0 := by
  let linear := (secondJetCLM period hPeriod metric outer inner).comp (entryCLM period hPeriod row column)
  have hEq : (fun variation => regularGeneralMetricC0MetricSecondDerivative
      period hPeriod metric variation outer inner row column) =
      linear ∘ regularGeneralMetricC2MetricMatrix period hPeriod metric := by
    funext variation
    exact (secondJetCLM_apply period hPeriod metric outer inner _).symm
  rw [hEq]
  exact metricReadout_hessian_zero period hPeriod metric linear first second

end
end P0EFTJanusProgramPT12MetricJetAcceleration4D
end JanusFormal
