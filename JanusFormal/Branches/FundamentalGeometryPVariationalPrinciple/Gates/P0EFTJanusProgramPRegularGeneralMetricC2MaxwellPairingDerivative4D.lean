import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPC2MaxwellMatrixContractionDerivative4D

/-! # Exact regular general-metric C² Maxwell pairing derivative -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2MaxwellPairingDerivative4D

set_option autoImplicit false
set_option maxHeartbeats 1200000

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
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularFrameMetricInverse4D
open P0EFTJanusProgramPRegularFrameMaxwellCurvature4D
open P0EFTJanusProgramPRegularGeneralMetricC2Maxwell4D
open P0EFTJanusProgramPRegularGeneralMetricC2InverseMetricDerivative4D
open P0EFTJanusProgramPC2MaxwellMatrixContractionDerivative4D

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

/-- Fréchet derivative of the full two-component Maxwell pairing. -/
def regularGeneralMetricC2MaxwellPairingDerivativeAtZero
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (first second : SmoothAbelianGaugePotential period hPeriod) :
    RegularGeneralMetricC2Core period hPeriod metric →L[Real]
      C2Scalar period hPeriod :=
  ∑ component : Fin 2,
    (c2MaxwellMatrixContractionDerivativeAt period hPeriod
      (regularFrameMetricInverseC2Matrix period hPeriod metric)
      (regularFrameGaugeCurvatureC2Matrix
        period hPeriod metric first component)
      (regularFrameGaugeCurvatureC2Matrix
        period hPeriod metric second component)).comp
      (regularGeneralMetricC2InverseMetricMatrixDerivativeAtZero
        period hPeriod metric)

theorem regularGeneralMetricC2MaxwellPairing_hasFDerivAt_zero
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (first second : SmoothAbelianGaugePotential period hPeriod) :
    HasFDerivAt
      (regularGeneralMetricC2MaxwellPairing
        period hPeriod metric first second)
      (regularGeneralMetricC2MaxwellPairingDerivativeAtZero
        period hPeriod metric first second) 0 := by
  let inverse := regularFrameMetricInverseC2Matrix period hPeriod metric
  let inverseMap := regularGeneralMetricC2InverseMetricMatrix
    period hPeriod metric
  let inverseDerivative :=
    regularGeneralMetricC2InverseMetricMatrixDerivativeAtZero
      period hPeriod metric
  let curvatureFirst := regularFrameGaugeCurvatureC2Matrix
    period hPeriod metric first
  let curvatureSecond := regularFrameGaugeCurvatureC2Matrix
    period hPeriod metric second
  let componentFunction := fun component : Fin 2 =>
    fun direction : RegularGeneralMetricC2Core period hPeriod metric =>
      c2MaxwellMatrixContraction period hPeriod (inverseMap direction)
        (curvatureFirst component) (curvatureSecond component)
  let componentDerivative := fun component : Fin 2 =>
    (c2MaxwellMatrixContractionDerivativeAt period hPeriod inverse
      (curvatureFirst component) (curvatureSecond component)).comp
        inverseDerivative
  have hInner :=
    regularGeneralMetricC2InverseMetricMatrix_hasFDerivAt_zero
      period hPeriod metric
  have hComponent (component : Fin 2) : HasFDerivAt
      (componentFunction component) (componentDerivative component) 0 := by
    have hOuter : HasFDerivAt
        (fun candidate => c2MaxwellMatrixContraction period hPeriod candidate
          (curvatureFirst component) (curvatureSecond component))
        (c2MaxwellMatrixContractionDerivativeAt period hPeriod inverse
          (curvatureFirst component) (curvatureSecond component))
        (inverseMap 0) := by
      have hBase : inverseMap 0 = inverse := by
        exact regularGeneralMetricC2InverseMetricMatrix_zero
          period hPeriod metric
      rw [hBase]
      exact c2MaxwellMatrixContraction_hasFDerivAt period hPeriod inverse
        (curvatureFirst component) (curvatureSecond component)
    exact hOuter.comp 0 hInner
  have hSum := HasFDerivAt.sum (u := Finset.univ)
    (fun component _ => hComponent component)
  have hTarget : HasFDerivAt
      (regularGeneralMetricC2MaxwellPairing
        period hPeriod metric first second)
      (∑ component : Fin 2, componentDerivative component) 0 := by
    apply hSum.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall fun direction => by
      simp only [Finset.sum_apply]
      rfl
  simpa [regularGeneralMetricC2MaxwellPairingDerivativeAtZero,
    componentDerivative, inverse, inverseDerivative, curvatureFirst,
    curvatureSecond] using hTarget

@[simp]
theorem regularGeneralMetricC2MaxwellPairingDerivativeAtZero_apply_inverse
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (first second : SmoothAbelianGaugePotential period hPeriod)
    (direction : RegularGeneralMetricC2Core period hPeriod metric) :
    regularGeneralMetricC2MaxwellPairingDerivativeAtZero
        period hPeriod metric first second direction =
      ∑ component : Fin 2,
        c2MaxwellMatrixContractionVelocity period hPeriod
          (regularFrameMetricInverseC2Matrix period hPeriod metric)
          (regularGeneralMetricC2InverseMetricMatrixDerivativeAtZero
            period hPeriod metric direction)
          (regularFrameGaugeCurvatureC2Matrix
            period hPeriod metric first component)
          (regularFrameGaugeCurvatureC2Matrix
            period hPeriod metric second component) := by
  unfold regularGeneralMetricC2MaxwellPairingDerivativeAtZero
  simp only [sum_apply, ContinuousLinearMap.comp_apply]
  apply Finset.sum_congr rfl
  intro component _
  exact c2MaxwellMatrixContractionDerivativeAt_apply period hPeriod
    (regularFrameMetricInverseC2Matrix period hPeriod metric)
    (regularGeneralMetricC2InverseMetricMatrixDerivativeAtZero
      period hPeriod metric direction)
    (regularFrameGaugeCurvatureC2Matrix
      period hPeriod metric first component)
    (regularFrameGaugeCurvatureC2Matrix
      period hPeriod metric second component)

@[simp]
theorem regularGeneralMetricC2MaxwellPairingDerivativeAtZero_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (first second : SmoothAbelianGaugePotential period hPeriod)
    (direction : RegularGeneralMetricC2Core period hPeriod metric) :
    regularGeneralMetricC2MaxwellPairingDerivativeAtZero
        period hPeriod metric first second direction =
      ∑ component : Fin 2,
        c2MaxwellMatrixContractionVelocity period hPeriod
          (regularFrameMetricInverseC2Matrix period hPeriod metric)
          (-c2FiniteMatrixProduct
            (period := period) (hPeriod := hPeriod) 4 direction.1
              (regularFrameMetricInverseC2Matrix period hPeriod metric))
          (regularFrameGaugeCurvatureC2Matrix
            period hPeriod metric first component)
          (regularFrameGaugeCurvatureC2Matrix
            period hPeriod metric second component) := by
  rw [regularGeneralMetricC2MaxwellPairingDerivativeAtZero_apply_inverse]
  have hVelocity :=
    regularGeneralMetricC2InverseMetricMatrixDerivativeAtZero_apply
      period hPeriod metric direction
  apply Finset.sum_congr rfl
  intro component _
  exact congrArg
    (fun velocity => c2MaxwellMatrixContractionVelocity period hPeriod
      (regularFrameMetricInverseC2Matrix period hPeriod metric) velocity
      (regularFrameGaugeCurvatureC2Matrix
        period hPeriod metric first component)
      (regularFrameGaugeCurvatureC2Matrix
        period hPeriod metric second component)) hVelocity

/-- Gate marker for the actual metric derivative of the C² Maxwell pairing. -/
theorem regular_general_metric_c2_maxwell_pairing_derivative_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (first second : SmoothAbelianGaugePotential period hPeriod) :
    HasFDerivAt
        (regularGeneralMetricC2MaxwellPairing
          period hPeriod metric first second)
        (regularGeneralMetricC2MaxwellPairingDerivativeAtZero
          period hPeriod metric first second) 0 ∧
      ∀ direction,
        regularGeneralMetricC2MaxwellPairingDerivativeAtZero
            period hPeriod metric first second direction =
          ∑ component : Fin 2,
            c2MaxwellMatrixContractionVelocity period hPeriod
              (regularFrameMetricInverseC2Matrix period hPeriod metric)
              (-c2FiniteMatrixProduct
                (period := period) (hPeriod := hPeriod) 4 direction.1
                  (regularFrameMetricInverseC2Matrix period hPeriod metric))
              (regularFrameGaugeCurvatureC2Matrix
                period hPeriod metric first component)
              (regularFrameGaugeCurvatureC2Matrix
                period hPeriod metric second component) :=
  ⟨regularGeneralMetricC2MaxwellPairing_hasFDerivAt_zero
      period hPeriod metric first second,
    regularGeneralMetricC2MaxwellPairingDerivativeAtZero_apply
      period hPeriod metric first second⟩

end
end P0EFTJanusProgramPRegularGeneralMetricC2MaxwellPairingDerivative4D
end JanusFormal
