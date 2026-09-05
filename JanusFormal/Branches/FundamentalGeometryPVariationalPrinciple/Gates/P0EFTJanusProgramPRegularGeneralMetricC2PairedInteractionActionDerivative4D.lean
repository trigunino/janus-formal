import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedRelativeRootSpectralDerivative4D

/-! # Exact derivative of the paired C² interaction density and action -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2PairedInteractionActionDerivative4D

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 600000

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalMetricCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalRelativeMetricCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomainOpen4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalInteractionC24D
open P0EFTJanusProgramPRegularGeneralMetricC2MatrixSpectralPotential4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedRelativeRootSpectralDerivative4D
open P0EFTJanusProgramPGeneralMetricC2IntegratedVolume4D
open P0EFTJanusMatrixInteractionFrechetNoether
open P0EFTJanusReciprocalBimetricPotential

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev C2Scalar :=
  CanonicalPhysicalScalarC2JetCore period hPeriod

private abbrev RelativeCore
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod) :=
  RegularGeneralMetricC2PairedRelativeCore
    period hPeriod plusBase minusBase

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

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

@[reducible] local instance c2ScalarNormedAddCommGroup :
    NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule
    period hPeriod).normedAddCommGroup

@[reducible] local instance c2ScalarNormedSpace :
    NormedSpace Real (C2Scalar period hPeriod) :=
  inferInstance

local instance c2ScalarCompleteSpace :
    CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod

@[reducible] local instance relativeCoreNormedAddCommGroup
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod) :
    NormedAddCommGroup
      (RelativeCore period hPeriod plusBase minusBase) :=
  inferInstance

@[reducible] local instance relativeCoreNormedSpace
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod) :
    NormedSpace Real (RelativeCore period hPeriod plusBase minusBase) :=
  inferInstance

/-- Exact derivative of the fixed-volume interaction density. -/
def regularGeneralMetricC2PairedInteractionC2DensityDerivative
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (core : RelativeCore period hPeriod plusBase minusBase)
    (hCore : core ∈ regularGeneralMetricC2PairedLorentzMatrixDomain
      period hPeriod plusBase minusBase) :
    RelativeCore period hPeriod plusBase minusBase →L[Real]
      C2Scalar period hPeriod :=
  (-interactionScale) •
    ((canonicalPhysicalScalarC2JetCoreProduct period hPeriod
      (smoothToCanonicalPhysicalScalarC2JetCore
        period hPeriod plusBase.volume)).comp
      (regularGeneralMetricC2PairedRelativeSpectralPotentialDerivative
        period hPeriod plusBase minusBase coefficients core hCore))

theorem regularGeneralMetricC2PairedInteractionC2Density_hasFDerivAt
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (core : RelativeCore period hPeriod plusBase minusBase)
    (hCore : core ∈ regularGeneralMetricC2PairedLorentzMatrixDomain
      period hPeriod plusBase minusBase) :
    HasFDerivAt
      (regularGeneralMetricC2PairedInteractionC2Density period hPeriod
        plusBase minusBase interactionScale coefficients)
      (regularGeneralMetricC2PairedInteractionC2DensityDerivative
        period hPeriod plusBase minusBase interactionScale coefficients
          core hCore) core := by
  let multiply := canonicalPhysicalScalarC2JetCoreProduct period hPeriod
    (smoothToCanonicalPhysicalScalarC2JetCore
      period hPeriod plusBase.volume)
  have hPotential :=
    regularGeneralMetricC2PairedRelativeSpectralPotential_hasFDerivAt
      period hPeriod plusBase minusBase coefficients core hCore
  have hMultiply := HasFDerivAt.comp
    (f := regularGeneralMetricC2PairedRelativeSpectralPotential
      period hPeriod plusBase minusBase coefficients)
    (g := fun field => multiply field) core
    multiply.hasFDerivAt hPotential
  have hScaled := hMultiply.const_smul (-interactionScale)
  apply hScaled.congr_of_eventuallyEq
  filter_upwards [] with current
  rfl

theorem regularGeneralMetricC2PairedInteractionC2DensityDerivative_valueAt
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (core : RelativeCore period hPeriod plusBase minusBase)
    (hCore : core ∈ regularGeneralMetricC2PairedLorentzMatrixDomain
      period hPeriod plusBase minusBase)
    (direction : RelativeCore period hPeriod plusBase minusBase)
    (point : EffectiveQuotient period hPeriod) :
    canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
        (regularGeneralMetricC2PairedInteractionC2DensityDerivative
          period hPeriod plusBase minusBase interactionScale coefficients
            core hCore direction) point =
      (-interactionScale) * plusBase.volume point *
        matrixSpectralPotentialDerivative coefficients
          (c2FiniteMatrixValueAt period hPeriod 4
            (regularGeneralMetricC2PairedRelativeRoot
              period hPeriod plusBase minusBase core) point)
          (c2FiniteMatrixValueAt period hPeriod 4
            (regularGeneralMetricC2PairedRelativeRootDerivative
              period hPeriod plusBase minusBase core hCore direction) point) := by
  unfold regularGeneralMetricC2PairedInteractionC2DensityDerivative
  change canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
      ((-interactionScale) •
        canonicalPhysicalScalarC2JetCoreProduct period hPeriod
          (smoothToCanonicalPhysicalScalarC2JetCore
            period hPeriod plusBase.volume)
          (regularGeneralMetricC2PairedRelativeSpectralPotentialDerivative
            period hPeriod plusBase minusBase coefficients core hCore
              direction)) point = _
  rw [c2ScalarSmul_valueAt, c2ScalarProduct_valueAt,
    canonicalPhysicalScalarC2JetCoreToContinuous_smooth,
    regularGeneralMetricC2PairedRelativeSpectralPotentialDerivative_valueAt]
  change -interactionScale * (plusBase.volume point * _) =
    -interactionScale * plusBase.volume point * _
  ring

/-- Exact derivative of the finite-measure interaction action. -/
def regularGeneralMetricC2PairedInteractionC2ActionDerivative
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (core : RelativeCore period hPeriod plusBase minusBase)
    (hCore : core ∈ regularGeneralMetricC2PairedLorentzMatrixDomain
      period hPeriod plusBase minusBase) :
    RelativeCore period hPeriod plusBase minusBase →L[Real] Real :=
  (canonicalPhysicalC2ScalarIntegralCLM period hPeriod measure).comp
    (regularGeneralMetricC2PairedInteractionC2DensityDerivative
      period hPeriod plusBase minusBase interactionScale coefficients
        core hCore)

theorem regularGeneralMetricC2PairedInteractionC2Action_hasFDerivAt
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (core : RelativeCore period hPeriod plusBase minusBase)
    (hCore : core ∈ regularGeneralMetricC2PairedLorentzMatrixDomain
      period hPeriod plusBase minusBase) :
    HasFDerivAt
      (regularGeneralMetricC2PairedInteractionC2Action period hPeriod
        plusBase minusBase measure interactionScale coefficients)
      (regularGeneralMetricC2PairedInteractionC2ActionDerivative
        period hPeriod plusBase minusBase measure interactionScale
          coefficients core hCore) core := by
  have hDensity :=
    regularGeneralMetricC2PairedInteractionC2Density_hasFDerivAt
      period hPeriod plusBase minusBase interactionScale coefficients
        core hCore
  have hIntegral := HasFDerivAt.comp
    (f := regularGeneralMetricC2PairedInteractionC2Density period hPeriod
      plusBase minusBase interactionScale coefficients)
    (g := fun field =>
      canonicalPhysicalC2ScalarIntegralCLM period hPeriod measure field)
    core
    (canonicalPhysicalC2ScalarIntegralCLM
      period hPeriod measure).hasFDerivAt hDensity
  apply hIntegral.congr_of_eventuallyEq
  filter_upwards [] with current
  rfl

/-- Explicit integrated first variation of the interaction block. -/
theorem regularGeneralMetricC2PairedInteractionC2ActionDerivative_apply
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (core : RelativeCore period hPeriod plusBase minusBase)
    (hCore : core ∈ regularGeneralMetricC2PairedLorentzMatrixDomain
      period hPeriod plusBase minusBase)
    (direction : RelativeCore period hPeriod plusBase minusBase) :
    regularGeneralMetricC2PairedInteractionC2ActionDerivative
        period hPeriod plusBase minusBase measure interactionScale
          coefficients core hCore direction =
      ∫ point,
        (-interactionScale) * plusBase.volume point *
          matrixSpectralPotentialDerivative coefficients
            (c2FiniteMatrixValueAt period hPeriod 4
              (regularGeneralMetricC2PairedRelativeRoot
                period hPeriod plusBase minusBase core) point)
            (c2FiniteMatrixValueAt period hPeriod 4
              (regularGeneralMetricC2PairedRelativeRootDerivative
                period hPeriod plusBase minusBase core hCore direction) point)
        ∂measure := by
  unfold regularGeneralMetricC2PairedInteractionC2ActionDerivative
  change canonicalPhysicalC2ScalarIntegralCLM period hPeriod measure
      (regularGeneralMetricC2PairedInteractionC2DensityDerivative
        period hPeriod plusBase minusBase interactionScale coefficients
          core hCore direction) = _
  rw [canonicalPhysicalC2ScalarIntegralCLM_apply]
  apply integral_congr_ae
  filter_upwards [] with point
  exact regularGeneralMetricC2PairedInteractionC2DensityDerivative_valueAt
    period hPeriod plusBase minusBase interactionScale coefficients core
      hCore direction point

/-- Gate marker: the full fixed-volume Candidate-A interaction action now has
an explicit integrated Fréchet derivative. -/
theorem regular_general_metric_c2_paired_interaction_action_derivative_gate
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (core : RelativeCore period hPeriod plusBase minusBase)
    (hCore : core ∈ regularGeneralMetricC2PairedLorentzMatrixDomain
      period hPeriod plusBase minusBase) :
    HasFDerivAt
        (regularGeneralMetricC2PairedInteractionC2Density period hPeriod
          plusBase minusBase interactionScale coefficients)
        (regularGeneralMetricC2PairedInteractionC2DensityDerivative
          period hPeriod plusBase minusBase interactionScale coefficients
            core hCore) core ∧
      HasFDerivAt
        (regularGeneralMetricC2PairedInteractionC2Action period hPeriod
          plusBase minusBase measure interactionScale coefficients)
        (regularGeneralMetricC2PairedInteractionC2ActionDerivative
          period hPeriod plusBase minusBase measure interactionScale
            coefficients core hCore) core :=
  ⟨regularGeneralMetricC2PairedInteractionC2Density_hasFDerivAt
      period hPeriod plusBase minusBase interactionScale coefficients
        core hCore,
    regularGeneralMetricC2PairedInteractionC2Action_hasFDerivAt
      period hPeriod plusBase minusBase measure interactionScale coefficients
        core hCore⟩

end
end P0EFTJanusProgramPRegularGeneralMetricC2PairedInteractionActionDerivative4D
end JanusFormal
