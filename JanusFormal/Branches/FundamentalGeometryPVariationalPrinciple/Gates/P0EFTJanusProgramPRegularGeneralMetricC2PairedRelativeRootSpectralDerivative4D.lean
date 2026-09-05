import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2MatrixSpectralPotentialDerivative4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalInteractionC24D

/-! # Exact derivative of the paired relative root and spectral potential -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2PairedRelativeRootSpectralDerivative4D

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 600000

noncomputable section

open Set Filter
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
open P0EFTJanusMappingTorusCanonicalPhysicalC2IdentityRootBranch4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2IdentityRootDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalMetricCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalRelativeMetricCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedRelativeMatrixCore4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedRelativeMatrixDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomainOpen4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalInteractionC24D
open P0EFTJanusProgramPRegularGeneralMetricC2MatrixSpectralPotential4D
open P0EFTJanusProgramPRegularGeneralMetricC2MatrixSpectralPotentialDerivative4D
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

private abbrev C2Matrix :=
  C2FiniteMatrix period hPeriod 4

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

@[reducible] local instance c2MatrixNormedAddCommGroup :
    NormedAddCommGroup (C2Matrix period hPeriod) :=
  inferInstance

@[reducible] local instance c2MatrixNormedSpace :
    NormedSpace Real (C2Matrix period hPeriod) :=
  inferInstance

@[reducible] local instance relativeCoreNormedAddCommGroup
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod) :
    NormedAddCommGroup
      (RelativeCore period hPeriod plusBase minusBase) :=
  inferInstance

@[reducible] local instance relativeCoreNormedSpace
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod) :
    NormedSpace Real (RelativeCore period hPeriod plusBase minusBase) :=
  inferInstance

/-- Chain-rule derivative of the selected root of the transported relative
matrix. -/
def regularGeneralMetricC2PairedRelativeRootDerivative
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (core : RelativeCore period hPeriod plusBase minusBase)
    (hCore : core ∈ regularGeneralMetricC2PairedLorentzMatrixDomain
      period hPeriod plusBase minusBase) :
    RelativeCore period hPeriod plusBase minusBase →L[Real]
      C2Matrix period hPeriod :=
  (c2IdentityRootDerivative period hPeriod
      (regularGeneralMetricC2PairedRelativeMatrix
        period hPeriod plusBase minusBase core)
      hCore.2.2.2.1).comp
    (regularGeneralMetricC2PairedRelativeMatrixDerivative
      period hPeriod plusBase minusBase core hCore.2.1)

theorem regularGeneralMetricC2PairedRelativeRoot_hasFDerivAt
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (core : RelativeCore period hPeriod plusBase minusBase)
    (hCore : core ∈ regularGeneralMetricC2PairedLorentzMatrixDomain
      period hPeriod plusBase minusBase) :
    HasFDerivAt
      (regularGeneralMetricC2PairedRelativeRoot
        period hPeriod plusBase minusBase)
      (regularGeneralMetricC2PairedRelativeRootDerivative
        period hPeriod plusBase minusBase core hCore) core := by
  have hOuter := c2IdentityRootBranch_hasFDerivAt period hPeriod
    (regularGeneralMetricC2PairedRelativeMatrix
      period hPeriod plusBase minusBase core) hCore.2.2.2.1
  have hInner :=
    regularGeneralMetricC2PairedRelativeMatrix_hasFDerivAt
      period hPeriod plusBase minusBase core hCore.2.1
  have hComposite := HasFDerivAt.comp
    (f := regularGeneralMetricC2PairedRelativeMatrix
      period hPeriod plusBase minusBase)
    (g := c2IdentityRootBranch period hPeriod)
    core hOuter hInner
  apply hComposite.congr_of_eventuallyEq
  filter_upwards [] with current
  rfl

/-- Spectral potential of the selected paired relative root. -/
def regularGeneralMetricC2PairedRelativeSpectralPotential
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (coefficients : PotentialCoefficients)
    (core : RelativeCore period hPeriod plusBase minusBase) :
    C2Scalar period hPeriod :=
  c2MatrixSpectralPotential period hPeriod coefficients
    (regularGeneralMetricC2PairedRelativeRoot
      period hPeriod plusBase minusBase core)

/-- Exact derivative of the paired relative spectral potential. -/
def regularGeneralMetricC2PairedRelativeSpectralPotentialDerivative
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (coefficients : PotentialCoefficients)
    (core : RelativeCore period hPeriod plusBase minusBase)
    (hCore : core ∈ regularGeneralMetricC2PairedLorentzMatrixDomain
      period hPeriod plusBase minusBase) :
    RelativeCore period hPeriod plusBase minusBase →L[Real]
      C2Scalar period hPeriod :=
  (c2MatrixSpectralPotentialDerivative period hPeriod coefficients
      (regularGeneralMetricC2PairedRelativeRoot
        period hPeriod plusBase minusBase core)).comp
    (regularGeneralMetricC2PairedRelativeRootDerivative
      period hPeriod plusBase minusBase core hCore)

theorem regularGeneralMetricC2PairedRelativeSpectralPotential_hasFDerivAt
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (coefficients : PotentialCoefficients)
    (core : RelativeCore period hPeriod plusBase minusBase)
    (hCore : core ∈ regularGeneralMetricC2PairedLorentzMatrixDomain
      period hPeriod plusBase minusBase) :
    HasFDerivAt
      (regularGeneralMetricC2PairedRelativeSpectralPotential
        period hPeriod plusBase minusBase coefficients)
      (regularGeneralMetricC2PairedRelativeSpectralPotentialDerivative
        period hPeriod plusBase minusBase coefficients core hCore) core := by
  have hOuter := c2MatrixSpectralPotential_hasFDerivAt
    period hPeriod coefficients
      (regularGeneralMetricC2PairedRelativeRoot
        period hPeriod plusBase minusBase core)
  have hInner := regularGeneralMetricC2PairedRelativeRoot_hasFDerivAt
    period hPeriod plusBase minusBase core hCore
  have hComposite := HasFDerivAt.comp
    (f := regularGeneralMetricC2PairedRelativeRoot
      period hPeriod plusBase minusBase)
    (g := c2MatrixSpectralPotential period hPeriod coefficients)
    core hOuter hInner
  apply hComposite.congr_of_eventuallyEq
  filter_upwards [] with current
  rfl

theorem regularGeneralMetricC2PairedRelativeSpectralPotentialDerivative_valueAt
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (coefficients : PotentialCoefficients)
    (core : RelativeCore period hPeriod plusBase minusBase)
    (hCore : core ∈ regularGeneralMetricC2PairedLorentzMatrixDomain
      period hPeriod plusBase minusBase)
    (direction : RelativeCore period hPeriod plusBase minusBase)
    (point : EffectiveQuotient period hPeriod) :
    canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
        (regularGeneralMetricC2PairedRelativeSpectralPotentialDerivative
          period hPeriod plusBase minusBase coefficients core hCore
            direction) point =
      matrixSpectralPotentialDerivative coefficients
        (c2FiniteMatrixValueAt period hPeriod 4
          (regularGeneralMetricC2PairedRelativeRoot
            period hPeriod plusBase minusBase core) point)
        (c2FiniteMatrixValueAt period hPeriod 4
          (regularGeneralMetricC2PairedRelativeRootDerivative
            period hPeriod plusBase minusBase core hCore direction) point) := by
  exact c2MatrixSpectralPotentialDerivative_valueAt period hPeriod
    coefficients
    (regularGeneralMetricC2PairedRelativeRoot
      period hPeriod plusBase minusBase core)
    (regularGeneralMetricC2PairedRelativeRootDerivative
      period hPeriod plusBase minusBase core hCore direction) point

/-- Gate marker: both nonlinear chain-rule stages of the relative spectral
block now have exact derivatives on the genuine paired Lorentz domain. -/
theorem regular_general_metric_c2_paired_relative_root_spectral_derivative_gate
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (coefficients : PotentialCoefficients)
    (core : RelativeCore period hPeriod plusBase minusBase)
    (hCore : core ∈ regularGeneralMetricC2PairedLorentzMatrixDomain
      period hPeriod plusBase minusBase) :
    HasFDerivAt
        (regularGeneralMetricC2PairedRelativeRoot
          period hPeriod plusBase minusBase)
        (regularGeneralMetricC2PairedRelativeRootDerivative
          period hPeriod plusBase minusBase core hCore) core ∧
      HasFDerivAt
        (regularGeneralMetricC2PairedRelativeSpectralPotential
          period hPeriod plusBase minusBase coefficients)
        (regularGeneralMetricC2PairedRelativeSpectralPotentialDerivative
          period hPeriod plusBase minusBase coefficients core hCore) core :=
  ⟨regularGeneralMetricC2PairedRelativeRoot_hasFDerivAt
      period hPeriod plusBase minusBase core hCore,
    regularGeneralMetricC2PairedRelativeSpectralPotential_hasFDerivAt
      period hPeriod plusBase minusBase coefficients core hCore⟩

end
end P0EFTJanusProgramPRegularGeneralMetricC2PairedRelativeRootSpectralDerivative4D
end JanusFormal
