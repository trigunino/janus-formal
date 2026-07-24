import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyL2OperatorMinimalProgramPClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszL2OperatorGraphMinimalProgramPClosure4D

/-!
# Conditional elliptic/coercive Program P obligations

This module packages an auxiliary positive elliptic realization.  It is not the
safe endpoint for the physical Lorentzian wave operator.

Its graph estimate, six continuous boundary `L² → L²` residual operators,
shifted coercivity and Rellich approximation are independent assumptions.  No
theorem here derives them from the Lorentzian principal symbol.  Once a separate
elliptic realization supplies those assumptions, the downstream
self-adjointness, compact-resolvent, variational and Gaussian conclusions follow.

The non-elliptic physical route, conditional on the canonical
local-divergence/cut-bulk identity, stops at the intrinsic Lorentzian Green
identity and smooth Lagrangian boundary symmetry, in
`P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveWeightedTransportedLorentzianBoundaryClosure4D`.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarProgramPFinalObligations4D

set_option autoImplicit false
noncomputable section

open Set Topology MeasureTheory
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveCanonicalNormalGreen4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarScalarRemainderEnergyIdentity4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetGeometricGreenCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyL2OperatorPDEClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyL2OperatorMinimalAnalyticClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyL2OperatorMinimalProgramPClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszL2OperatorPDEClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszL2OperatorGraphMinimalProgramPClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFiniteCoordinateRellich4D
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleShiftedForm4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleExternalPositiveShiftedForm4D

universe e

variable (period : Real) (hPeriod : period ≠ 0)
variable {massSquared : Real}
variable {Energy : Type e}
  [NormedAddCommGroup Energy] [NormedSpace Real Energy]

private abbrev BoundaryL2 := CanonicalPhysicalScalarFirstSheetL2 period

private abbrev BulkL2 :=
  P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D.CanonicalPhysicalBulkL2
    period hPeriod

/-- Assemble the energy-free Riesz boundary package. -/
def assembleCanonicalPhysicalScalarGraphBoundaryData
    (geometric : CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalGreenData
      period hPeriod massSquared)
    (eulerCoefficientOperators :
      geometric.toNormalTangentialGreenData.toIntrinsicWaveLocalGreenData.toCanonicalLocalDivergenceData.toCanonicalWaveCauchyJetData.toCanonicalCauchyJetCompatibilityData.toCompatibilityData.toCauchyJetGeometricData.CauchyJetEulerSixCanonicalL2OperatorData
        period hPeriod) :
    CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszL2OperatorPDEData
      period hPeriod massSquared where
  geometric := geometric
  eulerCoefficientOperators := eulerCoefficientOperators

/-- Conditional auxiliary elliptic frontier.  The graph estimate, boundary
operators and shifted coercivity must be supplied by that elliptic
realization; they are not consequences of the Lorentzian wave data. -/
structure CanonicalPhysicalScalarProgramPGraphDirectCoerciveFinalObligationsData
    (massSquared : Real) where
  geometric : CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalGreenData
    period hPeriod massSquared
  eulerCoefficientOperators :
    geometric.toNormalTangentialGreenData.toIntrinsicWaveLocalGreenData.toCanonicalLocalDivergenceData.toCanonicalWaveCauchyJetData.toCanonicalCauchyJetCompatibilityData.toCompatibilityData.toCauchyJetGeometricData.CauchyJetEulerSixCanonicalL2OperatorData
      period hPeriod
  graphEllipticEstimate :
    (geometric.greenCore period hPeriod).GraphEllipticEstimate period hPeriod
  condition : CanonicalScalarHilbertLagrangianBoundaryCondition
    (BoundaryL2 period)
  referenceParameter : Real
  shiftedFormCoercive :
    (assembleCanonicalPhysicalScalarGraphBoundaryData period hPeriod
      geometric eulerCoefficientOperators).triple
      |>.LagrangianShiftedFormCoerciveData condition referenceParameter
  finiteCoordinateRellich : CanonicalPhysicalScalarFiniteCoordinateRellichData
    period hPeriod

/-- Explicit name for the auxiliary elliptic/coercive frontier.  The older
`GraphDirectCoercive` name is retained for source compatibility. -/
abbrev CanonicalPhysicalScalarProgramPEllipticCoerciveFinalObligationsData
    (massSquared : Real) :=
  CanonicalPhysicalScalarProgramPGraphDirectCoerciveFinalObligationsData
    period hPeriod massSquared

namespace CanonicalPhysicalScalarProgramPGraphDirectCoerciveFinalObligationsData

/-- Energy-free completed-boundary package. -/
def boundaryData
    (data : CanonicalPhysicalScalarProgramPGraphDirectCoerciveFinalObligationsData
      period hPeriod massSquared) :
    CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszL2OperatorPDEData
      period hPeriod massSquared :=
  assembleCanonicalPhysicalScalarGraphBoundaryData period hPeriod
    data.geometric data.eulerCoefficientOperators

/-- Conditional graph/direct-coercive analytic package. -/
def analyticData
    (data : CanonicalPhysicalScalarProgramPGraphDirectCoerciveFinalObligationsData
      period hPeriod massSquared) :
    CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszL2OperatorGraphDirectCoerciveMinimalAnalyticData
      period hPeriod massSquared where
  boundary := data.boundaryData
  graphEllipticEstimate := data.graphEllipticEstimate
  condition := data.condition
  referenceParameter := data.referenceParameter
  shiftedFormCoercive := data.shiftedFormCoercive
  finiteCoordinateRellich := data.finiteCoordinateRellich

/-- Riesz-generated completed trace. -/
def completedBoundaryTrace
    (data : CanonicalPhysicalScalarProgramPGraphDirectCoerciveFinalObligationsData
      period hPeriod massSquared) :=
  data.boundaryData.completedBoundaryTrace

/-- Completed physical boundary triple. -/
def triple
    (data : CanonicalPhysicalScalarProgramPGraphDirectCoerciveFinalObligationsData
      period hPeriod massSquared) :=
  data.boundaryData.triple

/-- Classical source solution. -/
noncomputable def sourceSolution
    (data : CanonicalPhysicalScalarProgramPGraphDirectCoerciveFinalObligationsData
      period hPeriod massSquared) :=
  data.analyticData.sourceSolution period hPeriod

/-- Actual Hilbert self-adjointness. -/
theorem actualAdjointDomain_eq
    (data : CanonicalPhysicalScalarProgramPGraphDirectCoerciveFinalObligationsData
      period hPeriod massSquared) :
    data.triple.actualAdjointDomain data.condition =
      data.triple.realizationDomain data.condition :=
  data.analyticData.actualAdjointDomain_eq period hPeriod

/-- Compact reference resolvent. -/
noncomputable def compactResolvent
    (data : CanonicalPhysicalScalarProgramPGraphDirectCoerciveFinalObligationsData
      period hPeriod massSquared) :=
  data.analyticData.compactResolvent period hPeriod

/-- Strong shifted source equation. -/
theorem sourceSolution_equation
    (data : CanonicalPhysicalScalarProgramPGraphDirectCoerciveFinalObligationsData
      period hPeriod massSquared)
    (source : BulkL2 period hPeriod) :
    data.triple.lagrangianShiftedOperator
        data.condition data.referenceParameter
        (data.sourceSolution period hPeriod source) = source :=
  data.analyticData.sourceSolution_equation period hPeriod source

/-- Unique global variational minimizer. -/
theorem sourceSolution_unique_minimizer
    (data : CanonicalPhysicalScalarProgramPGraphDirectCoerciveFinalObligationsData
      period hPeriod massSquared)
    (source : BulkL2 period hPeriod) :
    (∀ field : data.triple.lagrangianDomainSubmodule data.condition,
      data.triple.lagrangianSourceAction
          data.condition data.referenceParameter source
          (data.sourceSolution period hPeriod source) ≤
        data.triple.lagrangianSourceAction
          data.condition data.referenceParameter source field) ∧
      (∀ field : data.triple.lagrangianDomainSubmodule data.condition,
        data.triple.lagrangianSourceAction
            data.condition data.referenceParameter source field =
          data.triple.lagrangianSourceAction
            data.condition data.referenceParameter source
            (data.sourceSolution period hPeriod source) →
        field = data.sourceSolution period hPeriod source) :=
  data.analyticData.sourceSolution_unique_minimizer period hPeriod source

/-- Gaussian generating functional. -/
def gaussianGeneratingFunctional
    (data : CanonicalPhysicalScalarProgramPGraphDirectCoerciveFinalObligationsData
      period hPeriod massSquared)
    (source : BulkL2 period hPeriod) : Real :=
  data.analyticData.gaussianGeneratingFunctional period hPeriod source

/-- On-shell Gaussian identity and positivity. -/
theorem gaussian_certificate
    (data : CanonicalPhysicalScalarProgramPGraphDirectCoerciveFinalObligationsData
      period hPeriod massSquared)
    (source : BulkL2 period hPeriod) :
    data.gaussianGeneratingFunctional period hPeriod source =
        -data.triple.lagrangianSourceAction
          data.condition data.referenceParameter source
          (data.sourceSolution period hPeriod source) ∧
      0 ≤ data.gaussianGeneratingFunctional period hPeriod source :=
  ⟨data.analyticData.gaussianGeneratingFunctional_eq_neg_onShell
      period hPeriod source,
    data.analyticData.gaussianGeneratingFunctional_nonnegative
      period hPeriod source⟩

/-- Fredholm alternative. -/
theorem fredholmAlternative
    (data : CanonicalPhysicalScalarProgramPGraphDirectCoerciveFinalObligationsData
      period hPeriod massSquared)
    (spectralParameter : Real)
    (hParameter : spectralParameter ≠ data.referenceParameter) :
    data.triple.LagrangianHasEigenvalue data.condition spectralParameter ∨
      data.triple.LagrangianResolventPoint data.condition spectralParameter :=
  data.analyticData.fredholmAlternative
    period hPeriod spectralParameter hParameter

/-- Conditional elliptic/coercive Program P certificate. -/
theorem certificate
    (data : CanonicalPhysicalScalarProgramPGraphDirectCoerciveFinalObligationsData
      period hPeriod massSquared)
    (source : BulkL2 period hPeriod) :
    P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerAtlasNaturality4D.CanonicalPhysicalScalarWaveAtlasNaturality
        period hPeriod ∧
      (∀ index boundary,
        MemLp
          (data.eulerCoefficientOperators.coefficient
            period hPeriod index boundary)
          (2 : ENNReal)
          (P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D.canonicalLatitudeBaseMeasure
            period)) ∧
      Function.Surjective data.completedBoundaryTrace ∧
      data.triple.actualAdjointDomain data.condition =
        data.triple.realizationDomain data.condition ∧
      data.triple.lagrangianShiftedOperator
          data.condition data.referenceParameter
          (data.sourceSolution period hPeriod source) = source ∧
      (∀ field : data.triple.lagrangianDomainSubmodule data.condition,
        data.triple.lagrangianSourceAction
            data.condition data.referenceParameter source
            (data.sourceSolution period hPeriod source) ≤
          data.triple.lagrangianSourceAction
            data.condition data.referenceParameter source field) ∧
      0 ≤ data.gaussianGeneratingFunctional period hPeriod source ∧
      (∀ spectralParameter : Real,
        spectralParameter ≠ data.referenceParameter →
          data.triple.LagrangianHasEigenvalue
              data.condition spectralParameter ∨
            data.triple.LagrangianResolventPoint
              data.condition spectralParameter) :=
  data.analyticData.finalProgramP_certificate period hPeriod source

end CanonicalPhysicalScalarProgramPGraphDirectCoerciveFinalObligationsData

/-- Assemble the final completed-boundary package from the three PDE inputs. -/
def assembleCanonicalPhysicalScalarBoundaryData
    (geometric : CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalGreenData
      period hPeriod massSquared)
    (energyIdentity : (geometric.greenCore period hPeriod).ScalarRemainderEnergyIdentityData
      period hPeriod)
    (eulerCoefficientOperators :
      geometric.toNormalTangentialGreenData.toIntrinsicWaveLocalGreenData.toCanonicalLocalDivergenceData.toCanonicalWaveCauchyJetData.toCanonicalCauchyJetCompatibilityData.toCompatibilityData.toCauchyJetGeometricData.CauchyJetEulerSixCanonicalL2OperatorData
        period hPeriod) :
    CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyL2OperatorPDEData
      period hPeriod massSquared where
  geometric := geometric
  energyIdentity := energyIdentity
  eulerCoefficientOperators := eulerCoefficientOperators

/-- Legacy conditional elliptic frontier with an exact energy identity. -/
structure CanonicalPhysicalScalarProgramPDirectCoerciveFinalObligationsData
    (massSquared : Real) where
  geometric : CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalGreenData
    period hPeriod massSquared
  energyIdentity : (geometric.greenCore period hPeriod).ScalarRemainderEnergyIdentityData
    period hPeriod
  eulerCoefficientOperators :
    geometric.toNormalTangentialGreenData.toIntrinsicWaveLocalGreenData.toCanonicalLocalDivergenceData.toCanonicalWaveCauchyJetData.toCanonicalCauchyJetCompatibilityData.toCompatibilityData.toCauchyJetGeometricData.CauchyJetEulerSixCanonicalL2OperatorData
      period hPeriod
  condition : CanonicalScalarHilbertLagrangianBoundaryCondition
    (BoundaryL2 period)
  referenceParameter : Real
  shiftedFormCoercive :
    (assembleCanonicalPhysicalScalarBoundaryData period hPeriod
      geometric energyIdentity eulerCoefficientOperators).triple
      |>.LagrangianShiftedFormCoerciveData condition referenceParameter
  finiteCoordinateRellich : CanonicalPhysicalScalarFiniteCoordinateRellichData
    period hPeriod

namespace CanonicalPhysicalScalarProgramPDirectCoerciveFinalObligationsData

/-- Completed-boundary package assembled from the direct frontier. -/
def boundaryData
    (data : CanonicalPhysicalScalarProgramPDirectCoerciveFinalObligationsData
      period hPeriod massSquared) :
    CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyL2OperatorPDEData
      period hPeriod massSquared :=
  assembleCanonicalPhysicalScalarBoundaryData period hPeriod
    data.geometric data.energyIdentity data.eulerCoefficientOperators

/-- The exact-energy compatibility package factors through the auxiliary
direct graph-estimate frontier. -/
def toGraphDirectCoerciveFinalObligationsData
    (data : CanonicalPhysicalScalarProgramPDirectCoerciveFinalObligationsData
      period hPeriod massSquared) :
    CanonicalPhysicalScalarProgramPGraphDirectCoerciveFinalObligationsData
      period hPeriod massSquared where
  geometric := data.geometric
  eulerCoefficientOperators := data.eulerCoefficientOperators
  graphEllipticEstimate :=
    data.energyIdentity.toGraphEllipticEstimate period hPeriod
      (data.geometric.greenCore period hPeriod)
  condition := data.condition
  referenceParameter := data.referenceParameter
  shiftedFormCoercive := data.shiftedFormCoercive
  finiteCoordinateRellich := data.finiteCoordinateRellich

/-- Direct-coercive minimal analytic package. -/
def analyticData
    (data : CanonicalPhysicalScalarProgramPDirectCoerciveFinalObligationsData
      period hPeriod massSquared) :
    CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyL2OperatorDirectCoerciveMinimalAnalyticData
      period hPeriod massSquared where
  boundary := data.boundaryData
  condition := data.condition
  referenceParameter := data.referenceParameter
  shiftedFormCoercive := data.shiftedFormCoercive
  finiteCoordinateRellich := data.finiteCoordinateRellich

/-- Riesz-generated completed trace. -/
def completedBoundaryTrace
    (data : CanonicalPhysicalScalarProgramPDirectCoerciveFinalObligationsData
      period hPeriod massSquared) :=
  data.boundaryData.completedBoundaryTrace

/-- Completed physical boundary triple. -/
def triple
    (data : CanonicalPhysicalScalarProgramPDirectCoerciveFinalObligationsData
      period hPeriod massSquared) :=
  data.boundaryData.triple

/-- Classical source solution. -/
noncomputable def sourceSolution
    (data : CanonicalPhysicalScalarProgramPDirectCoerciveFinalObligationsData
      period hPeriod massSquared) :=
  data.analyticData.sourceSolution period hPeriod

/-- Actual Hilbert self-adjointness. -/
theorem actualAdjointDomain_eq
    (data : CanonicalPhysicalScalarProgramPDirectCoerciveFinalObligationsData
      period hPeriod massSquared) :
    data.triple.actualAdjointDomain data.condition =
      data.triple.realizationDomain data.condition :=
  data.analyticData.actualAdjointDomain_eq period hPeriod

/-- Compact reference resolvent. -/
noncomputable def compactResolvent
    (data : CanonicalPhysicalScalarProgramPDirectCoerciveFinalObligationsData
      period hPeriod massSquared) :=
  data.analyticData.compactResolvent period hPeriod

/-- Strong shifted source equation. -/
theorem sourceSolution_equation
    (data : CanonicalPhysicalScalarProgramPDirectCoerciveFinalObligationsData
      period hPeriod massSquared)
    (source : BulkL2 period hPeriod) :
    data.triple.lagrangianShiftedOperator
        data.condition data.referenceParameter
        (data.sourceSolution period hPeriod source) = source :=
  data.analyticData.sourceSolution_equation period hPeriod source

/-- Unique global variational minimizer. -/
theorem sourceSolution_unique_minimizer
    (data : CanonicalPhysicalScalarProgramPDirectCoerciveFinalObligationsData
      period hPeriod massSquared)
    (source : BulkL2 period hPeriod) :
    (∀ field : data.triple.lagrangianDomainSubmodule data.condition,
      data.triple.lagrangianSourceAction
          data.condition data.referenceParameter source
          (data.sourceSolution period hPeriod source) ≤
        data.triple.lagrangianSourceAction
          data.condition data.referenceParameter source field) ∧
      (∀ field : data.triple.lagrangianDomainSubmodule data.condition,
        data.triple.lagrangianSourceAction
            data.condition data.referenceParameter source field =
          data.triple.lagrangianSourceAction
            data.condition data.referenceParameter source
            (data.sourceSolution period hPeriod source) →
        field = data.sourceSolution period hPeriod source) :=
  data.analyticData.sourceSolution_unique_minimizer period hPeriod source

/-- Gaussian generating functional. -/
def gaussianGeneratingFunctional
    (data : CanonicalPhysicalScalarProgramPDirectCoerciveFinalObligationsData
      period hPeriod massSquared)
    (source : BulkL2 period hPeriod) : Real :=
  data.analyticData.gaussianGeneratingFunctional period hPeriod source

/-- On-shell Gaussian identity and positivity. -/
theorem gaussian_certificate
    (data : CanonicalPhysicalScalarProgramPDirectCoerciveFinalObligationsData
      period hPeriod massSquared)
    (source : BulkL2 period hPeriod) :
    data.gaussianGeneratingFunctional period hPeriod source =
        -data.triple.lagrangianSourceAction
          data.condition data.referenceParameter source
          (data.sourceSolution period hPeriod source) ∧
      0 ≤ data.gaussianGeneratingFunctional period hPeriod source :=
  data.analyticData.gaussian_certificate period hPeriod source

/-- Fredholm alternative. -/
theorem fredholmAlternative
    (data : CanonicalPhysicalScalarProgramPDirectCoerciveFinalObligationsData
      period hPeriod massSquared)
    (spectralParameter : Real)
    (hParameter : spectralParameter ≠ data.referenceParameter) :
    data.triple.LagrangianHasEigenvalue
        data.condition spectralParameter ∨
      data.triple.LagrangianResolventPoint
        data.condition spectralParameter :=
  data.analyticData.fredholmAlternative
    period hPeriod spectralParameter hParameter

/-- Conditional direct-coercive Program P certificate. -/
theorem certificate
    (data : CanonicalPhysicalScalarProgramPDirectCoerciveFinalObligationsData
      period hPeriod massSquared)
    (source : BulkL2 period hPeriod) :
    P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerAtlasNaturality4D.CanonicalPhysicalScalarWaveAtlasNaturality
        period hPeriod ∧
      (∀ index boundary,
        MemLp
          (data.eulerCoefficientOperators.coefficient
            period hPeriod index boundary)
          (2 : ENNReal)
          (P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D.canonicalLatitudeBaseMeasure
            period)) ∧
      Function.Surjective data.completedBoundaryTrace ∧
      data.triple.actualAdjointDomain data.condition =
        data.triple.realizationDomain data.condition ∧
      data.triple.lagrangianShiftedOperator
          data.condition data.referenceParameter
          (data.sourceSolution period hPeriod source) = source ∧
      (∀ field : data.triple.lagrangianDomainSubmodule data.condition,
        data.triple.lagrangianSourceAction
            data.condition data.referenceParameter source
            (data.sourceSolution period hPeriod source) ≤
          data.triple.lagrangianSourceAction
            data.condition data.referenceParameter source field) ∧
      0 ≤ data.gaussianGeneratingFunctional period hPeriod source ∧
      (∀ spectralParameter : Real,
        spectralParameter ≠ data.referenceParameter →
          data.triple.LagrangianHasEigenvalue
              data.condition spectralParameter ∨
            data.triple.LagrangianResolventPoint
              data.condition spectralParameter) := by
  refine ⟨data.geometric.intrinsicWave.toWaveAtlasNaturality period hPeriod, ?_⟩
  exact data.analyticData.finalProgramP_certificate period hPeriod source

end CanonicalPhysicalScalarProgramPDirectCoerciveFinalObligationsData

/-- Legacy conditional positive-square compatibility frontier. -/
structure CanonicalPhysicalScalarProgramPFinalObligationsData
    (massSquared : Real) (Energy : Type e)
    [NormedAddCommGroup Energy] [NormedSpace Real Energy] where
  geometric : CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalGreenData
    period hPeriod massSquared
  energyIdentity : (geometric.greenCore period hPeriod).ScalarRemainderEnergyIdentityData
    period hPeriod
  eulerCoefficientOperators :
    geometric.toNormalTangentialGreenData.toIntrinsicWaveLocalGreenData.toCanonicalLocalDivergenceData.toCanonicalWaveCauchyJetData.toCanonicalCauchyJetCompatibilityData.toCompatibilityData.toCauchyJetGeometricData.CauchyJetEulerSixCanonicalL2OperatorData
      period hPeriod
  condition : CanonicalScalarHilbertLagrangianBoundaryCondition
    (BoundaryL2 period)
  referenceParameter : Real
  shiftedPositiveDecomposition :
    (assembleCanonicalPhysicalScalarBoundaryData period hPeriod
      geometric energyIdentity eulerCoefficientOperators).triple
      |>.LagrangianShiftedExternalPositiveDecompositionData
        condition referenceParameter Energy
  finiteCoordinateRellich : CanonicalPhysicalScalarFiniteCoordinateRellichData
    period hPeriod

namespace CanonicalPhysicalScalarProgramPFinalObligationsData

/-- The external positive-square frontier factors through direct coercivity. -/
def toDirectCoerciveFinalObligationsData
    (data : CanonicalPhysicalScalarProgramPFinalObligationsData
      period hPeriod massSquared Energy) :
    CanonicalPhysicalScalarProgramPDirectCoerciveFinalObligationsData
      period hPeriod massSquared where
  geometric := data.geometric
  energyIdentity := data.energyIdentity
  eulerCoefficientOperators := data.eulerCoefficientOperators
  condition := data.condition
  referenceParameter := data.referenceParameter
  shiftedFormCoercive :=
    data.shiftedPositiveDecomposition.toShiftedFormCoerciveData
      (assembleCanonicalPhysicalScalarBoundaryData period hPeriod
        data.geometric data.energyIdentity data.eulerCoefficientOperators).triple
      data.condition data.referenceParameter
  finiteCoordinateRellich := data.finiteCoordinateRellich

/-- Completed-boundary package assembled from the flat obligations. -/
def boundaryData
    (data : CanonicalPhysicalScalarProgramPFinalObligationsData
      period hPeriod massSquared Energy) :
    CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyL2OperatorPDEData
      period hPeriod massSquared :=
  assembleCanonicalPhysicalScalarBoundaryData period hPeriod
    data.geometric data.energyIdentity data.eulerCoefficientOperators

/-- Complete minimal analytic package assembled from the flat obligations. -/
def analyticData
    (data : CanonicalPhysicalScalarProgramPFinalObligationsData
      period hPeriod massSquared Energy) :
    CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyL2OperatorMinimalAnalyticData
      period hPeriod massSquared Energy where
  boundary := data.boundaryData
  condition := data.condition
  referenceParameter := data.referenceParameter
  shiftedPositiveDecomposition := data.shiftedPositiveDecomposition
  finiteCoordinateRellich := data.finiteCoordinateRellich

/-- Riesz-generated completed trace. -/
def completedBoundaryTrace
    (data : CanonicalPhysicalScalarProgramPFinalObligationsData
      period hPeriod massSquared Energy) :=
  data.boundaryData.completedBoundaryTrace

/-- Bounded right inverse of the completed trace. -/
def completedExtension
    (data : CanonicalPhysicalScalarProgramPFinalObligationsData
      period hPeriod massSquared Energy) :=
  data.boundaryData.completedExtension

/-- Completed physical boundary triple. -/
def triple
    (data : CanonicalPhysicalScalarProgramPFinalObligationsData
      period hPeriod massSquared Energy) :=
  data.boundaryData.triple

/-- Classical source solution. -/
noncomputable def sourceSolution
    (data : CanonicalPhysicalScalarProgramPFinalObligationsData
      period hPeriod massSquared Energy) :=
  data.analyticData.sourceSolution period hPeriod

/-- Actual Hilbert self-adjointness. -/
theorem actualAdjointDomain_eq
    (data : CanonicalPhysicalScalarProgramPFinalObligationsData
      period hPeriod massSquared Energy) :
    data.triple.actualAdjointDomain data.condition =
      data.triple.realizationDomain data.condition :=
  data.analyticData.actualAdjointDomain_eq period hPeriod

/-- Compact reference resolvent. -/
noncomputable def compactResolvent
    (data : CanonicalPhysicalScalarProgramPFinalObligationsData
      period hPeriod massSquared Energy) :=
  data.analyticData.compactResolvent period hPeriod

/-- Strong shifted source equation. -/
theorem sourceSolution_equation
    (data : CanonicalPhysicalScalarProgramPFinalObligationsData
      period hPeriod massSquared Energy)
    (source : BulkL2 period hPeriod) :
    data.triple.lagrangianShiftedOperator
        data.condition data.referenceParameter
        (data.sourceSolution period hPeriod source) = source :=
  data.analyticData.sourceSolution_equation period hPeriod source

/-- Unique global variational minimizer. -/
theorem sourceSolution_unique_minimizer
    (data : CanonicalPhysicalScalarProgramPFinalObligationsData
      period hPeriod massSquared Energy)
    (source : BulkL2 period hPeriod) :
    (∀ field : data.triple.lagrangianDomainSubmodule data.condition,
      data.triple.lagrangianSourceAction
          data.condition data.referenceParameter source
          (data.sourceSolution period hPeriod source) ≤
        data.triple.lagrangianSourceAction
          data.condition data.referenceParameter source field) ∧
      (∀ field : data.triple.lagrangianDomainSubmodule data.condition,
        data.triple.lagrangianSourceAction
            data.condition data.referenceParameter source field =
          data.triple.lagrangianSourceAction
            data.condition data.referenceParameter source
            (data.sourceSolution period hPeriod source) →
        field = data.sourceSolution period hPeriod source) :=
  data.analyticData.sourceSolution_unique_minimizer period hPeriod source

/-- Gaussian generating functional. -/
def gaussianGeneratingFunctional
    (data : CanonicalPhysicalScalarProgramPFinalObligationsData
      period hPeriod massSquared Energy)
    (source : BulkL2 period hPeriod) : Real :=
  data.analyticData.gaussianGeneratingFunctional period hPeriod source

/-- On-shell Gaussian identity and positivity. -/
theorem gaussian_certificate
    (data : CanonicalPhysicalScalarProgramPFinalObligationsData
      period hPeriod massSquared Energy)
    (source : BulkL2 period hPeriod) :
    data.gaussianGeneratingFunctional period hPeriod source =
        -data.triple.lagrangianSourceAction
          data.condition data.referenceParameter source
          (data.sourceSolution period hPeriod source) ∧
      0 ≤ data.gaussianGeneratingFunctional period hPeriod source :=
  data.analyticData.gaussian_certificate period hPeriod source

/-- Fredholm alternative. -/
theorem fredholmAlternative
    (data : CanonicalPhysicalScalarProgramPFinalObligationsData
      period hPeriod massSquared Energy)
    (spectralParameter : Real)
    (hParameter : spectralParameter ≠ data.referenceParameter) :
    data.triple.LagrangianHasEigenvalue
        data.condition spectralParameter ∨
      data.triple.LagrangianResolventPoint
        data.condition spectralParameter :=
  data.analyticData.fredholmAlternative
    period hPeriod spectralParameter hParameter

/-- Conditional positive-square Program P certificate. -/
theorem certificate
    (data : CanonicalPhysicalScalarProgramPFinalObligationsData
      period hPeriod massSquared Energy)
    (source : BulkL2 period hPeriod) :
    P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerAtlasNaturality4D.CanonicalPhysicalScalarWaveAtlasNaturality
        period hPeriod ∧
      (∀ index boundary,
        MemLp
          (data.eulerCoefficientOperators.coefficient
            period hPeriod index boundary)
          (2 : ENNReal)
          (P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D.canonicalLatitudeBaseMeasure
            period)) ∧
      Function.Surjective data.completedBoundaryTrace ∧
      data.triple.actualAdjointDomain data.condition =
        data.triple.realizationDomain data.condition ∧
      data.triple.lagrangianShiftedOperator
          data.condition data.referenceParameter
          (data.sourceSolution period hPeriod source) = source ∧
      (∀ field : data.triple.lagrangianDomainSubmodule data.condition,
        data.triple.lagrangianSourceAction
            data.condition data.referenceParameter source
            (data.sourceSolution period hPeriod source) ≤
          data.triple.lagrangianSourceAction
            data.condition data.referenceParameter source field) ∧
      0 ≤ data.gaussianGeneratingFunctional period hPeriod source ∧
      (∀ spectralParameter : Real,
        spectralParameter ≠ data.referenceParameter →
          data.triple.LagrangianHasEigenvalue
              data.condition spectralParameter ∨
            data.triple.LagrangianResolventPoint
              data.condition spectralParameter) := by
  refine ⟨data.geometric.intrinsicWave.toWaveAtlasNaturality period hPeriod, ?_⟩
  exact data.analyticData.finalProgramP_certificate period hPeriod source

end CanonicalPhysicalScalarProgramPFinalObligationsData

/-- Compatibility marker for the conditional elliptic obligations package. -/
theorem canonicalPhysicalScalarProgramPFinalObligations_available : True :=
  trivial

/-- Marker for the explicitly named auxiliary elliptic/coercive frontier. -/
theorem canonicalPhysicalScalarProgramPEllipticCoerciveFinalObligations_available :
    True :=
  trivial

/-- Compatibility marker for the older graph/direct-coercive name. -/
theorem canonicalPhysicalScalarProgramPGraphDirectCoerciveFinalObligations_available :
    True :=
  canonicalPhysicalScalarProgramPEllipticCoerciveFinalObligations_available

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarProgramPFinalObligations4D
end JanusFormal
