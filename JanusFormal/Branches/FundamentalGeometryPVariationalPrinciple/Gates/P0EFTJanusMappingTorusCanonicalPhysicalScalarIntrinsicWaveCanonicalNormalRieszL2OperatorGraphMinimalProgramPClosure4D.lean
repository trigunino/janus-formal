import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszL2OperatorPDEClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszMinimalProgramPClosure4D

/-!
# Program P closure from a direct graph estimate

This endpoint separates the two independent analytic inputs that were formerly
bundled into an exact positive first-jet identity:

* a graph estimate for the maximal physical operator;
* coercivity of the selected shifted Lagrangian form.

The Riesz boundary triple itself uses neither input.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszL2OperatorGraphMinimalProgramPClosure4D

set_option autoImplicit false
noncomputable section

open Set Topology MeasureTheory Module End
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetRellichCompactness4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetGreenCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetGreenCore4D.CanonicalPhysicalScalarFirstSheetGreenCoreData
open P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszL2OperatorPDEClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFiniteCoordinateRellich4D
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreLagrangianDensity4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleResolvent4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleShiftedForm4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleSelfAdjointResolvent4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleCompactSpectrum4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleEigenspace4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleFredholmAlternative4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleSemiboundedSpectrum4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleVariational4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleGaussian4D

variable (period : Real) (hPeriod : period ≠ 0)
variable {massSquared : Real}

local instance graphMinimalPhysicalH1CompleteSpace :
    CompleteSpace (CanonicalPhysicalScalarH1 period hPeriod) :=
  canonicalPhysicalScalarH1CompleteSpace period hPeriod

private abbrev BoundaryL2 := CanonicalPhysicalScalarFirstSheetL2 period

private abbrev BulkL2 :=
  P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D.CanonicalPhysicalBulkL2
    period hPeriod

/-- Minimal Program P data with the graph estimate supplied directly. -/
structure CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszL2OperatorGraphDirectCoerciveMinimalAnalyticData
    (massSquared : Real) where
  boundary : CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszL2OperatorPDEData
    period hPeriod massSquared
  graphEllipticEstimate :
    (boundary.geometric.greenCore period hPeriod).GraphEllipticEstimate
      period hPeriod
  condition : CanonicalScalarHilbertLagrangianBoundaryCondition
    (BoundaryL2 period)
  referenceParameter : Real
  shiftedFormCoercive : boundary.triple.LagrangianShiftedFormCoerciveData
    condition referenceParameter
  finiteCoordinateRellich : CanonicalPhysicalScalarFiniteCoordinateRellichData
    period hPeriod

namespace CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszL2OperatorGraphDirectCoerciveMinimalAnalyticData

/-- Density of the selected Lagrangian realization. -/
theorem denseDomain
    (analytic :
      CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszL2OperatorGraphDirectCoerciveMinimalAnalyticData
        period hPeriod massSquared) :
    DenseRange
      (analytic.boundary.triple.lagrangianInclusion analytic.condition) :=
  P0EFTJanusMappingTorusScalarHilbertGreenCoreLagrangianDensity4D.CanonicalScalarCompletedBoundaryTripleData.lagrangianInclusion_denseRange_of_minimalCore
    (analytic.boundary.triple period hPeriod) analytic.condition
    ((analytic.boundary.rieszBoundaryData period hPeriod).minimalCoreDense
      period hPeriod)

/-- Coercive-surjective shifted realization. -/
def coerciveSurjectiveAt
    (analytic :
      CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszL2OperatorGraphDirectCoerciveMinimalAnalyticData
        period hPeriod massSquared) :
    analytic.boundary.triple.LagrangianCoerciveSurjectiveAt
      analytic.condition analytic.referenceParameter :=
  analytic.shiftedFormCoercive.toCoerciveSurjectiveAt
    analytic.boundary.triple analytic.condition analytic.referenceParameter
    (analytic.denseDomain period hPeriod)

/-- Bounded real reference resolvent. -/
noncomputable def boundedResolvent
    (analytic :
      CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszL2OperatorGraphDirectCoerciveMinimalAnalyticData
        period hPeriod massSquared) :
    analytic.boundary.triple.LagrangianBoundedResolventAt
      analytic.condition analytic.referenceParameter :=
  analytic.shiftedFormCoercive.boundedResolvent
    analytic.boundary.triple analytic.condition analytic.referenceParameter
    (analytic.denseDomain period hPeriod)

/-- Actual Hilbert self-adjointness. -/
theorem actualAdjointDomain_eq
    (analytic :
      CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszL2OperatorGraphDirectCoerciveMinimalAnalyticData
        period hPeriod massSquared) :
    analytic.boundary.triple.actualAdjointDomain analytic.condition =
      analytic.boundary.triple.realizationDomain analytic.condition :=
  analytic.boundary.triple
    |>.actualAdjointDomain_eq_realizationDomain_of_boundedResolvent
      analytic.condition analytic.referenceParameter
      (analytic.boundedResolvent period hPeriod)

/-- Rellich compactness generated by finite coordinates. -/
theorem rellich
    (analytic :
      CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszL2OperatorGraphDirectCoerciveMinimalAnalyticData
        period hPeriod massSquared) :
    PhysicalH1RellichCompactness period hPeriod :=
  analytic.finiteCoordinateRellich.rellich

/-- Compactness of the selected realization inclusion. -/
theorem lagrangianInclusion_compact
    (analytic :
      CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszL2OperatorGraphDirectCoerciveMinimalAnalyticData
        period hPeriod massSquared) :
    IsCompactOperator
      (analytic.boundary.triple.lagrangianInclusion analytic.condition) :=
  ((analytic.boundary.geometric.greenCore period hPeriod).physicalH1RegularityData
      period hPeriod analytic.graphEllipticEstimate)
    |>.lagrangianInclusion_compact
      (analytic.boundary.triple period hPeriod) analytic.condition
      (analytic.rellich period hPeriod)

/-- Coercive inverse with compact selected-domain inclusion. -/
def coerciveCompactEmbeddingAt
    (analytic :
      CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszL2OperatorGraphDirectCoerciveMinimalAnalyticData
        period hPeriod massSquared) :
    analytic.boundary.triple.LagrangianCoerciveCompactEmbeddingAt
      analytic.condition analytic.referenceParameter where
  coercive := analytic.coerciveSurjectiveAt period hPeriod
  compact_inclusion := analytic.lagrangianInclusion_compact period hPeriod

/-- Compact physical reference resolvent. -/
noncomputable def compactResolvent
    (analytic :
      CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszL2OperatorGraphDirectCoerciveMinimalAnalyticData
        period hPeriod massSquared) :
    analytic.boundary.triple.LagrangianCompactResolventAt
      analytic.condition analytic.referenceParameter :=
  (analytic.coerciveCompactEmbeddingAt period hPeriod)
    |>.compactResolvent analytic.boundary.triple
      analytic.condition analytic.referenceParameter

/-- Lower form bound generated by coercivity. -/
def semibounded
    (analytic :
      CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszL2OperatorGraphDirectCoerciveMinimalAnalyticData
        period hPeriod massSquared) :
    analytic.boundary.triple.LagrangianSemiboundedData analytic.condition :=
  analytic.shiftedFormCoercive.toSemiboundedData
    analytic.boundary.triple analytic.condition analytic.referenceParameter

/-- Fredholm alternative away from the reference parameter. -/
theorem fredholmAlternative
    (analytic :
      CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszL2OperatorGraphDirectCoerciveMinimalAnalyticData
        period hPeriod massSquared)
    (spectralParameter : Real)
    (hParameter : spectralParameter ≠ analytic.referenceParameter) :
    analytic.boundary.triple.LagrangianHasEigenvalue
        analytic.condition spectralParameter ∨
      analytic.boundary.triple.LagrangianResolventPoint
        analytic.condition spectralParameter :=
  analytic.boundary.triple.lagrangian_fredholmAlternative
    analytic.condition analytic.referenceParameter spectralParameter
    (sub_ne_zero.mpr hParameter)
    (analytic.compactResolvent period hPeriod)

/-- Finite multiplicity away from the reference parameter. -/
theorem finiteDimensional_operatorEigenspace
    (analytic :
      CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszL2OperatorGraphDirectCoerciveMinimalAnalyticData
        period hPeriod massSquared)
    (eigenvalue : Real)
    (hEigenvalue : eigenvalue ≠ analytic.referenceParameter) :
    FiniteDimensional Real
      (analytic.boundary.triple.lagrangianOperatorEigenspace
        analytic.condition eigenvalue) :=
  (analytic.compactResolvent period hPeriod)
    |>.finiteDimensional_operatorEigenspace
      analytic.boundary.triple analytic.condition
      analytic.referenceParameter eigenvalue hEigenvalue

/-- Eigenfields at distinct eigenvalues are orthogonal. -/
theorem eigenfields_orthogonal
    (analytic :
      CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszL2OperatorGraphDirectCoerciveMinimalAnalyticData
        period hPeriod massSquared)
    (firstEigenvalue secondEigenvalue : Real)
    (hDistinct : firstEigenvalue ≠ secondEigenvalue)
    (first : analytic.boundary.triple.lagrangianOperatorEigenspace
      analytic.condition firstEigenvalue)
    (second : analytic.boundary.triple.lagrangianOperatorEigenspace
      analytic.condition secondEigenvalue) :
    inner Real
        (analytic.boundary.triple.lagrangianInclusion analytic.condition first.1)
        (analytic.boundary.triple.lagrangianInclusion analytic.condition second.1) = 0 :=
  analytic.boundary.triple.lagrangianEigenfields_orthogonal
    analytic.condition firstEigenvalue secondEigenvalue hDistinct first second

/-- Every eigenvalue lies above the coercive reference parameter. -/
theorem eigenvalue_ge_referenceParameter
    (analytic :
      CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszL2OperatorGraphDirectCoerciveMinimalAnalyticData
        period hPeriod massSquared)
    (eigenvalue : Real)
    (hEigenvalue : analytic.boundary.triple.LagrangianHasEigenvalue
      analytic.condition eigenvalue) :
    analytic.referenceParameter ≤ eigenvalue := by
  rcases hEigenvalue with ⟨field, hField, hEquation⟩
  exact (analytic.semibounded period hPeriod).eigenvalue_ge_lowerBound
    analytic.boundary.triple analytic.condition eigenvalue
    field hField hEquation

/-- Spectral completeness of the compact reference resolvent. -/
theorem spectral_complete
    (analytic :
      CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszL2OperatorGraphDirectCoerciveMinimalAnalyticData
        period hPeriod massSquared) :
    (⨆ eigenvalue : Real,
      Module.End.eigenspace
        ((analytic.compactResolvent period hPeriod).bounded.ambientResolvent
          analytic.boundary.triple analytic.condition
            analytic.referenceParameter).toLinearMap eigenvalue)ᗮ = ⊥ :=
  (analytic.compactResolvent period hPeriod).spectral_complete
    analytic.boundary.triple analytic.condition analytic.referenceParameter

/-- Classical domain-valued source solution. -/
noncomputable def sourceSolution
    (analytic :
      CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszL2OperatorGraphDirectCoerciveMinimalAnalyticData
        period hPeriod massSquared) :
    BulkL2 period hPeriod →L[Real]
      analytic.boundary.triple.lagrangianDomainSubmodule analytic.condition :=
  (analytic.boundedResolvent period hPeriod).resolvent

/-- Strong shifted source equation. -/
theorem sourceSolution_equation
    (analytic :
      CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszL2OperatorGraphDirectCoerciveMinimalAnalyticData
        period hPeriod massSquared)
    (source : BulkL2 period hPeriod) :
    analytic.boundary.triple.lagrangianShiftedOperator
        analytic.condition analytic.referenceParameter
        (analytic.sourceSolution period hPeriod source) = source :=
  (analytic.boundedResolvent period hPeriod).left_inverse source

/-- Weak stationarity. -/
theorem sourceSolution_stationary
    (analytic :
      CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszL2OperatorGraphDirectCoerciveMinimalAnalyticData
        period hPeriod massSquared)
    (source : BulkL2 period hPeriod) :
    analytic.boundary.triple.lagrangianSourceStationary
      analytic.condition analytic.referenceParameter source
      (analytic.sourceSolution period hPeriod source) :=
  analytic.boundary.triple.lagrangianSourceStationary_of_equation
    analytic.condition analytic.referenceParameter source _
    (analytic.sourceSolution_equation period hPeriod source)

/-- Weak stationarity is equivalent to the strong equation. -/
theorem sourceStationary_iff_equation
    (analytic :
      CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszL2OperatorGraphDirectCoerciveMinimalAnalyticData
        period hPeriod massSquared)
    (source : BulkL2 period hPeriod)
    (field : analytic.boundary.triple.lagrangianDomainSubmodule
      analytic.condition) :
    analytic.boundary.triple.lagrangianSourceStationary
        analytic.condition analytic.referenceParameter source field ↔
      analytic.boundary.triple.lagrangianShiftedOperator
        analytic.condition analytic.referenceParameter field = source :=
  analytic.boundary.triple.lagrangianSourceStationary_iff_equation
    analytic.condition analytic.referenceParameter source field
    (analytic.denseDomain period hPeriod)

/-- Exact first variation of the shifted source action. -/
theorem sourceAction_hasDerivAt
    (analytic :
      CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszL2OperatorGraphDirectCoerciveMinimalAnalyticData
        period hPeriod massSquared)
    (source : BulkL2 period hPeriod)
    (field variation : analytic.boundary.triple.lagrangianDomainSubmodule
      analytic.condition) :
    HasDerivAt
      (fun parameter : Real =>
        analytic.boundary.triple.lagrangianSourceAction
          analytic.condition analytic.referenceParameter source
          (field + parameter • variation))
      (inner Real
        (analytic.boundary.triple.lagrangianShiftedOperator
            analytic.condition analytic.referenceParameter field - source)
        (analytic.boundary.triple.lagrangianInclusion
          analytic.condition variation)) 0 :=
  analytic.boundary.triple.lagrangianSourceAction_hasDerivAt
    analytic.condition analytic.referenceParameter source field variation

/-- The source solution is the unique global minimizer. -/
theorem sourceSolution_unique_minimizer
    (analytic :
      CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszL2OperatorGraphDirectCoerciveMinimalAnalyticData
        period hPeriod massSquared)
    (source : BulkL2 period hPeriod) :
    (∀ field : analytic.boundary.triple.lagrangianDomainSubmodule
        analytic.condition,
      analytic.boundary.triple.lagrangianSourceAction
          analytic.condition analytic.referenceParameter source
          (analytic.sourceSolution period hPeriod source) ≤
        analytic.boundary.triple.lagrangianSourceAction
          analytic.condition analytic.referenceParameter source field) ∧
      (∀ field : analytic.boundary.triple.lagrangianDomainSubmodule
          analytic.condition,
        analytic.boundary.triple.lagrangianSourceAction
            analytic.condition analytic.referenceParameter source field =
          analytic.boundary.triple.lagrangianSourceAction
            analytic.condition analytic.referenceParameter source
            (analytic.sourceSolution period hPeriod source) →
        field = analytic.sourceSolution period hPeriod source) :=
  analytic.shiftedFormCoercive.unique_minimizer
    analytic.boundary.triple analytic.condition analytic.referenceParameter
    (analytic.denseDomain period hPeriod) source

/-- Symmetric Gaussian source pairing. -/
def gaussianPairing
    (analytic :
      CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszL2OperatorGraphDirectCoerciveMinimalAnalyticData
        period hPeriod massSquared)
    (first second : BulkL2 period hPeriod) : Real :=
  analytic.boundary.triple.lagrangianGaussianPairing
    analytic.condition analytic.referenceParameter
    (analytic.boundedResolvent period hPeriod) first second

/-- Gaussian generating functional. -/
def gaussianGeneratingFunctional
    (analytic :
      CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszL2OperatorGraphDirectCoerciveMinimalAnalyticData
        period hPeriod massSquared)
    (source : BulkL2 period hPeriod) : Real :=
  analytic.boundary.triple.lagrangianGaussianGeneratingFunctional
    analytic.condition analytic.referenceParameter
    (analytic.boundedResolvent period hPeriod) source

/-- Symmetry of the Gaussian response. -/
theorem gaussianPairing_comm
    (analytic :
      CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszL2OperatorGraphDirectCoerciveMinimalAnalyticData
        period hPeriod massSquared)
    (first second : BulkL2 period hPeriod) :
    analytic.gaussianPairing period hPeriod first second =
      analytic.gaussianPairing period hPeriod second first :=
  analytic.boundary.triple.lagrangianGaussianPairing_comm
    analytic.condition analytic.referenceParameter
    (analytic.boundedResolvent period hPeriod) first second

/-- On-shell Gaussian identity. -/
theorem gaussianGeneratingFunctional_eq_neg_onShell
    (analytic :
      CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszL2OperatorGraphDirectCoerciveMinimalAnalyticData
        period hPeriod massSquared)
    (source : BulkL2 period hPeriod) :
    analytic.gaussianGeneratingFunctional period hPeriod source =
      -analytic.boundary.triple.lagrangianSourceAction
        analytic.condition analytic.referenceParameter source
        (analytic.sourceSolution period hPeriod source) := by
  unfold gaussianGeneratingFunctional sourceSolution
  exact analytic.boundary.triple
    |>.lagrangianGaussianGeneratingFunctional_eq_neg_onShell
      analytic.condition analytic.referenceParameter
      (analytic.boundedResolvent period hPeriod) source

/-- Nonnegative Gaussian response. -/
theorem gaussianGeneratingFunctional_nonnegative
    (analytic :
      CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszL2OperatorGraphDirectCoerciveMinimalAnalyticData
        period hPeriod massSquared)
    (source : BulkL2 period hPeriod) :
    0 ≤ analytic.gaussianGeneratingFunctional period hPeriod source := by
  unfold gaussianGeneratingFunctional
  exact analytic.shiftedFormCoercive.gaussian_nonnegative
    analytic.boundary.triple analytic.condition analytic.referenceParameter
    (analytic.denseDomain period hPeriod) source

/-- Complete graph/direct-coercive Program P certificate. -/
theorem finalProgramP_certificate
    (analytic :
      CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszL2OperatorGraphDirectCoerciveMinimalAnalyticData
        period hPeriod massSquared)
    (source : BulkL2 period hPeriod) :
    P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerAtlasNaturality4D.CanonicalPhysicalScalarWaveAtlasNaturality
        period hPeriod ∧
      (∀ index boundary,
        MemLp
          (analytic.boundary.eulerCoefficientOperators.coefficient
            period hPeriod index boundary)
          (2 : ENNReal)
          (P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D.canonicalLatitudeBaseMeasure
            period)) ∧
      Function.Surjective analytic.boundary.completedBoundaryTrace ∧
      analytic.boundary.triple.actualAdjointDomain analytic.condition =
        analytic.boundary.triple.realizationDomain analytic.condition ∧
      analytic.boundary.triple.lagrangianShiftedOperator
          analytic.condition analytic.referenceParameter
          (analytic.sourceSolution period hPeriod source) = source ∧
      (∀ field : analytic.boundary.triple.lagrangianDomainSubmodule
          analytic.condition,
        analytic.boundary.triple.lagrangianSourceAction
            analytic.condition analytic.referenceParameter source
            (analytic.sourceSolution period hPeriod source) ≤
          analytic.boundary.triple.lagrangianSourceAction
            analytic.condition analytic.referenceParameter source field) ∧
      0 ≤ analytic.gaussianGeneratingFunctional period hPeriod source ∧
      (∀ spectralParameter : Real,
        spectralParameter ≠ analytic.referenceParameter →
          analytic.boundary.triple.LagrangianHasEigenvalue
              analytic.condition spectralParameter ∨
            analytic.boundary.triple.LagrangianResolventPoint
              analytic.condition spectralParameter) :=
  ⟨analytic.boundary.geometric.intrinsicWave.toWaveAtlasNaturality
      period hPeriod,
    analytic.boundary.eulerCoefficientOperators.coefficient_memLp period hPeriod,
    ((analytic.boundary.rieszBoundaryData period hPeriod).certificate
      period hPeriod).2.2.1,
    analytic.actualAdjointDomain_eq period hPeriod,
    analytic.sourceSolution_equation period hPeriod source,
    (analytic.sourceSolution_unique_minimizer period hPeriod source).1,
    analytic.gaussianGeneratingFunctional_nonnegative period hPeriod source,
    analytic.fredholmAlternative period hPeriod⟩

end CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszL2OperatorGraphDirectCoerciveMinimalAnalyticData

/-- Marker for the energy-free graph/direct-coercive Program P endpoint. -/
theorem canonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszL2OperatorGraphMinimalProgramPClosure_available :
    True :=
  trivial

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszL2OperatorGraphMinimalProgramPClosure4D
end JanusFormal
