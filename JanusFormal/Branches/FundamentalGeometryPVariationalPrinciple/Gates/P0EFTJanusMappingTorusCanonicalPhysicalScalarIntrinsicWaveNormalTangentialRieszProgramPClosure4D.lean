import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszResolventClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveRieszProgramPClosure4D

/-!
# Program P endpoint from the normal/tangential Riesz package

This is the full variational and Gaussian endpoint for the geometrically natural
normal/tangential Green decomposition.

The completed Cauchy trace is reconstructed by Riesz duality from the Green form
and the bounded explicit Cauchy extension.  A positive shifted-form
decomposition gives the classical source solution and self-adjointness, while
finite-rank Rellich approximation gives compact spectral theory.

No independent normal trace regularity or adjoint regularity input is present.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszResolventClosure4D

set_option autoImplicit false
noncomputable section

open Set Topology MeasureTheory
open P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszResolventClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveRieszProgramPClosure4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D

variable (period : Real) (hPeriod : period ≠ 0)
variable {massSquared : Real}

private abbrev BulkL2 :=
  P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D.CanonicalPhysicalBulkL2
    period hPeriod

namespace CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszResolventData

/-- Conversion to the generic Riesz Program P endpoint. -/
def toIntrinsicWaveRieszProgramPData
    (analytic : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszResolventData
      period hPeriod massSquared) :=
  analytic.toIntrinsicWaveRieszResolventData

/-- Classical domain-valued source solution. -/
noncomputable def sourceSolution
    (analytic : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszResolventData
      period hPeriod massSquared) :
    BulkL2 period hPeriod →L[Real]
      analytic.boundary.triple.lagrangianDomainSubmodule analytic.condition :=
  (analytic.toIntrinsicWaveRieszProgramPData period hPeriod)
    |>.sourceSolution period hPeriod

/-- Strong shifted source equation. -/
theorem sourceSolution_equation
    (analytic : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszResolventData
      period hPeriod massSquared)
    (source : BulkL2 period hPeriod) :
    analytic.boundary.triple.lagrangianShiftedOperator
        analytic.condition analytic.referenceParameter
        (analytic.sourceSolution period hPeriod source) = source :=
  (analytic.toIntrinsicWaveRieszProgramPData period hPeriod)
    |>.sourceSolution_equation period hPeriod source

/-- Weak stationarity of the classical source solution. -/
theorem sourceSolution_stationary
    (analytic : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszResolventData
      period hPeriod massSquared)
    (source : BulkL2 period hPeriod) :
    analytic.boundary.triple.lagrangianSourceStationary
      analytic.condition analytic.referenceParameter source
      (analytic.sourceSolution period hPeriod source) :=
  (analytic.toIntrinsicWaveRieszProgramPData period hPeriod)
    |>.sourceSolution_stationary period hPeriod source

/-- Weak stationarity is equivalent to the strong shifted equation. -/
theorem sourceStationary_iff_equation
    (analytic : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszResolventData
      period hPeriod massSquared)
    (source : BulkL2 period hPeriod)
    (field : analytic.boundary.triple.lagrangianDomainSubmodule
      analytic.condition) :
    analytic.boundary.triple.lagrangianSourceStationary
        analytic.condition analytic.referenceParameter source field ↔
      analytic.boundary.triple.lagrangianShiftedOperator
        analytic.condition analytic.referenceParameter field = source :=
  (analytic.toIntrinsicWaveRieszProgramPData period hPeriod)
    |>.sourceStationary_iff_equation period hPeriod source field

/-- Exact first variation of the physical source action. -/
theorem sourceAction_hasDerivAt
    (analytic : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszResolventData
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
  (analytic.toIntrinsicWaveRieszProgramPData period hPeriod)
    |>.sourceAction_hasDerivAt period hPeriod source field variation

/-- Positive shifted coercivity makes the source solution the unique global
minimizer. -/
theorem sourceSolution_unique_minimizer
    (analytic : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszResolventData
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
  (analytic.toIntrinsicWaveRieszProgramPData period hPeriod)
    |>.sourceSolution_unique_minimizer period hPeriod source

/-- Symmetric Gaussian source pairing. -/
def gaussianPairing
    (analytic : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszResolventData
      period hPeriod massSquared)
    (first second : BulkL2 period hPeriod) : Real :=
  (analytic.toIntrinsicWaveRieszProgramPData period hPeriod)
    |>.gaussianPairing period hPeriod first second

/-- Gaussian generating functional. -/
def gaussianGeneratingFunctional
    (analytic : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszResolventData
      period hPeriod massSquared)
    (source : BulkL2 period hPeriod) : Real :=
  (analytic.toIntrinsicWaveRieszProgramPData period hPeriod)
    |>.gaussianGeneratingFunctional period hPeriod source

/-- Symmetry of the Gaussian response. -/
theorem gaussianPairing_comm
    (analytic : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszResolventData
      period hPeriod massSquared)
    (first second : BulkL2 period hPeriod) :
    analytic.gaussianPairing period hPeriod first second =
      analytic.gaussianPairing period hPeriod second first :=
  (analytic.toIntrinsicWaveRieszProgramPData period hPeriod)
    |>.gaussianPairing_comm period hPeriod first second

/-- The Gaussian generating functional is minus the on-shell source action. -/
theorem gaussianGeneratingFunctional_eq_neg_onShell
    (analytic : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszResolventData
      period hPeriod massSquared)
    (source : BulkL2 period hPeriod) :
    analytic.gaussianGeneratingFunctional period hPeriod source =
      -analytic.boundary.triple.lagrangianSourceAction
        analytic.condition analytic.referenceParameter source
        (analytic.sourceSolution period hPeriod source) :=
  (analytic.toIntrinsicWaveRieszProgramPData period hPeriod)
    |>.gaussianGeneratingFunctional_eq_neg_onShell period hPeriod source

/-- Nonnegativity of the Gaussian response. -/
theorem gaussianGeneratingFunctional_nonnegative
    (analytic : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszResolventData
      period hPeriod massSquared)
    (source : BulkL2 period hPeriod) :
    0 ≤ analytic.gaussianGeneratingFunctional period hPeriod source :=
  (analytic.toIntrinsicWaveRieszProgramPData period hPeriod)
    |>.gaussianGeneratingFunctional_nonnegative period hPeriod source

/-- Complete normal/tangential Riesz Program P certificate. -/
theorem finalProgramP_certificate
    (analytic : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszResolventData
      period hPeriod massSquared)
    (source : BulkL2 period hPeriod) :
    (∀ field test,
      (∫ parameter,
        analytic.boundary.geometric.tangentialDensity field test parameter
        ∂P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetProductCoarea4D.canonicalLatitudeCauchyJetProductMeasure
          period) = 0) ∧
      Function.Surjective analytic.boundary.completedBoundaryTrace ∧
      analytic.boundary.triple.actualAdjointDomain analytic.condition =
        analytic.boundary.triple.realizationDomain analytic.condition ∧
      analytic.boundary.triple.lagrangianShiftedOperator
          analytic.condition analytic.referenceParameter
          (analytic.sourceSolution period hPeriod source) = source ∧
      analytic.boundary.triple.lagrangianSourceStationary
          analytic.condition analytic.referenceParameter source
          (analytic.sourceSolution period hPeriod source) ∧
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
  ⟨analytic.boundary.geometric.toNormalTangentialSplitData
      |>.tangential_integral_eq_zero,
    (analytic.boundary.certificate period hPeriod).2.2.2.1,
    analytic.actualAdjointDomain_eq period hPeriod,
    analytic.sourceSolution_equation period hPeriod source,
    analytic.sourceSolution_stationary period hPeriod source,
    (analytic.sourceSolution_unique_minimizer period hPeriod source).1,
    analytic.gaussianGeneratingFunctional_nonnegative period hPeriod source,
    analytic.fredholmAlternative period hPeriod⟩

end CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszResolventData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszResolventClosure4D

namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszProgramPClosure4D

/-- Marker theorem for the complete normal/tangential Riesz Program P endpoint. -/
theorem canonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszProgramPClosure_available : True :=
  trivial

end P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszProgramPClosure4D
end JanusFormal
