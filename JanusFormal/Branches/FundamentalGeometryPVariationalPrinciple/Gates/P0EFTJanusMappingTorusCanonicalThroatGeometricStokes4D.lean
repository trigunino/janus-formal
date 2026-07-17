import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteBoxBulkBoundaryStokes
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteStratifiedBoundaryVariation
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteNullFaceAction
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusPTSymmetricDifferentialLLStrongEquation4D

/-!
# Canonical-throat geometric Stokes bridge for the strong LL equation

The existing finite gates prove three exact algebraic statements:

* a variable-flux finite box has zero matched bulk/boundary residual;
* every supplied finite non-null/null/joint stratification has zero variation
  residual;
* every integrable finite null-face action is exactly reparametrization
  invariant.

This gate packages those statements into one finite boundary ledger and proves
that ledger vanishes without additional hypotheses.  It then isolates the two
genuinely geometric inputs still missing from the current manifold API:

1. continuum integration by parts for the actual finite smooth throat frame
   and canonical throat volume;
2. identification of its geometric boundary flux with the supplied finite
   ledger.

Given exactly those inputs, the existing StrongLL integration-by-parts
contract and its zero-flux boundary condition follow, so weak/stationary LL is
equivalent to the pointwise strong equation.  The finite telescoping theorems
alone are never promoted to a global manifold Stokes theorem.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalThroatGeometricStokes4D

set_option autoImplicit false

noncomputable section

open scoped BigOperators Manifold ContDiff Topology
open MeasureTheory
open P0EFTJanusFiniteBoxBulkBoundaryStokes
open P0EFTJanusFiniteStratifiedBoundaryVariation
open P0EFTJanusFiniteNullFaceAction
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLStrongEquation4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev throatData := fixedEquatorData period hPeriod
private abbrev EffectiveThroat := MappingTorus (throatData period hPeriod)

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance effectiveThroatCompactSpace :
    CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod

local instance effectiveThroatMeasurableSpace :
    MeasurableSpace (EffectiveThroat period hPeriod) := borel _

local instance effectiveThroatBorelSpace :
    BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

/-- Finite algebraic boundary data attached to every smooth LL test
direction.  The three face counts are explicit `Nat`s, so no hidden infinite
stratification is present. -/
structure CanonicalThroatFiniteBoundaryLedger where
  boxShape : BoxShape3
  boxFluxVariation :
    SmoothThroatField period hPeriod LLFieldFiber → VariableFlux3
  nonNullFaceCount : Nat
  nullFaceCount : Nat
  nullActionFaceCount : Nat
  nonNullFaces :
    SmoothThroatField period hPeriod LLFieldFiber →
      Fin nonNullFaceCount → NonNullFaceDatum
  nullFaces :
    SmoothThroatField period hPeriod LLFieldFiber →
      Fin nullFaceCount → NullFaceDatum
  nullActionFaces :
    SmoothThroatField period hPeriod LLFieldFiber →
      Fin nullActionFaceCount → FiniteNullFaceActionDatum
  nullActionIntegrability : ∀
    (direction : SmoothThroatField period hPeriod LLFieldFiber)
    (face : Fin nullActionFaceCount),
      NullFaceIntervalIntegrability (nullActionFaces direction face)

/-- The finite-box matched residual for one LL test direction. -/
def canonicalThroatFiniteBoxResidual
    (ledger : CanonicalThroatFiniteBoundaryLedger period hPeriod)
    (direction : SmoothThroatField period hPeriod LLFieldFiber) : Real :=
  matchedBulkBoundaryFirstVariation ledger.boxShape
    (ledger.boxFluxVariation direction)

/-- The finite non-null/null/joint residual for one direction. -/
def canonicalThroatFiniteStratifiedResidual
    (ledger : CanonicalThroatFiniteBoundaryLedger period hPeriod)
    (direction : SmoothThroatField period hPeriod LLFieldFiber) : Real :=
  finiteStratifiedBoundaryResidual (ledger.nonNullFaces direction)
    (ledger.nullFaces direction)

/-- Difference between transformed and original finite null-boundary actions.
It is included as an independent ledger entry rather than conflated with the
LL boundary flux. -/
def canonicalThroatFiniteNullActionResidual
    (ledger : CanonicalThroatFiniteBoundaryLedger period hPeriod)
    (direction : SmoothThroatField period hPeriod LLFieldFiber) : Real :=
  totalReparametrizedFiniteNullBoundaryAction
      (ledger.nullActionFaces direction) -
    totalFiniteNullBoundaryAction (ledger.nullActionFaces direction)

/-- Total finite residual assembled from the three already proved ledgers. -/
def canonicalThroatFiniteBoundaryLedgerResidual
    (ledger : CanonicalThroatFiniteBoundaryLedger period hPeriod)
    (direction : SmoothThroatField period hPeriod LLFieldFiber) : Real :=
  canonicalThroatFiniteBoxResidual period hPeriod ledger direction +
    canonicalThroatFiniteStratifiedResidual period hPeriod ledger direction +
    canonicalThroatFiniteNullActionResidual period hPeriod ledger direction

/-- Unconditional finite-box cancellation. -/
theorem canonicalThroatFiniteBoxResidual_eq_zero
    (ledger : CanonicalThroatFiniteBoundaryLedger period hPeriod)
    (direction : SmoothThroatField period hPeriod LLFieldFiber) :
    canonicalThroatFiniteBoxResidual period hPeriod ledger direction = 0 :=
  matchedBulkBoundaryFirstVariation_eq_zero ledger.boxShape
    (ledger.boxFluxVariation direction)

/-- Unconditional cancellation of every supplied finite stratified residual. -/
theorem canonicalThroatFiniteStratifiedResidual_eq_zero
    (ledger : CanonicalThroatFiniteBoundaryLedger period hPeriod)
    (direction : SmoothThroatField period hPeriod LLFieldFiber) :
    canonicalThroatFiniteStratifiedResidual period hPeriod ledger direction =
      0 :=
  finiteStratifiedBoundaryResidual_eq_zero (ledger.nonNullFaces direction)
    (ledger.nullFaces direction)

/-- Unconditional finite null-action invariance after using the already
explicit interval-integrability witnesses stored in the ledger. -/
theorem canonicalThroatFiniteNullActionResidual_eq_zero
    (ledger : CanonicalThroatFiniteBoundaryLedger period hPeriod)
    (direction : SmoothThroatField period hPeriod LLFieldFiber) :
    canonicalThroatFiniteNullActionResidual period hPeriod ledger direction =
      0 := by
  unfold canonicalThroatFiniteNullActionResidual
  rw [totalReparametrizedFiniteNullBoundaryAction_eq
    (ledger.nullActionFaces direction)
    (ledger.nullActionIntegrability direction)]
  ring

/-- Everything that genuinely follows from the finite gates is now closed. -/
theorem canonicalThroatFiniteBoundaryLedgerResidual_eq_zero
    (ledger : CanonicalThroatFiniteBoundaryLedger period hPeriod)
    (direction : SmoothThroatField period hPeriod LLFieldFiber) :
    canonicalThroatFiniteBoundaryLedgerResidual period hPeriod ledger
      direction = 0 := by
  rw [canonicalThroatFiniteBoundaryLedgerResidual,
    canonicalThroatFiniteBoxResidual_eq_zero,
    canonicalThroatFiniteStratifiedResidual_eq_zero,
    canonicalThroatFiniteNullActionResidual_eq_zero]
  ring

/-- Exact remaining geometry.  Neither field is derived from the finite
ledgers:

* `continuumIntegrationByParts` is the actual manifold IPP formula for the
  canonical throat measure and the implemented finite smooth frame;
* `boundaryFlux_eq_finiteLedgerResidual` identifies that genuine geometric
  flux with one supplied finite boundary discretization/stratification.

Keeping these as separate fields prevents finite telescoping from being
misreported as a global Stokes theorem. -/
structure CanonicalThroatGeometricStokesContractFor
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (regularity : LLStrongAnalyticRegularityContract period hPeriod
      frame) where
  finiteLedger : CanonicalThroatFiniteBoundaryLedger period hPeriod
  geometricBoundaryFlux :
    SmoothThroatField period hPeriod LLFieldFiber → Real
  continuumIntegrationByParts : ∀
      direction : SmoothThroatField period hPeriod LLFieldFiber,
    globalPTSymmetricDifferentialLLFluxFirstVariation period hPeriod
        frame fields direction
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) =
      (∫ point,
        inner Real
          (ptSymmetricStrongDifferentialLLEulerField period hPeriod
            frame regularity fields point)
          (direction point)
        ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) +
        geometricBoundaryFlux direction
  boundaryFlux_eq_finiteLedgerResidual : ∀
      direction : SmoothThroatField period hPeriod LLFieldFiber,
    geometricBoundaryFlux direction =
      canonicalThroatFiniteBoundaryLedgerResidual period hPeriod finiteLedger
        direction

/-- Backward-compatible specialization to the original POU frame. -/
abbrev CanonicalThroatGeometricStokesContract
    (fields : IndependentFields period hPeriod)
    (regularity : LLStrongAnalyticRegularityContract period hPeriod
      (finiteSmoothThroatGeneratingFrame period hPeriod)) :=
  CanonicalThroatGeometricStokesContractFor period hPeriod
    (finiteSmoothThroatGeneratingFrame period hPeriod) fields regularity

/-- Generic geometric Stokes input for an explicitly selected frame. -/
def CanonicalThroatGeometricStokesContractFor.toStrongLLIntegrationByParts
    {frame : SmoothThroatGeneratingFrame period hPeriod}
    {fields : IndependentFields period hPeriod}
    {regularity : LLStrongAnalyticRegularityContract period hPeriod frame}
    (contract : CanonicalThroatGeometricStokesContractFor period hPeriod
      frame fields regularity) :
    PTSymmetricLLIntegrationByPartsContract period hPeriod frame regularity
      fields (intrinsicCanonicalThroatVolumeMeasure period hPeriod) where
  boundaryFlux := contract.geometricBoundaryFlux
  integrationByParts := contract.continuumIntegrationByParts

/-- Every finite ledger has zero residual, independently of the frame. -/
theorem CanonicalThroatGeometricStokesContractFor.geometricBoundaryFlux_eq_zero
    {frame : SmoothThroatGeneratingFrame period hPeriod}
    {fields : IndependentFields period hPeriod}
    {regularity : LLStrongAnalyticRegularityContract period hPeriod frame}
    (contract : CanonicalThroatGeometricStokesContractFor period hPeriod
      frame fields regularity)
    (direction : SmoothThroatField period hPeriod LLFieldFiber) :
    contract.geometricBoundaryFlux direction = 0 := by
  rw [contract.boundaryFlux_eq_finiteLedgerResidual direction,
    canonicalThroatFiniteBoundaryLedgerResidual_eq_zero]

theorem CanonicalThroatGeometricStokesContractFor.satisfiesNaturalBoundaryCondition
    {frame : SmoothThroatGeneratingFrame period hPeriod}
    {fields : IndependentFields period hPeriod}
    {regularity : LLStrongAnalyticRegularityContract period hPeriod frame}
    (contract : CanonicalThroatGeometricStokesContractFor period hPeriod
      frame fields regularity) :
    SatisfiesPTSymmetricLLNaturalBoundaryCondition period hPeriod
      (contract.toStrongLLIntegrationByParts period hPeriod) := by
  intro direction
  change contract.geometricBoundaryFlux direction = 0
  exact contract.geometricBoundaryFlux_eq_zero period hPeriod direction

theorem canonicalThroat_geometricStokes_weak_iff_strong_for
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (regularity : LLStrongAnalyticRegularityContract period hPeriod frame)
    (contract : CanonicalThroatGeometricStokesContractFor period hPeriod
      frame fields regularity) :
    SatisfiesPTSymmetricWeakDifferentialLLEquation period hPeriod frame fields
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) ↔
      SatisfiesPTSymmetricStrongDifferentialLLEquation period hPeriod
        frame regularity fields := by
  letI : IsFiniteMeasure
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
    intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod
  letI : Measure.IsOpenPosMeasure
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
    intrinsicCanonicalThroatVolumeMeasure_isOpenPosMeasure period hPeriod
  exact satisfiesPTSymmetricWeakDifferentialLLEquation_iff_strong
    period hPeriod frame regularity fields
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod)
      (contract.toStrongLLIntegrationByParts period hPeriod)
      (contract.satisfiesNaturalBoundaryCondition period hPeriod)

/-- The geometric Stokes input instantiates exactly the StrongLL IPP
interface, with no additional analytic or boundary assumption. -/
def CanonicalThroatGeometricStokesContract.toStrongLLIntegrationByParts
    {fields : IndependentFields period hPeriod}
    {regularity : LLStrongAnalyticRegularityContract period hPeriod
      (finiteSmoothThroatGeneratingFrame period hPeriod)}
    (contract : CanonicalThroatGeometricStokesContract period hPeriod
      fields regularity) :
    PTSymmetricLLIntegrationByPartsContract period hPeriod
      (finiteSmoothThroatGeneratingFrame period hPeriod) regularity fields
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) where
  boundaryFlux := contract.geometricBoundaryFlux
  integrationByParts := contract.continuumIntegrationByParts

/-- Once the geometric boundary flux is identified with the finite ledger,
its vanishing is an unconditional consequence of the existing finite gates. -/
theorem CanonicalThroatGeometricStokesContract.geometricBoundaryFlux_eq_zero
    {fields : IndependentFields period hPeriod}
    {regularity : LLStrongAnalyticRegularityContract period hPeriod
      (finiteSmoothThroatGeneratingFrame period hPeriod)}
    (contract : CanonicalThroatGeometricStokesContract period hPeriod
      fields regularity)
    (direction : SmoothThroatField period hPeriod LLFieldFiber) :
    contract.geometricBoundaryFlux direction = 0 := by
  rw [contract.boundaryFlux_eq_finiteLedgerResidual direction,
    canonicalThroatFiniteBoundaryLedgerResidual_eq_zero]

/-- The StrongLL natural boundary condition is therefore discharged by the
geometric identification contract; no separate zero-flux hypothesis remains. -/
theorem CanonicalThroatGeometricStokesContract.satisfiesNaturalBoundaryCondition
    {fields : IndependentFields period hPeriod}
    {regularity : LLStrongAnalyticRegularityContract period hPeriod
      (finiteSmoothThroatGeneratingFrame period hPeriod)}
    (contract : CanonicalThroatGeometricStokesContract period hPeriod
      fields regularity) :
    SatisfiesPTSymmetricLLNaturalBoundaryCondition period hPeriod
      (contract.toStrongLLIntegrationByParts period hPeriod) := by
  intro direction
  change contract.geometricBoundaryFlux direction = 0
  exact contract.geometricBoundaryFlux_eq_zero period hPeriod direction

/-- Canonical full support and finite volume are already unconditional.  The
only remaining input here is the explicitly displayed geometric Stokes
contract. -/
theorem canonicalThroat_geometricStokes_weak_iff_strong
    (fields : IndependentFields period hPeriod)
    (regularity : LLStrongAnalyticRegularityContract period hPeriod
      (finiteSmoothThroatGeneratingFrame period hPeriod))
    (contract : CanonicalThroatGeometricStokesContract period hPeriod
      fields regularity) :
    SatisfiesPTSymmetricWeakDifferentialLLEquation period hPeriod
        (finiteSmoothThroatGeneratingFrame period hPeriod) fields
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) ↔
      SatisfiesPTSymmetricStrongDifferentialLLEquation period hPeriod
        (finiteSmoothThroatGeneratingFrame period hPeriod) regularity fields := by
  letI : IsFiniteMeasure
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
    intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod
  letI : Measure.IsOpenPosMeasure
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
    intrinsicCanonicalThroatVolumeMeasure_isOpenPosMeasure period hPeriod
  exact satisfiesPTSymmetricWeakDifferentialLLEquation_iff_strong
    period hPeriod (finiteSmoothThroatGeneratingFrame period hPeriod)
      regularity fields (intrinsicCanonicalThroatVolumeMeasure period hPeriod)
      (contract.toStrongLLIntegrationByParts period hPeriod)
      (contract.satisfiesNaturalBoundaryCondition period hPeriod)

/-- Stationarity of the unchanged canonical PT-symmetric differential LL
action is equivalent to the strong equation under the same exact geometric
contract. -/
theorem canonicalThroat_geometricStokes_stationary_iff_strong
    (fields : IndependentFields period hPeriod)
    (regularity : LLStrongAnalyticRegularityContract period hPeriod
      (finiteSmoothThroatGeneratingFrame period hPeriod))
    (contract : CanonicalThroatGeometricStokesContract period hPeriod
      fields regularity) :
    PTSymmetricDifferentialLLFluxStationary period hPeriod
        (finiteSmoothThroatGeneratingFrame period hPeriod) fields
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) ↔
      SatisfiesPTSymmetricStrongDifferentialLLEquation period hPeriod
        (finiteSmoothThroatGeneratingFrame period hPeriod) regularity fields :=
  canonicalThroat_ptSymmetricDifferentialLLStationary_iff_strong
    period hPeriod fields regularity
      (contract.toStrongLLIntegrationByParts period hPeriod)
      (contract.satisfiesNaturalBoundaryCondition period hPeriod)

end

end P0EFTJanusMappingTorusCanonicalThroatGeometricStokes4D
end JanusFormal
