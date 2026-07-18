import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalThroatGeometricStokes4D

/-!
# Exact remaining zero-boundary IPP lemma on the canonical throat

The finite boundary data are algebraically independent of the smooth frame
flux.  Consequently they cannot identify the continuum boundary term without
new geometric input.  Since every finite ledger residual is already zero, the
two fields of `CanonicalThroatGeometricStokesContract` reduce exactly to one
analytic statement: global integration by parts for the implemented weighted
LL frame flux, with zero boundary term.

This gate states that single missing lemma precisely and derives the complete
geometric Stokes contract from it using a canonical empty finite ledger.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalThroatGlobalZeroBoundaryIPP4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff Topology
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
open P0EFTJanusMappingTorusCanonicalThroatGeometricStokes4D

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

/-- The sole remaining statement needed by the current strong operator: the
global PT-averaged first variation integrates by parts against its weighted
frame Euler field with no boundary contribution.

Compactness alone does not imply this formula.  The implemented generators
are partition-of-unity-weighted local-frame fields, and no theorem currently
shows that they are divergence-free for the canonical measure.  A proof must
therefore establish that compatibility; otherwise the strong operator needs
the usual measure-divergence correction. -/
def CanonicalThroatScalarWeightedLLFrameFluxGlobalIPPFor
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (regularity : LLStrongAnalyticRegularityContract period hPeriod
      frame) : Prop :=
  ∀ direction : SmoothThroatField period hPeriod LLFieldFiber,
    globalPTSymmetricDifferentialLLFluxFirstVariation period hPeriod
        frame fields direction
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) =
      ∫ point,
        inner Real
          (ptSymmetricStrongDifferentialLLEulerField period hPeriod
            frame regularity fields point)
          (direction point)
        ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)

/-- Backward-compatible specialization to the original POU frame. -/
def CanonicalThroatScalarWeightedLLFrameFluxGlobalIPP
    (fields : IndependentFields period hPeriod)
    (regularity : LLStrongAnalyticRegularityContract period hPeriod
      (finiteSmoothThroatGeneratingFrame period hPeriod)) : Prop :=
  CanonicalThroatScalarWeightedLLFrameFluxGlobalIPPFor period hPeriod
    (finiteSmoothThroatGeneratingFrame period hPeriod) fields regularity

/-- Zero variable flux used by the canonical empty ledger. -/
def zeroVariableFlux3 : VariableFlux3 where
  xFlux := fun _ _ _ => 0
  yFlux := fun _ _ _ => 0
  zFlux := fun _ _ _ => 0

/-- A canonical empty finite ledger.  It carries no geometric information and
exists only to witness that the already-proved finite residual is zero. -/
def canonicalThroatEmptyFiniteBoundaryLedger :
    CanonicalThroatFiniteBoundaryLedger period hPeriod where
  boxShape := { xCells := 0, yCells := 0, zCells := 0 }
  boxFluxVariation := fun _ => zeroVariableFlux3
  nonNullFaceCount := 0
  nullFaceCount := 0
  nullActionFaceCount := 0
  nonNullFaces := fun _ face => Fin.elim0 face
  nullFaces := fun _ face => Fin.elim0 face
  nullActionFaces := fun _ face => Fin.elim0 face
  nullActionIntegrability := fun _ face => Fin.elim0 face

/-- Generic zero-boundary IPP produces the geometric contract for the same
explicitly selected frame. -/
def CanonicalThroatScalarWeightedLLFrameFluxGlobalIPPFor.toGeometricStokesContract
    {frame : SmoothThroatGeneratingFrame period hPeriod}
    {fields : IndependentFields period hPeriod}
    {regularity : LLStrongAnalyticRegularityContract period hPeriod frame}
    (hIPP : CanonicalThroatScalarWeightedLLFrameFluxGlobalIPPFor period hPeriod
      frame fields regularity) :
    CanonicalThroatGeometricStokesContractFor period hPeriod
      frame fields regularity where
  finiteLedger := canonicalThroatEmptyFiniteBoundaryLedger period hPeriod
  geometricBoundaryFlux := fun _ => 0
  continuumIntegrationByParts := by
    intro direction
    simpa using hIPP direction
  boundaryFlux_eq_finiteLedgerResidual := by
    intro direction
    exact (canonicalThroatFiniteBoundaryLedgerResidual_eq_zero period hPeriod
      (canonicalThroatEmptyFiniteBoundaryLedger period hPeriod) direction).symm

theorem canonicalThroatGeometricStokesContractFor_toGlobalZeroBoundaryIPP
    {frame : SmoothThroatGeneratingFrame period hPeriod}
    {fields : IndependentFields period hPeriod}
    {regularity : LLStrongAnalyticRegularityContract period hPeriod frame}
    (contract : CanonicalThroatGeometricStokesContractFor period hPeriod
      frame fields regularity) :
    CanonicalThroatScalarWeightedLLFrameFluxGlobalIPPFor period hPeriod
      frame fields regularity := by
  intro direction
  rw [contract.continuumIntegrationByParts direction,
    contract.geometricBoundaryFlux_eq_zero period hPeriod direction, add_zero]

theorem canonicalThroat_geometricStokesContractFor_nonempty_iff_globalIPP
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (regularity : LLStrongAnalyticRegularityContract period hPeriod frame) :
    Nonempty (CanonicalThroatGeometricStokesContractFor period hPeriod
        frame fields regularity) ↔
      CanonicalThroatScalarWeightedLLFrameFluxGlobalIPPFor period hPeriod
        frame fields regularity := by
  constructor
  · rintro ⟨contract⟩
    exact canonicalThroatGeometricStokesContractFor_toGlobalZeroBoundaryIPP
      period hPeriod contract
  · intro hIPP
    exact ⟨hIPP.toGeometricStokesContract period hPeriod⟩

theorem canonicalThroat_globalIPP_weak_iff_strong_for
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (regularity : LLStrongAnalyticRegularityContract period hPeriod frame)
    (hIPP : CanonicalThroatScalarWeightedLLFrameFluxGlobalIPPFor period hPeriod
      frame fields regularity) :
    SatisfiesPTSymmetricWeakDifferentialLLEquation period hPeriod frame fields
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) ↔
      SatisfiesPTSymmetricStrongDifferentialLLEquation period hPeriod
        frame regularity fields :=
  canonicalThroat_geometricStokes_weak_iff_strong_for period hPeriod frame
    fields regularity (hIPP.toGeometricStokesContract period hPeriod)

/-- The single global IPP lemma supplies both geometric-contract fields: the
boundary flux is zero and its finite-ledger realization is the empty ledger. -/
def CanonicalThroatScalarWeightedLLFrameFluxGlobalIPP.toGeometricStokesContract
    {fields : IndependentFields period hPeriod}
    {regularity : LLStrongAnalyticRegularityContract period hPeriod
      (finiteSmoothThroatGeneratingFrame period hPeriod)}
    (hIPP : CanonicalThroatScalarWeightedLLFrameFluxGlobalIPP period hPeriod
      fields regularity) :
    CanonicalThroatGeometricStokesContract period hPeriod fields regularity where
  finiteLedger := canonicalThroatEmptyFiniteBoundaryLedger period hPeriod
  geometricBoundaryFlux := fun _ => 0
  continuumIntegrationByParts := by
    intro direction
    simpa using hIPP direction
  boundaryFlux_eq_finiteLedgerResidual := by
    intro direction
    exact (canonicalThroatFiniteBoundaryLedgerResidual_eq_zero period hPeriod
      (canonicalThroatEmptyFiniteBoundaryLedger period hPeriod) direction).symm

/-- Conversely, every geometric Stokes contract implies the same zero-boundary
IPP lemma because its finite-ledger boundary flux is already proved zero. -/
theorem canonicalThroatGeometricStokesContract_toGlobalZeroBoundaryIPP
    {fields : IndependentFields period hPeriod}
    {regularity : LLStrongAnalyticRegularityContract period hPeriod
      (finiteSmoothThroatGeneratingFrame period hPeriod)}
    (contract : CanonicalThroatGeometricStokesContract period hPeriod
      fields regularity) :
    CanonicalThroatScalarWeightedLLFrameFluxGlobalIPP period hPeriod
      fields regularity := by
  intro direction
  rw [contract.continuumIntegrationByParts direction,
    contract.geometricBoundaryFlux_eq_zero period hPeriod direction, add_zero]

/-- Exact logical reduction: the two-field geometric interface is inhabited
if and only if the one genuinely missing global IPP lemma holds. -/
theorem canonicalThroat_geometricStokesContract_nonempty_iff_globalIPP
    (fields : IndependentFields period hPeriod)
    (regularity : LLStrongAnalyticRegularityContract period hPeriod
      (finiteSmoothThroatGeneratingFrame period hPeriod)) :
    Nonempty (CanonicalThroatGeometricStokesContract period hPeriod
        fields regularity) ↔
      CanonicalThroatScalarWeightedLLFrameFluxGlobalIPP period hPeriod
        fields regularity := by
  constructor
  · rintro ⟨contract⟩
    exact canonicalThroatGeometricStokesContract_toGlobalZeroBoundaryIPP
      period hPeriod contract
  · intro hIPP
    exact ⟨hIPP.toGeometricStokesContract period hPeriod⟩

/-- Once the unique analytic lemma is supplied, weak and strong canonical LL
equations are equivalent without any additional boundary hypothesis. -/
theorem canonicalThroat_globalIPP_weak_iff_strong
    (fields : IndependentFields period hPeriod)
    (regularity : LLStrongAnalyticRegularityContract period hPeriod
      (finiteSmoothThroatGeneratingFrame period hPeriod))
    (hIPP : CanonicalThroatScalarWeightedLLFrameFluxGlobalIPP period hPeriod
      fields regularity) :
    SatisfiesPTSymmetricWeakDifferentialLLEquation period hPeriod
        (finiteSmoothThroatGeneratingFrame period hPeriod) fields
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) ↔
      SatisfiesPTSymmetricStrongDifferentialLLEquation period hPeriod
        (finiteSmoothThroatGeneratingFrame period hPeriod) regularity fields :=
  canonicalThroat_geometricStokes_weak_iff_strong period hPeriod fields
    regularity (hIPP.toGeometricStokesContract period hPeriod)

end

end P0EFTJanusMappingTorusCanonicalThroatGlobalZeroBoundaryIPP4D
end JanusFormal
