import Mathlib.Analysis.InnerProductSpace.Positive
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicH1CoerciveVariationalClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalAnalysisDomain4D

/-!
# Compact regulator on the common bulk Dirichlet domain

The scalar Rellich inclusion is assembled over every finite bulk slot and
restricted to the common homogeneous Dirichlet domain.  Finite `ℓ²`
renormings provide the Hilbert structures needed for the adjoint.  The
resulting Gram response is compact, positive, self-adjoint, and its adjoint
lift lies in the original common Dirichlet domain.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalBulkDirichletCompactRegulator4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

noncomputable section

open scoped InnerProduct ENNReal lp
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1HilbertRenorming4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarSmoothRellichTransport4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicH1CoerciveVariationalClosure4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Finite product of the canonical physical bulk `L²` spaces. -/
abbrev GlobalBulkL2 :=
  GlobalBulkSobolevSlot period hPeriod →
    CanonicalPhysicalBulkL2 period hPeriod

/-- Hilbert `ℓ²` renorming of all global bulk `H¹` slots. -/
abbrev GlobalBulkHilbertLpH1 :=
  PiLp 2 fun _ : GlobalBulkSobolevSlot period hPeriod =>
    CanonicalPhysicalScalarHilbertH1 period hPeriod

/-- Hilbert `ℓ²` renorming of all global bulk `L²` slots. -/
abbrev GlobalBulkHilbertL2 :=
  PiLp 2 fun _ : GlobalBulkSobolevSlot period hPeriod =>
    CanonicalPhysicalBulkL2 period hPeriod

local instance physicalHilbertH1CompleteSpace :
    CompleteSpace (CanonicalPhysicalScalarHilbertH1 period hPeriod) :=
  canonicalPhysicalScalarHilbertH1CompleteSpace period hPeriod

local instance globalBulkHilbertLpH1InnerProductSpace :
    InnerProductSpace Real (GlobalBulkHilbertLpH1 period hPeriod) :=
  PiLp.innerProductSpace fun _ : GlobalBulkSobolevSlot period hPeriod =>
    CanonicalPhysicalScalarHilbertH1 period hPeriod

local instance globalBulkHilbertL2InnerProductSpace :
    InnerProductSpace Real (GlobalBulkHilbertL2 period hPeriod) :=
  PiLp.innerProductSpace fun _ : GlobalBulkSobolevSlot period hPeriod =>
    CanonicalPhysicalBulkL2 period hPeriod

/-- The finite `ℓ²` bulk `H¹` product is canonically equivalent to the
existing finite product used by the global analysis domain. -/
def globalBulkHilbertLpH1Equiv :
    GlobalBulkHilbertLpH1 period hPeriod ≃L[Real]
      GlobalBulkHilbertH1 period hPeriod :=
  PiLp.continuousLinearEquiv 2 Real
    (fun _ : GlobalBulkSobolevSlot period hPeriod =>
      CanonicalPhysicalScalarHilbertH1 period hPeriod)

/-- The finite `ℓ²` bulk `L²` product is canonically equivalent to the
ordinary finite product. -/
def globalBulkHilbertL2Equiv :
    GlobalBulkHilbertL2 period hPeriod ≃L[Real]
      GlobalBulkL2 period hPeriod :=
  PiLp.continuousLinearEquiv 2 Real
    (fun _ : GlobalBulkSobolevSlot period hPeriod =>
      CanonicalPhysicalBulkL2 period hPeriod)

private theorem canonicalPhysicalScalarHilbertH1ToBulkL2_isCompact :
    IsCompactOperator
      (canonicalPhysicalScalarHilbertH1ToBulkL2 period hPeriod) := by
  change IsCompactOperator
    ((canonicalPhysicalScalarH1ToBulkL2 period hPeriod).comp
      (canonicalPhysicalScalarHilbertH1EquivGraph
        period hPeriod).toContinuousLinearMap)
  exact
    (canonicalPhysicalScalarRellich period hPeriod).comp_clm
      (canonicalPhysicalScalarHilbertH1EquivGraph
        period hPeriod).toContinuousLinearMap

/-- One compact diagonal summand of the global bulk inclusion. -/
private def globalBulkHilbertH1ToBulkL2Slot
    (slot : GlobalBulkSobolevSlot period hPeriod) :
    GlobalBulkHilbertH1 period hPeriod →L[Real]
      GlobalBulkL2 period hPeriod :=
  (ContinuousLinearMap.single Real
      (fun _ : GlobalBulkSobolevSlot period hPeriod =>
        CanonicalPhysicalBulkL2 period hPeriod) slot).comp
    ((canonicalPhysicalScalarHilbertH1ToBulkL2 period hPeriod).comp
      (ContinuousLinearMap.proj slot))

private theorem globalBulkHilbertH1ToBulkL2Slot_isCompact
    (slot : GlobalBulkSobolevSlot period hPeriod) :
    IsCompactOperator
      (globalBulkHilbertH1ToBulkL2Slot period hPeriod slot) := by
  let projection :
      GlobalBulkHilbertH1 period hPeriod →L[Real]
        CanonicalPhysicalScalarHilbertH1 period hPeriod :=
    ContinuousLinearMap.proj slot
  let insertion :
      CanonicalPhysicalBulkL2 period hPeriod →L[Real]
        GlobalBulkL2 period hPeriod :=
    ContinuousLinearMap.single Real
      (fun _ : GlobalBulkSobolevSlot period hPeriod =>
        CanonicalPhysicalBulkL2 period hPeriod) slot
  have hPre :
      IsCompactOperator
        ((canonicalPhysicalScalarHilbertH1ToBulkL2
          period hPeriod).comp projection) :=
    (canonicalPhysicalScalarHilbertH1ToBulkL2_isCompact
      period hPeriod).comp_clm projection
  have hPost :
      IsCompactOperator
        (insertion.comp
          ((canonicalPhysicalScalarHilbertH1ToBulkL2
            period hPeriod).comp projection)) :=
    hPre.clm_comp insertion
  simpa only [globalBulkHilbertH1ToBulkL2Slot, projection, insertion]
    using hPost

/-- Coordinatewise canonical `H¹ → L²` inclusion on every bulk slot. -/
def globalBulkHilbertH1ToBulkL2 :
    GlobalBulkHilbertH1 period hPeriod →L[Real]
      GlobalBulkL2 period hPeriod :=
  ∑ slot : GlobalBulkSobolevSlot period hPeriod,
    globalBulkHilbertH1ToBulkL2Slot period hPeriod slot

/-- The finite-slot global bulk inclusion is compact. -/
theorem globalBulkHilbertH1ToBulkL2_isCompact :
    IsCompactOperator
      (globalBulkHilbertH1ToBulkL2 period hPeriod) := by
  classical
  change
    (∑ slot : GlobalBulkSobolevSlot period hPeriod,
      globalBulkHilbertH1ToBulkL2Slot period hPeriod slot) ∈
      compactOperator (RingHom.id Real)
        (GlobalBulkHilbertH1 period hPeriod)
        (GlobalBulkL2 period hPeriod)
  exact Submodule.sum_mem _ fun slot _ =>
    globalBulkHilbertH1ToBulkL2Slot_isCompact period hPeriod slot

/-- Hilbertized trace obtained by transporting the existing global trace. -/
def globalBulkHilbertLpH1Trace :
    GlobalBulkHilbertLpH1 period hPeriod →L[Real]
      GlobalBulkThroatL2 period hPeriod :=
  (globalBulkHilbertH1Trace period hPeriod).comp
    (globalBulkHilbertLpH1Equiv period hPeriod).toContinuousLinearMap

/-- Common homogeneous Dirichlet domain inside the finite Hilbert product. -/
abbrev GlobalBulkDirichletHilbertLpH1 :=
  (globalBulkHilbertLpH1Trace period hPeriod).ker

local instance globalBulkDirichletHilbertLpH1CompleteSpace :
    CompleteSpace (GlobalBulkDirichletHilbertLpH1 period hPeriod) :=
  (globalBulkHilbertLpH1Trace period hPeriod).isClosed_ker.completeSpace_coe

local instance globalBulkDirichletHilbertLpH1InnerProductSpace :
    InnerProductSpace Real
      (GlobalBulkDirichletHilbertLpH1 period hPeriod) :=
  Submodule.innerProductSpace
    (globalBulkHilbertLpH1Trace period hPeriod).ker

/-- Continuous identification of the Hilbertized Dirichlet domain with the
original common Dirichlet domain. -/
def globalBulkDirichletHilbertLpH1ToDomain :
    GlobalBulkDirichletHilbertLpH1 period hPeriod →L[Real]
      GlobalBulkDirichletHilbertH1 period hPeriod :=
  (((globalBulkHilbertLpH1Equiv period hPeriod).toContinuousLinearMap.comp
      (GlobalBulkDirichletHilbertLpH1 period hPeriod).subtypeL).codRestrict
    (GlobalBulkDirichletHilbertH1 period hPeriod)
    (by
      intro field
      exact field.property))

/-- Coordinatewise `H¹ → L²` inclusion between the finite Hilbert products. -/
def globalBulkHilbertLpH1ToBulkHilbertL2 :
    GlobalBulkHilbertLpH1 period hPeriod →L[Real]
      GlobalBulkHilbertL2 period hPeriod :=
  (globalBulkHilbertL2Equiv period hPeriod).symm.toContinuousLinearMap.comp
    ((globalBulkHilbertH1ToBulkL2 period hPeriod).comp
      (globalBulkHilbertLpH1Equiv period hPeriod).toContinuousLinearMap)

theorem globalBulkHilbertLpH1ToBulkHilbertL2_isCompact :
    IsCompactOperator
      (globalBulkHilbertLpH1ToBulkHilbertL2 period hPeriod) := by
  exact
    ((globalBulkHilbertH1ToBulkL2_isCompact period hPeriod).comp_clm
      (globalBulkHilbertLpH1Equiv
        period hPeriod).toContinuousLinearMap).clm_comp
      (globalBulkHilbertL2Equiv
        period hPeriod).symm.toContinuousLinearMap

/-- Compact inclusion restricted to the common homogeneous Dirichlet
domain. -/
def globalBulkDirichletHilbertLpH1ToBulkHilbertL2 :
    GlobalBulkDirichletHilbertLpH1 period hPeriod →L[Real]
      GlobalBulkHilbertL2 period hPeriod :=
  (globalBulkHilbertLpH1ToBulkHilbertL2 period hPeriod).comp
    (GlobalBulkDirichletHilbertLpH1 period hPeriod).subtypeL

theorem globalBulkDirichletHilbertLpH1ToBulkHilbertL2_isCompact :
    IsCompactOperator
      (globalBulkDirichletHilbertLpH1ToBulkHilbertL2
        period hPeriod) := by
  exact
    (globalBulkHilbertLpH1ToBulkHilbertL2_isCompact
      period hPeriod).comp_clm
      (GlobalBulkDirichletHilbertLpH1 period hPeriod).subtypeL

/-- Canonical adjoint lift of a Hilbertized bulk source into the common
Dirichlet domain. -/
def globalBulkDirichletRegulatorLift :
    GlobalBulkHilbertL2 period hPeriod →L[Real]
      GlobalBulkDirichletHilbertLpH1 period hPeriod :=
  (@ContinuousLinearMap.adjoint Real
    (GlobalBulkDirichletHilbertLpH1 period hPeriod)
    (GlobalBulkHilbertL2 period hPeriod)
    _ _ _
    (globalBulkDirichletHilbertLpH1InnerProductSpace period hPeriod)
    (globalBulkHilbertL2InnerProductSpace period hPeriod)
    (globalBulkDirichletHilbertLpH1CompleteSpace period hPeriod)
    inferInstance)
    (globalBulkDirichletHilbertLpH1ToBulkHilbertL2 period hPeriod)

/-- The regulator lift viewed in the original global analysis domain. -/
def globalBulkDirichletRegulatorDomainLift :
    GlobalBulkHilbertL2 period hPeriod →L[Real]
      GlobalBulkDirichletHilbertH1 period hPeriod :=
  (globalBulkDirichletHilbertLpH1ToDomain period hPeriod).comp
    (globalBulkDirichletRegulatorLift period hPeriod)

theorem globalBulkDirichletRegulatorDomainLift_trace_zero
    (source : GlobalBulkHilbertL2 period hPeriod) :
    globalBulkHilbertH1Trace period hPeriod
        ((globalBulkDirichletRegulatorDomainLift
          period hPeriod source :
            GlobalBulkDirichletHilbertH1 period hPeriod) :
          GlobalBulkHilbertH1 period hPeriod) =
      0 :=
  (globalBulkDirichletRegulatorDomainLift
    period hPeriod source).property

/-- Positive compact Gram regulator `J J†` on the common bulk `L²`. -/
def globalBulkDirichletRegulator :
    GlobalBulkHilbertL2 period hPeriod →L[Real]
      GlobalBulkHilbertL2 period hPeriod :=
  (globalBulkDirichletHilbertLpH1ToBulkHilbertL2
    period hPeriod).comp
    (globalBulkDirichletRegulatorLift period hPeriod)

theorem globalBulkDirichletRegulator_isCompact :
    IsCompactOperator
      (globalBulkDirichletRegulator period hPeriod) := by
  exact
    (globalBulkDirichletHilbertLpH1ToBulkHilbertL2_isCompact
      period hPeriod).comp_clm
      (globalBulkDirichletRegulatorLift period hPeriod)

theorem globalBulkDirichletRegulator_isPositive :
    (globalBulkDirichletRegulator period hPeriod).IsPositive := by
  exact @ContinuousLinearMap.isPositive_self_comp_adjoint Real
    (GlobalBulkDirichletHilbertLpH1 period hPeriod)
    (GlobalBulkHilbertL2 period hPeriod)
    _ _ _
    (globalBulkDirichletHilbertLpH1InnerProductSpace period hPeriod)
    (globalBulkHilbertL2InnerProductSpace period hPeriod)
    (globalBulkDirichletHilbertLpH1CompleteSpace period hPeriod)
    inferInstance
    (globalBulkDirichletHilbertLpH1ToBulkHilbertL2 period hPeriod)

theorem globalBulkDirichletRegulator_isSelfAdjoint :
    IsSelfAdjoint
      (globalBulkDirichletRegulator period hPeriod) :=
  (globalBulkDirichletRegulator_isPositive period hPeriod).isSelfAdjoint

end

end P0EFTJanusProgramPGlobalBulkDirichletCompactRegulator4D
end JanusFormal
