import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Topology.Algebra.Module.Basic
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalBulkReferenceNuclearRegulator4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSpinCMatterContinuumHeatRegulator4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD10ContinuumHeatOperatorNuclear4D

/-!
# Global nuclear reference regulator

The completed ambient space below contains exactly the finite bulk `L²`
slots, the two-sector signed SpinC coefficient space, the multiplicity-aware
D10 coefficient space, and the genuine LL flux `L²` space attached to the
global analysis datum.

A single basis-dependent separable-Hilbert regulator acts on this full
product.  It is compact, injective, and has an absolutely summable rank-one
expansion at every positive time.  The certificate also records the existing
physical matter and D10 heat expansions and the compact bulk Dirichlet lift.

This is a reference regularization theorem.  In particular, no equality with
the global physical Hessian, nor with its heat operator, is asserted here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalReferenceNuclearRegulator4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

noncomputable section

open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalBulkDirichletCompactRegulator4D
open P0EFTJanusProgramPGlobalBulkReferenceNuclearRegulator4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPLL2EllipticNuclearHeatRegulator4D
open P0EFTJanusProgramPLL2SeparableReferenceNuclearRegulator4D
open P0EFTJanusProgramPSpinCMatterContinuumHeatRegulator4D
open P0EFTJanusProgramPPrimitiveSpinCGeometricSignedFredholm4D
open P0EFTJanusProgramPCommonGeometricDomain4D
open P0EFTJanusProgramPD10ContinuumHeatRegulator4D
open P0EFTJanusProgramPD10ContinuumHeatOperatorNuclear4D
open scoped ENNReal lp

variable (period : Real) (hPeriod : period ≠ 0)

private theorem separableSpace_of_countable_complex_hilbertBasis
    {Index H : Type*} [Countable Index]
    [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [CompleteSpace H]
    (basis : HilbertBasis Index Complex H) :
    TopologicalSpace.SeparableSpace H := by
  have hRange :
      TopologicalSpace.IsSeparable (Set.range basis) :=
    (Set.countable_range basis).isSeparable
  have hSpan :
      TopologicalSpace.IsSeparable
        (Submodule.span Complex (Set.range basis) : Set H) :=
    hRange.span
  have hDense :
      Dense (Submodule.span Complex (Set.range basis) : Set H) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr basis.dense_span
  exact hDense.isSeparable_iff.mp hSpan

/-- One exact ambient Hilbert space for all globally completed sectors used by
the reference regularization. -/
abbrev ProgramPGlobalReferenceHilbert4D
    {configuration : GlobalFieldConfiguration period hPeriod}
    (data : GlobalAnalysisData period hPeriod configuration) :=
  WithLp 2
    (GlobalBulkHilbertL2 period hPeriod ×
      WithLp 2
        (ProgramPSpinCMatterHeatHilbert4D ×
          WithLp 2
            (ProgramPD10HeatHilbert4D
                (d10SpectralData period hPeriod
                  configuration.d10Completion) ×
              LLFluxL2 period hPeriod
                (data.llH1Data period hPeriod))))

local instance globalBulkHilbertL2InnerProductSpace :
    InnerProductSpace Real (GlobalBulkHilbertL2 period hPeriod) :=
  PiLp.innerProductSpace fun _ : GlobalBulkSobolevSlot period hPeriod =>
    CanonicalPhysicalBulkL2 period hPeriod

local instance globalBulkHilbertL2Separable :
    TopologicalSpace.SeparableSpace
      (GlobalBulkHilbertL2 period hPeriod) :=
  globalBulkHilbertL2SeparableSpace period hPeriod

local instance spinCMatterRealInnerProductSpace :
    InnerProductSpace Real ProgramPSpinCMatterHeatHilbert4D :=
  InnerProductSpace.complexToReal

local instance d10ModeCountable
    (spectralData : ProductThroatSpectralData) :
    Countable (ProgramPD10Mode4D spectralData) :=
  Countable.of_equiv (ProgramPD10HeatCoordinate4D spectralData)
    (programPD10HeatCoordinateEquiv spectralData).symm

local instance spinCMatterModeCountable :
    Countable
      (Sector × PrimitiveSpinCGeometricSignedMode) :=
  Countable.of_equiv
    (Sector × PrimitiveSpinCSignedHeatCoordinate4D
      (1 : Real) (by norm_num))
    ((Equiv.refl Sector).prodCongr
      (primitiveSpinCGeometricSignedHeatCoordinateEquiv
        (1 : Real) (by norm_num))).symm

local instance spinCMatterSeparable :
    TopologicalSpace.SeparableSpace
      ProgramPSpinCMatterHeatHilbert4D :=
  separableSpace_of_countable_complex_hilbertBasis
    programPSpinCMatterHeatBasis

local instance d10RealInnerProductSpace
    (spectralData : ProductThroatSpectralData) :
    InnerProductSpace Real
      (ProgramPD10HeatHilbert4D spectralData) :=
  InnerProductSpace.complexToReal

local instance d10Separable
    (spectralData : ProductThroatSpectralData) :
    TopologicalSpace.SeparableSpace
      (ProgramPD10HeatHilbert4D spectralData) :=
  separableSpace_of_countable_complex_hilbertBasis
    (programPD10HeatBasis spectralData)

local instance globalLLFluxL2Separable
    {configuration : GlobalFieldConfiguration period hPeriod}
    (data : GlobalAnalysisData period hPeriod configuration) :
    TopologicalSpace.SeparableSpace
      (LLFluxL2 period hPeriod (data.llH1Data period hPeriod)) :=
  llFluxL2SeparableSpace period hPeriod
    (data.llH1Data period hPeriod)

/-- Public separability witness for the exact global ambient product. -/
@[reducible] def programPGlobalReferenceHilbertSeparableSpace
    {configuration : GlobalFieldConfiguration period hPeriod}
    (data : GlobalAnalysisData period hPeriod configuration) :
    TopologicalSpace.SeparableSpace
      (ProgramPGlobalReferenceHilbert4D period hPeriod data) := by
  infer_instance

local instance programPGlobalReferenceHilbertSeparable
    {configuration : GlobalFieldConfiguration period hPeriod}
    (data : GlobalAnalysisData period hPeriod configuration) :
    TopologicalSpace.SeparableSpace
      (ProgramPGlobalReferenceHilbert4D period hPeriod data) :=
  programPGlobalReferenceHilbertSeparableSpace period hPeriod data

/-- The single unconditional nuclear reference regulator on every completed
global sector. -/
def programPGlobalReferenceOperator
    {configuration : GlobalFieldConfiguration period hPeriod}
    (data : GlobalAnalysisData period hPeriod configuration)
    (time : HeatTime) :
    ProgramPGlobalReferenceHilbert4D period hPeriod data →L[Real]
      ProgramPGlobalReferenceHilbert4D period hPeriod data :=
  referenceOperator
    (H := ProgramPGlobalReferenceHilbert4D period hPeriod data) time

theorem programPGlobalReferenceOperator_isCompact
    {configuration : GlobalFieldConfiguration period hPeriod}
    (data : GlobalAnalysisData period hPeriod configuration)
    (time : HeatTime) :
    IsCompactOperator
      (programPGlobalReferenceOperator period hPeriod data time) := by
  exact referenceOperator_isCompact
    (H := ProgramPGlobalReferenceHilbert4D period hPeriod data) time

theorem programPGlobalReferenceOperator_injective
    {configuration : GlobalFieldConfiguration period hPeriod}
    (data : GlobalAnalysisData period hPeriod configuration)
    (time : HeatTime) :
    Function.Injective
      (programPGlobalReferenceOperator period hPeriod data time) := by
  exact referenceOperator_injective
    (H := ProgramPGlobalReferenceHilbert4D period hPeriod data) time

/-- Terminal aggregate certificate.  The common operator is the reference
operator above; the matter and D10 fields retain their independently proved
physical heat certificates without identifying either one with the full
global Hessian. -/
structure ProgramPGlobalReferenceNuclearCertificate4D
    {configuration : GlobalFieldConfiguration period hPeriod}
    (data : GlobalAnalysisData period hPeriod configuration)
    (massSquared : Real) (time : HeatTime) where
  globalNuclear :
    ReferenceNuclearCertificate
      (H := ProgramPGlobalReferenceHilbert4D period hPeriod data) time
  globalCompact :
    IsCompactOperator
      (programPGlobalReferenceOperator period hPeriod data time)
  globalInjective :
    Function.Injective
      (programPGlobalReferenceOperator period hPeriod data time)
  bulkReference :
    ReferenceNuclearCertificate
      (H := GlobalBulkHilbertL2 period hPeriod) time
  bulkBoundaryCompact :
    IsCompactOperator
      (globalBulkDirichletRegulator period hPeriod)
  bulkBoundaryLiftTraceZero :
    ∀ source : GlobalBulkHilbertL2 period hPeriod,
      globalBulkHilbertH1Trace period hPeriod
          ((globalBulkDirichletRegulatorDomainLift
              period hPeriod source :
                GlobalBulkDirichletHilbertH1 period hPeriod) :
            GlobalBulkHilbertH1 period hPeriod) =
        0
  matterHeat :
    ProgramPSpinCMatterHeatNuclearCertificate4D
      period hPeriod massSquared time
  d10Heat :
    ProgramPD10HeatNuclearCertificate4D
      (d10SpectralData period hPeriod configuration.d10Completion) time
  llReference :
    ReferenceNuclearCertificate
      (H := LLFluxL2 period hPeriod
        (data.llH1Data period hPeriod)) time
  llReferenceCompact :
    IsCompactOperator
      (referenceOperator
        (H := LLFluxL2 period hPeriod
          (data.llH1Data period hPeriod)) time)
  llReferenceInjective :
    Function.Injective
      (referenceOperator
        (H := LLFluxL2 period hPeriod
          (data.llH1Data period hPeriod)) time)

def programPGlobalReferenceNuclearCertificate4D
    {configuration : GlobalFieldConfiguration period hPeriod}
    (data : GlobalAnalysisData period hPeriod configuration)
    (massSquared : Real) (time : HeatTime) :
    ProgramPGlobalReferenceNuclearCertificate4D
      period hPeriod data massSquared time where
  globalNuclear :=
    referenceNuclearCertificate
      (H := ProgramPGlobalReferenceHilbert4D period hPeriod data) time
  globalCompact :=
    programPGlobalReferenceOperator_isCompact
      period hPeriod data time
  globalInjective :=
    programPGlobalReferenceOperator_injective
      period hPeriod data time
  bulkReference :=
    referenceNuclearCertificate
      (H := GlobalBulkHilbertL2 period hPeriod) time
  bulkBoundaryCompact :=
    globalBulkDirichletRegulator_isCompact period hPeriod
  bulkBoundaryLiftTraceZero :=
    globalBulkDirichletRegulatorDomainLift_trace_zero period hPeriod
  matterHeat :=
    programPSpinCMatterHeatNuclearCertificate4D
      period hPeriod massSquared time
  d10Heat :=
    programPD10HeatNuclearCertificate4D
      (d10SpectralData period hPeriod configuration.d10Completion) time
  llReference :=
    referenceNuclearCertificate
      (H := LLFluxL2 period hPeriod
        (data.llH1Data period hPeriod)) time
  llReferenceCompact :=
    referenceOperator_isCompact
      (H := LLFluxL2 period hPeriod
        (data.llH1Data period hPeriod)) time
  llReferenceInjective :=
    referenceOperator_injective
      (H := LLFluxL2 period hPeriod
        (data.llH1Data period hPeriod)) time

/-- Closure gate for the common reference regularization.  Its conclusion is
deliberately independent of any global Hessian-identification statement. -/
theorem programP_global_reference_nuclear_regulator_gate
    {configuration : GlobalFieldConfiguration period hPeriod}
    (data : GlobalAnalysisData period hPeriod configuration)
    (massSquared : Real) (time : HeatTime) :
    Nonempty
      (ProgramPGlobalReferenceNuclearCertificate4D
        period hPeriod data massSquared time) :=
  ⟨programPGlobalReferenceNuclearCertificate4D
    period hPeriod data massSquared time⟩

end
end P0EFTJanusProgramPGlobalReferenceNuclearRegulator4D
end JanusFormal
