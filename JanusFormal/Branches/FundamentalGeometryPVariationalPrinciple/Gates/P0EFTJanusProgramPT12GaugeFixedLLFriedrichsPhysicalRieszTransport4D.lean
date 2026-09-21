import Mathlib.Analysis.InnerProductSpace.Adjoint
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12PreferredActualZeroMatterLLSevenPhysicalRieszDecomposition4D

/-!
# Bounded physical Riesz transport to the spectral--LL Friedrichs completion

The completed actual graph has canonical bounded matter and LL value maps.
Their product has an adjoint from the matter--LL Friedrichs carrier back to
the actual graph.  Pulling the existing seven-block Riesz operator through
this adjoint gives a bounded physical residual on the Friedrichs carrier and,
after the canonical spectral matter restriction, on the full spectral--LL
space.  Adding it to the unbounded Friedrichs family preserves its domain.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalRieszTransport4D

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 1200000
noncomputable section

open Set MeasureTheory
open scoped ENNReal lp Manifold ContDiff InnerProductSpace LinearPMap
open P0EFTJanusCircleQuillenMetricFlatConnection
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusImmersionFiberAlgebra
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalFullLLGraphRiesz4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalPairedAbelianBRSTGaugeFermion4D
open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateAAbelianExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateAFaithfulFredholmSum4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalLocalHessianBridge4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateACanonicalStablePerturbation4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorBismutFreedFamily4D
open P0EFTJanusProgramPGlobalGaugeFixedSpectralHessianFredholm4D
open P0EFTJanusProgramPGlobalGaugeFixedLLFriedrichsHessianFredholm4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsCommonDomainFamily4D
open P0EFTJanusProgramPT12LLCanonicalH1ClosedDomain4D
open P0EFTJanusProgramPT12LLCanonicalH1L2Bridge4D

attribute [local instance]
  programPGlobalGaugeFixedSpectralHessianHilbertRealInnerProductSpace
  programPPrimitiveSpinCMatterHilbertRealInnerProductSpace
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2DiffeomorphismNormedAddCommGroup
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2DiffeomorphismInnerProductSpace
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2AbelianInnerProductSpace
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2MatterInnerProductSpace
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2LLInnerProductSpace
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkNormedAddCommGroup
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkInnerProductSpace
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkCompleteSpace

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance spectralMatterRestrictionModeDecidableEq
    (iota : Type*) [DecidableEq iota] :
    DecidableEq (ProgramPGlobalGaugeFixedSpectralHessianMode iota) :=
  Classical.decEq _

/-- The matter--LL Hilbert carrier seen by the physical residual. -/
abbrev ProgramPT12GaugeFixedLLFriedrichsMatterLLHilbert
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :=
  WithLp 2
    (ProgramPPrimitiveSpinCMatterHilbert ×
      CanonicalLLL2 period hPeriod analysis)

/-- Restriction of the global spectral coefficient family to its matter
summand.  It is a contraction. -/
private theorem spectralMatterRestriction_finset_sum_le
    {iota : Type*} [DecidableEq iota]
    (state : ProgramPGlobalGaugeFixedSpectralHessianHilbert iota)
    (modes : Finset ProgramPPrimitiveSpinCMatterMode) :
    ∑ mode ∈ modes, ‖state (.inr mode)‖ ^ (2 : ENNReal).toReal ≤
      ‖state‖ ^ (2 : ENNReal).toReal := by
  simpa using
    (lp.sum_rpow_le_norm_rpow (by norm_num) state
      (modes.map ⟨Sum.inr, Sum.inr_injective⟩))

def programPT12GaugeFixedSpectralMatterRestriction
    {iota : Type*} [DecidableEq iota] :
    ProgramPGlobalGaugeFixedSpectralHessianHilbert iota →L[Real]
      ProgramPPrimitiveSpinCMatterHilbert :=
  LinearMap.mkContinuous
    { toFun := fun state =>
        ⟨fun mode => state (.inr mode), by
          exact memℓp_gen'
            (spectralMatterRestriction_finset_sum_le state)⟩
      map_add' := by
        intro first second
        ext mode
        rfl
      map_smul' := by
        intro scalar state
        ext mode
        rfl }
    1
    (by
      intro state
      rw [one_mul]
      exact lp.norm_le_of_forall_sum_le (by norm_num) (norm_nonneg state)
        (spectralMatterRestriction_finset_sum_le state))

@[simp]
theorem programPT12GaugeFixedSpectralMatterRestriction_apply
    {iota : Type*} [DecidableEq iota]
    (state : ProgramPGlobalGaugeFixedSpectralHessianHilbert iota)
    (mode : ProgramPPrimitiveSpinCMatterMode) :
    programPT12GaugeFixedSpectralMatterRestriction (iota := iota) state mode =
      state (.inr mode) :=
  rfl

section Physical

variable {couplings : GlobalCandidateAActionCouplings}
variable {NonNullFace NullFace : Type*}
variable [Fintype NonNullFace] [Fintype NullFace]
variable {measure : Measure (EffectiveQuotient period hPeriod)}
variable (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
variable (data : GlobalCandidateAActionData period hPeriod
  configuration.physical couplings NonNullFace NullFace)
variable (analysis : GlobalAnalysisData period hPeriod configuration.physical)
variable (chart : GlobalCandidateALocalVariationalChart period hPeriod
  couplings NonNullFace NullFace measure)
variable (sameAction : ProgramPGlobalMinimalPhysicalLocalMatterLLSameActionBridge4D
  period hPeriod configuration data analysis chart)
variable (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D
  period hPeriod configuration data analysis chart sameAction)

private abbrev ActualDiffeomorphism :=
  GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)

private abbrev ActualAbelian :=
  GlobalPairedAbelianOffShellGraphHilbert period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)

private abbrev ActualMatter :=
  ProgramPPrimitiveSpinCMatterL2GraphDomain period hPeriod
    couplings.matterMassSquared

private abbrev ActualLL :=
  GlobalFullLLGraphHilbert period hPeriod data analysis

private abbrev ActualMatterLLTail :=
  WithLp 2
    (ActualMatter (couplings := couplings) period hPeriod ×
      ActualLL period hPeriod configuration data analysis)

private abbrev ActualAbelianMatterLLTail :=
  WithLp 2
    (ActualAbelian period hPeriod configuration data ×
      ActualMatterLLTail period hPeriod configuration data analysis)

private def actualMatterGraphProjection :
    CommonAugmentedHilbert period hPeriod configuration
        data analysis →L[Real]
      ActualMatter (couplings := couplings) period hPeriod :=
  (WithLp.fstL 2 Real
      (ActualMatter (couplings := couplings) period hPeriod)
      (ActualLL period hPeriod configuration data analysis)).comp
    ((WithLp.sndL 2 Real
        (ActualAbelian period hPeriod configuration data)
        (ActualMatterLLTail period hPeriod configuration data analysis)).comp
      (WithLp.sndL 2 Real
        (ActualDiffeomorphism period hPeriod configuration data)
        (ActualAbelianMatterLLTail period hPeriod configuration data analysis)))

private def actualLLGraphProjection :
    CommonAugmentedHilbert period hPeriod configuration
        data analysis →L[Real]
      ActualLL period hPeriod configuration data analysis :=
  (WithLp.sndL 2 Real
      (ActualMatter (couplings := couplings) period hPeriod)
      (ActualLL period hPeriod configuration data analysis)).comp
    ((WithLp.sndL 2 Real
        (ActualAbelian period hPeriod configuration data)
        (ActualMatterLLTail period hPeriod configuration data analysis)).comp
      (WithLp.sndL 2 Real
        (ActualDiffeomorphism period hPeriod configuration data)
        (ActualAbelianMatterLLTail period hPeriod configuration data analysis)))

/-- Bounded matter value readout from the actual graph completion. -/
def programPT12ActualMatterReadout :
    CommonAugmentedHilbert period hPeriod configuration
        data analysis →L[Real]
      ProgramPPrimitiveSpinCMatterHilbert :=
  (programPPrimitiveSpinCMatterGraphFstRealCLM period hPeriod
      couplings.matterMassSquared).comp
    ((programPPrimitiveSpinCMatterL2GraphEquiv period hPeriod
        couplings.matterMassSquared).toContinuousLinearMap.comp
      (actualMatterGraphProjection (configuration := configuration)
        (data := data) (analysis := analysis) period hPeriod))

/-- Bounded LL value readout from the actual graph completion. -/
def programPT12ActualLLReadout :
    CommonAugmentedHilbert period hPeriod configuration
        data analysis →L[Real]
      CanonicalLLL2 period hPeriod analysis :=
  (canonicalLLH1ToFluxL2 period hPeriod analysis).comp
    ((globalCandidateAFullLLFieldProjection period hPeriod data analysis).comp
      (actualLLGraphProjection (configuration := configuration) (data := data)
        (analysis := analysis) period hPeriod))

/-- Joint bounded readout from the actual graph to the matter--LL Friedrichs
carrier. -/
def programPT12ActualToFriedrichsMatterLLReadout :
    CommonAugmentedHilbert period hPeriod configuration
        data analysis →L[Real]
      ProgramPT12GaugeFixedLLFriedrichsMatterLLHilbert period hPeriod
        analysis :=
  (WithLp.prodContinuousLinearEquiv 2 Real
      ProgramPPrimitiveSpinCMatterHilbert
      (CanonicalLLL2 period hPeriod analysis)).symm.toContinuousLinearMap.comp
    ((programPT12ActualMatterReadout (configuration := configuration)
      (data := data) (analysis := analysis) period hPeriod).prod
      (programPT12ActualLLReadout (configuration := configuration)
        (data := data) (analysis := analysis) period hPeriod))

/-- Canonical bounded transport from the matter--LL Friedrichs carrier into
the actual graph: the Hilbert adjoint of the value readout. -/
def programPT12FriedrichsMatterLLToActualTransport :
    ProgramPT12GaugeFixedLLFriedrichsMatterLLHilbert period hPeriod analysis
        →L[Real]
      CommonAugmentedHilbert period hPeriod configuration
        data analysis :=
  (programPT12ActualToFriedrichsMatterLLReadout
    (configuration := configuration) (data := data) (analysis := analysis)
      period hPeriod).adjoint

theorem programPT12FriedrichsMatterLLToActualTransport_pairing
    (source : ProgramPT12GaugeFixedLLFriedrichsMatterLLHilbert period hPeriod
      analysis)
    (actual : CommonAugmentedHilbert period hPeriod
      configuration data analysis) :
    inner Real
        (programPT12FriedrichsMatterLLToActualTransport
          (configuration := configuration) (data := data)
            (analysis := analysis) period hPeriod source)
        actual =
      inner Real source
        (programPT12ActualToFriedrichsMatterLLReadout
          (configuration := configuration) (data := data)
            (analysis := analysis) period hPeriod actual) :=
  (programPT12ActualToFriedrichsMatterLLReadout
    (configuration := configuration) (data := data) (analysis := analysis)
      period hPeriod).adjoint_inner_left actual source

/-- Pullback of the retained physical form to the matter--LL Friedrichs
carrier. -/
def programPT12FriedrichsMatterLLPhysicalForm :
    ProgramPT12GaugeFixedLLFriedrichsMatterLLHilbert period hPeriod analysis
        →L[Real]
      ProgramPT12GaugeFixedLLFriedrichsMatterLLHilbert period hPeriod analysis
        →L[Real] Real :=
  physical.form.bilinearComp
    (programPT12FriedrichsMatterLLToActualTransport
      (configuration := configuration) (data := data) (analysis := analysis)
        period hPeriod)
    (programPT12FriedrichsMatterLLToActualTransport
      (configuration := configuration) (data := data) (analysis := analysis)
        period hPeriod)

/-- Bounded Riesz representative of the pulled physical residual. -/
def programPT12FriedrichsMatterLLPhysicalRieszOperator :
    ProgramPT12GaugeFixedLLFriedrichsMatterLLHilbert period hPeriod analysis
        →L[Real]
      ProgramPT12GaugeFixedLLFriedrichsMatterLLHilbert period hPeriod
        analysis :=
  (programPT12ActualToFriedrichsMatterLLReadout
      (configuration := configuration) (data := data) (analysis := analysis)
        period hPeriod).comp
    ((globalCandidateASevenPhysicalCommonRieszOperator period hPeriod
        configuration data analysis chart sameAction physical).comp
      (programPT12FriedrichsMatterLLToActualTransport
        (configuration := configuration) (data := data) (analysis := analysis)
          period hPeriod))

theorem programPT12FriedrichsMatterLLPhysicalRieszOperator_pairing
    (first second : ProgramPT12GaugeFixedLLFriedrichsMatterLLHilbert period
      hPeriod analysis) :
    inner Real
        (programPT12FriedrichsMatterLLPhysicalRieszOperator
          (configuration := configuration) (data := data)
            (analysis := analysis) (chart := chart) (sameAction := sameAction)
              (physical := physical) period hPeriod first)
        second =
      programPT12FriedrichsMatterLLPhysicalForm
        (configuration := configuration) (data := data) (analysis := analysis)
          (chart := chart) (sameAction := sameAction) (physical := physical)
            period hPeriod first second := by
  let readout := programPT12ActualToFriedrichsMatterLLReadout
    (configuration := configuration) (data := data) (analysis := analysis)
      period hPeriod
  let transport := programPT12FriedrichsMatterLLToActualTransport
    (configuration := configuration) (data := data) (analysis := analysis)
      period hPeriod
  let perturbation := globalCandidateASevenPhysicalCommonRieszOperator
    period hPeriod configuration data analysis chart sameAction physical
  change inner Real (readout (perturbation (transport first))) second =
    physical.form (transport first) (transport second)
  calc
    _ = inner Real (perturbation (transport first)) (transport second) := by
      exact (readout.adjoint_inner_right
        (perturbation (transport first)) second).symm
    _ = physical.form (transport first) (transport second) := by
      simpa [perturbation] using
        (globalCandidateASevenPhysicalCommonRieszOperator_pairing period
          hPeriod configuration data analysis chart sameAction physical
          (transport first) (transport second))

theorem programPT12FriedrichsMatterLLPhysicalForm_symmetric
    (first second : ProgramPT12GaugeFixedLLFriedrichsMatterLLHilbert period
      hPeriod analysis) :
    programPT12FriedrichsMatterLLPhysicalForm
        (configuration := configuration) (data := data) (analysis := analysis)
          (chart := chart) (sameAction := sameAction) (physical := physical)
            period hPeriod first second =
      programPT12FriedrichsMatterLLPhysicalForm
        (configuration := configuration) (data := data) (analysis := analysis)
          (chart := chart) (sameAction := sameAction) (physical := physical)
            period hPeriod second first := by
  exact physical.symmetric _ _

/-- Projection of the full spectral--LL Friedrichs carrier onto its matter
and LL values. -/
def programPT12GaugeFixedLLFriedrichsMatterLLReadout
    {iota : Type*} [DecidableEq iota] :
    ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert period hPeriod iota
        analysis →L[Real]
      ProgramPT12GaugeFixedLLFriedrichsMatterLLHilbert period hPeriod
        analysis :=
  (WithLp.prodContinuousLinearEquiv 2 Real
      ProgramPPrimitiveSpinCMatterHilbert
      (CanonicalLLL2 period hPeriod analysis)).symm.toContinuousLinearMap.comp
    (((programPT12GaugeFixedSpectralMatterRestriction (iota := iota)).comp
        (WithLp.fstL 2 Real
          (ProgramPGlobalGaugeFixedSpectralHessianHilbert iota)
          (CanonicalLLL2 period hPeriod analysis))).prod
      (WithLp.sndL 2 Real
        (ProgramPGlobalGaugeFixedSpectralHessianHilbert iota)
        (CanonicalLLL2 period hPeriod analysis)))

/-- Actual-graph value represented by a full spectral--LL Friedrichs state. -/
def programPT12GaugeFixedLLFriedrichsToActualTransport
    {iota : Type*} [DecidableEq iota] :
    ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert period hPeriod iota
        analysis →L[Real]
      CommonAugmentedHilbert period hPeriod configuration
        data analysis :=
  (programPT12FriedrichsMatterLLToActualTransport
      (configuration := configuration) (data := data) (analysis := analysis)
        period hPeriod).comp
    (programPT12GaugeFixedLLFriedrichsMatterLLReadout
      (configuration := configuration) (iota := iota) period hPeriod analysis)

/-- Pulled physical form on the full spectral--LL Friedrichs carrier. -/
def programPT12GaugeFixedLLFriedrichsPhysicalResidualForm
    {iota : Type*} [DecidableEq iota] :
    ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert period hPeriod iota
        analysis →L[Real]
      ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert period hPeriod iota
        analysis →L[Real] Real :=
  physical.form.bilinearComp
    (programPT12GaugeFixedLLFriedrichsToActualTransport
      (configuration := configuration) (data := data) (analysis := analysis)
        (iota := iota) period hPeriod)
    (programPT12GaugeFixedLLFriedrichsToActualTransport
      (configuration := configuration) (data := data) (analysis := analysis)
        (iota := iota) period hPeriod)

/-- Bounded physical perturbation on the full Friedrichs carrier. -/
def programPT12GaugeFixedLLFriedrichsPhysicalPerturbation
    {iota : Type*} [DecidableEq iota] :
    ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert period hPeriod iota
        analysis →L[Real]
      ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert period hPeriod iota
        analysis :=
  (programPT12GaugeFixedLLFriedrichsMatterLLReadout
      (configuration := configuration) (iota := iota) period hPeriod
        analysis).adjoint.comp
    ((programPT12FriedrichsMatterLLPhysicalRieszOperator
        (configuration := configuration) (data := data) (analysis := analysis)
          (chart := chart) (sameAction := sameAction) (physical := physical)
            period hPeriod).comp
      (programPT12GaugeFixedLLFriedrichsMatterLLReadout
        (configuration := configuration) (iota := iota) period hPeriod
          analysis))

theorem programPT12GaugeFixedLLFriedrichsPhysicalPerturbation_pairing
    {iota : Type*} [DecidableEq iota]
    (first second : ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert period
      hPeriod iota analysis) :
    inner Real
        (programPT12GaugeFixedLLFriedrichsPhysicalPerturbation
          (configuration := configuration) (data := data)
            (analysis := analysis) (chart := chart)
              (sameAction := sameAction) (physical := physical)
                (iota := iota) period hPeriod first)
        second =
      programPT12GaugeFixedLLFriedrichsPhysicalResidualForm
        (configuration := configuration) (data := data) (analysis := analysis)
          (chart := chart) (sameAction := sameAction) (physical := physical)
            (iota := iota) period hPeriod first second := by
  let readout := programPT12GaugeFixedLLFriedrichsMatterLLReadout
    (configuration := configuration) (iota := iota) period hPeriod analysis
  let residual := programPT12FriedrichsMatterLLPhysicalRieszOperator
    (configuration := configuration) (data := data) (analysis := analysis)
      (chart := chart) (sameAction := sameAction) (physical := physical)
        period hPeriod
  change inner Real (readout.adjoint (residual (readout first))) second =
    programPT12FriedrichsMatterLLPhysicalForm
      (configuration := configuration) (data := data) (analysis := analysis)
        (chart := chart) (sameAction := sameAction) (physical := physical)
          period hPeriod (readout first) (readout second)
  calc
    _ = inner Real (residual (readout first)) (readout second) :=
      readout.adjoint_inner_left second (residual (readout first))
    _ = _ :=
      programPT12FriedrichsMatterLLPhysicalRieszOperator_pairing
        (configuration := configuration) (data := data) (analysis := analysis)
          (chart := chart) (sameAction := sameAction) (physical := physical)
            period hPeriod (readout first) (readout second)

theorem programPT12GaugeFixedLLFriedrichsPhysicalResidualForm_symmetric
    {iota : Type*} [DecidableEq iota]
    (first second : ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert period
      hPeriod iota analysis) :
    programPT12GaugeFixedLLFriedrichsPhysicalResidualForm
        (configuration := configuration) (data := data) (analysis := analysis)
          (chart := chart) (sameAction := sameAction) (physical := physical)
            (iota := iota) period hPeriod first second =
      programPT12GaugeFixedLLFriedrichsPhysicalResidualForm
        (configuration := configuration) (data := data) (analysis := analysis)
          (chart := chart) (sameAction := sameAction) (physical := physical)
            (iota := iota) period hPeriod second first := by
  exact physical.symmetric _ _

/-- The spectral--LL Friedrichs family plus the transported physical
residual. -/
def programPT12GaugeFixedLLFriedrichsFullPhysicalOperator
    {iota : Type*} [DecidableEq iota]
    (covector : iota → TangentVector3)
    (parameter : Real) :
    ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert period hPeriod iota
        analysis →ₗ.[Real]
      ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert period hPeriod iota
        analysis :=
  (programPT12GaugeFixedLLFriedrichsPhysicalPerturbation
      (configuration := configuration) (data := data) (analysis := analysis)
        (chart := chart) (sameAction := sameAction) (physical := physical)
          (iota := iota) period hPeriod).toLinearMap +ᵥ
    programPT12GaugeFixedLLFriedrichsD11Operator period hPeriod covector
      couplings.matterMassSquared analysis parameter

@[simp]
theorem programPT12GaugeFixedLLFriedrichsFullPhysicalOperator_domain
    {iota : Type*} [DecidableEq iota]
    (covector : iota → TangentVector3)
    (parameter : Real) :
    (programPT12GaugeFixedLLFriedrichsFullPhysicalOperator
      (configuration := configuration) (data := data) (analysis := analysis)
        (chart := chart) (sameAction := sameAction) (physical := physical)
          period hPeriod covector parameter).domain =
      ProgramPT12GaugeFixedLLFriedrichsD11CommonDomain period hPeriod
        covector couplings.matterMassSquared analysis := by
  rw [programPT12GaugeFixedLLFriedrichsFullPhysicalOperator,
    LinearPMap.vadd_domain,
    programPT12GaugeFixedLLFriedrichsD11Operator_domain]

theorem programPT12GaugeFixedLLFriedrichsFullPhysicalOperator_pairing
    {iota : Type*} [DecidableEq iota]
    (covector : iota → TangentVector3)
    (parameter : Real)
    (state : ProgramPT12GaugeFixedLLFriedrichsD11CommonDomain period hPeriod
      covector couplings.matterMassSquared analysis)
    (test : ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert period hPeriod
      iota analysis) :
    inner Real
        (programPT12GaugeFixedLLFriedrichsFullPhysicalOperator
          (configuration := configuration) (data := data)
            (analysis := analysis) (chart := chart)
              (sameAction := sameAction) (physical := physical)
                period hPeriod covector parameter state)
        test =
      inner Real
          (programPT12GaugeFixedLLFriedrichsD11Operator period hPeriod
            covector couplings.matterMassSquared analysis parameter state)
          test +
        programPT12GaugeFixedLLFriedrichsPhysicalResidualForm
          (configuration := configuration) (data := data)
            (analysis := analysis) (chart := chart)
              (sameAction := sameAction) (physical := physical)
                (iota := iota) period hPeriod state.1 test := by
  change inner Real
      (programPT12GaugeFixedLLFriedrichsPhysicalPerturbation
          (configuration := configuration) (data := data)
            (analysis := analysis) (chart := chart)
              (sameAction := sameAction) (physical := physical)
                (iota := iota) period hPeriod state.1 +
        programPT12GaugeFixedLLFriedrichsD11Operator period hPeriod covector
          couplings.matterMassSquared analysis parameter state)
      test = _
  rw [inner_add_left,
    programPT12GaugeFixedLLFriedrichsPhysicalPerturbation_pairing]
  exact add_comm _ _

/-- Positive gate: the existing physical residual has a bounded Riesz
transport to the full Friedrichs carrier and its sum with every D11 fibre
retains the common domain. -/
theorem programPT12GaugeFixedLLFriedrichsFullPhysicalOperator_gate
    {iota : Type*} [DecidableEq iota]
    (covector : iota → TangentVector3)
    (parameter : Real) :
    (programPT12GaugeFixedLLFriedrichsFullPhysicalOperator
        (configuration := configuration) (data := data) (analysis := analysis)
          (chart := chart) (sameAction := sameAction) (physical := physical)
            period hPeriod covector parameter).domain =
        ProgramPT12GaugeFixedLLFriedrichsD11CommonDomain period hPeriod
          covector couplings.matterMassSquared analysis ∧
      ∀ (state : ProgramPT12GaugeFixedLLFriedrichsD11CommonDomain period
          hPeriod covector couplings.matterMassSquared analysis)
        (test : ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert period
          hPeriod iota analysis),
        inner Real
            (programPT12GaugeFixedLLFriedrichsFullPhysicalOperator
              (configuration := configuration) (data := data)
                (analysis := analysis) (chart := chart)
                  (sameAction := sameAction) (physical := physical)
                    period hPeriod covector parameter state)
            test =
          inner Real
              (programPT12GaugeFixedLLFriedrichsD11Operator period hPeriod
                covector couplings.matterMassSquared analysis parameter state)
              test +
            programPT12GaugeFixedLLFriedrichsPhysicalResidualForm
              (configuration := configuration) (data := data)
                (analysis := analysis) (chart := chart)
                  (sameAction := sameAction) (physical := physical)
                    (iota := iota) period hPeriod state.1 test := by
  exact ⟨
    programPT12GaugeFixedLLFriedrichsFullPhysicalOperator_domain
      (configuration := configuration) (data := data) (analysis := analysis)
        (chart := chart) (sameAction := sameAction) (physical := physical)
          period hPeriod covector parameter,
    programPT12GaugeFixedLLFriedrichsFullPhysicalOperator_pairing
      (configuration := configuration) (data := data) (analysis := analysis)
        (chart := chart) (sameAction := sameAction) (physical := physical)
          period hPeriod covector parameter⟩

end Physical
end
end P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalRieszTransport4D
end JanusFormal
