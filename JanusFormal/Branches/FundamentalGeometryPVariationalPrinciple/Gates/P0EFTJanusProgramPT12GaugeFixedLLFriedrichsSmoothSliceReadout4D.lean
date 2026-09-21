import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalRieszTransport4D

/-!
# Smooth matter--LL slice readout for the Friedrichs transport

The actual graph and Friedrichs smooth-core realizations have the same
matter and LL value readout.  Consequently, the adjoint transport pairing on
this slice is the `L²` pairing of those readouts.  No isometry of the graph
inclusions is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT12GaugeFixedLLFriedrichsSmoothSliceReadout4D

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 1200000
noncomputable section

open Set MeasureTheory
open scoped ENNReal lp Manifold ContDiff InnerProductSpace LinearPMap
open P0EFTJanusImmersionFiberAlgebra
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalFullLLGraphRiesz4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateADiagonalCovariantHessianResidualBridge4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalGaugeFixedSpectralHessianFredholm4D
open P0EFTJanusProgramPGlobalGaugeFixedSpectralFiniteCore4D
open P0EFTJanusProgramPGlobalGaugeFixedLLFriedrichsHessianFredholm4D
open P0EFTJanusProgramPGlobalGaugeFixedLLFriedrichsSmoothCore4D
open P0EFTJanusProgramPGlobalGaugeFixedMatterLLSmoothSlice4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusMappingTorusPTSymmetricLLH1RieszOperator4D
open P0EFTJanusMappingTorusLLH1SmoothEmbeddingKernel4D
open P0EFTJanusProgramPT12LLCanonicalH1L2Bridge4D
open P0EFTJanusProgramPT12LLCanonicalH1ClosedDomain4D
open P0EFTJanusProgramPT12LLCanonicalFriedrichsRealization4D
open P0EFTJanusProgramPLL2EllipticNuclearHeatRegulator4D
open P0EFTJanusProgramPT12MinimalPhysicalMatterLLReducedSliceToChart4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalRieszTransport4D

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

variable {couplings : GlobalCandidateAActionCouplings}
variable {NonNullFace NullFace : Type*}
variable [Fintype NonNullFace] [Fintype NullFace]
variable (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
variable (data : GlobalCandidateAActionData period hPeriod
  configuration.physical couplings NonNullFace NullFace)
variable (analysis : GlobalAnalysisData period hPeriod configuration.physical)

/-- The reduced smooth matter--LL slice inside the actual graph Hilbert
space. -/
def programPT12ActualMatterLLSmoothSliceEmbedding :
    ProgramPT12MinimalPhysicalMatterLLReducedSlice period hPeriod
        configuration analysis →ₗ[Real]
      CommonAugmentedHilbert period hPeriod configuration data analysis :=
  (P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalExtendedBulkL2SmoothEmbedding
      period hPeriod (globalCandidateAMetricBySector period hPeriod data)
        couplings.matterMassSquared data analysis).comp
    (programPT12MinimalPhysicalMatterLLReducedSliceCore period hPeriod
      configuration analysis)

/-- The same reduced smooth slice inside the ambient Friedrichs Hilbert
carrier, after forgetting maximal-domain membership. -/
def programPT12FriedrichsMatterLLSmoothSliceEmbedding
    {iota : Type*} [DecidableEq iota]
    (covector : iota → TangentVector3) :
    ProgramPT12MinimalPhysicalMatterLLReducedSlice period hPeriod
        configuration analysis →ₗ[Real]
      ProgramPGlobalGaugeFixedLLFriedrichsHessianHilbert period hPeriod iota
        analysis :=
  (programPGlobalGaugeFixedLLFriedrichsHessianOperator period hPeriod covector
      couplings.matterMassSquared analysis).domain.subtype.comp
    ((programPGlobalGaugeFixedLLFriedrichsSmoothCoreMap period hPeriod
        covector couplings.matterMassSquared analysis).comp
      (programPGlobalGaugeFixedMatterLLSmoothSliceMap period hPeriod
        (iota := iota) analysis))

/-- The actual graph realization of the smooth matter--LL slice has the
expected matter and LL `L²` values. -/
@[simp]
theorem programPT12ActualToFriedrichsMatterLLReadout_on_smoothSlice
    (direction : ProgramPT12MinimalPhysicalMatterLLReducedSlice period
      hPeriod configuration analysis) :
    programPT12ActualToFriedrichsMatterLLReadout
        (configuration := configuration) (data := data) (analysis := analysis)
          period hPeriod
        (programPT12ActualMatterLLSmoothSliceEmbedding period hPeriod
          configuration data analysis direction) =
      WithLp.toLp 2
        (programPPrimitiveSpinCMatterFiniteHilbertEmbedding direction.1,
          llH1SmoothToFluxL2 period hPeriod
            (analysis.llH1Data period hPeriod) direction.2) := by
  classical
  unfold programPT12ActualMatterLLSmoothSliceEmbedding
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · ext mode
    change
      (programPPrimitiveSpinCMatterGraphFinite period hPeriod
          couplings.matterMassSquared direction.1).1.1 mode =
        programPPrimitiveSpinCMatterFiniteHilbertEmbedding direction.1 mode
    rw [programPPrimitiveSpinCMatterGraphFinite_fst]
  · change
      canonicalLLH1ToFluxL2 period hPeriod analysis
          (llH1SmoothEmbedding period hPeriod
            (analysis.llH1Data period hPeriod) direction.2) =
        llH1SmoothToFluxL2 period hPeriod
          (analysis.llH1Data period hPeriod) direction.2
    exact canonicalLLH1ToFluxL2_agrees_on_smooth period hPeriod analysis
      direction.2

/-- The Friedrichs smooth-core realization of the same slice has the same
explicit matter and LL `L²` values. -/
@[simp]
theorem programPT12GaugeFixedLLFriedrichsMatterLLReadout_on_smoothSlice
    {iota : Type*} [DecidableEq iota]
    (covector : iota → TangentVector3)
    (direction : ProgramPT12MinimalPhysicalMatterLLReducedSlice period
      hPeriod configuration analysis) :
    programPT12GaugeFixedLLFriedrichsMatterLLReadout
        (configuration := configuration) (iota := iota) period hPeriod analysis
        (programPT12FriedrichsMatterLLSmoothSliceEmbedding
          (couplings := couplings) period hPeriod configuration analysis
            covector direction) =
      WithLp.toLp 2
        (programPPrimitiveSpinCMatterFiniteHilbertEmbedding direction.1,
          llH1SmoothToFluxL2 period hPeriod
            (analysis.llH1Data period hPeriod) direction.2) := by
  classical
  unfold programPT12FriedrichsMatterLLSmoothSliceEmbedding
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · ext mode
    change
      ((programPGlobalGaugeFixedSpectralFiniteCore period hPeriod covector
          couplings.matterMassSquared
          (programPGlobalGaugeFixedMatterFiniteCoefficientsEmbedding
            (iota := iota) direction.1) :
            (programPGlobalGaugeFixedSpectralHessianRealMaximalOperator
              period hPeriod covector couplings.matterMassSquared).domain) :
        ProgramPGlobalGaugeFixedSpectralHessianHilbert iota) (.inr mode) =
      programPPrimitiveSpinCMatterFiniteHilbertEmbedding direction.1 mode
    rw [programPGlobalGaugeFixedSpectralFiniteCore_value_apply,
      programPGlobalGaugeFixedMatterFiniteCoefficientsEmbedding_matter,
      programPPrimitiveSpinCMatterFiniteHilbertEmbedding_apply]
  · change
      ((canonicalLLFriedrichsSmoothDomainElement period hPeriod analysis
          direction.2 :
            (canonicalLLFriedrichsJacobi period hPeriod analysis).domain) :
        CanonicalLLL2 period hPeriod analysis) =
      llH1SmoothToFluxL2 period hPeriod
        (analysis.llH1Data period hPeriod) direction.2
    exact canonicalLLFriedrichsSmoothDomainElement_value period hPeriod
      analysis direction.2

/-- The two completed realizations agree after applying their value
readouts on the smooth matter--LL slice. -/
theorem programPT12MatterLLReadouts_agree_on_smoothSlice
    {iota : Type*} [DecidableEq iota]
    (covector : iota → TangentVector3)
    (direction : ProgramPT12MinimalPhysicalMatterLLReducedSlice period
      hPeriod configuration analysis) :
    programPT12ActualToFriedrichsMatterLLReadout
        (configuration := configuration) (data := data) (analysis := analysis)
          period hPeriod
        (programPT12ActualMatterLLSmoothSliceEmbedding period hPeriod
          configuration data analysis direction) =
      programPT12GaugeFixedLLFriedrichsMatterLLReadout
        (configuration := configuration) (iota := iota) period hPeriod analysis
        (programPT12FriedrichsMatterLLSmoothSliceEmbedding
          (couplings := couplings) period hPeriod configuration analysis
            covector direction) := by
  rw [programPT12ActualToFriedrichsMatterLLReadout_on_smoothSlice,
    programPT12GaugeFixedLLFriedrichsMatterLLReadout_on_smoothSlice]

/-- Pairing the adjoint transport of a Friedrichs smooth-slice state against
an actual smooth-slice state gives exactly the `L²` pairing of their value
readouts. -/
theorem programPT12GaugeFixedLLFriedrichsToActualTransport_smoothSlice_pairing
    {iota : Type*} [DecidableEq iota]
    (covector : iota → TangentVector3)
    (first second : ProgramPT12MinimalPhysicalMatterLLReducedSlice period
      hPeriod configuration analysis) :
    inner Real
        (programPT12GaugeFixedLLFriedrichsToActualTransport
          (configuration := configuration) (data := data) (analysis := analysis)
            (iota := iota) period hPeriod
            (programPT12FriedrichsMatterLLSmoothSliceEmbedding
              (couplings := couplings) period hPeriod configuration analysis
                covector first))
        (programPT12ActualMatterLLSmoothSliceEmbedding period hPeriod
          configuration data analysis second) =
      inner Real
        (programPT12GaugeFixedLLFriedrichsMatterLLReadout
          (configuration := configuration) (iota := iota) period hPeriod
            analysis
            (programPT12FriedrichsMatterLLSmoothSliceEmbedding
              (couplings := couplings) period hPeriod configuration analysis
                covector first))
        (programPT12GaugeFixedLLFriedrichsMatterLLReadout
          (configuration := configuration) (iota := iota) period hPeriod
            analysis
            (programPT12FriedrichsMatterLLSmoothSliceEmbedding
              (couplings := couplings) period hPeriod configuration analysis
                covector second)) := by
  rw [programPT12GaugeFixedLLFriedrichsToActualTransport]
  rw [ContinuousLinearMap.comp_apply]
  rw [programPT12FriedrichsMatterLLToActualTransport_pairing]
  rw [programPT12MatterLLReadouts_agree_on_smoothSlice period hPeriod
    configuration data analysis covector second]

end
end P0EFTJanusProgramPT12GaugeFixedLLFriedrichsSmoothSliceReadout4D
end JanusFormal
