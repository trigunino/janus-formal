import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12GaugeFixedLLFriedrichsMatterLLReducedFormMatch4D

/-!
# Exact reduced transport defect on the T12 matter--LL slice

The missing reduced-coordinate equality is equivalent to the adjoint-readout
defect lying in the closed minimal-physical null space.  Equivalently, the
actual value readout preserves the relevant mixed inner products against the
physical orthogonal complement.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT12GaugeFixedLLFriedrichsReducedTransportDefect4D

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 1200000
set_option maxRecDepth 10000

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff InnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusImmersionFiberAlgebra
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalLocalHessianBridge4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedHilbert4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCoreToChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedAugmentedBRSTAction4D
open P0EFTJanusProgramPGlobalGaugeFixedSpectralHessianFredholm4D
open P0EFTJanusProgramPGlobalGaugeFixedLLFriedrichsHessianFredholm4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPT12MinimalPhysicalMatterLLReducedSliceToChart4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsPhysicalRieszTransport4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsSmoothSliceReadout4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsMatterLLReducedFormMatch4D

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

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance : IsManifold coverModelWithCorners ω
    (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance : BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

section

variable {couplings : GlobalCandidateAActionCouplings}
variable {NonNullFace NullFace : Type*}
variable [Fintype NonNullFace] [Fintype NullFace]
variable {measure : Measure (EffectiveQuotient period hPeriod)}
variable (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
variable (data : GlobalCandidateAActionData period hPeriod
  configuration.physical couplings NonNullFace NullFace)
variable (analysis : GlobalAnalysisData period hPeriod configuration.physical)

/-- Equality after minimal physical reduction is exactly membership of the
transport defect in the closed null space. -/
theorem programPT12GaugeFixedLLFriedrichsMatterLL_reduction_eq_iff_transportDefect_mem_closedNull
    {iota : Type*} [DecidableEq iota]
    (covector : iota → TangentVector3)
    (direction : ProgramPT12MinimalPhysicalMatterLLReducedSlice period
      hPeriod configuration analysis) :
    globalCandidateAMinimalPhysicalHilbertReduction period hPeriod
        configuration data analysis
        (programPT12GaugeFixedLLFriedrichsToActualTransport
          (configuration := configuration) (data := data)
            (analysis := analysis) (iota := iota) period hPeriod
            (programPT12FriedrichsMatterLLSmoothSliceEmbedding
              (couplings := couplings) period hPeriod configuration analysis
                covector direction)) =
      globalCandidateAMinimalPhysicalHilbertReduction period hPeriod
        configuration data analysis
        (programPT12ActualMatterLLSmoothSliceEmbedding period hPeriod
          configuration data analysis direction) ↔
    programPT12GaugeFixedLLFriedrichsToActualTransport
          (configuration := configuration) (data := data)
            (analysis := analysis) (iota := iota) period hPeriod
            (programPT12FriedrichsMatterLLSmoothSliceEmbedding
              (couplings := couplings) period hPeriod configuration analysis
                covector direction) -
        programPT12ActualMatterLLSmoothSliceEmbedding period hPeriod
          configuration data analysis direction ∈
      globalCandidateAMinimalPhysicalClosedNullHilbertSubmodule period hPeriod
        configuration data analysis := by
  let reduction := globalCandidateAMinimalPhysicalHilbertReduction period
    hPeriod configuration data analysis
  let transported := programPT12GaugeFixedLLFriedrichsToActualTransport
    (configuration := configuration) (data := data) (analysis := analysis)
      (iota := iota) period hPeriod
      (programPT12FriedrichsMatterLLSmoothSliceEmbedding
        (couplings := couplings) period hPeriod configuration analysis
          covector direction)
  let actual := programPT12ActualMatterLLSmoothSliceEmbedding period hPeriod
    configuration data analysis direction
  change reduction transported = reduction actual ↔
    transported - actual ∈
      globalCandidateAMinimalPhysicalClosedNullHilbertSubmodule period hPeriod
        configuration data analysis
  constructor
  · intro hEquality
    rw [← globalCandidateAMinimalPhysicalHilbertReduction_ker period hPeriod
      configuration data analysis]
    exact
      (LinearMap.sub_mem_ker_iff (f := reduction.toLinearMap)).mpr hEquality
  · intro hDefect
    apply (LinearMap.sub_mem_ker_iff (f := reduction.toLinearMap)).mp
    rw [globalCandidateAMinimalPhysicalHilbertReduction_ker period hPeriod
      configuration data analysis]
    exact hDefect

/-- The closed-null defect criterion is exactly preservation of the mixed
inner product against every reduced physical test. -/
theorem programPT12GaugeFixedLLFriedrichsMatterLL_transportDefect_mem_closedNull_iff_pairing
    {iota : Type*} [DecidableEq iota]
    (covector : iota → TangentVector3)
    (direction : ProgramPT12MinimalPhysicalMatterLLReducedSlice period
      hPeriod configuration analysis) :
    programPT12GaugeFixedLLFriedrichsToActualTransport
          (configuration := configuration) (data := data)
            (analysis := analysis) (iota := iota) period hPeriod
            (programPT12FriedrichsMatterLLSmoothSliceEmbedding
              (couplings := couplings) period hPeriod configuration analysis
                covector direction) -
        programPT12ActualMatterLLSmoothSliceEmbedding period hPeriod
          configuration data analysis direction ∈
      globalCandidateAMinimalPhysicalClosedNullHilbertSubmodule period hPeriod
        configuration data analysis ↔
    ∀ test :
        (globalCandidateAMinimalPhysicalClosedNullHilbertSubmodule period
          hPeriod configuration data analysis)ᗮ,
      inner Real
          (programPT12ActualToFriedrichsMatterLLReadout
            (configuration := configuration) (data := data)
              (analysis := analysis) period hPeriod
              (programPT12ActualMatterLLSmoothSliceEmbedding period hPeriod
                configuration data analysis direction))
          (programPT12ActualToFriedrichsMatterLLReadout
            (configuration := configuration) (data := data)
              (analysis := analysis) period hPeriod test) =
        inner Real
          (programPT12ActualMatterLLSmoothSliceEmbedding period hPeriod
            configuration data analysis direction) test := by
  let nullSpace :=
    globalCandidateAMinimalPhysicalClosedNullHilbertSubmodule period hPeriod
      configuration data analysis
  let actual := programPT12ActualMatterLLSmoothSliceEmbedding period hPeriod
    configuration data analysis direction
  let friedrichs := programPT12FriedrichsMatterLLSmoothSliceEmbedding
    (couplings := couplings) period hPeriod configuration analysis covector
      direction
  let transported := programPT12GaugeFixedLLFriedrichsToActualTransport
    (configuration := configuration) (data := data) (analysis := analysis)
      (iota := iota) period hPeriod friedrichs
  let readout := programPT12ActualToFriedrichsMatterLLReadout
    (configuration := configuration) (data := data) (analysis := analysis)
      period hPeriod
  have hTransportPairing : ∀ test,
      inner Real transported test = inner Real (readout actual) (readout test) := by
    intro test
    change inner Real
        (programPT12GaugeFixedLLFriedrichsToActualTransport
          (configuration := configuration) (data := data)
            (analysis := analysis) (iota := iota) period hPeriod friedrichs)
        test = _
    rw [programPT12GaugeFixedLLFriedrichsToActualTransport,
      ContinuousLinearMap.comp_apply,
      programPT12FriedrichsMatterLLToActualTransport_pairing]
    rw [← programPT12MatterLLReadouts_agree_on_smoothSlice period hPeriod
      configuration data analysis covector direction]
  have hNullClosed : IsClosed
      (nullSpace : Set
        (CommonAugmentedHilbert period hPeriod configuration data analysis)) :=
    Submodule.isClosed_topologicalClosure _
  constructor
  · intro hDefect test
    have hZero : inner Real (transported - actual) test = 0 :=
      (nullSpace.mem_orthogonal test).mp test.property
        (transported - actual) hDefect
    rw [inner_sub_left, hTransportPairing test] at hZero
    exact sub_eq_zero.mp hZero
  · intro hPairing
    have hDoubleOrthogonal : transported - actual ∈ nullSpaceᗮᗮ := by
      rw [(nullSpaceᗮ).mem_orthogonal']
      intro test hTest
      let reducedTest : nullSpaceᗮ := ⟨test, hTest⟩
      rw [inner_sub_left, hTransportPairing test,
        hPairing reducedTest, sub_self]
    rw [nullSpace.orthogonal_orthogonal_eq_closure,
      hNullClosed.submodule_topologicalClosure_eq] at hDoubleOrthogonal
    exact hDoubleOrthogonal

variable (chartData : ProgramPGlobalMinimalPhysicalActionChartData4D period
  hPeriod (measure := measure) configuration data analysis)
variable (reducedChart : ProgramPGlobalMinimalPhysicalReducedHilbertChart4D
  period hPeriod configuration data analysis chartData)

private abbrev CanonicalPhysical :=
  globalCandidateAGaugeFixedAugmentedPhysicalExtension period hPeriod
    configuration data analysis chartData reducedChart

/-- Closed-null control of the two transport defects gives the canonical
physical-form match on the smooth matter--LL slice. -/
theorem programPT12GaugeFixedLLFriedrichsMatterLL_physicalForm_eq_actual_of_transportDefects_mem_closedNull
    {iota : Type*} [DecidableEq iota]
    (covector : iota → TangentVector3)
    (first second : ProgramPT12MinimalPhysicalMatterLLReducedSlice period
      hPeriod configuration analysis)
    (hFirst :
      programPT12GaugeFixedLLFriedrichsToActualTransport
            (configuration := configuration) (data := data)
              (analysis := analysis) (iota := iota) period hPeriod
              (programPT12FriedrichsMatterLLSmoothSliceEmbedding
                (couplings := couplings) period hPeriod configuration analysis
                  covector first) -
          programPT12ActualMatterLLSmoothSliceEmbedding period hPeriod
            configuration data analysis first ∈
        globalCandidateAMinimalPhysicalClosedNullHilbertSubmodule period hPeriod
          configuration data analysis)
    (hSecond :
      programPT12GaugeFixedLLFriedrichsToActualTransport
            (configuration := configuration) (data := data)
              (analysis := analysis) (iota := iota) period hPeriod
              (programPT12FriedrichsMatterLLSmoothSliceEmbedding
                (couplings := couplings) period hPeriod configuration analysis
                  covector second) -
          programPT12ActualMatterLLSmoothSliceEmbedding period hPeriod
            configuration data analysis second ∈
        globalCandidateAMinimalPhysicalClosedNullHilbertSubmodule period hPeriod
          configuration data analysis) :
    (CanonicalPhysical period hPeriod configuration data analysis chartData
      reducedChart).form
        (programPT12GaugeFixedLLFriedrichsToActualTransport
          (configuration := configuration) (data := data)
            (analysis := analysis) (iota := iota) period hPeriod
            (programPT12FriedrichsMatterLLSmoothSliceEmbedding
              (couplings := couplings) period hPeriod configuration analysis
                covector first))
        (programPT12GaugeFixedLLFriedrichsToActualTransport
          (configuration := configuration) (data := data)
            (analysis := analysis) (iota := iota) period hPeriod
            (programPT12FriedrichsMatterLLSmoothSliceEmbedding
              (couplings := couplings) period hPeriod configuration analysis
                covector second)) =
      (CanonicalPhysical period hPeriod configuration data analysis chartData
        reducedChart).form
        (programPT12ActualMatterLLSmoothSliceEmbedding period hPeriod
          configuration data analysis first)
        (programPT12ActualMatterLLSmoothSliceEmbedding period hPeriod
          configuration data analysis second) := by
  apply
    programPT12GaugeFixedLLFriedrichsMatterLL_physicalForm_eq_actual_of_reductions_eq
      period hPeriod configuration data analysis chartData reducedChart
        covector first second
  · exact
      (programPT12GaugeFixedLLFriedrichsMatterLL_reduction_eq_iff_transportDefect_mem_closedNull
        period hPeriod configuration data analysis covector first).2 hFirst
  · exact
      (programPT12GaugeFixedLLFriedrichsMatterLL_reduction_eq_iff_transportDefect_mem_closedNull
        period hPeriod configuration data analysis covector second).2 hSecond

end
end
end P0EFTJanusProgramPT12GaugeFixedLLFriedrichsReducedTransportDefect4D
end JanusFormal
