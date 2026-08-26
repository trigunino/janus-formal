import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANonSpinCBulkGlobalTangentBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateASpinCMatterGlobalTangentBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkD10GlobalTangentBridge4D

/-!
# Full Candidate-A bulk, SpinC and D10 global-tangent bridge

The physical non-SpinC bulk core, finite primitive SpinC coefficients and the
separate D10 Hilbert coordinate occupy disjoint slots of `GlobalFieldTangent`.
The same source has an injective zero-nonminimal realization in the existing
diagonal bulk plus D10 spine, without any additional coordinate.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAFullBulkSpinCD10GlobalTangentBridge4D

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 1200000
noncomputable section

open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusMappingTorusPTSymmetricLLH1RieszOperator4D
open P0EFTJanusProgramPCommonGeometricDomain4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalGaugeTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateABulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D
open P0EFTJanusProgramPGlobalFullLLGraphRiesz4D
open P0EFTJanusProgramPGlobalPairedAbelianBRSTGaugeFermion4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPGlobalCandidateANonSpinCBulkGlobalTangentBridge4D
open P0EFTJanusProgramPGlobalCandidateASpinCMatterGlobalTangentBridge4D
open P0EFTJanusProgramPGlobalAnalyticSpine4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkD10SpineL2Bridge4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Faithful source containing every bulk physical coordinate exactly once. -/
abbrev GlobalCandidateAFullBulkSpinCD10Core
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :=
  GlobalCandidateANonSpinCPhysicalBulkSmoothCore period hPeriod analysis ×
    (ProgramPPrimitiveSpinCMatterFiniteCoefficients ×
      ProgramPD10ModeHilbert4D
        (d10SpectralData period hPeriod configuration.d10Completion))

/-! ## Exact graph-spine realization -/

/-- The physical source as a zero-nonminimal diagonal bulk core with its D10
coordinate retained separately. -/
def globalCandidateAFullBulkSpinCD10SpineCoreLinearMap
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalCandidateAFullBulkSpinCD10Core period hPeriod analysis →ₗ[Real]
      GlobalCandidateADiagonalExtendedBulkD10SpineCore4D period hPeriod data
        analysis where
  toFun core :=
    ((({ metricPerturbation := core.1.1
         nonminimal := 0 },
       { potential := core.1.2.1
         nonminimal := 0 }),
      (core.2.1, core.1.2.2)),
     core.2.2)
  map_add' first second := by
    apply Prod.ext
    · apply Prod.ext
      · apply Prod.ext
        · apply GlobalCandidateADiagonalDiffeomorphismBRSTState.ext
          · rfl
          · change (0 : GlobalDiffeomorphismNonminimalFields
                period hPeriod) = 0 + 0
            simp
        · apply GlobalPairedAbelianBRSTState.ext
          · rfl
          · change (0 : Sector → GlobalAbelianNonminimalFields
                period hPeriod) = 0 + 0
            simp
      · rfl
    · rfl
  map_smul' scalar core := by
    apply Prod.ext
    · apply Prod.ext
      · apply Prod.ext
        · apply GlobalCandidateADiagonalDiffeomorphismBRSTState.ext
          · rfl
          · change (0 : GlobalDiffeomorphismNonminimalFields
                period hPeriod) = scalar • 0
            simp
        · apply GlobalPairedAbelianBRSTState.ext
          · rfl
          · change (0 : Sector → GlobalAbelianNonminimalFields
                period hPeriod) = scalar • 0
            simp
      · rfl
    · rfl

@[simp]
theorem globalCandidateAFullBulkSpinCD10SpineCore_metric
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (core : GlobalCandidateAFullBulkSpinCD10Core period hPeriod analysis) :
    (globalCandidateAFullBulkSpinCD10SpineCoreLinearMap period hPeriod data
      analysis core).1.1.1.metricPerturbation = core.1.1 :=
  rfl

@[simp]
theorem globalCandidateAFullBulkSpinCD10SpineCore_potential
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (core : GlobalCandidateAFullBulkSpinCD10Core period hPeriod analysis) :
    (globalCandidateAFullBulkSpinCD10SpineCoreLinearMap period hPeriod data
      analysis core).1.1.2.potential = core.1.2.1 :=
  rfl

@[simp]
theorem globalCandidateAFullBulkSpinCD10SpineCore_spinC
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (core : GlobalCandidateAFullBulkSpinCD10Core period hPeriod analysis) :
    (globalCandidateAFullBulkSpinCD10SpineCoreLinearMap period hPeriod data
      analysis core).1.2.1 = core.2.1 :=
  rfl

@[simp]
theorem globalCandidateAFullBulkSpinCD10SpineCore_ll
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (core : GlobalCandidateAFullBulkSpinCD10Core period hPeriod analysis) :
    (globalCandidateAFullBulkSpinCD10SpineCoreLinearMap period hPeriod data
      analysis core).1.2.2 = core.1.2.2 :=
  rfl

@[simp]
theorem globalCandidateAFullBulkSpinCD10SpineCore_d10
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (core : GlobalCandidateAFullBulkSpinCD10Core period hPeriod analysis) :
    (globalCandidateAFullBulkSpinCD10SpineCoreLinearMap period hPeriod data
      analysis core).2 = core.2.2 :=
  rfl

theorem globalCandidateAFullBulkSpinCD10SpineCore_injective
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    Function.Injective
      (globalCandidateAFullBulkSpinCD10SpineCoreLinearMap period hPeriod data
        analysis) := by
  intro first second hEqual
  have hMetric := congrArg
    (fun state : GlobalCandidateADiagonalExtendedBulkD10SpineCore4D
        period hPeriod data analysis => state.1.1.1.metricPerturbation) hEqual
  have hPotential := congrArg
    (fun state : GlobalCandidateADiagonalExtendedBulkD10SpineCore4D
        period hPeriod data analysis => state.1.1.2.potential) hEqual
  have hSpinC := congrArg
    (fun state : GlobalCandidateADiagonalExtendedBulkD10SpineCore4D
        period hPeriod data analysis => state.1.2.1) hEqual
  have hLL := congrArg
    (fun state : GlobalCandidateADiagonalExtendedBulkD10SpineCore4D
        period hPeriod data analysis => state.1.2.2) hEqual
  have hD10 := congrArg
    (fun state : GlobalCandidateADiagonalExtendedBulkD10SpineCore4D
        period hPeriod data analysis => state.2) hEqual
  exact Prod.ext (Prod.ext hMetric (Prod.ext hPotential hLL))
    (Prod.ext hSpinC hD10)

/-- Injective realization in the existing completed bulk L2 plus D10 spine. -/
def globalCandidateAFullBulkSpinCD10SpineEmbedding
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalCandidateAFullBulkSpinCD10Core period hPeriod analysis ↪
      GlobalCandidateADiagonalExtendedBulkD10SpineHilbert4D period hPeriod data
        analysis where
  toFun core :=
    globalCandidateADiagonalExtendedBulkD10SpineEmbedding period hPeriod data
      analysis
      (globalCandidateAFullBulkSpinCD10SpineCoreLinearMap period hPeriod data
        analysis core)
  inj' :=
    (globalCandidateADiagonalExtendedBulkD10SpineEmbedding_injective
      period hPeriod data analysis).comp
      (globalCandidateAFullBulkSpinCD10SpineCore_injective period hPeriod data
        analysis)

@[simp]
theorem globalCandidateAFullBulkSpinCD10SpineEmbedding_bulkGraph
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (core : GlobalCandidateAFullBulkSpinCD10Core period hPeriod analysis) :
    (WithLp.ofLp
      (globalCandidateAFullBulkSpinCD10SpineEmbedding period hPeriod data
        analysis core)).1 =
      P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Graph4D.diagonalExtendedBulkL2SmoothEmbedding
        period hPeriod (globalCandidateAMetricBySector period hPeriod data)
        couplings.matterMassSquared data analysis
        (globalCandidateAFullBulkSpinCD10SpineCoreLinearMap period hPeriod data
          analysis core).1 :=
  rfl

@[simp]
theorem globalCandidateAFullBulkSpinCD10SpineEmbedding_d10
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (core : GlobalCandidateAFullBulkSpinCD10Core period hPeriod analysis) :
    globalCandidateADiagonalExtendedBulkD10Coordinate period hPeriod data
        analysis
        (globalCandidateAFullBulkSpinCD10SpineEmbedding period hPeriod data
          analysis core) = core.2.2 :=
  rfl

/-! ## Direct sum in `GlobalFieldTangent` -/

/-- Sum of the three already faithful bridges into their disjoint slots. -/
def globalCandidateAFullBulkSpinCD10GlobalFieldTangentLinearMap
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalCandidateAFullBulkSpinCD10Core period hPeriod analysis →ₗ[Real]
      GlobalFieldTangent period hPeriod configuration where
  toFun core :=
    globalCandidateANonSpinCPhysicalBulkGlobalFieldTangentLinearMap
        period hPeriod data analysis core.1 +
      globalCandidateABulkMatterGlobalFieldTangentLinearMap period hPeriod
        configuration core.2.1 +
      globalFieldTangentD10SectionLinearMap period hPeriod core.2.2
  map_add' first second := by
    change
      globalCandidateANonSpinCPhysicalBulkGlobalFieldTangentLinearMap
            period hPeriod data analysis (first.1 + second.1) +
          globalCandidateABulkMatterGlobalFieldTangentLinearMap period hPeriod
            configuration (first.2.1 + second.2.1) +
        globalFieldTangentD10SectionLinearMap period hPeriod
            (first.2.2 + second.2.2) =
      (globalCandidateANonSpinCPhysicalBulkGlobalFieldTangentLinearMap
            period hPeriod data analysis first.1 +
          globalCandidateABulkMatterGlobalFieldTangentLinearMap period hPeriod
            configuration first.2.1 +
        globalFieldTangentD10SectionLinearMap period hPeriod first.2.2) +
      (globalCandidateANonSpinCPhysicalBulkGlobalFieldTangentLinearMap
            period hPeriod data analysis second.1 +
          globalCandidateABulkMatterGlobalFieldTangentLinearMap period hPeriod
            configuration second.2.1 +
        globalFieldTangentD10SectionLinearMap period hPeriod second.2.2)
    simp only [map_add]
    abel
  map_smul' scalar core := by
    change
      globalCandidateANonSpinCPhysicalBulkGlobalFieldTangentLinearMap
            period hPeriod data analysis (scalar • core.1) +
          globalCandidateABulkMatterGlobalFieldTangentLinearMap period hPeriod
            configuration (scalar • core.2.1) +
        globalFieldTangentD10SectionLinearMap period hPeriod
            (scalar • core.2.2) =
      scalar •
        (globalCandidateANonSpinCPhysicalBulkGlobalFieldTangentLinearMap
              period hPeriod data analysis core.1 +
            globalCandidateABulkMatterGlobalFieldTangentLinearMap period hPeriod
              configuration core.2.1 +
          globalFieldTangentD10SectionLinearMap period hPeriod core.2.2)
    simp only [map_smul, smul_add]

@[simp]
theorem globalCandidateAFullBulkSpinCD10GlobalFieldTangent_metric
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (core : GlobalCandidateAFullBulkSpinCD10Core period hPeriod analysis) :
    (GlobalFieldTangent.completeVariation period hPeriod
      (globalCandidateAFullBulkSpinCD10GlobalFieldTangentLinearMap
        period hPeriod data analysis core)).fullMetricPerturbation = core.1.1 := by
  change
    (GlobalFieldTangent.completeVariation period hPeriod
      (globalCandidateANonSpinCPhysicalBulkGlobalFieldTangentLinearMap
        period hPeriod data analysis core.1)).fullMetricPerturbation + 0 + 0 =
      core.1.1
  rw [globalCandidateANonSpinCPhysicalBulkGlobalFieldTangent_metric]
  simp

@[simp]
theorem globalCandidateAFullBulkSpinCD10GlobalFieldTangent_gauge
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (core : GlobalCandidateAFullBulkSpinCD10Core period hPeriod analysis) :
    (GlobalFieldTangent.completeVariation period hPeriod
      (globalCandidateAFullBulkSpinCD10GlobalFieldTangentLinearMap
        period hPeriod data analysis core)).independent.gauge =
      globalCandidateAPairedGaugePotentialCoefficientLinearMap period hPeriod
        data core.1.2.1 := by
  change
    (GlobalFieldTangent.completeVariation period hPeriod
      (globalCandidateANonSpinCPhysicalBulkGlobalFieldTangentLinearMap
        period hPeriod data analysis core.1)).independent.gauge + 0 + 0 = _
  rw [globalCandidateANonSpinCPhysicalBulkGlobalFieldTangent_gauge]
  simp

@[simp]
theorem globalCandidateAFullBulkSpinCD10GlobalFieldTangent_llAuxMetric
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (core : GlobalCandidateAFullBulkSpinCD10Core period hPeriod analysis) :
    (GlobalFieldTangent.completeVariation period hPeriod
      (globalCandidateAFullBulkSpinCD10GlobalFieldTangentLinearMap
        period hPeriod data analysis core)).independent.llAuxMetric =
      core.1.2.2.1.1 := by
  change
    (GlobalFieldTangent.completeVariation period hPeriod
      (globalCandidateANonSpinCPhysicalBulkGlobalFieldTangentLinearMap
        period hPeriod data analysis core.1)).independent.llAuxMetric + 0 + 0 =
      core.1.2.2.1.1
  rw [globalCandidateANonSpinCPhysicalBulkGlobalFieldTangent_llAuxMetric]
  simp

@[simp]
theorem globalCandidateAFullBulkSpinCD10GlobalFieldTangent_llMeasure
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (core : GlobalCandidateAFullBulkSpinCD10Core period hPeriod analysis) :
    (GlobalFieldTangent.completeVariation period hPeriod
      (globalCandidateAFullBulkSpinCD10GlobalFieldTangentLinearMap
        period hPeriod data analysis core)).independent.llMeasure =
      core.1.2.2.1.2 := by
  change
    (GlobalFieldTangent.completeVariation period hPeriod
      (globalCandidateANonSpinCPhysicalBulkGlobalFieldTangentLinearMap
        period hPeriod data analysis core.1)).independent.llMeasure + 0 + 0 =
      core.1.2.2.1.2
  rw [globalCandidateANonSpinCPhysicalBulkGlobalFieldTangent_llMeasure]
  simp

@[simp]
theorem globalCandidateAFullBulkSpinCD10GlobalFieldTangent_llField
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (core : GlobalCandidateAFullBulkSpinCD10Core period hPeriod analysis) :
    (GlobalFieldTangent.completeVariation period hPeriod
      (globalCandidateAFullBulkSpinCD10GlobalFieldTangentLinearMap
        period hPeriod data analysis core)).independent.llField =
      core.1.2.2.2.toTest := by
  change
    (GlobalFieldTangent.completeVariation period hPeriod
      (globalCandidateANonSpinCPhysicalBulkGlobalFieldTangentLinearMap
        period hPeriod data analysis core.1)).independent.llField + 0 + 0 =
      core.1.2.2.2.toTest
  rw [globalCandidateANonSpinCPhysicalBulkGlobalFieldTangent_llField]
  simp

@[simp]
theorem globalCandidateAFullBulkSpinCD10GlobalFieldTangent_spinCMatter
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (core : GlobalCandidateAFullBulkSpinCD10Core period hPeriod analysis) :
    (globalCandidateAFullBulkSpinCD10GlobalFieldTangentLinearMap
      period hPeriod data analysis core).spinCMatter period hPeriod =
      programPPrimitiveSpinCMatterSmoothFiniteSynthesis period hPeriod
        core.2.1 := by
  change
    (globalCandidateANonSpinCPhysicalBulkGlobalFieldTangentLinearMap
        period hPeriod data analysis core.1).spinCMatter period hPeriod +
      (globalCandidateABulkMatterGlobalFieldTangentLinearMap period hPeriod
        configuration core.2.1).spinCMatter period hPeriod + 0 = _
  rw [globalCandidateANonSpinCPhysicalBulkGlobalFieldTangent_spinCMatter,
    globalCandidateABulkMatterGlobalFieldTangent_spinCMatter]
  simp

@[simp]
theorem globalCandidateAFullBulkSpinCD10GlobalFieldTangent_d10
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (core : GlobalCandidateAFullBulkSpinCD10Core period hPeriod analysis) :
    (globalCandidateAFullBulkSpinCD10GlobalFieldTangentLinearMap
      period hPeriod data analysis core).d10Coordinates period hPeriod =
      core.2.2 := by
  change 0 + 0 + core.2.2 = core.2.2
  simp

/-- Exact compatibility of the combined tangent with the finite SpinC graph
coordinate. -/
@[simp]
theorem globalCandidateAFullBulkSpinCD10GlobalFieldTangent_toSpinCGraph
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared)
    (core : GlobalCandidateAFullBulkSpinCD10Core period hPeriod analysis) :
    realization.toGraph
        ((globalCandidateAFullBulkSpinCD10GlobalFieldTangentLinearMap
          period hPeriod data analysis core).spinCMatter period hPeriod) =
      programPPrimitiveSpinCMatterGraphFiniteRealLinearMap period hPeriod
        couplings.matterMassSquared core.2.1 := by
  rw [globalCandidateAFullBulkSpinCD10GlobalFieldTangent_spinCMatter]
  exact realization.finite_compatibility core.2.1

theorem globalCandidateAFullBulkSpinCD10GlobalFieldTangent_injective
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    Function.Injective
      (globalCandidateAFullBulkSpinCD10GlobalFieldTangentLinearMap period
        hPeriod data analysis) := by
  intro first second hEqual
  have hMetric := congrArg
    (fun tangent : GlobalFieldTangent period hPeriod configuration =>
      (tangent.completeVariation period hPeriod).fullMetricPerturbation) hEqual
  have hGauge := congrArg
    (fun tangent : GlobalFieldTangent period hPeriod configuration =>
      (tangent.completeVariation period hPeriod).independent.gauge) hEqual
  have hAux := congrArg
    (fun tangent : GlobalFieldTangent period hPeriod configuration =>
      (tangent.completeVariation period hPeriod).independent.llAuxMetric) hEqual
  have hMeasure := congrArg
    (fun tangent : GlobalFieldTangent period hPeriod configuration =>
      (tangent.completeVariation period hPeriod).independent.llMeasure) hEqual
  have hField := congrArg
    (fun tangent : GlobalFieldTangent period hPeriod configuration =>
      (tangent.completeVariation period hPeriod).independent.llField) hEqual
  have hSpinC := congrArg
    (fun tangent : GlobalFieldTangent period hPeriod configuration =>
      tangent.spinCMatter period hPeriod) hEqual
  have hD10 := congrArg
    (fun tangent : GlobalFieldTangent period hPeriod configuration =>
      tangent.d10Coordinates period hPeriod) hEqual
  simp only [globalCandidateAFullBulkSpinCD10GlobalFieldTangent_metric]
    at hMetric
  simp only [globalCandidateAFullBulkSpinCD10GlobalFieldTangent_gauge]
    at hGauge
  simp only [globalCandidateAFullBulkSpinCD10GlobalFieldTangent_llAuxMetric]
    at hAux
  simp only [globalCandidateAFullBulkSpinCD10GlobalFieldTangent_llMeasure]
    at hMeasure
  simp only [globalCandidateAFullBulkSpinCD10GlobalFieldTangent_llField]
    at hField
  simp only [globalCandidateAFullBulkSpinCD10GlobalFieldTangent_spinCMatter]
    at hSpinC
  simp only [globalCandidateAFullBulkSpinCD10GlobalFieldTangent_d10] at hD10
  apply Prod.ext
  · exact Prod.ext hMetric
      (Prod.ext
        ((globalCandidateAPairedGaugePotentialCoefficientLinearMap_injective
          period hPeriod data) hGauge)
        (Prod.ext (Prod.ext hAux hMeasure)
          (LLH1Smooth.ext period hPeriod hField)))
  · exact Prod.ext
      (programPPrimitiveSpinCMatterSmoothFiniteSynthesis_injective
        period hPeriod hSpinC) hD10

end
end P0EFTJanusProgramPGlobalCandidateAFullBulkSpinCD10GlobalTangentBridge4D
end JanusFormal
