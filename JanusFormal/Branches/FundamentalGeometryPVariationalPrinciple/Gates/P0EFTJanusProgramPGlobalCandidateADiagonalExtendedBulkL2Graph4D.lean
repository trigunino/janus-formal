import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D

/-!
# Regrouped smooth core for the diagonal Candidate-A L2 graph

The pre-existing graph chart stores the four smooth factors as

```text
diffeomorphism × (Abelian × (matter × LL)).
```

The physical coordinate layer uses the equivalent grouping

```text
(diffeomorphism × Abelian) × (matter × LL),
```

so that the first factor is the complete diagonal bulk block.  This file
provides the missing linear reassociation, composes it with the genuine L2
smooth embedding, and exposes the exact componentwise L2 graph pairing used by
the dense-core projectors.

No new completion, action term or analytic premise is introduced.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Graph4D

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 1200000
noncomputable section

open scoped InnerProductSpace ENNReal
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalPairedAbelianBRSTGaugeFermion4D
open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPGlobalFullLLGraphRiesz4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateAAbelianExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateAAbelianExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- The same four smooth factors as the legacy chart, regrouped so that the
first coordinate is the complete diagonal bulk block. -/
abbrev GlobalCandidateADiagonalExtendedBulkSmoothCore
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :=
  (GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod ×
      GlobalPairedAbelianBRSTState period hPeriod) ×
    (ProgramPPrimitiveSpinCMatterFiniteCoefficients ×
      GlobalFullLLSmooth period hPeriod analysis)

/-- Linear reassociation to the legacy four-factor smooth-core chart. -/
def diagonalExtendedBulkSmoothCoreToLegacy
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod data analysis
      →ₗ[Real]
    P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D.GlobalCandidateADiagonalExtendedBulkSmoothCore
      period hPeriod analysis where
  toFun core := (core.1.1, (core.1.2, (core.2.1, core.2.2)))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

local instance (priority := 30000) regroupedL2NormedAddCommGroup
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    NormedAddCommGroup
      (GlobalCandidateADiagonalExtendedBulkL2Hilbert period hPeriod metric
        massSquared data analysis) :=
  diagonalL2ExtendedBulkNormedAddCommGroup period hPeriod metric massSquared
    data analysis

local instance (priority := 30000) regroupedL2InnerProductSpace
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    InnerProductSpace Real
      (GlobalCandidateADiagonalExtendedBulkL2Hilbert period hPeriod metric
        massSquared data analysis) :=
  diagonalL2ExtendedBulkInnerProductSpace period hPeriod metric massSquared
    data analysis

local instance (priority := 30000) regroupedL2NormedSpace
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    NormedSpace Real
      (GlobalCandidateADiagonalExtendedBulkL2Hilbert period hPeriod metric
        massSquared data analysis) :=
  diagonalL2ExtendedBulkNormedSpace period hPeriod metric massSquared data
    analysis

local instance (priority := 30000) regroupedL2Module
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    Module Real
      (GlobalCandidateADiagonalExtendedBulkL2Hilbert period hPeriod metric
        massSquared data analysis) :=
  diagonalL2ExtendedBulkModule period hPeriod metric massSquared data analysis

/-- The regrouped smooth core embedded in the already constructed genuine L2
completion. -/
def diagonalExtendedBulkL2SmoothEmbedding
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod data analysis
      →ₗ[Real]
    GlobalCandidateADiagonalExtendedBulkL2Hilbert period hPeriod metric
      massSquared data analysis :=
  (P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalExtendedBulkL2SmoothEmbedding
      period hPeriod metric massSquared
        data analysis).comp
    (diagonalExtendedBulkSmoothCoreToLegacy period hPeriod data analysis)

@[simp]
theorem diagonalExtendedBulkL2SmoothEmbedding_apply
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (core : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod data
      analysis) :
    diagonalExtendedBulkL2SmoothEmbedding period hPeriod metric massSquared data
        analysis core =
      P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalExtendedBulkL2SmoothEmbedding
        period hPeriod metric massSquared
          data analysis
          (diagonalExtendedBulkSmoothCoreToLegacy period hPeriod data analysis
            core) :=
  rfl

end
end P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Graph4D

namespace P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Bilinear4D

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 1200000
noncomputable section

open scoped InnerProductSpace
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalPairedAbelianBRSTGaugeFermion4D
open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPGlobalFullLLGraphRiesz4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateAAbelianExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateAAbelianExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Graph4D

variable (period : Real) (hPeriod : period ≠ 0)

local instance (priority := 30000) coreDiffeomorphismNormedAddCommGroup
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    NormedAddCommGroup
      (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert period hPeriod
        metric) :=
  diagonalL2DiffeomorphismNormedAddCommGroup period hPeriod metric

local instance (priority := 30000) coreDiffeomorphismNormedSpace
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert period hPeriod
        metric) :=
  diagonalL2DiffeomorphismNormedSpace period hPeriod metric

local instance (priority := 30000) coreDiffeomorphismModule
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    Module Real
      (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert period hPeriod
        metric) :=
  diagonalL2DiffeomorphismModule period hPeriod metric

local instance (priority := 30000) coreDiffeomorphismInnerProductSpace
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    InnerProductSpace Real
      (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert period hPeriod
        metric) :=
  diagonalL2DiffeomorphismInnerProductSpace period hPeriod metric

local instance (priority := 30000) coreAbelianNormedSpace
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric) :=
  diagonalL2AbelianNormedSpace period hPeriod metric

local instance (priority := 30000) coreAbelianModule
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    Module Real
      (GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric) :=
  diagonalL2AbelianModule period hPeriod metric

local instance (priority := 30000) coreAbelianInnerProductSpace
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    InnerProductSpace Real
      (GlobalPairedAbelianOffShellGraphHilbert period hPeriod metric) :=
  diagonalL2AbelianInnerProductSpace period hPeriod metric

local instance (priority := 30000) coreMatterInnerProductSpace
    (massSquared : Real) :
    InnerProductSpace Real
      (ProgramPPrimitiveSpinCMatterL2GraphDomain period hPeriod massSquared) :=
  diagonalL2MatterInnerProductSpace period hPeriod massSquared

local instance (priority := 30000) coreLLInnerProductSpace
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    InnerProductSpace Real (GlobalFullLLGraphHilbert period hPeriod data analysis) :=
  diagonalL2LLInnerProductSpace period hPeriod data analysis

local instance (priority := 30000) coreLLNormedSpace
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    NormedSpace Real (GlobalFullLLGraphHilbert period hPeriod data analysis) :=
  diagonalL2LLNormedSpace period hPeriod data analysis

local instance (priority := 30000) coreLLModule
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    Module Real (GlobalFullLLGraphHilbert period hPeriod data analysis) :=
  diagonalL2LLModule period hPeriod data analysis

/-- Component formula for the exact nested-L2 graph pairing on the regrouped
smooth core. -/
def diagonalExtendedBulkL2CoreInner
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (first second :
      GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod data
        analysis) : Real :=
  inner Real
      (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding period
        hPeriod metric first.1.1)
      (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding period
        hPeriod metric second.1.1) +
    inner Real
      (globalPairedAbelianOffShellSmoothEmbedding period hPeriod metric
        first.1.2)
      (globalPairedAbelianOffShellSmoothEmbedding period hPeriod metric
        second.1.2) +
    inner Real
      ((programPPrimitiveSpinCMatterL2GraphEquiv period hPeriod massSquared).symm
        (programPPrimitiveSpinCMatterGraphFiniteRealLinearMap period hPeriod
          massSquared first.2.1))
      ((programPPrimitiveSpinCMatterL2GraphEquiv period hPeriod massSquared).symm
        (programPPrimitiveSpinCMatterGraphFiniteRealLinearMap period hPeriod
          massSquared second.2.1)) +
    inner Real
      (globalCandidateAFullLLSmoothEmbedding period hPeriod data analysis
        first.2.2)
      (globalCandidateAFullLLSmoothEmbedding period hPeriod data analysis
        second.2.2)

end
end P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Bilinear4D

namespace P0EFTJanusProgramPGlobalCandidateAExtendedBulkCoreCoordinates4D

/-- Public compatibility name used by the physical coordinate and five-sector
layers. -/
abbrev GlobalCandidateADiagonalExtendedBulkSmoothCore :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Graph4D.GlobalCandidateADiagonalExtendedBulkSmoothCore

/-- Public compatibility name for the regrouped genuine L2 embedding. -/
noncomputable abbrev diagonalExtendedBulkL2SmoothEmbedding :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Graph4D.diagonalExtendedBulkL2SmoothEmbedding

end P0EFTJanusProgramPGlobalCandidateAExtendedBulkCoreCoordinates4D
end JanusFormal
