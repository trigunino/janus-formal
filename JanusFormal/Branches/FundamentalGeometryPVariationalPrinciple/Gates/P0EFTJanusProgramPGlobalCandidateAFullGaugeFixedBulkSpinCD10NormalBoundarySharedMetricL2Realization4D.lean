import Mathlib.Analysis.InnerProductSpace.ProdL2
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkD10SpineL2Bridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2Pairing4D

/-!
# Hilbert realization of the full shared-metric core

The smooth common core is inserted into the orthogonal sum of the faithful
bulk completion, the separate D10 spine and the orientation-double normal
`L2` space.  The duplicate boundary metric is determined by the pullback
equation and is therefore not inserted a second time.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2Realization4D

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 1200000
noncomputable section

open scoped InnerProductSpace ENNReal
open P0EFTJanusMappingTorusOrientationDoubleCover
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusScalarRobinJunctionL2Fredholm4D
open P0EFTJanusD8NormalBundleD9DisplacementBridge4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPCommonGeometricDomain4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkD10SpineL2Bridge4D
open P0EFTJanusProgramPGlobalCandidateAFullGaugeFixedBulkSpinCL2CorePairingBridge4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryGaugeFixedSmoothTangentL2Pairing4D
open P0EFTJanusProgramPGlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricTangent4D
open P0EFTJanusProgramPGlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2Pairing4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Canonical scalar `L2` target for the genuine normal displacement. -/
abbrev GlobalCandidateAFullGaugeFixedNormalDisplacementL2 :=
  ThroatScalarL2
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
    (intrinsicCanonicalThroatVolumeMeasure
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))

attribute [local instance]
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkNormedAddCommGroup
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkInnerProductSpace
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkNormedSpace
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkModule
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkCompleteSpace

/-- Orthogonal Hilbert ambient: faithful bulk, separate D10 and normal `L2`. -/
abbrev GlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2Ambient
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :=
  WithLp 2
    (GlobalCandidateADiagonalExtendedBulkD10SpineHilbert4D period hPeriod data
        analysis ×
      GlobalCandidateAFullGaugeFixedNormalDisplacementL2 period hPeriod)

@[implicit_reducible]
private def sharedMetricSpineNormedAddCommGroup
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    NormedAddCommGroup
      (GlobalCandidateADiagonalExtendedBulkD10SpineHilbert4D period hPeriod
        data analysis) :=
  @WithLp.instProdNormedAddCommGroup 2
    (GlobalCandidateADiagonalExtendedBulkL2Hilbert period hPeriod
      (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis)
    (ProgramPD10ModeHilbert4D
      (d10SpectralData period hPeriod
        configuration.physical.d10Completion))
    inferInstance
    (diagonalL2ExtendedBulkNormedAddCommGroup period hPeriod
      (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis)
    inferInstance

attribute [local instance] sharedMetricSpineNormedAddCommGroup

@[implicit_reducible]
private def sharedMetricSpineInnerProductSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    InnerProductSpace Real
      (GlobalCandidateADiagonalExtendedBulkD10SpineHilbert4D period hPeriod
        data analysis) :=
  @WithLp.instProdInnerProductSpace Real
    (GlobalCandidateADiagonalExtendedBulkL2Hilbert period hPeriod
      (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis)
    (ProgramPD10ModeHilbert4D
      (d10SpectralData period hPeriod
        configuration.physical.d10Completion))
    inferInstance
    (diagonalL2ExtendedBulkNormedAddCommGroup period hPeriod
      (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis)
    (diagonalL2ExtendedBulkInnerProductSpace period hPeriod
      (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis)
    inferInstance inferInstance

attribute [local instance] sharedMetricSpineInnerProductSpace

@[implicit_reducible]
private def sharedMetricSpineCompleteSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    CompleteSpace
      (GlobalCandidateADiagonalExtendedBulkD10SpineHilbert4D period hPeriod
        data analysis) :=
  @WithLp.instProdCompleteSpace 2
    (GlobalCandidateADiagonalExtendedBulkL2Hilbert period hPeriod
      (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis)
    (ProgramPD10ModeHilbert4D
      (d10SpectralData period hPeriod
        configuration.physical.d10Completion))
    inferInstance inferInstance
    (diagonalL2ExtendedBulkCompleteSpace period hPeriod
      (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis)
    inferInstance

/-- Opaque normed-group provider for the full ambient Hilbert sum. -/
@[implicit_reducible]
def globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2AmbientNormedAddCommGroup
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    NormedAddCommGroup
      (GlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2Ambient
        period hPeriod configuration data analysis) :=
  @WithLp.instProdNormedAddCommGroup 2
    (GlobalCandidateADiagonalExtendedBulkD10SpineHilbert4D period hPeriod data
      analysis)
    (GlobalCandidateAFullGaugeFixedNormalDisplacementL2 period hPeriod)
    inferInstance
    (sharedMetricSpineNormedAddCommGroup period hPeriod configuration data
      analysis)
    inferInstance

attribute [local instance]
  globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2AmbientNormedAddCommGroup

/-- Opaque inner-product provider for the full ambient Hilbert sum. -/
@[implicit_reducible]
def globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2AmbientInnerProductSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    InnerProductSpace Real
      (GlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2Ambient
        period hPeriod configuration data analysis) :=
  @WithLp.instProdInnerProductSpace Real
    (GlobalCandidateADiagonalExtendedBulkD10SpineHilbert4D period hPeriod data
      analysis)
    (GlobalCandidateAFullGaugeFixedNormalDisplacementL2 period hPeriod)
    inferInstance
    (sharedMetricSpineNormedAddCommGroup period hPeriod configuration data
      analysis)
    (sharedMetricSpineInnerProductSpace period hPeriod configuration data
      analysis)
    inferInstance inferInstance

attribute [local instance]
  globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2AmbientInnerProductSpace

/-- Opaque normed-space provider for the full ambient Hilbert sum. -/
@[implicit_reducible]
def globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2AmbientNormedSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    NormedSpace Real
      (GlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2Ambient
        period hPeriod configuration data analysis) :=
  (globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2AmbientInnerProductSpace
    period hPeriod configuration data analysis).toNormedSpace

attribute [local instance]
  globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2AmbientNormedSpace

/-- Opaque real-module provider for the full ambient Hilbert sum. -/
@[implicit_reducible]
def globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2AmbientModule
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    Module Real
      (GlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2Ambient
        period hPeriod configuration data analysis) :=
  (globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2AmbientNormedSpace
    period hPeriod configuration data analysis).toModule

attribute [local instance]
  globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2AmbientModule

/-- Opaque completeness provider, constructed by the two product levels. -/
@[implicit_reducible]
def globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2AmbientCompleteSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    CompleteSpace
      (GlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2Ambient
        period hPeriod configuration data analysis) :=
  @WithLp.instProdCompleteSpace 2
    (GlobalCandidateADiagonalExtendedBulkD10SpineHilbert4D period hPeriod data
      analysis)
    (GlobalCandidateAFullGaugeFixedNormalDisplacementL2 period hPeriod)
    inferInstance inferInstance
    (sharedMetricSpineCompleteSpace period hPeriod configuration data analysis)
    inferInstance

def globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricCoreSubtype
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    GlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricCore
        period hPeriod analysis →ₗ[Real]
      GlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundaryAmbientCore
        period hPeriod analysis :=
  (LinearMap.ker
    (globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundaryMetricDisagreementLinearMap
      period hPeriod analysis)).subtype

def globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricBulkL2LinearMap
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    GlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricCore
        period hPeriod analysis →ₗ[Real]
      GlobalCandidateADiagonalExtendedBulkL2Hilbert period hPeriod
        (globalCandidateAMetricBySector period hPeriod data)
        couplings.matterMassSquared data analysis :=
  (P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Graph4D.diagonalExtendedBulkL2SmoothEmbedding
      period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis).comp
    ((globalCandidateAFullGaugeFixedBulkSpinCToDiagonalExtendedBulkLinearMap
        period hPeriod data analysis).comp
      ((globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundaryBulkProjection
          period hPeriod analysis).comp
        (globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricCoreSubtype
          period hPeriod analysis)))

def globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricD10LinearMap
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    GlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricCore
        period hPeriod analysis →ₗ[Real]
      ProgramPD10ModeHilbert4D
        (d10SpectralData period hPeriod
          configuration.physical.d10Completion) :=
  (globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundaryD10Projection
      period hPeriod analysis).comp
    (globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricCoreSubtype
      period hPeriod analysis)

def globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricNormalProjection
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    GlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricCore
        period hPeriod analysis →ₗ[Real]
      SmoothNormalDisplacement period hPeriod where
  toFun core := core.1.2.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricNormalL2LinearMap
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    GlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricCore
        period hPeriod analysis →ₗ[Real]
      GlobalCandidateAFullGaugeFixedNormalDisplacementL2 period hPeriod :=
  (candidateANormalBoundaryNormalL2LinearMap period hPeriod).comp
    (globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricNormalProjection
      period hPeriod analysis)

def globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricSpineL2LinearMap
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    GlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricCore
        period hPeriod analysis →ₗ[Real]
      GlobalCandidateADiagonalExtendedBulkD10SpineHilbert4D period hPeriod data
        analysis :=
  (WithLp.linearEquiv 2 Real
      (GlobalCandidateADiagonalExtendedBulkL2Hilbert period hPeriod
          (globalCandidateAMetricBySector period hPeriod data)
          couplings.matterMassSquared data analysis ×
        ProgramPD10ModeHilbert4D
          (d10SpectralData period hPeriod
            configuration.physical.d10Completion))).symm.toLinearMap.comp
    ((globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricBulkL2LinearMap
        period hPeriod configuration data analysis).prod
      (globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricD10LinearMap
        period hPeriod analysis))

/-- Canonical linear realization of every independent shared-core coordinate. -/
def globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2LinearMap
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    GlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricCore
        period hPeriod analysis →ₗ[Real]
      GlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2Ambient
        period hPeriod configuration data analysis :=
  (WithLp.linearEquiv 2 Real
      (GlobalCandidateADiagonalExtendedBulkD10SpineHilbert4D period hPeriod
          data analysis ×
        GlobalCandidateAFullGaugeFixedNormalDisplacementL2
          period hPeriod)).symm.toLinearMap.comp
    ((globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricSpineL2LinearMap
        period hPeriod configuration data analysis).prod
      (globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricNormalL2LinearMap
        period hPeriod analysis))

@[simp]
theorem globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2LinearMap_apply
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (core :
      GlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricCore
        period hPeriod analysis) :
    globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2LinearMap
        period hPeriod configuration data analysis core =
      WithLp.toLp 2
        (WithLp.toLp 2
          (P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Graph4D.diagonalExtendedBulkL2SmoothEmbedding
              period hPeriod
              (globalCandidateAMetricBySector period hPeriod data)
              couplings.matterMassSquared data analysis
              (globalCandidateAFullGaugeFixedBulkSpinCToDiagonalExtendedBulkLinearMap
                period hPeriod data analysis core.1.1.1),
            core.1.1.2),
          candidateANormalBoundaryNormalL2LinearMap
            period hPeriod core.1.2.2) :=
  rfl

/-- The ambient inner product is exactly the full common pairing. -/
theorem globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2LinearMap_inner
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (first second :
      GlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricCore
        period hPeriod analysis) :
    inner Real
        (globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2LinearMap
          period hPeriod configuration data analysis first)
        (globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2LinearMap
          period hPeriod configuration data analysis second) =
      globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2Inner
        period hPeriod configuration data analysis first second := by
  rw [
    globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2LinearMap_apply
      period hPeriod configuration data analysis first,
    globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2LinearMap_apply
      period hPeriod configuration data analysis second]
  rw [@WithLp.prod_inner_apply Real
    (GlobalCandidateADiagonalExtendedBulkD10SpineHilbert4D period hPeriod data
      analysis)
    (GlobalCandidateAFullGaugeFixedNormalDisplacementL2 period hPeriod)
    inferInstance
    (sharedMetricSpineNormedAddCommGroup period hPeriod configuration data
      analysis)
    (sharedMetricSpineInnerProductSpace period hPeriod configuration data
      analysis)
    inferInstance inferInstance]
  rw [@WithLp.prod_inner_apply Real
    (GlobalCandidateADiagonalExtendedBulkL2Hilbert period hPeriod
      (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis)
    (ProgramPD10ModeHilbert4D
      (d10SpectralData period hPeriod
        configuration.physical.d10Completion))
    inferInstance
    (diagonalL2ExtendedBulkNormedAddCommGroup period hPeriod
      (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis)
    (diagonalL2ExtendedBulkInnerProductSpace period hPeriod
      (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis)
    inferInstance inferInstance]
  unfold
    globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2Inner
  change
    @inner Real
          (GlobalCandidateADiagonalExtendedBulkL2Hilbert period hPeriod
            (globalCandidateAMetricBySector period hPeriod data)
            couplings.matterMassSquared data analysis)
          (diagonalL2ExtendedBulkInnerProductSpace period hPeriod
            (globalCandidateAMetricBySector period hPeriod data)
            couplings.matterMassSquared data analysis).toInner
          (P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Graph4D.diagonalExtendedBulkL2SmoothEmbedding
            period hPeriod (globalCandidateAMetricBySector period hPeriod data)
            couplings.matterMassSquared data analysis
            (globalCandidateAFullGaugeFixedBulkSpinCToDiagonalExtendedBulkLinearEquiv
              period hPeriod data analysis first.1.1.1))
          (P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Graph4D.diagonalExtendedBulkL2SmoothEmbedding
            period hPeriod (globalCandidateAMetricBySector period hPeriod data)
            couplings.matterMassSquared data analysis
            (globalCandidateAFullGaugeFixedBulkSpinCToDiagonalExtendedBulkLinearEquiv
              period hPeriod data analysis second.1.1.1)) +
        inner Real first.1.1.2 second.1.1.2 +
      inner Real
        (candidateANormalBoundaryNormalL2LinearMap
          period hPeriod first.1.2.2)
        (candidateANormalBoundaryNormalL2LinearMap
          period hPeriod second.1.2.2) =
    globalCandidateAFullGaugeFixedBulkSpinCL2CoreInner period hPeriod data
          analysis first.1.1.1 second.1.1.1 +
        inner Real first.1.1.2 second.1.1.2 +
      inner Real
        (candidateANormalBoundaryNormalL2LinearMap
          period hPeriod first.1.2.2)
        (candidateANormalBoundaryNormalL2LinearMap
          period hPeriod second.1.2.2)
  have hBulk :=
    globalCandidateAFullGaugeFixedBulkSpinCDiagonalL2SmoothEmbedding_inner
      period hPeriod data analysis first.1.1.1 second.1.1.1
  exact congrArg
    (fun bulkPair : Real =>
      bulkPair + inner Real first.1.1.2 second.1.1.2 +
        inner Real
          (candidateANormalBoundaryNormalL2LinearMap
            period hPeriod first.1.2.2)
          (candidateANormalBoundaryNormalL2LinearMap
            period hPeriod second.1.2.2))
    hBulk

/-- No smooth bulk, D10 or normal coordinate is lost. -/
theorem globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2LinearMap_injective
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    Function.Injective
      (globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2LinearMap
        period hPeriod configuration data analysis) := by
  refine (injective_iff_map_eq_zero _).mpr ?_
  intro core hZero
  apply
    (globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2Inner_self_eq_zero_iff
      period hPeriod configuration data analysis core).mp
  calc
    globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2Inner
        period hPeriod configuration data analysis core core =
      inner Real
        (globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2LinearMap
          period hPeriod configuration data analysis core)
        (globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2LinearMap
          period hPeriod configuration data analysis core) :=
      (globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2LinearMap_inner
        period hPeriod configuration data analysis core core).symm
    _ = 0 :=
      (@inner_self_eq_zero Real
        (GlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2Ambient
          period hPeriod configuration data analysis)
        inferInstance
        (globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2AmbientNormedAddCommGroup
          period hPeriod configuration data analysis)
        (globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2AmbientInnerProductSpace
          period hPeriod configuration data analysis)).mpr hZero

end
end P0EFTJanusProgramPGlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricL2Realization4D
end JanusFormal
