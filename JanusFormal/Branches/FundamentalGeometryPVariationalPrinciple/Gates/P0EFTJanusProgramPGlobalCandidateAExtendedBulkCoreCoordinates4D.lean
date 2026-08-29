import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Graph4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D

/-!
# Canonical coordinates on the actual extended-bulk smooth core

The dense smooth core of the common Candidate-A Hilbert space is definitionally

`bulk diagonal × (primitive SpinC matter × full LL)`.

This file does not postulate three subspaces. It extracts the three coordinate
projectors directly from that product, proves that they resolve the identity,
and proves their pairwise orthogonality for the exact L2 graph inner product.
The subsequent five-sector construction only has to refine the bulk-diagonal
factor into metric/diffeomorphism, Abelian and finite-boundary/BV coordinates.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAExtendedBulkCoreCoordinates4D

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
noncomputable section

open scoped InnerProductSpace
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Bilinear4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Graph4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D

attribute [local instance]
  coreDiffeomorphismNormedAddCommGroup
  coreDiffeomorphismNormedSpace
  coreDiffeomorphismModule
  coreDiffeomorphismInnerProductSpace
  coreAbelianNormedSpace
  coreAbelianModule
  coreAbelianInnerProductSpace
  coreMatterInnerProductSpace
  coreLLInnerProductSpace
  coreLLNormedSpace
  coreLLModule

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ExtendedCore
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :=
  GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod data analysis

/-- Keep only the diagonal bulk component. -/
def globalCandidateAExtendedBulkCoreBulkProjector
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    ExtendedCore period hPeriod configuration data analysis →ₗ[Real]
      ExtendedCore period hPeriod configuration data analysis where
  toFun core := (core.1, (0, 0))
  map_add' _ _ := by ext <;> simp
  map_smul' _ _ := by ext <;> simp

/-- Keep only the primitive SpinC matter component. -/
def globalCandidateAExtendedBulkCoreMatterProjector
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    ExtendedCore period hPeriod configuration data analysis →ₗ[Real]
      ExtendedCore period hPeriod configuration data analysis where
  toFun core := (0, (core.2.1, 0))
  map_add' _ _ := by ext <;> simp
  map_smul' _ _ := by ext <;> simp

/-- Keep only the full longitudinal/LL graph component. -/
def globalCandidateAExtendedBulkCoreLLProjector
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    ExtendedCore period hPeriod configuration data analysis →ₗ[Real]
      ExtendedCore period hPeriod configuration data analysis where
  toFun core := (0, (0, core.2.2))
  map_add' _ _ := by ext <;> simp
  map_smul' _ _ := by ext <;> simp

@[simp]
theorem globalCandidateAExtendedBulkCoreBulkProjector_idempotent
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (core : ExtendedCore period hPeriod configuration data analysis) :
    globalCandidateAExtendedBulkCoreBulkProjector period hPeriod configuration
        data analysis
        (globalCandidateAExtendedBulkCoreBulkProjector period hPeriod
          configuration data analysis core) =
      globalCandidateAExtendedBulkCoreBulkProjector period hPeriod configuration
        data analysis core := by
  ext <;> simp [globalCandidateAExtendedBulkCoreBulkProjector]

@[simp]
theorem globalCandidateAExtendedBulkCoreMatterProjector_idempotent
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (core : ExtendedCore period hPeriod configuration data analysis) :
    globalCandidateAExtendedBulkCoreMatterProjector period hPeriod configuration
        data analysis
        (globalCandidateAExtendedBulkCoreMatterProjector period hPeriod
          configuration data analysis core) =
      globalCandidateAExtendedBulkCoreMatterProjector period hPeriod
        configuration data analysis core := by
  ext <;> simp [globalCandidateAExtendedBulkCoreMatterProjector]

@[simp]
theorem globalCandidateAExtendedBulkCoreLLProjector_idempotent
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (core : ExtendedCore period hPeriod configuration data analysis) :
    globalCandidateAExtendedBulkCoreLLProjector period hPeriod configuration
        data analysis
        (globalCandidateAExtendedBulkCoreLLProjector period hPeriod
          configuration data analysis core) =
      globalCandidateAExtendedBulkCoreLLProjector period hPeriod configuration
        data analysis core := by
  ext <;> simp [globalCandidateAExtendedBulkCoreLLProjector]

/-- The three definitionally present factors resolve every smooth-core vector. -/
theorem globalCandidateAExtendedBulkCore_projectors_decompose
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (core : ExtendedCore period hPeriod configuration data analysis) :
    globalCandidateAExtendedBulkCoreBulkProjector period hPeriod configuration
          data analysis core +
      globalCandidateAExtendedBulkCoreMatterProjector period hPeriod
          configuration data analysis core +
      globalCandidateAExtendedBulkCoreLLProjector period hPeriod configuration
          data analysis core = core := by
  ext <;> simp [globalCandidateAExtendedBulkCoreBulkProjector,
    globalCandidateAExtendedBulkCoreMatterProjector,
    globalCandidateAExtendedBulkCoreLLProjector]

/-- Bulk and primitive matter are orthogonal for the exact common graph inner
product. -/
theorem globalCandidateAExtendedBulkCore_bulk_matter_inner_zero
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (first second : ExtendedCore period hPeriod configuration data analysis) :
    diagonalExtendedBulkL2CoreInner period hPeriod
        (globalCandidateAMetricBySector period hPeriod data)
        couplings.matterMassSquared data analysis
        (globalCandidateAExtendedBulkCoreBulkProjector period hPeriod
          configuration data analysis first)
        (globalCandidateAExtendedBulkCoreMatterProjector period hPeriod
          configuration data analysis second) = 0 := by
  rcases first with ⟨⟨firstDiffeomorphism, firstAbelian⟩,
    firstMatter, firstLL⟩
  rcases second with ⟨⟨secondDiffeomorphism, secondAbelian⟩,
    secondMatter, secondLL⟩
  unfold diagonalExtendedBulkL2CoreInner
    globalCandidateAExtendedBulkCoreBulkProjector
    globalCandidateAExtendedBulkCoreMatterProjector
  simp [inner_zero_left, inner_zero_right]

/-- Bulk and LL are orthogonal for the exact common graph inner product. -/
theorem globalCandidateAExtendedBulkCore_bulk_ll_inner_zero
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (first second : ExtendedCore period hPeriod configuration data analysis) :
    diagonalExtendedBulkL2CoreInner period hPeriod
        (globalCandidateAMetricBySector period hPeriod data)
        couplings.matterMassSquared data analysis
        (globalCandidateAExtendedBulkCoreBulkProjector period hPeriod
          configuration data analysis first)
        (globalCandidateAExtendedBulkCoreLLProjector period hPeriod
          configuration data analysis second) = 0 := by
  rcases first with ⟨⟨firstDiffeomorphism, firstAbelian⟩,
    firstMatter, firstLL⟩
  rcases second with ⟨⟨secondDiffeomorphism, secondAbelian⟩,
    secondMatter, secondLL⟩
  unfold diagonalExtendedBulkL2CoreInner
    globalCandidateAExtendedBulkCoreBulkProjector
    globalCandidateAExtendedBulkCoreLLProjector
  simp [inner_zero_left, inner_zero_right]

/-- Primitive matter and LL are orthogonal for the exact common graph inner
product. -/
theorem globalCandidateAExtendedBulkCore_matter_ll_inner_zero
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (first second : ExtendedCore period hPeriod configuration data analysis) :
    diagonalExtendedBulkL2CoreInner period hPeriod
        (globalCandidateAMetricBySector period hPeriod data)
        couplings.matterMassSquared data analysis
        (globalCandidateAExtendedBulkCoreMatterProjector period hPeriod
          configuration data analysis first)
        (globalCandidateAExtendedBulkCoreLLProjector period hPeriod
          configuration data analysis second) = 0 := by
  rcases first with ⟨⟨firstDiffeomorphism, firstAbelian⟩,
    firstMatter, firstLL⟩
  rcases second with ⟨⟨secondDiffeomorphism, secondAbelian⟩,
    secondMatter, secondLL⟩
  unfold diagonalExtendedBulkL2CoreInner
    globalCandidateAExtendedBulkCoreMatterProjector
    globalCandidateAExtendedBulkCoreLLProjector
  simp [inner_zero_left, inner_zero_right]

/-- Public checkpoint: the top-level sector split is already canonical on the
actual dense core. -/
theorem global_candidateA_extended_bulk_core_coordinates_gate
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    (∀ core : ExtendedCore period hPeriod configuration data analysis,
      globalCandidateAExtendedBulkCoreBulkProjector period hPeriod configuration
            data analysis core +
        globalCandidateAExtendedBulkCoreMatterProjector period hPeriod
            configuration data analysis core +
        globalCandidateAExtendedBulkCoreLLProjector period hPeriod configuration
            data analysis core = core) ∧
    (∀ first second : ExtendedCore period hPeriod configuration data analysis,
      diagonalExtendedBulkL2CoreInner period hPeriod
        (globalCandidateAMetricBySector period hPeriod data)
        couplings.matterMassSquared data analysis
        (globalCandidateAExtendedBulkCoreBulkProjector period hPeriod
          configuration data analysis first)
        (globalCandidateAExtendedBulkCoreMatterProjector period hPeriod
          configuration data analysis second) = 0) ∧
    (∀ first second : ExtendedCore period hPeriod configuration data analysis,
      diagonalExtendedBulkL2CoreInner period hPeriod
        (globalCandidateAMetricBySector period hPeriod data)
        couplings.matterMassSquared data analysis
        (globalCandidateAExtendedBulkCoreBulkProjector period hPeriod
          configuration data analysis first)
        (globalCandidateAExtendedBulkCoreLLProjector period hPeriod
          configuration data analysis second) = 0) ∧
    (∀ first second : ExtendedCore period hPeriod configuration data analysis,
      diagonalExtendedBulkL2CoreInner period hPeriod
        (globalCandidateAMetricBySector period hPeriod data)
        couplings.matterMassSquared data analysis
        (globalCandidateAExtendedBulkCoreMatterProjector period hPeriod
          configuration data analysis first)
        (globalCandidateAExtendedBulkCoreLLProjector period hPeriod
          configuration data analysis second) = 0) :=
  ⟨globalCandidateAExtendedBulkCore_projectors_decompose period hPeriod
      configuration data analysis,
    globalCandidateAExtendedBulkCore_bulk_matter_inner_zero period hPeriod
      configuration data analysis,
    globalCandidateAExtendedBulkCore_bulk_ll_inner_zero period hPeriod
      configuration data analysis,
    globalCandidateAExtendedBulkCore_matter_ll_inner_zero period hPeriod
      configuration data analysis⟩

end
end P0EFTJanusProgramPGlobalCandidateAExtendedBulkCoreCoordinates4D
end JanusFormal
