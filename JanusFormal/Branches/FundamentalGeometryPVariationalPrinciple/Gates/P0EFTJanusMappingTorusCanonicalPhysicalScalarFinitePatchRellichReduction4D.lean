import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetRellichCompactness4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarEuclideanRellichCore4D
import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Finite-patch reduction of physical Rellich compactness

The canonical tangent construction already supplies a finite atlas with a
subordinate smooth partition of unity.  This file proves the functional
analytic gluing step: if every localized chart inclusion is compact and the
partition-localized contributions reconstruct the physical `H¹ → L²`
inclusion, then the global inclusion is compact.

The local Euclidean Rellich theorem on the actual four-dimensional chart
model is imported and proved unconditionally. Consequently the continuum
obstruction is reduced to the explicit chart-measure transport and
localization/reconstruction identities. Global compactness is not assumed as
a field of this package.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarFinitePatchRellichReduction4D

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetGreenCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetGreenCore4D.CanonicalPhysicalScalarFirstSheetGreenCoreData
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEuclideanRellichCore4D

universe u v

variable (period : Real) (hPeriod : period ≠ 0)
variable {LocalH1 : Type u} [NormedAddCommGroup LocalH1]
  [NormedSpace Real LocalH1]
variable {LocalL2 : Type v} [NormedAddCommGroup LocalL2]
  [NormedSpace Real LocalL2]

private abbrev Patch :=
  FiniteTangentGeneratorPatch period hPeriod

/-- Local chart data sufficient for the finite partition-of-unity Rellich
argument.  Only the local embeddings are required to be compact. -/
structure CanonicalPhysicalScalarFinitePatchRellichData
    (LocalH1 : Type u) [NormedAddCommGroup LocalH1]
    [NormedSpace Real LocalH1]
    (LocalL2 : Type v) [NormedAddCommGroup LocalL2]
    [NormedSpace Real LocalL2] where
  localize : Patch period hPeriod →
    CanonicalPhysicalScalarH1 period hPeriod →L[Real] LocalH1
  localEmbedding : Patch period hPeriod → LocalH1 →L[Real] LocalL2
  extend : Patch period hPeriod → LocalL2 →L[Real]
    CanonicalPhysicalBulkL2 period hPeriod
  localCompact : ∀ patch, IsCompactOperator (localEmbedding patch)
  factorization :
    canonicalPhysicalScalarH1ToBulkL2 period hPeriod =
      ∑ patch : Patch period hPeriod,
        (extend patch).comp ((localEmbedding patch).comp (localize patch))

namespace CanonicalPhysicalScalarFinitePatchRellichData

/-- One partition-localized chart contribution to the bulk inclusion. -/
def patchContribution
    (data : CanonicalPhysicalScalarFinitePatchRellichData
      period hPeriod LocalH1 LocalL2)
    (patch : Patch period hPeriod) :
    CanonicalPhysicalScalarH1 period hPeriod →L[Real]
      CanonicalPhysicalBulkL2 period hPeriod :=
  (data.extend patch).comp
    ((data.localEmbedding patch).comp (data.localize patch))

/-- Every localized contribution is compact. -/
theorem patchContribution_compact
    (data : CanonicalPhysicalScalarFinitePatchRellichData
      period hPeriod LocalH1 LocalL2)
    (patch : Patch period hPeriod) :
    IsCompactOperator (data.patchContribution period hPeriod patch) := by
  change IsCompactOperator
    ((data.extend patch).comp
      ((data.localEmbedding patch).comp (data.localize patch)))
  exact ((data.localCompact patch).comp_clm
    (data.localize patch)).clm_comp (data.extend patch)

/-- A finite sum of localized contributions remains compact. -/
theorem patchContribution_finset_compact
    (data : CanonicalPhysicalScalarFinitePatchRellichData
      period hPeriod LocalH1 LocalL2)
    (patches : Finset (Patch period hPeriod)) :
    IsCompactOperator
      ((∑ patch ∈ patches,
          data.patchContribution period hPeriod patch) :
        CanonicalPhysicalScalarH1 period hPeriod →L[Real]
          CanonicalPhysicalBulkL2 period hPeriod) := by
  classical
  induction patches using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      change IsCompactOperator
        (fun _ : CanonicalPhysicalScalarH1 period hPeriod =>
          (0 : CanonicalPhysicalBulkL2 period hPeriod))
      exact isCompactOperator_zero
  | @insert patch patches hPatch ih =>
      rw [Finset.sum_insert hPatch]
      exact (data.patchContribution_compact period hPeriod patch).add ih

/-- Local compactness on the canonical finite atlas implies physical Rellich
compactness globally. -/
theorem rellich
    (data : CanonicalPhysicalScalarFinitePatchRellichData
      period hPeriod LocalH1 LocalL2) :
    PhysicalH1RellichCompactness period hPeriod := by
  change IsCompactOperator
    (canonicalPhysicalScalarH1ToBulkL2 period hPeriod)
  rw [data.factorization]
  simpa [patchContribution] using
    data.patchContribution_finset_compact
      period hPeriod (Finset.univ : Finset (Patch period hPeriod))

/-- Exact finite-patch reduction certificate. -/
theorem certificate
    (data : CanonicalPhysicalScalarFinitePatchRellichData
      period hPeriod LocalH1 LocalL2) :
    (∀ patch : Patch period hPeriod,
      IsCompactOperator (data.localEmbedding patch)) ∧
      canonicalPhysicalScalarH1ToBulkL2 period hPeriod =
        ∑ patch : Patch period hPeriod,
          data.patchContribution period hPeriod patch ∧
      PhysicalH1RellichCompactness period hPeriod := by
  exact ⟨data.localCompact, by simpa [patchContribution] using data.factorization,
    data.rellich period hPeriod⟩

end CanonicalPhysicalScalarFinitePatchRellichData

/-- Remaining geometric transport data after the local Euclidean Rellich
theorem has been discharged. No compactness assumption is a field. -/
structure CanonicalPhysicalScalarEuclideanRellichTransportData where
  localize : Patch period hPeriod →
    CanonicalPhysicalScalarH1 period hPeriod →L[Real]
      FiniteAtlasEuclideanH1 period hPeriod
  extend : Patch period hPeriod →
    FiniteAtlasEuclideanL2 →L[Real]
      CanonicalPhysicalBulkL2 period hPeriod
  factorization :
    canonicalPhysicalScalarH1ToBulkL2 period hPeriod =
      ∑ patch : Patch period hPeriod,
        (extend patch).comp
          ((finiteAtlasEuclideanRellichEmbedding
            period hPeriod).comp (localize patch))

/-- Smooth-core form of the chart transport data. A uniform graph-norm
bound on each patch is enough to extend every localizer to completed physical
`H¹`; exact reconstruction then extends from the dense smooth core. -/
structure CanonicalPhysicalScalarSmoothEuclideanRellichTransportData where
  localizeCore : Patch period hPeriod →
    SmoothQuotientField period hPeriod Real →ₗ[Real]
      FiniteAtlasEuclideanH1 period hPeriod
  localizeBound :
    ∀ patch, ∃ constant : Real,
      ∀ field : SmoothQuotientField period hPeriod Real,
        ‖localizeCore patch field‖ ≤
          constant *
            ‖smoothToCanonicalPhysicalScalarH1 period hPeriod field‖
  extend : Patch period hPeriod →
    FiniteAtlasEuclideanL2 →L[Real]
      CanonicalPhysicalBulkL2 period hPeriod
  factorizationCore :
    ∀ field : SmoothQuotientField period hPeriod Real,
      canonicalPhysicalScalarH1ToBulkL2 period hPeriod
          (smoothToCanonicalPhysicalScalarH1 period hPeriod field) =
        ∑ patch : Patch period hPeriod,
          extend patch
            (finiteAtlasEuclideanRellichEmbedding period hPeriod
              (localizeCore patch field))

namespace CanonicalPhysicalScalarSmoothEuclideanRellichTransportData

/-- Extension of a bounded chart localizer from the dense smooth physical
core. -/
def localize
    (data : CanonicalPhysicalScalarSmoothEuclideanRellichTransportData
      period hPeriod)
    (patch : Patch period hPeriod) :
    CanonicalPhysicalScalarH1 period hPeriod →L[Real]
      FiniteAtlasEuclideanH1 period hPeriod := by
  letI : IsBoundedSMul Real
      (FiniteAtlasEuclideanH1 period hPeriod) :=
    @NormedSpace.toIsBoundedSMul
      Real (FiniteAtlasEuclideanH1 period hPeriod)
      inferInstance inferInstance inferInstance
  have hBound := data.localizeBound patch
  exact LinearMap.extendOfNorm
    (𝕜 := Real) (𝕜₂ := Real)
    (E := SmoothQuotientField period hPeriod Real)
    (Eₗ := CanonicalPhysicalScalarH1 period hPeriod)
    (F := FiniteAtlasEuclideanH1 period hPeriod)
    (σ₁₂ := RingHom.id Real)
    (data.localizeCore patch)
    (smoothToCanonicalPhysicalScalarH1 period hPeriod)

theorem localize_agrees_on_smooth
    (data : CanonicalPhysicalScalarSmoothEuclideanRellichTransportData
      period hPeriod)
    (patch : Patch period hPeriod)
    (field : SmoothQuotientField period hPeriod Real) :
    data.localize period hPeriod patch
        (smoothToCanonicalPhysicalScalarH1 period hPeriod field) =
      data.localizeCore patch field := by
  letI : IsBoundedSMul Real
      (FiniteAtlasEuclideanH1 period hPeriod) :=
    @NormedSpace.toIsBoundedSMul
      Real (FiniteAtlasEuclideanH1 period hPeriod)
      inferInstance inferInstance inferInstance
  unfold localize
  apply LinearMap.extendOfNorm_eq
  · exact smoothToCanonicalPhysicalScalarH1_denseRange period hPeriod
  · exact data.localizeBound patch

/-- Completion of smooth chart transport. The reconstruction identity is
propagated from the smooth core by continuity and density. -/
def toEuclideanRellichTransportData
    (data : CanonicalPhysicalScalarSmoothEuclideanRellichTransportData
      period hPeriod) :
    CanonicalPhysicalScalarEuclideanRellichTransportData
      period hPeriod where
  localize := data.localize period hPeriod
  extend := data.extend
  factorization := by
    let lhs :=
      canonicalPhysicalScalarH1ToBulkL2 period hPeriod
    let rhs :=
      ∑ patch : Patch period hPeriod,
        (data.extend patch).comp
          ((finiteAtlasEuclideanRellichEmbedding
            period hPeriod).comp (data.localize period hPeriod patch))
    have hFunctions : (fun field => lhs field) = fun field => rhs field :=
      (smoothToCanonicalPhysicalScalarH1_denseRange
        period hPeriod).equalizer lhs.continuous rhs.continuous (by
          funext field
          simpa [lhs, rhs, localize_agrees_on_smooth] using
            data.factorizationCore field)
    apply ContinuousLinearMap.coe_injective
    apply LinearMap.ext
    intro field
    exact congrFun hFunctions field

end CanonicalPhysicalScalarSmoothEuclideanRellichTransportData

namespace CanonicalPhysicalScalarEuclideanRellichTransportData

/-- Forgetful map to the generic finite-patch gluing package. The local
compactness field is filled by the proved Euclidean theorem. -/
def toFinitePatchRellichData
    (data : CanonicalPhysicalScalarEuclideanRellichTransportData
      period hPeriod) :
    CanonicalPhysicalScalarFinitePatchRellichData
      period hPeriod
      (FiniteAtlasEuclideanH1 period hPeriod)
      FiniteAtlasEuclideanL2 where
  localize := data.localize
  localEmbedding := fun _ =>
    finiteAtlasEuclideanRellichEmbedding period hPeriod
  extend := data.extend
  localCompact := fun _ =>
    finiteAtlasEuclideanRellichEmbedding_isCompact period hPeriod
  factorization := data.factorization

/-- Exact chart transport and partition reconstruction now suffice for
physical Rellich compactness; local compactness is no longer assumed. -/
theorem rellich
    (data : CanonicalPhysicalScalarEuclideanRellichTransportData
      period hPeriod) :
    PhysicalH1RellichCompactness period hPeriod :=
  (data.toFinitePatchRellichData period hPeriod).rellich period hPeriod

/-- Reduced certificate: the only remaining obligations are the continuous
localization/extension maps and their exact finite reconstruction identity. -/
theorem certificate
    (data : CanonicalPhysicalScalarEuclideanRellichTransportData
      period hPeriod) :
    IsCompactOperator
        (finiteAtlasEuclideanRellichEmbedding period hPeriod) ∧
      canonicalPhysicalScalarH1ToBulkL2 period hPeriod =
        ∑ patch : Patch period hPeriod,
          (data.extend patch).comp
            ((finiteAtlasEuclideanRellichEmbedding
              period hPeriod).comp (data.localize patch)) ∧
      PhysicalH1RellichCompactness period hPeriod :=
  ⟨finiteAtlasEuclideanRellichEmbedding_isCompact period hPeriod,
    data.factorization, data.rellich period hPeriod⟩

end CanonicalPhysicalScalarEuclideanRellichTransportData

namespace CanonicalPhysicalScalarSmoothEuclideanRellichTransportData

/-- Smooth bounded chart transport already implies physical Rellich
compactness. -/
theorem rellich
    (data : CanonicalPhysicalScalarSmoothEuclideanRellichTransportData
      period hPeriod) :
    PhysicalH1RellichCompactness period hPeriod :=
  (data.toEuclideanRellichTransportData period hPeriod).rellich
    period hPeriod

end CanonicalPhysicalScalarSmoothEuclideanRellichTransportData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarFinitePatchRellichReduction4D
end JanusFormal
