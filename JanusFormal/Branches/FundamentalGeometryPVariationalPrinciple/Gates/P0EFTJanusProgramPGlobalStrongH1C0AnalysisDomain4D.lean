import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0CoreClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalAnalysisDomain4D

/-!
# Strong `C⁰ ∩ H¹` bulk analysis domain

The existing finite bulk Sobolev slot type already contains all metric, gauge
and ghost coefficient coordinates. Applying the scalar strong equalizer to
each slot gives a complete bulk Banach space with compatible continuous and
intrinsic `H¹` projections. The genuine smooth global tangent has its exact
coordinatewise lift into this space.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalStrongH1C0AnalysisDomain4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarSmoothL2Density4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicH1CoerciveVariationalClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0Space4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0CoreClosure4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev ContinuousScalar :=
  C(EffectiveQuotient period hPeriod, Real)

local instance scalarStrongH1C0CompleteSpace :
    CompleteSpace (CanonicalPhysicalScalarStrongH1C0 period hPeriod) :=
  canonicalPhysicalScalarStrongH1C0CompleteSpace period hPeriod

local instance scalarStrongH1C0CoreCompleteSpace :
    CompleteSpace (CanonicalPhysicalScalarStrongH1C0Core period hPeriod) :=
  canonicalPhysicalScalarStrongH1C0CoreCompleteSpace period hPeriod

/-- Finite product of continuous bulk coefficient fields. -/
abbrev GlobalBulkContinuousC0 :=
  GlobalBulkSobolevSlot period hPeriod → ContinuousScalar period hPeriod

/-- Finite product of physical bulk `L²` coefficient fields. -/
abbrev GlobalBulkPhysicalL2 :=
  GlobalBulkSobolevSlot period hPeriod →
    CanonicalPhysicalBulkL2 period hPeriod

/-- Strong bulk domain obtained from the scalar `C⁰ ∩ H¹` equalizer on every
existing metric, gauge and ghost coordinate slot. -/
abbrev GlobalBulkStrongH1C0 :=
  GlobalBulkSobolevSlot period hPeriod →
    CanonicalPhysicalScalarStrongH1C0 period hPeriod

/-- Independent smooth scalar families on the existing finite bulk slots. -/
abbrev GlobalBulkSmoothScalarFamily :=
  GlobalBulkSobolevSlot period hPeriod →
    SmoothQuotientField period hPeriod Real

/-- Coordinatewise smooth-core closure inside the global strong product. -/
abbrev GlobalBulkStrongH1C0Core :=
  GlobalBulkSobolevSlot period hPeriod →
    CanonicalPhysicalScalarStrongH1C0Core period hPeriod

@[implicit_reducible]
def globalBulkStrongH1C0CompleteSpace :
    CompleteSpace (GlobalBulkStrongH1C0 period hPeriod) :=
  inferInstance

@[implicit_reducible]
def globalBulkStrongH1C0CoreCompleteSpace :
    CompleteSpace (GlobalBulkStrongH1C0Core period hPeriod) :=
  inferInstance

/-- Coordinatewise lift of an independent smooth bulk scalar family. -/
def globalBulkSmoothToStrongH1C0Core :
    GlobalBulkSmoothScalarFamily period hPeriod →ₗ[Real]
      GlobalBulkStrongH1C0Core period hPeriod where
  toFun fields slot :=
    smoothToCanonicalPhysicalScalarStrongH1C0Core
      period hPeriod (fields slot)
  map_add' first second := by
    funext slot
    exact (smoothToCanonicalPhysicalScalarStrongH1C0Core
      period hPeriod).map_add (first slot) (second slot)
  map_smul' scalar fields := by
    funext slot
    exact (smoothToCanonicalPhysicalScalarStrongH1C0Core
      period hPeriod).map_smul scalar (fields slot)

theorem globalBulkSmoothToStrongH1C0Core_denseRange :
    DenseRange (globalBulkSmoothToStrongH1C0Core period hPeriod) := by
  exact DenseRange.piMap fun _ =>
    smoothToCanonicalPhysicalScalarStrongH1C0Core_denseRange
      period hPeriod

/-- Coordinatewise inclusion of the dense strong core into the ambient
equalizer product. -/
def globalBulkStrongH1C0CoreToStrong :
    GlobalBulkStrongH1C0Core period hPeriod →L[Real]
      GlobalBulkStrongH1C0 period hPeriod :=
  ContinuousLinearMap.piMap fun _ =>
    canonicalPhysicalScalarStrongH1C0CoreToStrong period hPeriod

/-- Coordinatewise continuous representative. -/
def globalBulkStrongH1C0ToContinuous :
    GlobalBulkStrongH1C0 period hPeriod →L[Real]
      GlobalBulkContinuousC0 period hPeriod :=
  ContinuousLinearMap.piMap fun _ =>
    canonicalPhysicalScalarStrongH1C0ToContinuous period hPeriod

/-- Coordinatewise intrinsic `H¹` representative. -/
def globalBulkStrongH1C0ToHilbertH1 :
    GlobalBulkStrongH1C0 period hPeriod →L[Real]
      GlobalBulkHilbertH1 period hPeriod :=
  ContinuousLinearMap.piMap fun _ =>
    canonicalPhysicalScalarStrongH1C0ToHilbertH1 period hPeriod

/-- Physical `L²` representative obtained through the continuous projection. -/
def globalBulkStrongH1C0ToBulkL2FromContinuous :
    GlobalBulkStrongH1C0 period hPeriod →L[Real]
      GlobalBulkPhysicalL2 period hPeriod :=
  ContinuousLinearMap.piMap fun _ =>
    (continuousToCanonicalPhysicalBulkL2 period hPeriod).comp
      (canonicalPhysicalScalarStrongH1C0ToContinuous period hPeriod)

/-- Physical `L²` representative obtained through the `H¹` projection. -/
def globalBulkStrongH1C0ToBulkL2FromHilbertH1 :
    GlobalBulkStrongH1C0 period hPeriod →L[Real]
      GlobalBulkPhysicalL2 period hPeriod :=
  ContinuousLinearMap.piMap fun _ =>
    (canonicalPhysicalScalarHilbertH1ToBulkL2 period hPeriod).comp
      (canonicalPhysicalScalarStrongH1C0ToHilbertH1 period hPeriod)

theorem globalBulkStrongH1C0_l2_compatibility
    (field : GlobalBulkStrongH1C0 period hPeriod) :
    globalBulkStrongH1C0ToBulkL2FromContinuous period hPeriod field =
      globalBulkStrongH1C0ToBulkL2FromHilbertH1 period hPeriod field := by
  funext slot
  exact canonicalPhysicalScalarStrongH1C0_l2_compatibility
    period hPeriod (field slot)

/-- Exact strong lift of the genuine smooth global tangent. -/
def GlobalFieldTangent.bulkStrongH1C0
    {configuration : GlobalFieldConfiguration period hPeriod}
    (variation : GlobalFieldTangent period hPeriod configuration) :
    GlobalBulkStrongH1C0 period hPeriod :=
  fun slot =>
    smoothToCanonicalPhysicalScalarStrongH1C0 period hPeriod
      (GlobalFieldTangent.bulkSmoothCoordinate
        period hPeriod variation slot)

/-- Exact lift of the genuine smooth global tangent into the dense strong
core product. -/
def GlobalFieldTangent.bulkStrongH1C0Core
    {configuration : GlobalFieldConfiguration period hPeriod}
    (variation : GlobalFieldTangent period hPeriod configuration) :
    GlobalBulkStrongH1C0Core period hPeriod :=
  fun slot =>
    smoothToCanonicalPhysicalScalarStrongH1C0Core period hPeriod
      (GlobalFieldTangent.bulkSmoothCoordinate
        period hPeriod variation slot)

@[simp]
theorem globalBulkStrongH1C0CoreToStrong_agrees_on_globalTangent
    {configuration : GlobalFieldConfiguration period hPeriod}
    (variation : GlobalFieldTangent period hPeriod configuration) :
    globalBulkStrongH1C0CoreToStrong period hPeriod
        (GlobalFieldTangent.bulkStrongH1C0Core
          period hPeriod variation) =
      GlobalFieldTangent.bulkStrongH1C0 period hPeriod variation :=
  rfl

@[simp]
theorem globalBulkStrongH1C0ToContinuous_agrees_on_globalTangent
    {configuration : GlobalFieldConfiguration period hPeriod}
    (variation : GlobalFieldTangent period hPeriod configuration)
    (slot : GlobalBulkSobolevSlot period hPeriod) :
    globalBulkStrongH1C0ToContinuous period hPeriod
        (GlobalFieldTangent.bulkStrongH1C0
          period hPeriod variation) slot =
      smoothToCanonicalPhysicalContinuousScalar period hPeriod
        (GlobalFieldTangent.bulkSmoothCoordinate
          period hPeriod variation slot) :=
  rfl

@[simp]
theorem globalBulkStrongH1C0ToHilbertH1_agrees_on_globalTangent
    {configuration : GlobalFieldConfiguration period hPeriod}
    (variation : GlobalFieldTangent period hPeriod configuration) :
    globalBulkStrongH1C0ToHilbertH1 period hPeriod
        (GlobalFieldTangent.bulkStrongH1C0
          period hPeriod variation) =
      GlobalFieldTangent.bulkHilbertH1 period hPeriod variation :=
  rfl

/-- Summary gate for the finite bulk strong domain. -/
theorem global_bulk_strong_h1_c0_analysis_domain_gate :
    (∀ field : GlobalBulkStrongH1C0 period hPeriod,
      globalBulkStrongH1C0ToBulkL2FromContinuous period hPeriod field =
        globalBulkStrongH1C0ToBulkL2FromHilbertH1 period hPeriod field) ∧
      DenseRange (globalBulkSmoothToStrongH1C0Core period hPeriod) ∧
      (∀ (configuration : GlobalFieldConfiguration period hPeriod)
        (variation : GlobalFieldTangent period hPeriod configuration),
        globalBulkStrongH1C0ToHilbertH1 period hPeriod
            (GlobalFieldTangent.bulkStrongH1C0
              period hPeriod variation) =
          GlobalFieldTangent.bulkHilbertH1 period hPeriod variation) := by
  exact ⟨globalBulkStrongH1C0_l2_compatibility period hPeriod,
    globalBulkSmoothToStrongH1C0Core_denseRange period hPeriod,
    fun _ variation =>
      globalBulkStrongH1C0ToHilbertH1_agrees_on_globalTangent
        period hPeriod variation⟩

end

end P0EFTJanusProgramPGlobalStrongH1C0AnalysisDomain4D
end JanusFormal
