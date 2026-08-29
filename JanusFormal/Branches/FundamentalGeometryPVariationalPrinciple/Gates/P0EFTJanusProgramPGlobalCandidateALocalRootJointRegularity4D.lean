import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAPositiveSelectedRootSylvester4D

/-!
# Joint regularity of a selected local root family

The strong root branch already lives in a `C⁰ ∩ H¹` Banach algebra.  This
gate records the missing composition step: a `C²` target family pulls the open
inverse branch back to an open parameter domain, and every matrix coefficient
is jointly continuous in the parameter and spacetime point.  No separate
joint-regularity axiom is introduced.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateALocalRootJointRegularity4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

open MeasureTheory Set Topology
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0CoreClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0FiniteMatrixProduct4D
open P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameCornerLocalRoot4D

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

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance physicalMeasureFinite :
    IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

local instance strongCoreNormedAddCommGroup :
    NormedAddCommGroup
      (CanonicalPhysicalScalarStrongH1C0Core period hPeriod) :=
  (canonicalPhysicalScalarStrongH1C0CoreSubmodule
    period hPeriod).normedAddCommGroup

local instance strongCoreNormedSpace :
    NormedSpace Real
      (CanonicalPhysicalScalarStrongH1C0Core period hPeriod) :=
  inferInstance

local instance strongCoreCompleteSpace :
    CompleteSpace
      (CanonicalPhysicalScalarStrongH1C0Core period hPeriod) :=
  canonicalPhysicalScalarStrongH1C0CoreCompleteSpace period hPeriod

/-! ## Generic pullback of an open inverse branch -/

def localC2InverseOpenBranchPullbackDomain
    {E Model : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E]
    [NormedAddCommGroup Model] [NormedSpace Real Model]
    {map : E → E} {center : E}
    (branch : LocalC2InverseOpenBranch E map center)
    (target : Model → E) : Set Model :=
  target ⁻¹' branch.domain

theorem localC2InverseOpenBranchPullbackDomain_isOpen
    {E Model : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E]
    [NormedAddCommGroup Model] [NormedSpace Real Model]
    {map : E → E} {center : E}
    (branch : LocalC2InverseOpenBranch E map center)
    (target : Model → E) (hTarget : ContDiff Real 2 target) :
    IsOpen (localC2InverseOpenBranchPullbackDomain branch target) :=
  branch.domain_isOpen.preimage hTarget.continuous

theorem localC2InverseOpenBranchComp_contDiffOn_pullbackDomain
    {E Model : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E]
    [NormedAddCommGroup Model] [NormedSpace Real Model]
    {map : E → E} {center : E}
    (branch : LocalC2InverseOpenBranch E map center)
    (target : Model → E) (hTarget : ContDiff Real 2 target) :
    ContDiffOn Real 2 (branch.branch ∘ target)
      (localC2InverseOpenBranchPullbackDomain branch target) := by
  exact branch.branch_contDiffOn.comp hTarget.contDiffOn
    (fun _ hPoint => hPoint)

theorem localC2InverseOpenBranchComp_rightInverse_on_pullbackDomain
    {E Model : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E]
    [NormedAddCommGroup Model] [NormedSpace Real Model]
    {map : E → E} {center : E}
    (branch : LocalC2InverseOpenBranch E map center)
    (target : Model → E) (point : Model)
    (hPoint : point ∈
      localC2InverseOpenBranchPullbackDomain branch target) :
    map (branch.branch (target point)) = map center + target point :=
  branch.branch_rightInverse (target point) hPoint

/-! ## From strong-field continuity to joint parameter--spacetime continuity -/

theorem strongScalarFamily_jointContinuous
    {Parameter : Type*} [TopologicalSpace Parameter]
    (domain : Set Parameter)
    (family : Parameter →
      CanonicalPhysicalScalarStrongH1C0Core period hPeriod)
    (hFamily : ContinuousOn family domain) :
    Continuous
      (fun input : domain × EffectiveQuotient period hPeriod =>
        canonicalPhysicalScalarStrongH1C0CoreToContinuous
          period hPeriod (family input.1.1) input.2) := by
  have hRestricted : Continuous (domain.restrict family) := hFamily.restrict
  have hContinuousFamily : Continuous
      (fun point : domain =>
        canonicalPhysicalScalarStrongH1C0CoreToContinuous
          period hPeriod (family point.1)) :=
    (canonicalPhysicalScalarStrongH1C0CoreToContinuous
      period hPeriod).continuous.comp hRestricted
  exact (hContinuousFamily.comp continuous_fst).eval continuous_snd

theorem strongFiniteMatrixFamily_jointContinuous
    {Parameter : Type*} [TopologicalSpace Parameter]
    (dimension : Nat) (domain : Set Parameter)
    (family : Parameter → StrongFiniteMatrix period hPeriod dimension)
    (hFamily : ContinuousOn family domain)
    (row column : Fin dimension) :
    Continuous
      (fun input : domain × EffectiveQuotient period hPeriod =>
        canonicalPhysicalScalarStrongH1C0CoreToContinuous
          period hPeriod (family input.1.1 row column) input.2) := by
  have hCoefficientOn : ContinuousOn
      (fun point => family point row column) domain := by
    exact ((continuous_apply column).comp (continuous_apply row)).continuousOn.comp
      hFamily (mapsTo_univ _ _)
  exact strongScalarFamily_jointContinuous period hPeriod domain
    (fun point => family point row column) hCoefficientOn

/-- A strong `C²` local square-root branch automatically has joint continuous
matrix coefficients on its pulled-back admissible parameter domain. -/
theorem localC2InverseOpenBranch_strongFiniteMatrix_jointContinuous
    {Model : Type*}
    [NormedAddCommGroup Model] [NormedSpace Real Model]
    (dimension : Nat)
    {map : StrongFiniteMatrix period hPeriod dimension →
      StrongFiniteMatrix period hPeriod dimension}
    {center : StrongFiniteMatrix period hPeriod dimension}
    (branch : LocalC2InverseOpenBranch
      (StrongFiniteMatrix period hPeriod dimension) map center)
    (target : Model → StrongFiniteMatrix period hPeriod dimension)
    (hTarget : ContDiff Real 2 target)
    (row column : Fin dimension) :
    Continuous
      (fun input : localC2InverseOpenBranchPullbackDomain branch target ×
          EffectiveQuotient period hPeriod =>
        canonicalPhysicalScalarStrongH1C0CoreToContinuous
          period hPeriod
          (branch.branch (target input.1.1) row column) input.2) := by
  exact strongFiniteMatrixFamily_jointContinuous period hPeriod dimension
    (localC2InverseOpenBranchPullbackDomain branch target)
    (branch.branch ∘ target)
    (localC2InverseOpenBranchComp_contDiffOn_pullbackDomain
      branch target hTarget).continuousOn
    row column

end
end P0EFTJanusProgramPGlobalCandidateALocalRootJointRegularity4D
end JanusFormal
