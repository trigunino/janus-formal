import Mathlib.Analysis.Normed.Operator.Banach
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameCornerAlgebra4D

/-!
# Local root chart in the Candidate-A finite-frame projector corner

A reusable inverse-function certificate first constructs a zero-centered
local `C²` inverse germ for any Banach-space map with invertible derivative.
It is then applied to squaring in the complete finite-frame projector corner.
No global tangent frame or additional geometric assumption is introduced.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameCornerLocalRoot4D

set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option synthInstance.maxHeartbeats 500000

noncomputable section

open scoped Manifold ContDiff Topology BigOperators
open MeasureTheory Set Topology Filter TopologicalSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0Space4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0CoreClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0FiniteMatrixProduct4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameCorner4D
open P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameCornerAlgebra4D

/-- Data and proofs carried by a zero-centered local `C²` inverse germ. -/
structure LocalC2InverseGerm
    (E : Type*) [NormedAddCommGroup E] [NormedSpace Real E]
    (map : E → E) (center : E) where
  domain : Set E
  branch : E → E
  domain_isOpen : IsOpen domain
  zero_mem_domain : (0 : E) ∈ domain
  branch_contDiffAt_zero : ContDiffAt Real 2 branch 0
  branch_rightInverse : ∀ variation, variation ∈ domain →
    map (branch variation) = map center + variation

/-- Existence of a zero-centered local `C²` inverse germ. -/
def HasLocalC2InverseGerm
    (E : Type*) [NormedAddCommGroup E] [NormedSpace Real E]
    (map : E → E) (center : E) : Prop :=
  Nonempty (LocalC2InverseGerm E map center)

section GenericLocalInverse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [CompleteSpace E]
variable (map : E → E) (center : E) (equiv : E ≃L[Real] E)
variable (hSmooth : ContDiffAt Real 2 map center)
variable (hDerivative : HasFDerivAt map (equiv : E →L[Real] E) center)

private def localC2InverseChart : OpenPartialHomeomorph E E :=
  hSmooth.toOpenPartialHomeomorph map hDerivative (by norm_num)

private def localC2InverseDomain : Set E :=
  (fun variation => map center + variation) ⁻¹'
    (localC2InverseChart map center equiv hSmooth hDerivative).target

private def localC2InverseBranch : E → E :=
  hSmooth.localInverse hDerivative (by norm_num) ∘
    fun variation => map center + variation

/-- Banach inverse-function theorem in the exact zero-centered form needed by
the Hessian construction. -/
def localC2InverseGerm : LocalC2InverseGerm E map center := by
  refine LocalC2InverseGerm.mk
    (localC2InverseDomain map center equiv hSmooth hDerivative)
    (localC2InverseBranch map center equiv hSmooth hDerivative) ?_ ?_ ?_ ?_
  · exact (localC2InverseChart map center equiv hSmooth hDerivative).open_target
      |>.preimage (continuous_const.add continuous_id)
  · change map center + 0 ∈
      (localC2InverseChart map center equiv hSmooth hDerivative).target
    simpa only [add_zero, localC2InverseChart] using
      hSmooth.image_mem_toOpenPartialHomeomorph_target hDerivative (by norm_num)
  · have hOuter := hSmooth.to_localInverse hDerivative (by norm_num)
    have hOuter' : ContDiffAt Real 2
        (hSmooth.localInverse hDerivative (by norm_num))
        (map center + (0 : E)) := by
      simpa only [add_zero] using hOuter
    exact hOuter'.comp 0 (contDiffAt_const.add contDiffAt_id)
  · intro variation hVariation
    change map center + variation ∈
      (localC2InverseChart map center equiv hSmooth hDerivative).target at hVariation
    change map
      ((localC2InverseChart map center equiv hSmooth hDerivative).symm
        (map center + variation)) = map center + variation
    exact (localC2InverseChart
      map center equiv hSmooth hDerivative).right_inv hVariation

end GenericLocalInverse

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev StrongScalar :=
  CanonicalPhysicalScalarStrongH1C0Core period hPeriod

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

local instance effectiveQuotientMetrizableSpace :
    MetrizableSpace (EffectiveQuotient period hPeriod) :=
  Manifold.metrizableSpace coverModelWithCorners _

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

private abbrev physicalMeasure :=
  intrinsicCanonicalLorentzVolumeMeasure period hPeriod

local instance physicalMeasureFinite :
    IsFiniteMeasure (physicalMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

local instance strongCoreNormedAddCommGroup :
    NormedAddCommGroup (StrongScalar period hPeriod) :=
  (canonicalPhysicalScalarStrongH1C0CoreSubmodule
    period hPeriod).normedAddCommGroup

local instance strongCoreNormedSpace :
    NormedSpace Real (StrongScalar period hPeriod) :=
  inferInstance

local instance strongCoreCompleteSpace :
    CompleteSpace (StrongScalar period hPeriod) :=
  canonicalPhysicalScalarStrongH1C0CoreCompleteSpace period hPeriod

local instance strongFiniteFrameCornerNormedAddCommGroup
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    NormedAddCommGroup
      (StrongFiniteFrameCorner period hPeriod frame metric) :=
  (strongFiniteFrameCornerSubmodule
    period hPeriod frame metric).normedAddCommGroup

local instance strongFiniteFrameCornerNormedSpace
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (StrongFiniteFrameCorner period hPeriod frame metric) :=
  inferInstance

local instance strongFiniteFrameCornerCompleteSpaceInstance
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    CompleteSpace (StrongFiniteFrameCorner period hPeriod frame metric) :=
  strongFiniteFrameCornerCompleteSpace period hPeriod frame metric

/-- A bijective corner Sylvester operator is a bounded linear equivalence. -/
def strongFiniteFrameCornerSylvesterEquivOfBijective
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (root : StrongFiniteFrameCorner period hPeriod frame metric)
    (hRegular : Function.Bijective
      (strongFiniteFrameCornerSylvester period hPeriod frame metric root)) :
    StrongFiniteFrameCorner period hPeriod frame metric ≃L[Real]
      StrongFiniteFrameCorner period hPeriod frame metric :=
  ContinuousLinearEquiv.ofBijective
    (strongFiniteFrameCornerSylvester period hPeriod frame metric root)
    (LinearMap.ker_eq_bot.mpr hRegular.1)
    (LinearMap.range_eq_top.mpr hRegular.2)

theorem strongFiniteFrameCornerSylvesterEquiv_forward_eq
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (root : StrongFiniteFrameCorner period hPeriod frame metric)
    (hRegular : Function.Bijective
      (strongFiniteFrameCornerSylvester period hPeriod frame metric root)) :
    (strongFiniteFrameCornerSylvesterEquivOfBijective
        period hPeriod frame metric root hRegular :
      StrongFiniteFrameCorner period hPeriod frame metric →L[Real]
        StrongFiniteFrameCorner period hPeriod frame metric) =
      strongFiniteFrameCornerSylvester period hPeriod frame metric root :=
  rfl

/-- Continuous family of corner Sylvester derivatives. -/
def strongFiniteFrameCornerSylvesterFamily
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    StrongFiniteFrameCorner period hPeriod frame metric →
      StrongFiniteFrameCorner period hPeriod frame metric →L[Real]
        StrongFiniteFrameCorner period hPeriod frame metric :=
  fun root => strongFiniteFrameCornerSylvester
    period hPeriod frame metric root

theorem strongFiniteFrameCornerSylvesterFamily_continuous
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    Continuous (strongFiniteFrameCornerSylvesterFamily
      period hPeriod frame metric) := by
  change Continuous (fun root =>
    strongFiniteFrameCornerProduct period hPeriod frame metric root +
      (strongFiniteFrameCornerProduct
        period hPeriod frame metric).flip root)
  exact (strongFiniteFrameCornerProduct
    period hPeriod frame metric).continuous.add
      (strongFiniteFrameCornerProduct
        period hPeriod frame metric).flip.continuous

/-- Open locus where the corner Sylvester derivative is invertible. -/
def strongFiniteFrameCornerSylvesterRegularRootSet
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    Set (StrongFiniteFrameCorner period hPeriod frame metric) :=
  strongFiniteFrameCornerSylvesterFamily period hPeriod frame metric ⁻¹'
    Set.range ((↑) :
      (StrongFiniteFrameCorner period hPeriod frame metric ≃L[Real]
        StrongFiniteFrameCorner period hPeriod frame metric) →
      StrongFiniteFrameCorner period hPeriod frame metric →L[Real]
        StrongFiniteFrameCorner period hPeriod frame metric)

theorem strongFiniteFrameCornerSylvesterRegularRootSet_isOpen
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    IsOpen (strongFiniteFrameCornerSylvesterRegularRootSet
      period hPeriod frame metric) := by
  apply ContinuousLinearEquiv.isOpen.preimage
  exact strongFiniteFrameCornerSylvesterFamily_continuous
    period hPeriod frame metric

theorem strongFiniteFrameCornerSquare_contDiff_two
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    ContDiff Real 2
      (strongFiniteFrameCornerSquare period hPeriod frame metric) :=
  (strongFiniteFrameCornerSquare_contDiff period hPeriod frame metric).of_le
    (by norm_num)

/-- The generic Banach inverse germ specialized to the strong projector
corner. -/
def strongFiniteFrameCornerLocalRootGerm
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (root : StrongFiniteFrameCorner period hPeriod frame metric)
    (hRegular : Function.Bijective
      (strongFiniteFrameCornerSylvester period hPeriod frame metric root)) :
    LocalC2InverseGerm
      (StrongFiniteFrameCorner period hPeriod frame metric)
      (strongFiniteFrameCornerSquare period hPeriod frame metric) root :=
  localC2InverseGerm
    (strongFiniteFrameCornerSquare period hPeriod frame metric) root
    (strongFiniteFrameCornerSylvesterEquivOfBijective
      period hPeriod frame metric root hRegular)
    (strongFiniteFrameCornerSquare_contDiff_two
      period hPeriod frame metric).contDiffAt
    ((strongFiniteFrameCornerSquare_hasFDerivAt
      period hPeriod frame metric root).congr_fderiv
        (strongFiniteFrameCornerSylvesterEquiv_forward_eq
          period hPeriod frame metric root hRegular).symm)

/-- A local `C²` root germ exists on an open neighborhood of zero in the
complete strong projector corner. -/
theorem strong_finite_frame_corner_local_root_gate
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (root : StrongFiniteFrameCorner period hPeriod frame metric)
    (hRegular : Function.Bijective
      (strongFiniteFrameCornerSylvester period hPeriod frame metric root)) :
    HasLocalC2InverseGerm
      (StrongFiniteFrameCorner period hPeriod frame metric)
      (strongFiniteFrameCornerSquare period hPeriod frame metric) root := by
  exact ⟨strongFiniteFrameCornerLocalRootGerm
    period hPeriod frame metric root hRegular⟩

/-- Candidate-A specialization of the local corner root germ. -/
theorem global_candidate_a_strong_finite_frame_corner_local_root_gate
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (frame : SmoothD8Frame period hPeriod)
    (hRegular : Function.Bijective
      (strongFiniteFrameCornerSylvester
        period hPeriod frame geometry.plusMetric
        (strongGlobalCandidateAFiniteFrameRootCorner
          period hPeriod geometry frame))) :
    HasLocalC2InverseGerm
      (StrongFiniteFrameCorner period hPeriod frame geometry.plusMetric)
      (strongFiniteFrameCornerSquare
        period hPeriod frame geometry.plusMetric)
      (strongGlobalCandidateAFiniteFrameRootCorner
        period hPeriod geometry frame) := by
  exact strong_finite_frame_corner_local_root_gate
    period hPeriod frame geometry.plusMetric
    (strongGlobalCandidateAFiniteFrameRootCorner
      period hPeriod geometry frame) hRegular

/-- A zero-centered inverse branch which is C² on its whole open domain. -/
structure LocalC2InverseOpenBranch
    (E : Type*) [NormedAddCommGroup E] [NormedSpace Real E]
    (map : E → E) (center : E) where
  domain : Set E
  branch : E → E
  domain_isOpen : IsOpen domain
  zero_mem_domain : (0 : E) ∈ domain
  branch_contDiffOn : ContDiffOn Real 2 branch domain
  branch_rightInverse : ∀ variation, variation ∈ domain →
    map (branch variation) = map center + variation

def HasLocalC2InverseOpenBranch
    (E : Type*) [NormedAddCommGroup E] [NormedSpace Real E]
    (map : E → E) (center : E) : Prop :=
  Nonempty (LocalC2InverseOpenBranch E map center)

section GenericOpenLocalInverse

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
  [CompleteSpace F]

/-- The existing IFT chart, restricted to points where the derivative remains
a bounded equivalence, yields a branch smooth on the whole target. -/
def regularLocalC2InverseOpenBranch
    (map : F → F) (center : F)
    (derivative : F → F →L[Real] F)
    (equiv : F ≃L[Real] F)
    (hForward : (equiv : F →L[Real] F) = derivative center)
    (hMap : ContDiff Real 2 map)
    (hDerivative : ∀ point, HasFDerivAt map (derivative point) point)
    (hDerivativeContinuous : Continuous derivative) :
    LocalC2InverseOpenBranch F map center := by
  let regularSet : Set F :=
    derivative ⁻¹' Set.range ((↑) : (F ≃L[Real] F) → (F →L[Real] F))
  have hRegularSetOpen : IsOpen regularSet := by
    exact ContinuousLinearEquiv.isOpen.preimage hDerivativeContinuous
  let baseChart : OpenPartialHomeomorph F F :=
    hMap.contDiffAt.toOpenPartialHomeomorph map
      ((hDerivative center).congr_fderiv hForward.symm) (by norm_num)
  let chart : OpenPartialHomeomorph F F :=
    baseChart.restrOpen regularSet hRegularSetOpen
  have hCenterSource : center ∈ chart.source := by
    rw [show chart = baseChart.restrOpen regularSet hRegularSetOpen by rfl,
      OpenPartialHomeomorph.restrOpen_source]
    exact ⟨hMap.contDiffAt.mem_toOpenPartialHomeomorph_source
        ((hDerivative center).congr_fderiv hForward.symm) (by norm_num),
      ⟨equiv, hForward⟩⟩
  have hMapCenterTarget : map center ∈ chart.target := by
    exact chart.map_source hCenterSource
  let domain : Set F :=
    (fun variation => map center + variation) ⁻¹' chart.target
  let branch : F → F :=
    fun variation => chart.symm (map center + variation)
  refine {
    domain := domain
    branch := branch
    domain_isOpen := chart.open_target.preimage
      (continuous_const.add continuous_id)
    zero_mem_domain := by
      simpa [domain] using hMapCenterTarget
    branch_contDiffOn := ?_
    branch_rightInverse := ?_
  }
  · intro variation hVariation
    have hNearby : map center + variation ∈ chart.target := hVariation
    have hSource := chart.map_target hNearby
    have hSourceRegular : chart.symm (map center + variation) ∈ regularSet := by
      rw [show chart = baseChart.restrOpen regularSet hRegularSetOpen by rfl,
        OpenPartialHomeomorph.restrOpen_source] at hSource
      exact hSource.2
    rcases hSourceRegular with ⟨pointEquiv, hPointEquiv⟩
    have hOuter : ContDiffAt Real 2 chart.symm (map center + variation) := by
      apply chart.contDiffAt_symm hNearby (f₀' := pointEquiv)
      · exact (hDerivative (chart.symm (map center + variation))).congr_fderiv
          hPointEquiv.symm
      · exact hMap.contDiffAt
    have hInner : ContDiffAt Real 2
        (fun current : F => map center + current) variation :=
      contDiffAt_const.add contDiffAt_id
    change ContDiffWithinAt Real 2
      (chart.symm ∘ fun current : F => map center + current) domain variation
    exact (hOuter.comp variation hInner).contDiffWithinAt
  · intro variation hVariation
    exact chart.right_inv hVariation

end GenericOpenLocalInverse

/-- The complete strong-corner certificate exposes one open perturbation
domain, a C² branch on all of it, and the exact square identity. -/
theorem strong_finite_frame_corner_contDiff_local_root_gate
    (frame : SmoothD8Frame period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (root : StrongFiniteFrameCorner period hPeriod frame metric)
    (hRegular : Function.Bijective
      (strongFiniteFrameCornerSylvester period hPeriod frame metric root)) :
    HasLocalC2InverseOpenBranch
      (StrongFiniteFrameCorner period hPeriod frame metric)
      (strongFiniteFrameCornerSquare period hPeriod frame metric) root := by
  let equiv := strongFiniteFrameCornerSylvesterEquivOfBijective
    period hPeriod frame metric root hRegular
  exact ⟨regularLocalC2InverseOpenBranch
    (strongFiniteFrameCornerSquare period hPeriod frame metric) root
    (strongFiniteFrameCornerSylvesterFamily period hPeriod frame metric)
    equiv
    (strongFiniteFrameCornerSylvesterEquiv_forward_eq
      period hPeriod frame metric root hRegular)
    (strongFiniteFrameCornerSquare_contDiff_two period hPeriod frame metric)
    (strongFiniteFrameCornerSquare_hasFDerivAt period hPeriod frame metric)
    (strongFiniteFrameCornerSylvesterFamily_continuous
      period hPeriod frame metric)⟩

theorem global_candidate_a_strong_finite_frame_corner_contDiff_local_root_gate
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (frame : SmoothD8Frame period hPeriod)
    (hRegular : Function.Bijective
      (strongFiniteFrameCornerSylvester
        period hPeriod frame geometry.plusMetric
        (strongGlobalCandidateAFiniteFrameRootCorner
          period hPeriod geometry frame))) :
    HasLocalC2InverseOpenBranch
      (StrongFiniteFrameCorner period hPeriod frame geometry.plusMetric)
      (strongFiniteFrameCornerSquare
        period hPeriod frame geometry.plusMetric)
      (strongGlobalCandidateAFiniteFrameRootCorner
        period hPeriod geometry frame) :=
  strong_finite_frame_corner_contDiff_local_root_gate
    period hPeriod frame geometry.plusMetric
    (strongGlobalCandidateAFiniteFrameRootCorner
      period hPeriod geometry frame) hRegular

end
end P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameCornerLocalRoot4D
end JanusFormal
