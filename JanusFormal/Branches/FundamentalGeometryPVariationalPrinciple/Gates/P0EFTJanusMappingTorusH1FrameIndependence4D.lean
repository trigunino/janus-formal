import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusH1GraphFrameChange4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalH1HilbertRenorming4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusFixedAtlasHolonomicDensityEquivalence4D

/-!
# Frame independence of the graph-H¹ completion

Finite compact-patch changes with smooth, uniformly bounded coefficients give
equivalent graph norms and canonically equivalent completions.  The canonical
physical spanning family is also identified with its fixed-atlas localized
components.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusH1FrameIndependence4D

set_option autoImplicit false
noncomputable section

open scoped ENNReal Manifold ContDiff
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusFixedAtlasHolonomicDensityEquivalence4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarStaticH1FixedLocalEnergyReduction4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _
local instance : BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

universe u

variable (Fiber : Type u) [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]

/-- A finite compact-cover expression of `target` in `source`, smooth and
uniformly bounded on every patch. -/
structure CompactFiniteSmoothFrameChange
    (source target : SmoothD8Frame period hPeriod) where
  patchCount : Nat
  compactPatch : Fin patchCount → Set (EffectiveQuotient period hPeriod)
  isCompact_patch : ∀ patch, IsCompact (compactPatch patch)
  covers : ∀ point, ∃ patch, point ∈ compactPatch patch
  coefficient : Fin patchCount → EffectiveQuotient period hPeriod →
    Fin target.count → Fin source.count → Real
  coefficient_smoothOn : ∀ patch j i,
    ContMDiffOn coverModelWithCorners 𝓘(Real, Real) ∞
      (fun point => coefficient patch point j i) (compactPatch patch)
  vector_eq : ∀ patch point, point ∈ compactPatch patch → ∀ j,
    target.vectorAt point j =
      ∑ i, coefficient patch point j i • source.vectorAt point i
  bound : Real
  one_le_bound : 1 ≤ bound
  matrix_bound : ∀ patch point, point ∈ compactPatch patch →
    ∀ values : Fin source.count → Fiber,
      ‖fun j => ∑ i, coefficient patch point j i • values i‖ ≤ bound * ‖values‖

theorem frameDerivative_eq_patch_matrix
    (source target : SmoothD8Frame period hPeriod)
    (change : CompactFiniteSmoothFrameChange period hPeriod Fiber source target)
    (field : SmoothQuotientField period hPeriod Fiber)
    (point : EffectiveQuotient period hPeriod) :
    ∃ patch, point ∈ change.compactPatch patch ∧
      frameDerivative period hPeriod Fiber target field point =
        fun j => ∑ i, change.coefficient patch point j i •
          frameDerivative period hPeriod Fiber source field point i := by
  obtain ⟨patch, hPoint⟩ := change.covers point
  refine ⟨patch, hPoint, ?_⟩
  funext j
  rw [frameDerivative_eq_mfderiv, change.vector_eq patch point hPoint j, map_sum]
  simp only [map_smul, frameDerivative_eq_mfderiv]

theorem compactSmoothFirstJet_norm_le
    (source target : SmoothD8Frame period hPeriod)
    (change : CompactFiniteSmoothFrameChange period hPeriod Fiber source target)
    (field : SmoothQuotientField period hPeriod Fiber)
    (point : EffectiveQuotient period hPeriod) :
    ‖smoothFirstJet period hPeriod Fiber target field point‖ ≤
      change.bound * ‖smoothFirstJet period hPeriod Fiber source field point‖ := by
  obtain ⟨patch, hPoint, hDerivative⟩ :=
    frameDerivative_eq_patch_matrix period hPeriod Fiber source target change field point
  change max ‖field point‖
      ‖frameDerivative period hPeriod Fiber target field point‖ ≤
    change.bound * max ‖field point‖
      ‖frameDerivative period hPeriod Fiber source field point‖
  apply max_le
  · exact (le_max_left _ _).trans
      (le_mul_of_one_le_left
        ((norm_nonneg _).trans (le_max_left _ _)) change.one_le_bound)
  · rw [hDerivative]
    exact (change.matrix_bound patch point hPoint _).trans
      (mul_le_mul_of_nonneg_left (le_max_right _ _)
        (zero_le_one.trans change.one_le_bound))

theorem compactSmoothToH1Graph_norm_le
    (source target : SmoothD8Frame period hPeriod)
    (change : CompactFiniteSmoothFrameChange period hPeriod Fiber source target)
    (mu : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure mu]
    (field : SmoothQuotientField period hPeriod Fiber) :
    ‖smoothToH1GraphLinearMap period hPeriod Fiber target mu field‖ ≤
      change.bound *
        ‖smoothToH1GraphLinearMap period hPeriod Fiber source mu field‖ := by
  change ‖smoothFirstJetToL2 period hPeriod Fiber target mu field‖ ≤
    change.bound * ‖smoothFirstJetToL2 period hPeriod Fiber source mu field‖
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards
    [(smoothFirstJet_memLp period hPeriod Fiber target mu field).coeFn_toLp,
      (smoothFirstJet_memLp period hPeriod Fiber source mu field).coeFn_toLp]
    with point hTarget hSource
  change
    ‖(smoothFirstJetToL2 period hPeriod Fiber target mu field :
      EffectiveQuotient period hPeriod → _) point‖ ≤ _
  rw [show (smoothFirstJetToL2 period hPeriod Fiber target mu field :
      EffectiveQuotient period hPeriod → _) point =
        smoothFirstJet period hPeriod Fiber target field point by
      simpa only [smoothFirstJetToL2] using hTarget,
    show (smoothFirstJetToL2 period hPeriod Fiber source mu field :
      EffectiveQuotient period hPeriod → _) point =
        smoothFirstJet period hPeriod Fiber source field point by
      simpa only [smoothFirstJetToL2] using hSource]
  exact compactSmoothFirstJet_norm_le period hPeriod Fiber
    source target change field point

/-- Two reverse compact finite-cover changes canonically identify the graph
completions while acting as the identity on smooth fields. -/
def compactH1GraphFrameEquiv
    [CompleteSpace Fiber]
    (source target : SmoothD8Frame period hPeriod)
    (forward : CompactFiniteSmoothFrameChange period hPeriod Fiber source target)
    (backward : CompactFiniteSmoothFrameChange period hPeriod Fiber target source)
    (mu : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure mu] :
    H1GraphSpace period hPeriod Fiber source mu ≃L[Real]
      H1GraphSpace period hPeriod Fiber target mu := by
  letI : CompleteSpace (H1GraphSpace period hPeriod Fiber source mu) :=
    h1GraphCompleteSpace period hPeriod Fiber source mu
  letI : CompleteSpace (H1GraphSpace period hPeriod Fiber target mu) :=
    h1GraphCompleteSpace period hPeriod Fiber target mu
  exact (LinearEquiv.refl Real
    (SmoothQuotientField period hPeriod Fiber)).extend
      (smoothToH1GraphLinearMap period hPeriod Fiber source mu)
      (smoothToH1GraphLinearMap period hPeriod Fiber target mu)
      (smoothToH1Graph_denseRange period hPeriod Fiber source mu)
      ⟨forward.bound, compactSmoothToH1Graph_norm_le period hPeriod Fiber
        source target forward mu⟩
      (smoothToH1Graph_denseRange period hPeriod Fiber target mu)
      ⟨backward.bound, compactSmoothToH1Graph_norm_le period hPeriod Fiber
        target source backward mu⟩

@[simp] theorem compactH1GraphFrameEquiv_smooth
    [CompleteSpace Fiber]
    (source target : SmoothD8Frame period hPeriod)
    (forward : CompactFiniteSmoothFrameChange period hPeriod Fiber source target)
    (backward : CompactFiniteSmoothFrameChange period hPeriod Fiber target source)
    (mu : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure mu]
    (field : SmoothQuotientField period hPeriod Fiber) :
    compactH1GraphFrameEquiv period hPeriod Fiber source target forward backward mu
        (smoothToH1GraphLinearMap period hPeriod Fiber source mu field) =
      smoothToH1GraphLinearMap period hPeriod Fiber target mu field := by
  letI : CompleteSpace (H1GraphSpace period hPeriod Fiber source mu) :=
    h1GraphCompleteSpace period hPeriod Fiber source mu
  letI : CompleteSpace (H1GraphSpace period hPeriod Fiber target mu) :=
    h1GraphCompleteSpace period hPeriod Fiber target mu
  apply LinearEquiv.extend_eq

/-- The canonical physical graph derivative is exactly the corresponding
partition-localized fixed-atlas component. -/
theorem canonicalFrameDerivative_eq_fixedAtlasLocalized
    (field : SmoothQuotientField period hPeriod Real)
    (point : EffectiveQuotient period hPeriod)
    (index : FiniteTangentGeneratorIndex period hPeriod) :
    frameDerivative period hPeriod Real
        (finiteSmoothTangentFrame period hPeriod) field point
          (finiteTangentGeneratorIndexEquivFin period hPeriod index) =
      fixedAtlasLocalizedHolonomicComponent period hPeriod field point index :=
  finiteFrameDerivative_eq_fixedAtlasLocalizedComponent
    period hPeriod field point index

/-- Two-sided fixed-atlas/canonical-frame density comparison. -/
theorem canonicalFrame_fixedAtlas_density_equivalence
    (field : SmoothQuotientField period hPeriod Real)
    (point : EffectiveQuotient period hPeriod) :
    finiteFixedLocalJacobiDensity period hPeriod field point ≤
        fixedAtlasToGraphDensityConstant period hPeriod *
          fixedAtlasHolonomicDensity period hPeriod field point ∧
      fixedAtlasHolonomicDensity period hPeriod field point ≤
        graphToFixedAtlasDensityConstant period hPeriod *
          finiteFixedLocalJacobiDensity period hPeriod field point :=
  fixed_atlas_holonomic_density_equivalence4D_closure
    period hPeriod field point

end
end P0EFTJanusMappingTorusH1FrameIndependence4D
end JanusFormal
