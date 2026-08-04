import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalNormalDisplacementCollarOrthogonalLiftBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusEquivariantSmoothDescent4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicMetricBVThroatBracket4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusExplicitBoundaryDensityLedger
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGaussianNormalEmbeddedHypersurface
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalHolonomicRiemannNaturality4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionWinding4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusTubularBandToAmbientCoverDerivativeIsomorphism4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalTotalR4BallParametrization4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBoundaryTwoSheetOrientedCurrentIntegral4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteStratifiedBoundaryVariation
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCovariantAction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundaryC3MetricCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPThroatFiniteFrameReconstruction4D
import Mathlib.MeasureTheory.Function.L1Space.HasFiniteIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Normal-boundary same-action closure for global Candidate A

This is the sole P2 assembly file of `HESSIAN-GLOBAL-01`.  It first constructs
the metric genuinely induced by the existing normal collar graph from an
arbitrary smooth ambient Lorentz metric.  The construction is symmetric,
specializes exactly to the existing throat trace at zero displacement, and
defines the intrinsic non-null parameter domain without adding a supplied
boundary geometry.

The local extrinsic curvature is adapted to the unchanged GHY ledger and its
normal/orientation descent law is proved.  The canonical global metric unit
normal is smooth and deck-odd.  Its Gauss second fundamental form and mean
curvature are independent of the ambient holonomic chart.  The descended GHY
scalar is integrated on the genuine mobile two-sheet boundary with the
already constructed induced measure.  Joint `C²` extension to the metric and
normal cores and its second Fréchet derivative remain the explicit frontier.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 600000
set_option maxHeartbeats 1200000

noncomputable section

open scoped Manifold ContDiff Topology
open Bundle ContinuousLinearMap Filter MeasureTheory Module TopologicalSpace
open P0EFTJanusExplicitBoundaryDensityLedger
open P0EFTJanusFiniteStratifiedBoundaryVariation
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothThroatEmbedding
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusMappingTorusIntrinsicMetricBVThroatBracket4D
open P0EFTJanusMappingTorusIntrinsicMetricThroatNondegenerate4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCutBoundaryFirstSheetCurrentBridge4D
open P0EFTJanusMappingTorusCutBoundaryTwoSheetOrientedCurrentIntegral4D
open P0EFTJanusMappingTorusCanonicalNormalLiftContinuityReduction4D
open P0EFTJanusMappingTorusCanonicalLatitudeTubularCollarEmbedding4D
open P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionDeck4D
open P0EFTJanusEquatorialTubularDiffeomorph4D
open P0EFTJanusEquatorialTubularAmbientInverseJointSmooth4D
open P0EFTJanusMappingTorusCanonicalLatitudeTubularCollarEmbedding4D
open P0EFTJanusMappingTorusTubularBandToAmbientCoverDerivativeIsomorphism4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusCanonicalHolonomicAtlasCoverReduction4D
open P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D
open P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionThirdJet4D
open P0EFTJanusMappingTorusCanonicalHolonomicRiemannNaturality4D
open P0EFTJanusMappingTorusCanonicalTotalR4BallParametrization4D
open P0EFTJanusNormalBundleOrientationCover
open P0EFTJanusMappingTorusOrientationDoubleCover
open P0EFTJanusMappingTorusCutThroatBoundaryDoubleCover4D
open P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusSmoothNormalVectorBundle
open P0EFTJanusD8NormalBundleD9DisplacementBridge4D
open P0EFTJanusProgramPGlobalNormalDisplacementCollarGraph4D
open P0EFTJanusProgramPGlobalNormalDisplacementCollarJointSmooth4D
open P0EFTJanusProgramPGlobalNormalDisplacementCollarOrthogonalLiftBridge4D
open P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionWinding4D
open P0EFTJanusMappingTorusEquivariantSmoothDescent4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryC3MetricCore4D
open P0EFTJanusProgramPThroatFiniteFrameReconstruction4D
open P0EFTJanusProgramPGeneralMetricC2RelativeEndomorphism4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev EffectiveThroatCover :=
  MappingTorusCover (fixedEquatorData period hPeriod)

private abbrev OrientationBoundary :=
  CutThroatBoundary period hPeriod

private abbrev OrientationBoundaryCover :=
  MappingTorusCover (orientationDoubleData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance (priority := 20000) effectiveThroatCoverChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroatCover period hPeriod) :=
  fixedThroatCoverChartedSpace period hPeriod

local instance (priority := 20000) effectiveThroatCoverIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroatCover period hPeriod) :=
  fixedThroatCover_isManifold period hPeriod

local instance effectiveThroatCompactSpace :
    CompactSpace (EffectiveThroat period hPeriod) :=
  P0EFTJanusMappingTorusCompactQuotient.fixedThroatQuotientCompactSpace
    period hPeriod

local instance effectiveThroatMeasurableSpace :
    MeasurableSpace (EffectiveThroat period hPeriod) := borel _

local instance effectiveThroatBorelSpace :
    BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

local instance orientationBoundaryCoverChartedSpace :
    ChartedSpace ThroatCoverModel (OrientationBoundaryCover period hPeriod) :=
  fixedThroatCoverChartedSpace
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)

local instance orientationBoundaryCoverIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (OrientationBoundaryCover period hPeriod) :=
  fixedThroatCover_isManifold
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)

local instance orientationBoundaryChartedSpace :
    ChartedSpace ThroatCoverModel (OrientationBoundary period hPeriod) :=
  cutThroatBoundaryChartedSpace period hPeriod

local instance orientationBoundaryIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (OrientationBoundary period hPeriod) :=
  cutThroatBoundary_isManifold period hPeriod

local instance orientationBoundaryCompactSpace :
    CompactSpace (OrientationBoundary period hPeriod) :=
  P0EFTJanusMappingTorusCompactQuotient.fixedThroatQuotientCompactSpace
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)

private theorem isOpen_forall_prod_of_compact
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace X]
    (s : Set (X × Y)) (hOpen : IsOpen s) :
    IsOpen {y | ∀ x, (x, y) ∈ s} := by
  rw [isOpen_iff_mem_nhds]
  intro y hy
  have hSubset : (Set.univ : Set X) ×ˢ {y} ⊆ s := by
    rintro ⟨x, current⟩ ⟨-, hCurrent⟩
    change current = y at hCurrent
    subst current
    exact hy x
  obtain ⟨u, v, hUOpen, hVOpen, hUnivSubset, hYSubset, hUVSubset⟩ :=
    generalized_tube_lemma
      (s := (Set.univ : Set X)) (t := ({y} : Set Y))
      isCompact_univ isCompact_singleton hOpen hSubset
  refine Filter.mem_of_superset (hVOpen.mem_nhds (hYSubset (by simp))) ?_
  intro current hCurrent x
  exact hUVSubset ⟨hUnivSubset (Set.mem_univ x), hCurrent⟩

local instance throatTangentFiniteDimensional
    (point : EffectiveThroat period hPeriod) :
    FiniteDimensional Real (ThroatTangentFiber period hPeriod point) := by
  change FiniteDimensional Real ThroatCoverCoordinates
  infer_instance

local instance quotientTangentFiniteDimensional
    (point : EffectiveQuotient period hPeriod) :
    FiniteDimensional Real (TangentSpace coverModelWithCorners point) := by
  change FiniteDimensional Real CoverCoordinates
  infer_instance

local instance throatTangentT2
    (point : EffectiveThroat period hPeriod) :
    T2Space (ThroatTangentFiber period hPeriod point) := by
  change T2Space ThroatCoverCoordinates
  infer_instance

private theorem throatTangent_finrank_eq_cotangent
    (point : EffectiveThroat period hPeriod) :
    Module.finrank Real (ThroatTangentFiber period hPeriod point) =
      Module.finrank Real (ThroatCotangentFiber period hPeriod point) := by
  calc
    Module.finrank Real (ThroatTangentFiber period hPeriod point) =
        Module.finrank Real
          (Module.Dual Real (ThroatTangentFiber period hPeriod point)) :=
      (Subspace.dual_finrank_eq (K := Real)
        (V := ThroatTangentFiber period hPeriod point)).symm
    _ = Module.finrank Real
        (ThroatCotangentFiber period hPeriod point) :=
      (LinearMap.toContinuousLinearMap
        (𝕜 := Real)
        (E := ThroatTangentFiber period hPeriod point)
        (F' := Real)).finrank_eq

/-! ## The genuinely induced metric family -/

/-- Pullback of an ambient metric by an arbitrary throat-to-bulk map. -/
def throatMapInducedMetricValue
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (embedding : EffectiveThroat period hPeriod →
      EffectiveQuotient period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    ThroatCovariantTwoTensorFiber period hPeriod point :=
  let derivative :=
    mfderiv throatCoverModelWithCorners coverModelWithCorners embedding point
  (derivative.precomp Real).comp
    ((metric.tensor.tensor (embedding point)).comp derivative)

@[simp]
theorem throatMapInducedMetricValue_apply
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (embedding : EffectiveThroat period hPeriod →
      EffectiveQuotient period hPeriod)
    (point : EffectiveThroat period hPeriod)
    (first second : ThroatTangentFiber period hPeriod point) :
    throatMapInducedMetricValue period hPeriod metric embedding point
        first second =
      metric.tensor.tensor (embedding point)
        (mfderiv throatCoverModelWithCorners coverModelWithCorners
          embedding point first)
        (mfderiv throatCoverModelWithCorners coverModelWithCorners
          embedding point second) :=
  rfl

theorem throatMapInducedMetricValue_symmetric
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (embedding : EffectiveThroat period hPeriod →
      EffectiveQuotient period hPeriod)
    (point : EffectiveThroat period hPeriod)
    (first second : ThroatTangentFiber period hPeriod point) :
    throatMapInducedMetricValue period hPeriod metric embedding point
        first second =
      throatMapInducedMetricValue period hPeriod metric embedding point
        second first := by
  simp only [throatMapInducedMetricValue_apply]
  exact metric.tensor.symmetric _ _ _

private def throatMapDerivativeCoordinates
    (embedding : EffectiveThroat period hPeriod →
      EffectiveQuotient period hPeriod)
    (point current : EffectiveThroat period hPeriod) :
    ThroatCoverCoordinates →L[Real] CoverCoordinates :=
  inTangentCoordinates throatCoverModelWithCorners coverModelWithCorners
    id embedding
    (mfderiv throatCoverModelWithCorners coverModelWithCorners embedding)
    point current

private def throatMapAmbientTensorCoordinates
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (embedding : EffectiveThroat period hPeriod →
      EffectiveQuotient period hPeriod)
    (point current : EffectiveThroat period hPeriod) :
    CoverCoordinates →L[Real] CoverCoordinates →L[Real] Real :=
  ContinuousLinearMap.inCoordinates CoverCoordinates
    (fun base : EffectiveQuotient period hPeriod =>
      TangentSpace coverModelWithCorners base)
    (CoverCoordinates →L[Real] Real)
    (fun base : EffectiveQuotient period hPeriod =>
      TangentSpace coverModelWithCorners base →L[Real] Real)
    (embedding point) (embedding current)
    (embedding point) (embedding current)
    (metric.tensor.tensor (embedding current))

private def throatMapTraceTensorCoordinates
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (embedding : EffectiveThroat period hPeriod →
      EffectiveQuotient period hPeriod)
    (point current : EffectiveThroat period hPeriod) :
    ThroatCovariantTwoTensorModel :=
  ContinuousLinearMap.inCoordinates ThroatCoverCoordinates
    (ThroatTangentFiber period hPeriod)
    (ThroatCoverCoordinates →L[Real] Real)
    (ThroatCotangentFiber period hPeriod)
    point current point current
    (throatMapInducedMetricValue period hPeriod metric embedding current)

private def throatMapCoordinateRestriction
    (derivative : ThroatCoverCoordinates →L[Real] CoverCoordinates)
    (tensor : CoverCoordinates →L[Real]
      CoverCoordinates →L[Real] Real) :
    ThroatCovariantTwoTensorModel :=
  (derivative.precomp Real).comp (tensor.comp derivative)

private theorem throatMapDerivativeCoordinates_apply
    (embedding : EffectiveThroat period hPeriod →
      EffectiveQuotient period hPeriod)
    (point current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) point).baseSet)
    (hImage : embedding current ∈
      (trivializationAt CoverCoordinates
        (fun base : EffectiveQuotient period hPeriod =>
          TangentSpace coverModelWithCorners base)
        (embedding point)).baseSet)
    (vector : ThroatCoverCoordinates) :
    throatMapDerivativeCoordinates period hPeriod embedding point current
        vector =
      (trivializationAt CoverCoordinates
        (fun base : EffectiveQuotient period hPeriod =>
          TangentSpace coverModelWithCorners base)
        (embedding point)).linearMapAt Real (embedding current)
          (mfderiv throatCoverModelWithCorners coverModelWithCorners embedding
            current
            ((trivializationAt ThroatCoverCoordinates
              (ThroatTangentFiber period hPeriod) point).symm current
                vector)) := by
  rw [show throatMapDerivativeCoordinates period hPeriod embedding point current =
      ContinuousLinearMap.inCoordinates ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) CoverCoordinates
        (fun base : EffectiveQuotient period hPeriod =>
          TangentSpace coverModelWithCorners base)
        point current (embedding point) (embedding current)
        (mfderiv throatCoverModelWithCorners coverModelWithCorners embedding
          current) by rfl]
  rw [ContinuousLinearMap.inCoordinates_eq hCurrent hImage]
  rw [Trivialization.linearMapAt_apply, if_pos hImage]
  rfl

private theorem throatMapTraceTensorCoordinates_eq
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (embedding : EffectiveThroat period hPeriod →
      EffectiveQuotient period hPeriod)
    (point current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) point).baseSet)
    (hImage : embedding current ∈
      (trivializationAt CoverCoordinates
        (fun base : EffectiveQuotient period hPeriod =>
          TangentSpace coverModelWithCorners base)
        (embedding point)).baseSet) :
    throatMapTraceTensorCoordinates period hPeriod metric embedding
        point current =
      throatMapCoordinateRestriction
        (throatMapDerivativeCoordinates period hPeriod embedding point current)
        (throatMapAmbientTensorCoordinates period hPeriod metric embedding
          point current) := by
  apply ContinuousLinearMap.ext
  intro first
  apply ContinuousLinearMap.ext
  intro second
  rw [show throatMapTraceTensorCoordinates period hPeriod metric embedding
        point current first second =
      ContinuousLinearMap.inCoordinates ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod)
        (ThroatCoverCoordinates →L[Real] Real)
        (ThroatCotangentFiber period hPeriod)
        point current point current
        (throatMapInducedMetricValue period hPeriod metric embedding current)
        first second by rfl]
  rw [inCoordinates_apply_eq₂ hCurrent hCurrent (Set.mem_univ _)]
  simp only [throatMapInducedMetricValue_apply,
    throatMapCoordinateRestriction, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.precomp_apply]
  rw [show throatMapAmbientTensorCoordinates period hPeriod metric embedding
        point current
        (throatMapDerivativeCoordinates period hPeriod embedding point current
          first)
        (throatMapDerivativeCoordinates period hPeriod embedding point current
          second) =
      ContinuousLinearMap.inCoordinates CoverCoordinates
        (fun base : EffectiveQuotient period hPeriod =>
          TangentSpace coverModelWithCorners base)
        (CoverCoordinates →L[Real] Real)
        (fun base : EffectiveQuotient period hPeriod =>
          TangentSpace coverModelWithCorners base →L[Real] Real)
        (embedding point) (embedding current)
        (embedding point) (embedding current)
        (metric.tensor.tensor (embedding current))
        (throatMapDerivativeCoordinates period hPeriod embedding point current
          first)
        (throatMapDerivativeCoordinates period hPeriod embedding point current
          second) by rfl]
  rw [inCoordinates_apply_eq₂ hImage hImage (Set.mem_univ _)]
  rw [throatMapDerivativeCoordinates_apply period hPeriod embedding point
      current hCurrent hImage first,
    throatMapDerivativeCoordinates_apply period hPeriod embedding point
      current hCurrent hImage second]
  simp only [Trivialization.symm_linearMapAt _ hImage]
  rfl

/-- Pullback of a smooth ambient metric by any smooth throat map is a genuine
smooth throat tensor. -/
theorem throatMapInducedMetricValue_contMDiff
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (embedding : EffectiveThroat period hPeriod →
      EffectiveQuotient period hPeriod)
    (hEmbedding : ContMDiff throatCoverModelWithCorners coverModelWithCorners
      ∞ embedding) :
    ContMDiff throatCoverModelWithCorners
      (throatCoverModelWithCorners.prod
        𝓘(Real, ThroatCovariantTwoTensorModel)) ∞
      (fun point => TotalSpace.mk' ThroatCovariantTwoTensorModel
        (E := ThroatCovariantTwoTensorFiber period hPeriod) point
        (throatMapInducedMetricValue period hPeriod metric embedding point)) := by
  intro point
  have hD := hEmbedding.contMDiffAt
    |>.mfderiv_const (x₀ := point) (m := ∞) (by simp)
  have hMap := hEmbedding.of_le (m := ∞) (by simp)
  have hTensor := metric.tensor.tensor.contMDiff.comp hMap
  have hTensorAt := hTensor point
  rw [contMDiffAt_hom_bundle] at hTensorAt
  have hPre := hD.clm_precomp (F₃ := Real)
  have hOuter := hTensorAt.2.clm_comp hD
  have hFormula := hPre.clm_comp hOuter
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  apply hFormula.congr_of_eventuallyEq
  have hCurrent : ∀ᶠ current in nhds point,
      current ∈
        (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) point).baseSet :=
    (trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) point).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) point)
  have hImage : ∀ᶠ current in nhds point,
      embedding current ∈
        (trivializationAt CoverCoordinates
          (fun base : EffectiveQuotient period hPeriod =>
            TangentSpace coverModelWithCorners base)
          (embedding point)).baseSet :=
    hEmbedding.continuous.continuousAt
      ((trivializationAt CoverCoordinates
        (fun base : EffectiveQuotient period hPeriod =>
          TangentSpace coverModelWithCorners base)
        (embedding point)).open_baseSet.mem_nhds
          (mem_baseSet_trivializationAt CoverCoordinates
            (fun base : EffectiveQuotient period hPeriod =>
              TangentSpace coverModelWithCorners base)
            (embedding point)))
  filter_upwards [hCurrent, hImage] with current hCurrent' hImage'
  simpa only [throatMapTraceTensorCoordinates,
    throatMapCoordinateRestriction, throatMapDerivativeCoordinates,
    throatMapAmbientTensorCoordinates, Function.comp_apply] using
      (throatMapTraceTensorCoordinates_eq period hPeriod metric embedding
        point current hCurrent' hImage')

/-- Smooth symmetric metric induced by a smooth throat map. -/
def throatMapInducedMetric
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (embedding : EffectiveThroat period hPeriod →
      EffectiveQuotient period hPeriod)
    (hEmbedding : ContMDiff throatCoverModelWithCorners coverModelWithCorners
      ∞ embedding) :
    SmoothSymmetricThroatCovariantTwoTensor period hPeriod where
  tensor :=
    { toFun := throatMapInducedMetricValue period hPeriod metric embedding
      contMDiff_toFun := throatMapInducedMetricValue_contMDiff
        period hPeriod metric embedding hEmbedding }
  symmetric := throatMapInducedMetricValue_symmetric
    period hPeriod metric embedding

/-- Each fixed normal parameter is a genuine smooth throat-to-bulk map. -/
theorem normalGraph_fixedParameter_contMDiff
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) :
    ContMDiff throatCoverModelWithCorners coverModelWithCorners ∞
      (normalGraph period hPeriod displacement parameter) := by
  exact ((normalGraph_joint_contMDiff period hPeriod displacement).comp
    (contMDiff_id.prodMk contMDiff_const)).congr (fun _ => rfl)

private def normalGraphFamilyDerivativeCoordinates
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base current : EffectiveThroat period hPeriod × Real) :
    ThroatCoverCoordinates →L[Real] CoverCoordinates :=
  inTangentCoordinates throatCoverModelWithCorners coverModelWithCorners
    Prod.fst
    (fun point => normalGraph period hPeriod displacement point.2 point.1)
    (fun point => mfderiv throatCoverModelWithCorners coverModelWithCorners
      (normalGraph period hPeriod displacement point.2) point.1)
    base current

/-- Metric induced on the displaced throat by the actual collar graph. -/
def normalGraphInducedMetricValue
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (point : EffectiveThroat period hPeriod) :
    ThroatCovariantTwoTensorFiber period hPeriod point :=
  throatMapInducedMetricValue period hPeriod metric
    (normalGraph period hPeriod displacement parameter) point

/-- Every member of the normal family carries the genuinely induced smooth
symmetric metric. -/
def normalGraphInducedMetric
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) :
    SmoothSymmetricThroatCovariantTwoTensor period hPeriod :=
  throatMapInducedMetric period hPeriod metric
    (normalGraph period hPeriod displacement parameter)
    (normalGraph_fixedParameter_contMDiff period hPeriod displacement parameter)

@[simp]
theorem normalGraphInducedMetricValue_apply
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (point : EffectiveThroat period hPeriod)
    (first second : ThroatTangentFiber period hPeriod point) :
    normalGraphInducedMetricValue period hPeriod metric displacement parameter
        point first second =
      metric.tensor.tensor
        (normalGraph period hPeriod displacement parameter point)
        (mfderiv throatCoverModelWithCorners coverModelWithCorners
          (normalGraph period hPeriod displacement parameter) point first)
        (mfderiv throatCoverModelWithCorners coverModelWithCorners
          (normalGraph period hPeriod displacement parameter) point second) :=
  rfl

theorem normalGraphInducedMetricValue_symmetric
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (point : EffectiveThroat period hPeriod)
    (first second : ThroatTangentFiber period hPeriod point) :
    normalGraphInducedMetricValue period hPeriod metric displacement parameter
        point first second =
      normalGraphInducedMetricValue period hPeriod metric displacement parameter
        point second first :=
  throatMapInducedMetricValue_symmetric period hPeriod metric _ point first second

private def normalGraphFamilyAmbientTensorCoordinates
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base current : EffectiveThroat period hPeriod × Real) :
    CoverCoordinates →L[Real] CoverCoordinates →L[Real] Real :=
  ContinuousLinearMap.inCoordinates CoverCoordinates
    (fun point : EffectiveQuotient period hPeriod =>
      TangentSpace coverModelWithCorners point)
    (CoverCoordinates →L[Real] Real)
    (fun point : EffectiveQuotient period hPeriod =>
      TangentSpace coverModelWithCorners point →L[Real] Real)
    (normalGraph period hPeriod displacement base.2 base.1)
    (normalGraph period hPeriod displacement current.2 current.1)
    (normalGraph period hPeriod displacement base.2 base.1)
    (normalGraph period hPeriod displacement current.2 current.1)
    (metric.tensor.tensor
      (normalGraph period hPeriod displacement current.2 current.1))

private def normalGraphFamilyTraceTensorCoordinates
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base current : EffectiveThroat period hPeriod × Real) :
    ThroatCovariantTwoTensorModel :=
  ContinuousLinearMap.inCoordinates ThroatCoverCoordinates
    (ThroatTangentFiber period hPeriod)
    (ThroatCoverCoordinates →L[Real] Real)
    (ThroatCotangentFiber period hPeriod)
    base.1 current.1 base.1 current.1
    (normalGraphInducedMetricValue period hPeriod metric displacement
      current.2 current.1)

private theorem normalGraphFamilyDerivativeCoordinates_apply
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base current : EffectiveThroat period hPeriod × Real)
    (hCurrent : current.1 ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) base.1).baseSet)
    (hImage : normalGraph period hPeriod displacement current.2 current.1 ∈
      (trivializationAt CoverCoordinates
        (fun point : EffectiveQuotient period hPeriod =>
          TangentSpace coverModelWithCorners point)
        (normalGraph period hPeriod displacement base.2 base.1)).baseSet)
    (vector : ThroatCoverCoordinates) :
    normalGraphFamilyDerivativeCoordinates period hPeriod displacement
        base current vector =
      (trivializationAt CoverCoordinates
        (fun point : EffectiveQuotient period hPeriod =>
          TangentSpace coverModelWithCorners point)
        (normalGraph period hPeriod displacement base.2 base.1)).linearMapAt
          Real
          (normalGraph period hPeriod displacement current.2 current.1)
          (mfderiv throatCoverModelWithCorners coverModelWithCorners
            (normalGraph period hPeriod displacement current.2) current.1
            ((trivializationAt ThroatCoverCoordinates
              (ThroatTangentFiber period hPeriod) base.1).symm current.1
                vector)) := by
  rw [show normalGraphFamilyDerivativeCoordinates period hPeriod displacement
      base current =
    ContinuousLinearMap.inCoordinates ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) CoverCoordinates
      (fun point : EffectiveQuotient period hPeriod =>
        TangentSpace coverModelWithCorners point)
      base.1 current.1
      (normalGraph period hPeriod displacement base.2 base.1)
      (normalGraph period hPeriod displacement current.2 current.1)
      (mfderiv throatCoverModelWithCorners coverModelWithCorners
        (normalGraph period hPeriod displacement current.2) current.1) by rfl]
  rw [ContinuousLinearMap.inCoordinates_eq hCurrent hImage]
  rw [Trivialization.linearMapAt_apply, if_pos hImage]
  rfl

private theorem normalGraphFamilyTraceTensorCoordinates_eq
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base current : EffectiveThroat period hPeriod × Real)
    (hCurrent : current.1 ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) base.1).baseSet)
    (hImage : normalGraph period hPeriod displacement current.2 current.1 ∈
      (trivializationAt CoverCoordinates
        (fun point : EffectiveQuotient period hPeriod =>
          TangentSpace coverModelWithCorners point)
        (normalGraph period hPeriod displacement base.2 base.1)).baseSet) :
    normalGraphFamilyTraceTensorCoordinates period hPeriod metric displacement
        base current =
      throatMapCoordinateRestriction
        (normalGraphFamilyDerivativeCoordinates period hPeriod displacement
          base current)
        (normalGraphFamilyAmbientTensorCoordinates period hPeriod metric
          displacement base current) := by
  apply ContinuousLinearMap.ext
  intro first
  apply ContinuousLinearMap.ext
  intro second
  rw [show normalGraphFamilyTraceTensorCoordinates period hPeriod metric
      displacement base current first second =
    ContinuousLinearMap.inCoordinates ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod)
      (ThroatCoverCoordinates →L[Real] Real)
      (ThroatCotangentFiber period hPeriod)
      base.1 current.1 base.1 current.1
      (normalGraphInducedMetricValue period hPeriod metric displacement
        current.2 current.1) first second by rfl]
  rw [inCoordinates_apply_eq₂ hCurrent hCurrent (Set.mem_univ _)]
  simp only [normalGraphInducedMetricValue_apply,
    throatMapCoordinateRestriction, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.precomp_apply]
  rw [show normalGraphFamilyAmbientTensorCoordinates period hPeriod metric
      displacement base current
      (normalGraphFamilyDerivativeCoordinates period hPeriod displacement
        base current first)
      (normalGraphFamilyDerivativeCoordinates period hPeriod displacement
        base current second) =
    ContinuousLinearMap.inCoordinates CoverCoordinates
      (fun point : EffectiveQuotient period hPeriod =>
        TangentSpace coverModelWithCorners point)
      (CoverCoordinates →L[Real] Real)
      (fun point : EffectiveQuotient period hPeriod =>
        TangentSpace coverModelWithCorners point →L[Real] Real)
      (normalGraph period hPeriod displacement base.2 base.1)
      (normalGraph period hPeriod displacement current.2 current.1)
      (normalGraph period hPeriod displacement base.2 base.1)
      (normalGraph period hPeriod displacement current.2 current.1)
      (metric.tensor.tensor
        (normalGraph period hPeriod displacement current.2 current.1))
      (normalGraphFamilyDerivativeCoordinates period hPeriod displacement
        base current first)
      (normalGraphFamilyDerivativeCoordinates period hPeriod displacement
        base current second) by rfl]
  rw [inCoordinates_apply_eq₂ hImage hImage (Set.mem_univ _)]
  rw [normalGraphFamilyDerivativeCoordinates_apply period hPeriod displacement
      base current hCurrent hImage first,
    normalGraphFamilyDerivativeCoordinates_apply period hPeriod displacement
      base current hCurrent hImage second]
  simp only [Trivialization.symm_linearMapAt _ hImage]
  rfl

private theorem normalGraphFamilyTraceTensorCoordinates_injective_iff
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base current : EffectiveThroat period hPeriod × Real)
    (hCurrent : current.1 ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) base.1).baseSet)
    (hCotangent : current.1 ∈
      (trivializationAt (ThroatCoverCoordinates →L[Real] Real)
        (ThroatCotangentFiber period hPeriod) base.1).baseSet) :
    Function.Injective
        (normalGraphFamilyTraceTensorCoordinates period hPeriod metric
          displacement base current) ↔
      Function.Injective
        (normalGraphInducedMetricValue period hPeriod metric displacement
          current.2 current.1) := by
  rw [show normalGraphFamilyTraceTensorCoordinates period hPeriod metric
      displacement base current =
    ContinuousLinearMap.inCoordinates ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod)
      (ThroatCoverCoordinates →L[Real] Real)
      (ThroatCotangentFiber period hPeriod)
      base.1 current.1 base.1 current.1
      (normalGraphInducedMetricValue period hPeriod metric displacement
        current.2 current.1) by rfl]
  rw [ContinuousLinearMap.inCoordinates_eq
    (F := ThroatCoverCoordinates)
    (E := ThroatTangentFiber period hPeriod)
    (F' := ThroatCoverCoordinates →L[Real] Real)
    (E' := ThroatCotangentFiber period hPeriod) hCurrent hCotangent]
  let tangentEquiv :=
    (trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) base.1).continuousLinearEquivAt
        Real current.1 hCurrent
  let cotangentEquiv :=
    (trivializationAt (ThroatCoverCoordinates →L[Real] Real)
      (ThroatCotangentFiber period hPeriod) base.1).continuousLinearEquivAt
        Real current.1 hCotangent
  constructor
  · intro hCoordinates first second hMetric
    apply tangentEquiv.injective
    apply hCoordinates
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe]
    rw [tangentEquiv.symm_apply_apply, tangentEquiv.symm_apply_apply, hMetric]
  · intro hMetric
    exact cotangentEquiv.injective.comp
      (hMetric.comp tangentEquiv.symm.injective)

/-- The genuinely induced metric is a single smooth family in the normal
parameter and the throat point. -/
theorem normalGraphInducedMetricValue_joint_contMDiff
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod) :
    ContMDiff
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (throatCoverModelWithCorners.prod
        𝓘(Real, ThroatCovariantTwoTensorModel)) ∞
      (fun current : EffectiveThroat period hPeriod × Real =>
        TotalSpace.mk' ThroatCovariantTwoTensorModel
          (E := ThroatCovariantTwoTensorFiber period hPeriod) current.1
          (normalGraphInducedMetricValue period hPeriod metric displacement
            current.2 current.1)) := by
  intro base
  let f : (EffectiveThroat period hPeriod × Real) →
      EffectiveThroat period hPeriod → EffectiveQuotient period hPeriod :=
    fun parameterPoint point =>
      normalGraph period hPeriod displacement parameterPoint.2 point
  let g : (EffectiveThroat period hPeriod × Real) →
      EffectiveThroat period hPeriod := Prod.fst
  have hJoint : ContMDiff
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      coverModelWithCorners ∞
      (fun current : EffectiveThroat period hPeriod × Real =>
        normalGraph period hPeriod displacement current.2 current.1) := by
    exact normalGraph_joint_contMDiff period hPeriod displacement
  have hReorder : ContMDiff
      ((throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real)).prod
        throatCoverModelWithCorners)
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real)) ∞
      (fun point : (EffectiveThroat period hPeriod × Real) ×
          EffectiveThroat period hPeriod => (point.2, point.1.2)) :=
    contMDiff_snd.prodMk (contMDiff_snd.comp contMDiff_fst)
  have hg : ContMDiffAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      throatCoverModelWithCorners ∞ g base := by
    simpa [g] using
      (contMDiff_fst : ContMDiff
        (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
        throatCoverModelWithCorners ∞
        (Prod.fst : EffectiveThroat period hPeriod × Real →
          EffectiveThroat period hPeriod)).contMDiffAt
  have hDerivative :=
    (hJoint.comp hReorder).contMDiffAt.mfderiv f g hg (by simp)
  have hTensor := metric.tensor.tensor.contMDiff.comp hJoint
  have hTensorAt := hTensor base
  rw [contMDiffAt_hom_bundle] at hTensorAt
  have hPre := hDerivative.clm_precomp (F₃ := Real)
  have hOuter := hTensorAt.2.clm_comp hDerivative
  have hFormula := hPre.clm_comp hOuter
  rw [contMDiffAt_hom_bundle]
  refine ⟨?_, ?_⟩
  · simpa [g] using hg
  · apply hFormula.congr_of_eventuallyEq
    have hCurrent : ∀ᶠ current in nhds base,
        current.1 ∈
          (trivializationAt ThroatCoverCoordinates
            (ThroatTangentFiber period hPeriod) base.1).baseSet :=
      continuous_fst.continuousAt
        ((trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) base.1).open_baseSet.mem_nhds
            (mem_baseSet_trivializationAt ThroatCoverCoordinates
              (ThroatTangentFiber period hPeriod) base.1))
    have hImage : ∀ᶠ current in nhds base,
        normalGraph period hPeriod displacement current.2 current.1 ∈
          (trivializationAt CoverCoordinates
            (fun point : EffectiveQuotient period hPeriod =>
              TangentSpace coverModelWithCorners point)
            (normalGraph period hPeriod displacement base.2 base.1)).baseSet :=
      hJoint.continuous.continuousAt
        ((trivializationAt CoverCoordinates
          (fun point : EffectiveQuotient period hPeriod =>
            TangentSpace coverModelWithCorners point)
          (normalGraph period hPeriod displacement base.2 base.1)).open_baseSet.mem_nhds
            (mem_baseSet_trivializationAt CoverCoordinates
              (fun point : EffectiveQuotient period hPeriod =>
                TangentSpace coverModelWithCorners point)
              (normalGraph period hPeriod displacement base.2 base.1)))
    filter_upwards [hCurrent, hImage] with current hCurrent' hImage'
    simpa only [normalGraphFamilyTraceTensorCoordinates,
      throatMapCoordinateRestriction, normalGraphFamilyDerivativeCoordinates,
      normalGraphFamilyAmbientTensorCoordinates, f, g, Function.comp_apply]
      using normalGraphFamilyTraceTensorCoordinates_eq period hPeriod metric
        displacement base current hCurrent' hImage'

private theorem normalGraphFamilyDerivativeCoordinates_contMDiffAt
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real) :
    ContMDiffAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      𝓘(Real, ThroatCoverCoordinates →L[Real] CoverCoordinates) ∞
      (normalGraphFamilyDerivativeCoordinates period hPeriod displacement base)
      base := by
  let f : (EffectiveThroat period hPeriod × Real) →
      EffectiveThroat period hPeriod → EffectiveQuotient period hPeriod :=
    fun parameterPoint point =>
      normalGraph period hPeriod displacement parameterPoint.2 point
  let g : (EffectiveThroat period hPeriod × Real) →
      EffectiveThroat period hPeriod := Prod.fst
  have hJoint : ContMDiff
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      coverModelWithCorners ∞
      (fun current : EffectiveThroat period hPeriod × Real =>
        normalGraph period hPeriod displacement current.2 current.1) :=
    normalGraph_joint_contMDiff period hPeriod displacement
  have hReorder : ContMDiff
      ((throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real)).prod
        throatCoverModelWithCorners)
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real)) ∞
      (fun point : (EffectiveThroat period hPeriod × Real) ×
          EffectiveThroat period hPeriod => (point.2, point.1.2)) :=
    contMDiff_snd.prodMk (contMDiff_snd.comp contMDiff_fst)
  have hg : ContMDiffAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      throatCoverModelWithCorners ∞ g base := by
    simpa [g] using
      (contMDiff_fst : ContMDiff
        (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
        throatCoverModelWithCorners ∞
        (Prod.fst : EffectiveThroat period hPeriod × Real →
          EffectiveThroat period hPeriod)).contMDiffAt
  have hDerivative :=
    (hJoint.comp hReorder).contMDiffAt.mfderiv f g hg (by simp)
  exact hDerivative

private theorem normalGraphFamilyAmbientTensorCoordinates_contMDiffAt
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real) :
    ContMDiffAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      𝓘(Real, CoverCoordinates →L[Real] CoverCoordinates →L[Real] Real) ∞
      (normalGraphFamilyAmbientTensorCoordinates period hPeriod metric
        displacement base) base := by
  have hJoint : ContMDiff
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      coverModelWithCorners ∞
      (fun current : EffectiveThroat period hPeriod × Real =>
        normalGraph period hPeriod displacement current.2 current.1) :=
    normalGraph_joint_contMDiff period hPeriod displacement
  have hTensor := metric.tensor.tensor.contMDiff.comp hJoint
  have hTensorAt := hTensor base
  rw [contMDiffAt_hom_bundle] at hTensorAt
  exact hTensorAt.2

/-- At zero displacement the induced family is definitionally the already
proved general-Lorentz throat trace. -/
theorem normalGraphInducedMetricValue_zero
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    normalGraphInducedMetricValue period hPeriod metric displacement 0 point =
      generalLorentzMetricThroatTraceValue period hPeriod metric point := by
  have hEmbedding :
      normalGraph period hPeriod displacement 0 =
        fixedThroatQuotientInclusion period hPeriod := by
    funext current
    exact normalGraph_zero period hPeriod displacement current
  simp only [normalGraphInducedMetricValue, hEmbedding]
  rfl

theorem normalGraphInducedMetric_zero
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod) :
    normalGraphInducedMetric period hPeriod metric displacement 0 =
      generalLorentzMetricThroatTrace period hPeriod metric := by
  apply SmoothSymmetricThroatCovariantTwoTensor.ext
  apply ContMDiffSection.ext
  intro point
  exact normalGraphInducedMetricValue_zero
    period hPeriod metric displacement point

/-! ## Intrinsic non-null domain -/

/-- The normal graph is non-null at a parameter precisely when its genuinely
induced metric has no tangential radical at any throat point. -/
def NormalGraphNonNullAt
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) : Prop :=
  ∀ point, Function.Injective
    (normalGraphInducedMetricValue period hPeriod metric displacement
      parameter point)

def normalGraphNonNullDomain
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod) : Set Real :=
  {parameter | NormalGraphNonNullAt period hPeriod metric displacement parameter}

private def normalGraphNonNullJointDomain
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod) :
    Set (EffectiveThroat period hPeriod × Real) :=
  {current | Function.Injective
    (normalGraphInducedMetricValue period hPeriod metric displacement
      current.2 current.1)}

private theorem normalGraphNonNullJointDomain_isOpen
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod) :
    IsOpen (normalGraphNonNullJointDomain period hPeriod metric displacement) := by
  rw [isOpen_iff_mem_nhds]
  intro base hBase
  have hSmoothAt :=
    normalGraphInducedMetricValue_joint_contMDiff period hPeriod metric
      displacement base
  rw [contMDiffAt_hom_bundle] at hSmoothAt
  have hTangentBase : base.1 ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) base.1).baseSet :=
    mem_baseSet_trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) base.1
  have hCotangentBase : base.1 ∈
      (trivializationAt (ThroatCoverCoordinates →L[Real] Real)
        (ThroatCotangentFiber period hPeriod) base.1).baseSet :=
    mem_baseSet_trivializationAt (ThroatCoverCoordinates →L[Real] Real)
      (ThroatCotangentFiber period hPeriod) base.1
  have hCoordinateInjective : Function.Injective
      (normalGraphFamilyTraceTensorCoordinates period hPeriod metric
        displacement base base) :=
    (normalGraphFamilyTraceTensorCoordinates_injective_iff period hPeriod
      metric displacement base base hTangentBase hCotangentBase).2 hBase
  have hCoordinateEventually : ∀ᶠ current in nhds base,
      Function.Injective
        (normalGraphFamilyTraceTensorCoordinates period hPeriod metric
          displacement base current) :=
    hSmoothAt.2.continuousAt
      (ContinuousLinearMap.isOpen_injective.mem_nhds hCoordinateInjective)
  have hTangentEventually : ∀ᶠ current in nhds base,
      current.1 ∈
        (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) base.1).baseSet :=
    continuous_fst.continuousAt
      ((trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) base.1).open_baseSet.mem_nhds
          hTangentBase)
  have hCotangentEventually : ∀ᶠ current in nhds base,
      current.1 ∈
        (trivializationAt (ThroatCoverCoordinates →L[Real] Real)
          (ThroatCotangentFiber period hPeriod) base.1).baseSet :=
    continuous_fst.continuousAt
      ((trivializationAt (ThroatCoverCoordinates →L[Real] Real)
        (ThroatCotangentFiber period hPeriod) base.1).open_baseSet.mem_nhds
          hCotangentBase)
  filter_upwards [hCoordinateEventually, hTangentEventually,
      hCotangentEventually] with current hCoordinate hTangent hCotangent
  exact (normalGraphFamilyTraceTensorCoordinates_injective_iff period hPeriod
    metric displacement base current hTangent hCotangent).1 hCoordinate

/-- The admissible parameters form a genuine open neighborhood whenever they
contain the base point; compactness of the throat supplies uniformity. -/
theorem normalGraphNonNullDomain_isOpen
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod) :
    IsOpen (normalGraphNonNullDomain period hPeriod metric displacement) := by
  change IsOpen {parameter | ∀ point,
    (point, parameter) ∈
      normalGraphNonNullJointDomain period hPeriod metric displacement}
  exact isOpen_forall_prod_of_compact
    (normalGraphNonNullJointDomain period hPeriod metric displacement)
    (normalGraphNonNullJointDomain_isOpen period hPeriod metric displacement)

/-- Transversality of the base metric proves that the physical base point
belongs to the non-null graph domain; it is not installed as a new datum. -/
theorem zero_mem_normalGraphNonNullDomain
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (hTransverse : HasNoTangentialRadical period hPeriod metric) :
    0 ∈ normalGraphNonNullDomain period hPeriod metric displacement := by
  intro point
  rw [normalGraphInducedMetricValue_zero period hPeriod metric displacement]
  exact ((throatTrace_nondegenerate_iff_no_tangential_radical
    period hPeriod metric).2 hTransverse) point

/-! ## Intrinsic inverse on the non-null domain -/

/-- On the non-null domain, the genuinely induced metric identifies each
throat tangent fiber continuously with its cotangent fiber. -/
def normalGraphInducedMetricEquiv
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (point : EffectiveThroat period hPeriod) :
    ThroatTangentFiber period hPeriod point ≃L[Real]
      ThroatCotangentFiber period hPeriod point :=
  (normalGraphInducedMetricValue period hPeriod metric displacement
      parameter point).toLinearMap
    |>.linearEquivOfInjective (hNonNull point)
      (throatTangent_finrank_eq_cotangent period hPeriod point)
    |>.toContinuousLinearEquiv

@[simp]
theorem normalGraphInducedMetricEquiv_apply
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (point : EffectiveThroat period hPeriod)
    (vector : ThroatTangentFiber period hPeriod point) :
    normalGraphInducedMetricEquiv period hPeriod metric displacement parameter
        hNonNull point vector =
      normalGraphInducedMetricValue period hPeriod metric displacement
        parameter point vector := by
  simp [normalGraphInducedMetricEquiv,
    LinearMap.linearEquivOfInjective_apply]

/-- Intrinsic inverse metric (`sharp`) of the displaced induced metric. -/
def normalGraphInducedMetricInverse
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (point : EffectiveThroat period hPeriod) :
    ThroatCotangentFiber period hPeriod point ≃L[Real]
      ThroatTangentFiber period hPeriod point :=
  (normalGraphInducedMetricEquiv period hPeriod metric displacement parameter
    hNonNull point).symm

@[simp]
theorem normalGraphInducedMetricInverse_metric
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (point : EffectiveThroat period hPeriod)
    (vector : ThroatTangentFiber period hPeriod point) :
    normalGraphInducedMetricInverse period hPeriod metric displacement parameter
        hNonNull point
        (normalGraphInducedMetricValue period hPeriod metric displacement
          parameter point vector) =
      vector := by
  rw [← normalGraphInducedMetricEquiv_apply period hPeriod metric displacement
    parameter hNonNull point vector]
  exact (normalGraphInducedMetricEquiv period hPeriod metric displacement parameter
    hNonNull point).symm_apply_apply vector

@[simp]
theorem normalGraphInducedMetric_metricInverse
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (point : EffectiveThroat period hPeriod)
    (covector : ThroatCotangentFiber period hPeriod point) :
    normalGraphInducedMetricValue period hPeriod metric displacement parameter
        point
        (normalGraphInducedMetricInverse period hPeriod metric displacement
          parameter hNonNull point covector) =
      covector := by
  rw [← normalGraphInducedMetricEquiv_apply period hPeriod metric displacement
    parameter hNonNull point
      (normalGraphInducedMetricInverse period hPeriod metric displacement
        parameter hNonNull point covector)]
  exact (normalGraphInducedMetricEquiv period hPeriod metric displacement parameter
    hNonNull point).apply_symm_apply covector

/-- Local-coordinate inverse of the jointly smooth induced metric family.
Outside the non-null locus the library inverse has no geometric meaning; the
regularity theorem below is stated only at admissible base points. -/
def normalGraphInducedMetricInverseCoordinates
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base current : EffectiveThroat period hPeriod × Real) :
    (ThroatCoverCoordinates →L[Real] Real) →L[Real]
      ThroatCoverCoordinates :=
  (normalGraphFamilyTraceTensorCoordinates period hPeriod metric displacement
    base current).inverse

private theorem normalGraphFamilyTraceTensorCoordinates_isInvertible
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement base.2) :
    (normalGraphFamilyTraceTensorCoordinates period hPeriod metric displacement
      base base).IsInvertible := by
  have hTangent : base.1 ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) base.1).baseSet :=
    mem_baseSet_trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) base.1
  have hCotangent : base.1 ∈
      (trivializationAt (ThroatCoverCoordinates →L[Real] Real)
        (ThroatCotangentFiber period hPeriod) base.1).baseSet :=
    mem_baseSet_trivializationAt (ThroatCoverCoordinates →L[Real] Real)
      (ThroatCotangentFiber period hPeriod) base.1
  have hFiber :
      (normalGraphInducedMetricEquiv period hPeriod metric displacement base.2
          hNonNull base.1 :
        ThroatTangentFiber period hPeriod base.1 →L[Real]
          ThroatCotangentFiber period hPeriod base.1) =
        normalGraphInducedMetricValue period hPeriod metric displacement base.2
          base.1 := by
    apply ContinuousLinearMap.ext
    intro vector
    exact normalGraphInducedMetricEquiv_apply period hPeriod metric displacement
      base.2 hNonNull base.1 vector
  unfold normalGraphFamilyTraceTensorCoordinates
  rw [ContinuousLinearMap.inCoordinates_eq hTangent hCotangent, ← hFiber]
  exact isInvertible_equiv.comp
    (isInvertible_equiv.comp isInvertible_equiv)

/-- The intrinsic inverse metric is jointly smooth in graph parameter and
throat point on the genuine non-null locus. -/
theorem normalGraphInducedMetricInverseCoordinates_contMDiffAt
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement base.2) :
    ContMDiffAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      𝓘(Real,
        (ThroatCoverCoordinates →L[Real] Real) →L[Real]
          ThroatCoverCoordinates) ∞
      (normalGraphInducedMetricInverseCoordinates period hPeriod metric
        displacement base) base := by
  have hMetric := normalGraphInducedMetricValue_joint_contMDiff
    period hPeriod metric displacement base
  rw [contMDiffAt_hom_bundle] at hMetric
  exact
    (normalGraphFamilyTraceTensorCoordinates_isInvertible period hPeriod metric
      displacement base hNonNull |>.contDiffAt_map_inverse (n := ∞)
      ).comp_contMDiffAt hMetric.2

/-- The smooth coordinate inverse is exactly the coordinate expression of the
intrinsic inverse metric already constructed above. -/
theorem normalGraphInducedMetricInverseCoordinates_eq_inCoordinates
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base current : EffectiveThroat period hPeriod × Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement
      current.2)
    (hTangent : current.1 ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) base.1).baseSet)
    (hCotangent : current.1 ∈
      (trivializationAt (ThroatCoverCoordinates →L[Real] Real)
        (ThroatCotangentFiber period hPeriod) base.1).baseSet) :
    normalGraphInducedMetricInverseCoordinates period hPeriod metric
        displacement base current =
      ContinuousLinearMap.inCoordinates
        (ThroatCoverCoordinates →L[Real] Real)
        (ThroatCotangentFiber period hPeriod)
        ThroatCoverCoordinates (ThroatTangentFiber period hPeriod)
        base.1 current.1 base.1 current.1
        (normalGraphInducedMetricInverse period hPeriod metric displacement
          current.2 hNonNull current.1).toContinuousLinearMap := by
  have hFiber :
      (normalGraphInducedMetricEquiv period hPeriod metric displacement current.2
          hNonNull current.1 :
        ThroatTangentFiber period hPeriod current.1 →L[Real]
          ThroatCotangentFiber period hPeriod current.1) =
        normalGraphInducedMetricValue period hPeriod metric displacement
          current.2 current.1 := by
    apply ContinuousLinearMap.ext
    intro vector
    exact normalGraphInducedMetricEquiv_apply period hPeriod metric displacement
      current.2 hNonNull current.1 vector
  unfold normalGraphInducedMetricInverseCoordinates
    normalGraphFamilyTraceTensorCoordinates normalGraphInducedMetricInverse
  rw [ContinuousLinearMap.inCoordinates_eq hTangent hCotangent,
    ← hFiber,
    ContinuousLinearMap.inCoordinates_eq hCotangent hTangent]
  simp only [ContinuousLinearMap.inverse_equiv_comp,
    ContinuousLinearMap.inverse_comp_equiv,
    ContinuousLinearMap.comp_assoc,
    ContinuousLinearMap.inverse_equiv,
    ContinuousLinearEquiv.symm_symm]

/-- Change of tangent coordinates between two fixed source trivializations at
the same physical throat point. -/
def normalGraphThroatTangentCoordinateTransition
    (firstBase secondBase current : EffectiveThroat period hPeriod)
    (hFirst : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) firstBase).baseSet)
    (hSecond : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) secondBase).baseSet) :
    ThroatCoverCoordinates ≃L[Real] ThroatCoverCoordinates :=
  ((trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) firstBase)
    |>.continuousLinearEquivAt Real current hFirst).symm.trans
  ((trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) secondBase)
    |>.continuousLinearEquivAt Real current hSecond)

/-- The corresponding cotangent coordinate transition.  Keeping this as the
actual cotangent-bundle transition avoids installing an independent dual
frame. -/
def normalGraphThroatCotangentCoordinateTransition
    (firstBase secondBase current : EffectiveThroat period hPeriod)
    (hFirst : current ∈
      (trivializationAt (ThroatCoverCoordinates →L[Real] Real)
        (ThroatCotangentFiber period hPeriod) firstBase).baseSet)
    (hSecond : current ∈
      (trivializationAt (ThroatCoverCoordinates →L[Real] Real)
        (ThroatCotangentFiber period hPeriod) secondBase).baseSet) :
    (ThroatCoverCoordinates →L[Real] Real) ≃L[Real]
      (ThroatCoverCoordinates →L[Real] Real) :=
  ((trivializationAt (ThroatCoverCoordinates →L[Real] Real)
      (ThroatCotangentFiber period hPeriod) firstBase)
    |>.continuousLinearEquivAt Real current hFirst).symm.trans
  ((trivializationAt (ThroatCoverCoordinates →L[Real] Real)
      (ThroatCotangentFiber period hPeriod) secondBase)
    |>.continuousLinearEquivAt Real current hSecond)

/-- Cotangent coordinates evaluate on the matching tangent coordinates as the
underlying intrinsic covector evaluates on the underlying tangent vector. -/
theorem normalGraphThroatCotangentCoordinates_apply
    (base current : EffectiveThroat period hPeriod)
    (hTangent : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) base).baseSet)
    (hCotangent : current ∈
      (trivializationAt (ThroatCoverCoordinates →L[Real] Real)
        (ThroatCotangentFiber period hPeriod) base).baseSet)
    (covector : ThroatCotangentFiber period hPeriod current)
    (vector : ThroatTangentFiber period hPeriod current) :
    ((trivializationAt (ThroatCoverCoordinates →L[Real] Real)
        (ThroatCotangentFiber period hPeriod) base)
      |>.continuousLinearEquivAt Real current hCotangent) covector
        (((trivializationAt ThroatCoverCoordinates
            (ThroatTangentFiber period hPeriod) base)
          |>.continuousLinearEquivAt Real current hTangent) vector) =
      covector vector := by
  rw [Bundle.Trivialization.coe_continuousLinearEquivAt_eq
      (trivializationAt (ThroatCoverCoordinates →L[Real] Real)
        (ThroatCotangentFiber period hPeriod) base) hCotangent,
    Bundle.Trivialization.coe_continuousLinearEquivAt_eq
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) base) hTangent]
  rw [(trivializationAt (ThroatCoverCoordinates →L[Real] Real)
        (ThroatCotangentFiber period hPeriod) base)
      |>.continuousLinearMapAt_apply_of_mem (R := Real) hCotangent,
    (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) base)
      |>.continuousLinearMapAt_apply_of_mem (R := Real) hTangent]
  rw [hom_trivializationAt_apply]
  unfold ContinuousLinearMap.inCoordinates
  simp
  rw [(trivializationAt ThroatCoverCoordinates
    (ThroatTangentFiber period hPeriod) base).symm_apply_apply_mk hTangent]

/-- The tangent and cotangent changes of source coordinates preserve the
canonical pairing. -/
theorem normalGraphThroatCoordinateTransition_pairing
    (firstBase secondBase current : EffectiveThroat period hPeriod)
    (hFirstTangent : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) firstBase).baseSet)
    (hSecondTangent : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) secondBase).baseSet)
    (hFirstCotangent : current ∈
      (trivializationAt (ThroatCoverCoordinates →L[Real] Real)
        (ThroatCotangentFiber period hPeriod) firstBase).baseSet)
    (hSecondCotangent : current ∈
      (trivializationAt (ThroatCoverCoordinates →L[Real] Real)
        (ThroatCotangentFiber period hPeriod) secondBase).baseSet)
    (covector : ThroatCoverCoordinates →L[Real] Real)
    (vector : ThroatCoverCoordinates) :
    normalGraphThroatCotangentCoordinateTransition period hPeriod firstBase
        secondBase current hFirstCotangent hSecondCotangent covector
          (normalGraphThroatTangentCoordinateTransition period hPeriod
            firstBase secondBase current hFirstTangent hSecondTangent vector) =
      covector vector := by
  let tangentFirst :=
    (trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) firstBase)
      |>.continuousLinearEquivAt Real current hFirstTangent
  let tangentSecond :=
    (trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) secondBase)
      |>.continuousLinearEquivAt Real current hSecondTangent
  let cotangentFirst :=
    (trivializationAt (ThroatCoverCoordinates →L[Real] Real)
      (ThroatCotangentFiber period hPeriod) firstBase)
      |>.continuousLinearEquivAt Real current hFirstCotangent
  let cotangentSecond :=
    (trivializationAt (ThroatCoverCoordinates →L[Real] Real)
      (ThroatCotangentFiber period hPeriod) secondBase)
      |>.continuousLinearEquivAt Real current hSecondCotangent
  change cotangentSecond (cotangentFirst.symm covector)
      (tangentSecond (tangentFirst.symm vector)) = covector vector
  rw [normalGraphThroatCotangentCoordinates_apply period hPeriod secondBase
    current hSecondTangent hSecondCotangent]
  have hFirst := normalGraphThroatCotangentCoordinates_apply period hPeriod
    firstBase current hFirstTangent hFirstCotangent
      (cotangentFirst.symm covector) (tangentFirst.symm vector)
  change cotangentFirst (cotangentFirst.symm covector)
      (tangentFirst (tangentFirst.symm vector)) = _ at hFirst
  rw [cotangentFirst.apply_symm_apply, tangentFirst.apply_symm_apply] at hFirst
  exact hFirst.symm

/-- Naturality of the already constructed intrinsic inverse metric under a
change of source trivialization. -/
theorem normalGraphInducedMetricInverseCoordinates_natural
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (firstBase secondBase current : EffectiveThroat period hPeriod × Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement current.2)
    (hFirstTangent : current.1 ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) firstBase.1).baseSet)
    (hSecondTangent : current.1 ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) secondBase.1).baseSet)
    (hFirstCotangent : current.1 ∈
      (trivializationAt (ThroatCoverCoordinates →L[Real] Real)
        (ThroatCotangentFiber period hPeriod) firstBase.1).baseSet)
    (hSecondCotangent : current.1 ∈
      (trivializationAt (ThroatCoverCoordinates →L[Real] Real)
        (ThroatCotangentFiber period hPeriod) secondBase.1).baseSet) :
    (normalGraphInducedMetricInverseCoordinates period hPeriod metric
        displacement secondBase current).comp
        (normalGraphThroatCotangentCoordinateTransition period hPeriod
          firstBase.1 secondBase.1 current.1 hFirstCotangent hSecondCotangent :
            (ThroatCoverCoordinates →L[Real] Real) →L[Real]
              (ThroatCoverCoordinates →L[Real] Real)) =
      (normalGraphThroatTangentCoordinateTransition period hPeriod firstBase.1
        secondBase.1 current.1 hFirstTangent hSecondTangent :
          ThroatCoverCoordinates →L[Real] ThroatCoverCoordinates).comp
        (normalGraphInducedMetricInverseCoordinates period hPeriod metric
          displacement firstBase current) := by
  rw [normalGraphInducedMetricInverseCoordinates_eq_inCoordinates period hPeriod
      metric displacement firstBase current hNonNull hFirstTangent
        hFirstCotangent,
    normalGraphInducedMetricInverseCoordinates_eq_inCoordinates period hPeriod
      metric displacement secondBase current hNonNull hSecondTangent
        hSecondCotangent]
  rw [ContinuousLinearMap.inCoordinates_eq hFirstCotangent hFirstTangent,
    ContinuousLinearMap.inCoordinates_eq hSecondCotangent hSecondTangent]
  let tangentFirst :=
    (trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) firstBase.1)
      |>.continuousLinearEquivAt Real current.1 hFirstTangent
  let tangentSecond :=
    (trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) secondBase.1)
      |>.continuousLinearEquivAt Real current.1 hSecondTangent
  let cotangentFirst :=
    (trivializationAt (ThroatCoverCoordinates →L[Real] Real)
      (ThroatCotangentFiber period hPeriod) firstBase.1)
      |>.continuousLinearEquivAt Real current.1 hFirstCotangent
  let cotangentSecond :=
    (trivializationAt (ThroatCoverCoordinates →L[Real] Real)
      (ThroatCotangentFiber period hPeriod) secondBase.1)
      |>.continuousLinearEquivAt Real current.1 hSecondCotangent
  apply ContinuousLinearMap.ext
  intro covector
  change tangentSecond
      (normalGraphInducedMetricInverse period hPeriod metric displacement
        current.2 hNonNull current.1
          (cotangentSecond.symm (cotangentSecond (cotangentFirst.symm covector)))) =
    tangentSecond (tangentFirst.symm
      (tangentFirst
        (normalGraphInducedMetricInverse period hPeriod metric displacement
          current.2 hNonNull current.1 (cotangentFirst.symm covector))))
  rw [cotangentSecond.symm_apply_apply, tangentFirst.symm_apply_apply]

/-- Any intrinsic tangent-to-cotangent fiber map obeys the complementary
covariant source-coordinate transition law. -/
theorem normalGraphThroatFiberLinearMapCoordinates_natural
    (firstBase secondBase current : EffectiveThroat period hPeriod)
    (hFirstTangent : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) firstBase).baseSet)
    (hSecondTangent : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) secondBase).baseSet)
    (hFirstCotangent : current ∈
      (trivializationAt (ThroatCoverCoordinates →L[Real] Real)
        (ThroatCotangentFiber period hPeriod) firstBase).baseSet)
    (hSecondCotangent : current ∈
      (trivializationAt (ThroatCoverCoordinates →L[Real] Real)
        (ThroatCotangentFiber period hPeriod) secondBase).baseSet)
    (fiberMap : ThroatTangentFiber period hPeriod current →L[Real]
      ThroatCotangentFiber period hPeriod current) :
    (ContinuousLinearMap.inCoordinates ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod)
        (ThroatCoverCoordinates →L[Real] Real)
        (ThroatCotangentFiber period hPeriod)
        secondBase current secondBase current fiberMap).comp
      (normalGraphThroatTangentCoordinateTransition period hPeriod firstBase
        secondBase current hFirstTangent hSecondTangent :
          ThroatCoverCoordinates →L[Real] ThroatCoverCoordinates) =
    (normalGraphThroatCotangentCoordinateTransition period hPeriod firstBase
        secondBase current hFirstCotangent hSecondCotangent :
          (ThroatCoverCoordinates →L[Real] Real) →L[Real]
            (ThroatCoverCoordinates →L[Real] Real)).comp
      (ContinuousLinearMap.inCoordinates ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod)
        (ThroatCoverCoordinates →L[Real] Real)
        (ThroatCotangentFiber period hPeriod)
        firstBase current firstBase current fiberMap) := by
  rw [ContinuousLinearMap.inCoordinates_eq hFirstTangent hFirstCotangent,
    ContinuousLinearMap.inCoordinates_eq hSecondTangent hSecondCotangent]
  let tangentFirst :=
    (trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) firstBase)
      |>.continuousLinearEquivAt Real current hFirstTangent
  let tangentSecond :=
    (trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) secondBase)
      |>.continuousLinearEquivAt Real current hSecondTangent
  let cotangentFirst :=
    (trivializationAt (ThroatCoverCoordinates →L[Real] Real)
      (ThroatCotangentFiber period hPeriod) firstBase)
      |>.continuousLinearEquivAt Real current hFirstCotangent
  let cotangentSecond :=
    (trivializationAt (ThroatCoverCoordinates →L[Real] Real)
      (ThroatCotangentFiber period hPeriod) secondBase)
      |>.continuousLinearEquivAt Real current hSecondCotangent
  apply ContinuousLinearMap.ext
  intro vector
  change cotangentSecond
      (fiberMap (tangentSecond.symm (tangentSecond (tangentFirst.symm vector)))) =
    cotangentSecond (cotangentFirst.symm
      (cotangentFirst (fiberMap (tangentFirst.symm vector))))
  rw [tangentSecond.symm_apply_apply, cotangentFirst.symm_apply_apply]

/-- Intertwined endomorphisms have the same trace.  This is the exact linear
algebra used when the inverse metric and second fundamental form carry their
opposite source-coordinate transition laws. -/
theorem normalGraphThroatTrace_eq_of_intertwining
    (first second : ThroatCoverCoordinates →ₗ[Real] ThroatCoverCoordinates)
    (transition : ThroatCoverCoordinates ≃ₗ[Real] ThroatCoverCoordinates)
    (hIntertwine : second.comp transition.toLinearMap =
      transition.toLinearMap.comp first) :
    LinearMap.trace Real ThroatCoverCoordinates second =
      LinearMap.trace Real ThroatCoverCoordinates first := by
  have hConj : second = transition.conj first := by
    apply LinearMap.ext
    intro vector
    have hApply := LinearMap.congr_fun hIntertwine (transition.symm vector)
    simpa [LinearEquiv.conj_apply] using hApply
  rw [hConj]
  exact LinearMap.trace_conj' first transition

/-- Opposite transition laws for an inverse metric and a covariant form imply
invariance of their contracted trace. -/
theorem normalGraphThroatContractedTrace_natural
    (firstInverse secondInverse :
      (ThroatCoverCoordinates →L[Real] Real) →L[Real]
        ThroatCoverCoordinates)
    (firstForm secondForm : ThroatCoverCoordinates →L[Real]
      (ThroatCoverCoordinates →L[Real] Real))
    (tangentTransition :
      ThroatCoverCoordinates ≃L[Real] ThroatCoverCoordinates)
    (cotangentTransition :
      (ThroatCoverCoordinates →L[Real] Real) ≃L[Real]
        (ThroatCoverCoordinates →L[Real] Real))
    (hInverse : secondInverse.comp
        (cotangentTransition :
          (ThroatCoverCoordinates →L[Real] Real) →L[Real]
            (ThroatCoverCoordinates →L[Real] Real)) =
      (tangentTransition : ThroatCoverCoordinates →L[Real]
        ThroatCoverCoordinates).comp firstInverse)
    (hForm : secondForm.comp
        (tangentTransition : ThroatCoverCoordinates →L[Real]
          ThroatCoverCoordinates) =
      (cotangentTransition :
        (ThroatCoverCoordinates →L[Real] Real) →L[Real]
          (ThroatCoverCoordinates →L[Real] Real)).comp firstForm) :
    LinearMap.trace Real ThroatCoverCoordinates
        (secondInverse.toLinearMap.comp secondForm.toLinearMap) =
      LinearMap.trace Real ThroatCoverCoordinates
        (firstInverse.toLinearMap.comp firstForm.toLinearMap) := by
  apply normalGraphThroatTrace_eq_of_intertwining
    (transition := tangentTransition.toLinearEquiv)
  apply LinearMap.ext
  intro vector
  change secondInverse (secondForm (tangentTransition vector)) =
    tangentTransition (firstInverse (firstForm vector))
  have hFormApply := congrArg (fun map => map vector) hForm
  simp only [ContinuousLinearMap.comp_apply] at hFormApply
  erw [hFormApply]
  have hInverseApply := congrArg (fun map => map (firstForm vector)) hInverse
  simp only [ContinuousLinearMap.comp_apply] at hInverseApply
  exact hInverseApply

/-! ## Metric-normal projection of the moving graph -/

/-- Pairing of an ambient vector with the tangent image of the moving graph. -/
def normalGraphTangentialPairing
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (point : EffectiveThroat period hPeriod)
    (ambientVector : TangentSpace coverModelWithCorners
      (normalGraph period hPeriod displacement parameter point)) :
    ThroatCotangentFiber period hPeriod point :=
  (metric.tensor.tensor
      (normalGraph period hPeriod displacement parameter point)
      ambientVector).comp
    (mfderiv throatCoverModelWithCorners coverModelWithCorners
      (normalGraph period hPeriod displacement parameter) point)

@[simp]
theorem normalGraphTangentialPairing_apply
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (point : EffectiveThroat period hPeriod)
    (ambientVector : TangentSpace coverModelWithCorners
      (normalGraph period hPeriod displacement parameter point))
    (tangent : ThroatTangentFiber period hPeriod point) :
    normalGraphTangentialPairing period hPeriod metric displacement parameter
        point ambientVector tangent =
      metric.tensor.tensor
        (normalGraph period hPeriod displacement parameter point)
        ambientVector
        (mfderiv throatCoverModelWithCorners coverModelWithCorners
          (normalGraph period hPeriod displacement parameter) point tangent) :=
  rfl

/-- Tangential component of an ambient vector, computed with the inverse of
the genuinely induced metric. -/
def normalGraphTangentialProjection
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (point : EffectiveThroat period hPeriod)
    (ambientVector : TangentSpace coverModelWithCorners
      (normalGraph period hPeriod displacement parameter point)) :
    TangentSpace coverModelWithCorners
      (normalGraph period hPeriod displacement parameter point) :=
  mfderiv throatCoverModelWithCorners coverModelWithCorners
      (normalGraph period hPeriod displacement parameter) point
    (normalGraphInducedMetricInverse period hPeriod metric displacement parameter
      hNonNull point
      (normalGraphTangentialPairing period hPeriod metric displacement parameter
        point ambientVector))

/-- Orthogonal representative of an ambient transverse vector.  It is built
from the same graph and the same ambient metric as the induced family. -/
def normalGraphMetricNormal
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (point : EffectiveThroat period hPeriod)
    (ambientVector : TangentSpace coverModelWithCorners
      (normalGraph period hPeriod displacement parameter point)) :
    TangentSpace coverModelWithCorners
      (normalGraph period hPeriod displacement parameter point) :=
  ambientVector -
    normalGraphTangentialProjection period hPeriod metric displacement parameter
      hNonNull point ambientVector

/-- The metric-normal projection is orthogonal to every genuine graph
tangent. -/
theorem normalGraphMetricNormal_orthogonal
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (point : EffectiveThroat period hPeriod)
    (ambientVector : TangentSpace coverModelWithCorners
      (normalGraph period hPeriod displacement parameter point))
    (tangent : ThroatTangentFiber period hPeriod point) :
    metric.tensor.tensor
        (normalGraph period hPeriod displacement parameter point)
        (normalGraphMetricNormal period hPeriod metric displacement parameter
          hNonNull point ambientVector)
        (mfderiv throatCoverModelWithCorners coverModelWithCorners
          (normalGraph period hPeriod displacement parameter) point tangent) =
      0 := by
  let pairing := normalGraphTangentialPairing period hPeriod metric displacement
    parameter point ambientVector
  let sharp := normalGraphInducedMetricInverse period hPeriod metric displacement
    parameter hNonNull point pairing
  have hInverse := congrArg (fun covector => covector tangent)
    (normalGraphInducedMetric_metricInverse period hPeriod metric displacement
      parameter hNonNull point pairing)
  change metric.tensor.tensor _
      (ambientVector -
        mfderiv throatCoverModelWithCorners coverModelWithCorners
          (normalGraph period hPeriod displacement parameter) point sharp) _ = 0
  rw [map_sub]
  change metric.tensor.tensor _ ambientVector _ -
      metric.tensor.tensor _
        (mfderiv throatCoverModelWithCorners coverModelWithCorners
          (normalGraph period hPeriod displacement parameter) point sharp) _ = 0
  rw [sub_eq_zero]
  change pairing tangent =
    normalGraphInducedMetricValue period hPeriod metric displacement parameter
      point sharp tangent
  exact hInverse.symm

/-- Transversality is the intrinsic statement that the chosen ambient vector
does not lie in the tangent image of the graph. -/
def NormalGraphTransverseVectorAt
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (point : EffectiveThroat period hPeriod)
    (ambientVector : TangentSpace coverModelWithCorners
      (normalGraph period hPeriod displacement parameter point)) : Prop :=
  ambientVector ∉ Set.range
    (mfderiv throatCoverModelWithCorners coverModelWithCorners
      (normalGraph period hPeriod displacement parameter) point)

/-- Orthogonal projection cannot kill a genuinely transverse vector. -/
theorem normalGraphMetricNormal_ne_zero
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (point : EffectiveThroat period hPeriod)
    (ambientVector : TangentSpace coverModelWithCorners
      (normalGraph period hPeriod displacement parameter point))
    (hTransverse : NormalGraphTransverseVectorAt period hPeriod displacement
      parameter point ambientVector) :
    normalGraphMetricNormal period hPeriod metric displacement parameter
      hNonNull point ambientVector ≠ 0 := by
  intro hZero
  apply hTransverse
  refine ⟨normalGraphInducedMetricInverse period hPeriod metric displacement
      parameter hNonNull point
      (normalGraphTangentialPairing period hPeriod metric displacement parameter
        point ambientVector), ?_⟩
  exact (sub_eq_zero.mp hZero).symm

/-- Adding a graph tangent changes the tangential pairing by the induced
metric of that tangent. -/
theorem normalGraphTangentialPairing_add_tangent
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (point : EffectiveThroat period hPeriod)
    (ambientVector : TangentSpace coverModelWithCorners
      (normalGraph period hPeriod displacement parameter point))
    (shift : ThroatTangentFiber period hPeriod point) :
    normalGraphTangentialPairing period hPeriod metric displacement parameter
        point
        (ambientVector +
          mfderiv throatCoverModelWithCorners coverModelWithCorners
            (normalGraph period hPeriod displacement parameter) point shift) =
      normalGraphTangentialPairing period hPeriod metric displacement parameter
          point ambientVector +
        normalGraphInducedMetricValue period hPeriod metric displacement
          parameter point shift := by
  apply ContinuousLinearMap.ext
  intro tangent
  simp only [normalGraphTangentialPairing_apply,
    normalGraphInducedMetricValue_apply, map_add, add_apply]

/-- The orthogonal representative depends only on the normal quotient class:
changing a local lift by a genuine graph tangent leaves it unchanged. -/
theorem normalGraphMetricNormal_add_tangent
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (point : EffectiveThroat period hPeriod)
    (ambientVector : TangentSpace coverModelWithCorners
      (normalGraph period hPeriod displacement parameter point))
    (shift : ThroatTangentFiber period hPeriod point) :
    normalGraphMetricNormal period hPeriod metric displacement parameter
        hNonNull point
        (ambientVector +
          mfderiv throatCoverModelWithCorners coverModelWithCorners
            (normalGraph period hPeriod displacement parameter) point shift) =
      normalGraphMetricNormal period hPeriod metric displacement parameter
        hNonNull point ambientVector := by
  unfold normalGraphMetricNormal normalGraphTangentialProjection
  rw [normalGraphTangentialPairing_add_tangent period hPeriod metric
    displacement parameter point ambientVector shift, map_add,
    normalGraphInducedMetricInverse_metric, map_add]
  abel

/-- Tangent range of the actual displaced embedding. -/
def NormalGraphTangentRange
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (point : EffectiveThroat period hPeriod) :
    Submodule Real (TangentSpace coverModelWithCorners
      (normalGraph period hPeriod displacement parameter point)) :=
  LinearMap.range
    (mfderiv throatCoverModelWithCorners coverModelWithCorners
      (normalGraph period hPeriod displacement parameter) point).toLinearMap

/-- Differential normal fiber of the moving graph, defined without selecting
a global normal frame. -/
abbrev MovingGraphDifferentialNormalFiber
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (point : EffectiveThroat period hPeriod) :=
  (TangentSpace coverModelWithCorners
      (normalGraph period hPeriod displacement parameter point)) ⧸
    (NormalGraphTangentRange period hPeriod displacement parameter point)

/-- Continuous-linear form of the metric-normal projector. -/
def normalGraphMetricNormalLinearMap
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (point : EffectiveThroat period hPeriod) :
    TangentSpace coverModelWithCorners
        (normalGraph period hPeriod displacement parameter point) →L[Real]
      TangentSpace coverModelWithCorners
        (normalGraph period hPeriod displacement parameter point) :=
  let derivative :=
    mfderiv throatCoverModelWithCorners coverModelWithCorners
      (normalGraph period hPeriod displacement parameter) point
  let pairing := (derivative.precomp Real).comp
    (metric.tensor.tensor
      (normalGraph period hPeriod displacement parameter point))
  ContinuousLinearMap.id Real _ -
    derivative.comp
      ((normalGraphInducedMetricInverse period hPeriod metric displacement
        parameter hNonNull point).toContinuousLinearMap.comp pairing)

/-- Fixed-model coordinate expression of the metric-normal projector.  It is
assembled only from the graph differential, the ambient metric and the
inverse of the genuinely induced metric. -/
def normalGraphMetricNormalProjectorCoordinates
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base current : EffectiveThroat period hPeriod × Real) :
    CoverCoordinates →L[Real] CoverCoordinates :=
  let derivative := normalGraphFamilyDerivativeCoordinates period hPeriod
    displacement base current
  let ambientMetric := normalGraphFamilyAmbientTensorCoordinates period hPeriod
    metric displacement base current
  let inverseMetric := normalGraphInducedMetricInverseCoordinates period hPeriod
    metric displacement base current
  ContinuousLinearMap.id Real CoverCoordinates -
    derivative.comp
      (inverseMetric.comp ((derivative.precomp Real).comp ambientMetric))

/-- The actual normal projector is jointly smooth in the moving graph
parameter and throat point on the intrinsic non-null locus. -/
theorem normalGraphMetricNormalProjectorCoordinates_contMDiffAt
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement base.2) :
    ContMDiffAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      𝓘(Real, CoverCoordinates →L[Real] CoverCoordinates) ∞
      (normalGraphMetricNormalProjectorCoordinates period hPeriod metric
        displacement base) base := by
  have hDerivative :=
    normalGraphFamilyDerivativeCoordinates_contMDiffAt period hPeriod
      displacement base
  have hAmbient :=
    normalGraphFamilyAmbientTensorCoordinates_contMDiffAt period hPeriod metric
      displacement base
  have hInverse :=
    normalGraphInducedMetricInverseCoordinates_contMDiffAt period hPeriod metric
      displacement base hNonNull
  have hPairing :=
    (hDerivative.clm_precomp (F₃ := Real)).clm_comp hAmbient
  have hTangential := hDerivative.clm_comp (hInverse.clm_comp hPairing)
  exact contMDiffAt_const.sub hTangential

private theorem normalGraphMetricTangentialPairingCoordinates_apply
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base current : EffectiveThroat period hPeriod × Real)
    (hTangent : current.1 ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) base.1).baseSet)
    (hImage : normalGraph period hPeriod displacement current.2 current.1 ∈
      (trivializationAt CoverCoordinates
        (fun point : EffectiveQuotient period hPeriod =>
          TangentSpace coverModelWithCorners point)
        (normalGraph period hPeriod displacement base.2 base.1)).baseSet)
    (ambientVector : CoverCoordinates)
    (tangent : ThroatCoverCoordinates) :
    ((normalGraphFamilyDerivativeCoordinates period hPeriod displacement base
          current).precomp Real).comp
        (normalGraphFamilyAmbientTensorCoordinates period hPeriod metric
          displacement base current) ambientVector tangent =
      normalGraphTangentialPairing period hPeriod metric displacement current.2
        current.1
        ((trivializationAt CoverCoordinates
          (fun point : EffectiveQuotient period hPeriod =>
            TangentSpace coverModelWithCorners point)
          (normalGraph period hPeriod displacement base.2 base.1)).symm
            (normalGraph period hPeriod displacement current.2 current.1)
            ambientVector)
        ((trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) base.1).symm current.1 tangent) := by
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.precomp_apply]
  rw [show normalGraphFamilyAmbientTensorCoordinates period hPeriod metric
      displacement base current ambientVector
      (normalGraphFamilyDerivativeCoordinates period hPeriod displacement base
        current tangent) =
    ContinuousLinearMap.inCoordinates CoverCoordinates
      (fun point : EffectiveQuotient period hPeriod =>
        TangentSpace coverModelWithCorners point)
      (CoverCoordinates →L[Real] Real)
      (fun point : EffectiveQuotient period hPeriod =>
        TangentSpace coverModelWithCorners point →L[Real] Real)
      (normalGraph period hPeriod displacement base.2 base.1)
      (normalGraph period hPeriod displacement current.2 current.1)
      (normalGraph period hPeriod displacement base.2 base.1)
      (normalGraph period hPeriod displacement current.2 current.1)
      (metric.tensor.tensor
        (normalGraph period hPeriod displacement current.2 current.1))
      ambientVector
      (normalGraphFamilyDerivativeCoordinates period hPeriod displacement base
        current tangent) by rfl]
  rw [inCoordinates_apply_eq₂ hImage hImage (Set.mem_univ _)]
  rw [normalGraphFamilyDerivativeCoordinates_apply period hPeriod displacement
    base current hTangent hImage]
  simp only [Trivialization.symm_linearMapAt _ hImage]
  simp

/-- The smooth fixed-model projector is exactly the coordinate expression of
the intrinsic metric-normal projector, not an additional boundary datum. -/
theorem normalGraphMetricNormalProjectorCoordinates_eq_inCoordinates
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base current : EffectiveThroat period hPeriod × Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement
      current.2)
    (hTangent : current.1 ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) base.1).baseSet)
    (hCotangent : current.1 ∈
      (trivializationAt (ThroatCoverCoordinates →L[Real] Real)
        (ThroatCotangentFiber period hPeriod) base.1).baseSet)
    (hImage : normalGraph period hPeriod displacement current.2 current.1 ∈
      (trivializationAt CoverCoordinates
        (fun point : EffectiveQuotient period hPeriod =>
          TangentSpace coverModelWithCorners point)
        (normalGraph period hPeriod displacement base.2 base.1)).baseSet) :
    normalGraphMetricNormalProjectorCoordinates period hPeriod metric
        displacement base current =
      ContinuousLinearMap.inCoordinates CoverCoordinates
        (fun point : EffectiveQuotient period hPeriod =>
          TangentSpace coverModelWithCorners point)
        CoverCoordinates
        (fun point : EffectiveQuotient period hPeriod =>
          TangentSpace coverModelWithCorners point)
        (normalGraph period hPeriod displacement base.2 base.1)
        (normalGraph period hPeriod displacement current.2 current.1)
        (normalGraph period hPeriod displacement base.2 base.1)
        (normalGraph period hPeriod displacement current.2 current.1)
        (normalGraphMetricNormalLinearMap period hPeriod metric displacement
          current.2 hNonNull current.1) := by
  unfold normalGraphMetricNormalProjectorCoordinates
  rw [normalGraphInducedMetricInverseCoordinates_eq_inCoordinates period hPeriod
    metric displacement base current hNonNull hTangent hCotangent]
  apply ContinuousLinearMap.ext
  intro vector
  let ambientEquiv :=
    (trivializationAt CoverCoordinates
      (fun point : EffectiveQuotient period hPeriod =>
        TangentSpace coverModelWithCorners point)
      (normalGraph period hPeriod displacement base.2 base.1)
      ).continuousLinearEquivAt Real
        (normalGraph period hPeriod displacement current.2 current.1) hImage
  let tangentEquiv :=
    (trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) base.1).continuousLinearEquivAt
        Real current.1 hTangent
  let cotangentEquiv :=
    (trivializationAt (ThroatCoverCoordinates →L[Real] Real)
      (ThroatCotangentFiber period hPeriod) base.1).continuousLinearEquivAt
        Real current.1 hCotangent
  let ambientVector := ambientEquiv.symm vector
  let pairing := normalGraphTangentialPairing period hPeriod metric displacement
    current.2 current.1 ambientVector
  have hDerivativeCoordinates
      (tangent : ThroatCoverCoordinates) :
      normalGraphFamilyDerivativeCoordinates period hPeriod displacement base
          current tangent =
        ambientEquiv
          (mfderiv throatCoverModelWithCorners coverModelWithCorners
            (normalGraph period hPeriod displacement current.2) current.1
            (tangentEquiv.symm tangent)) := by
    rw [normalGraphFamilyDerivativeCoordinates_apply period hPeriod displacement
      base current hTangent hImage]
    rw [Trivialization.linearMapAt_apply, if_pos hImage]
    rfl
  have hPairingCoordinates :
      ((normalGraphFamilyDerivativeCoordinates period hPeriod displacement base
            current).precomp Real).comp
          (normalGraphFamilyAmbientTensorCoordinates period hPeriod metric
            displacement base current) vector =
        cotangentEquiv pairing := by
    apply ContinuousLinearMap.ext
    intro tangent
    rw [normalGraphMetricTangentialPairingCoordinates_apply period hPeriod
      metric displacement base current hTangent hImage vector tangent]
    change _ =
      ContinuousLinearMap.inCoordinates ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) Real
        (fun _ : EffectiveThroat period hPeriod => Real)
        base.1 current.1 base.1 current.1 pairing tangent
    rw [ContinuousLinearMap.inCoordinates_eq hTangent (by simp)]
    simp
    exact (normalGraphTangentialPairing_apply period hPeriod metric displacement
      current.2 current.1 ambientVector (tangentEquiv.symm tangent)).symm
  have hInverseCoordinates :
      ContinuousLinearMap.inCoordinates
          (ThroatCoverCoordinates →L[Real] Real)
          (ThroatCotangentFiber period hPeriod)
          ThroatCoverCoordinates (ThroatTangentFiber period hPeriod)
          base.1 current.1 base.1 current.1
          (normalGraphInducedMetricInverse period hPeriod metric displacement
            current.2 hNonNull current.1).toContinuousLinearMap
          (((normalGraphFamilyDerivativeCoordinates period hPeriod displacement
                base current).precomp Real).comp
            (normalGraphFamilyAmbientTensorCoordinates period hPeriod metric
              displacement base current) vector) =
        tangentEquiv
          (normalGraphInducedMetricInverse period hPeriod metric displacement
            current.2 hNonNull current.1 pairing) := by
    rw [ContinuousLinearMap.inCoordinates_eq hCotangent hTangent,
      hPairingCoordinates]
    change tangentEquiv
        (normalGraphInducedMetricInverse period hPeriod metric displacement
          current.2 hNonNull current.1
          (cotangentEquiv.symm (cotangentEquiv pairing))) =
      tangentEquiv
        (normalGraphInducedMetricInverse period hPeriod metric displacement
          current.2 hNonNull current.1 pairing)
    rw [ContinuousLinearEquiv.symm_apply_apply]
  simp only [sub_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.comp_apply]
  change vector -
      normalGraphFamilyDerivativeCoordinates period hPeriod displacement base
        current
        (ContinuousLinearMap.inCoordinates
          (ThroatCoverCoordinates →L[Real] Real)
          (ThroatCotangentFiber period hPeriod)
          ThroatCoverCoordinates (ThroatTangentFiber period hPeriod)
          base.1 current.1 base.1 current.1
          (normalGraphInducedMetricInverse period hPeriod metric displacement
            current.2 hNonNull current.1).toContinuousLinearMap
          (((normalGraphFamilyDerivativeCoordinates period hPeriod displacement
                base current).precomp Real).comp
            (normalGraphFamilyAmbientTensorCoordinates period hPeriod metric
              displacement base current) vector)) = _
  rw [hInverseCoordinates, hDerivativeCoordinates]
  simp only [ContinuousLinearEquiv.symm_apply_apply]
  rw [ContinuousLinearMap.inCoordinates_eq hImage hImage]
  simp only [normalGraphMetricNormalLinearMap,
    ContinuousLinearMap.comp_apply, sub_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.precomp_apply,
    ContinuousLinearEquiv.coe_coe, map_sub,
    ContinuousLinearEquiv.apply_symm_apply]
  rfl

@[simp]
theorem normalGraphMetricNormalLinearMap_apply
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (point : EffectiveThroat period hPeriod)
    (ambientVector : TangentSpace coverModelWithCorners
      (normalGraph period hPeriod displacement parameter point)) :
    normalGraphMetricNormalLinearMap period hPeriod metric displacement parameter
        hNonNull point ambientVector =
      normalGraphMetricNormal period hPeriod metric displacement parameter
        hNonNull point ambientVector :=
  rfl

@[simp]
theorem normalGraphMetricNormalLinearMap_tangent
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (point : EffectiveThroat period hPeriod)
    (tangent : ThroatTangentFiber period hPeriod point) :
    normalGraphMetricNormalLinearMap period hPeriod metric displacement parameter
        hNonNull point
        (mfderiv throatCoverModelWithCorners coverModelWithCorners
          (normalGraph period hPeriod displacement parameter) point tangent) =
      0 := by
  rw [normalGraphMetricNormalLinearMap_apply]
  calc
    normalGraphMetricNormal period hPeriod metric displacement parameter
        hNonNull point
        (mfderiv throatCoverModelWithCorners coverModelWithCorners
          (normalGraph period hPeriod displacement parameter) point tangent) =
      normalGraphMetricNormal period hPeriod metric displacement parameter
        hNonNull point
        (0 + mfderiv throatCoverModelWithCorners coverModelWithCorners
          (normalGraph period hPeriod displacement parameter) point tangent) := by
            rw [zero_add]
    _ = normalGraphMetricNormal period hPeriod metric displacement parameter
        hNonNull point 0 :=
      normalGraphMetricNormal_add_tangent period hPeriod metric displacement
        parameter hNonNull point 0 tangent
    _ = 0 := by
      simp [normalGraphMetricNormal, normalGraphTangentialProjection,
        normalGraphTangentialPairing]

/-- The metric-normal projector therefore descends canonically to the moving
differential-normal quotient. -/
def normalGraphMetricNormalFromClass
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (point : EffectiveThroat period hPeriod) :
    MovingGraphDifferentialNormalFiber period hPeriod displacement parameter
        point →ₗ[Real]
      TangentSpace coverModelWithCorners
        (normalGraph period hPeriod displacement parameter point) :=
  (NormalGraphTangentRange period hPeriod displacement parameter point).liftQ
    (normalGraphMetricNormalLinearMap period hPeriod metric displacement
      parameter hNonNull point).toLinearMap
    (by
      intro vector hVector
      obtain ⟨tangent, rfl⟩ := hVector
      exact normalGraphMetricNormalLinearMap_tangent period hPeriod metric
        displacement parameter hNonNull point tangent)

@[simp]
theorem normalGraphMetricNormalFromClass_mk
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (point : EffectiveThroat period hPeriod)
    (ambientVector : TangentSpace coverModelWithCorners
      (normalGraph period hPeriod displacement parameter point)) :
    normalGraphMetricNormalFromClass period hPeriod metric displacement parameter
        hNonNull point
        (Submodule.Quotient.mk ambientVector :
          MovingGraphDifferentialNormalFiber period hPeriod displacement
            parameter point) =
      normalGraphMetricNormal period hPeriod metric displacement parameter
        hNonNull point ambientVector :=
  rfl

/-- The kernel of the metric-normal projector is exactly the graph tangent
range. -/
theorem normalGraphMetricNormalLinearMap_eq_zero_iff
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (point : EffectiveThroat period hPeriod)
    (ambientVector : TangentSpace coverModelWithCorners
      (normalGraph period hPeriod displacement parameter point)) :
    normalGraphMetricNormalLinearMap period hPeriod metric displacement parameter
        hNonNull point ambientVector = 0 ↔
      ambientVector ∈
        NormalGraphTangentRange period hPeriod displacement parameter point := by
  constructor
  · intro hZero
    rw [normalGraphMetricNormalLinearMap_apply] at hZero
    refine ⟨normalGraphInducedMetricInverse period hPeriod metric displacement
        parameter hNonNull point
        (normalGraphTangentialPairing period hPeriod metric displacement parameter
          point ambientVector), ?_⟩
    exact (sub_eq_zero.mp hZero).symm
  · rintro ⟨tangent, rfl⟩
    exact normalGraphMetricNormalLinearMap_tangent period hPeriod metric
      displacement parameter hNonNull point tangent

/-- No nonzero moving normal class is lost by metric orthogonalization. -/
theorem normalGraphMetricNormalFromClass_injective
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (point : EffectiveThroat period hPeriod) :
    Function.Injective
      (normalGraphMetricNormalFromClass period hPeriod metric displacement
        parameter hNonNull point) := by
  refine (injective_iff_map_eq_zero _).mpr ?_
  intro normalClass hZero
  induction normalClass using Submodule.Quotient.induction_on with
  | _ ambientVector =>
      rw [normalGraphMetricNormalFromClass_mk] at hZero
      apply (Submodule.Quotient.mk_eq_zero
        (NormalGraphTangentRange period hPeriod displacement parameter point)).2
      exact (normalGraphMetricNormalLinearMap_eq_zero_iff period hPeriod metric
        displacement parameter hNonNull point ambientVector).1 hZero

/-- In particular, every nonzero twisted normal class has a nonzero canonical
metric-normal representative. -/
theorem normalGraphMetricNormalFromClass_ne_zero
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (point : EffectiveThroat period hPeriod)
    (normalClass : MovingGraphDifferentialNormalFiber period hPeriod displacement
      parameter point)
    (hClass : normalClass ≠ 0) :
    normalGraphMetricNormalFromClass period hPeriod metric displacement parameter
      hNonNull point normalClass ≠ 0 := by
  intro hZero
  have hEq :
      normalGraphMetricNormalFromClass period hPeriod metric displacement
          parameter hNonNull point normalClass =
        normalGraphMetricNormalFromClass period hPeriod metric displacement
          parameter hNonNull point 0 := by
    simpa using hZero
  exact hClass ((normalGraphMetricNormalFromClass_injective period hPeriod metric
    displacement parameter hNonNull point) hEq)

/-- Nondegeneracy of the induced metric forces the graph differential itself
to be injective. -/
theorem normalGraph_mfderiv_injective
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (point : EffectiveThroat period hPeriod) :
    Function.Injective
      (mfderiv throatCoverModelWithCorners coverModelWithCorners
        (normalGraph period hPeriod displacement parameter) point) := by
  refine (injective_iff_map_eq_zero _).mpr ?_
  intro tangent hTangent
  apply (injective_iff_map_eq_zero _).mp (hNonNull point)
  apply ContinuousLinearMap.ext
  intro other
  rw [normalGraphInducedMetricValue_apply, hTangent]
  simp

/-- The moving differential-normal quotient is intrinsically one-dimensional;
this is derived from the actual graph differential, not postulated. -/
theorem movingGraphDifferentialNormalFiber_finrank
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (point : EffectiveThroat period hPeriod) :
    Module.finrank Real
        (MovingGraphDifferentialNormalFiber period hPeriod displacement
          parameter point) = 1 := by
  let derivative :=
    (mfderiv throatCoverModelWithCorners coverModelWithCorners
      (normalGraph period hPeriod displacement parameter) point).toLinearMap
  have hDerivative : Function.Injective derivative :=
    normalGraph_mfderiv_injective period hPeriod metric displacement parameter
      hNonNull point
  have hRange : Module.finrank Real
      (NormalGraphTangentRange period hPeriod displacement parameter point) = 3 := by
    change Module.finrank Real (LinearMap.range derivative) = 3
    rw [LinearMap.finrank_range_of_inj hDerivative]
    change Module.finrank Real ThroatCoverCoordinates = 3
    simp [ThroatCoverCoordinates]
  have hAmbient : Module.finrank Real
      (TangentSpace coverModelWithCorners
        (normalGraph period hPeriod displacement parameter point)) = 4 := by
    change Module.finrank Real CoverCoordinates = 4
    simp [CoverCoordinates]
  have hDimension :=
    (NormalGraphTangentRange period hPeriod displacement parameter point
      ).finrank_quotient_add_finrank
  have hDimension' :
      Module.finrank Real
          (MovingGraphDifferentialNormalFiber period hPeriod displacement
            parameter point) + 3 = 4 := by
    simpa only [hRange, hAmbient] using hDimension
  omega

/-- The descended representative is orthogonal to every graph tangent. -/
theorem normalGraphMetricNormalFromClass_orthogonal
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (point : EffectiveThroat period hPeriod)
    (normalClass : MovingGraphDifferentialNormalFiber period hPeriod displacement
      parameter point)
    (tangent : ThroatTangentFiber period hPeriod point) :
    metric.tensor.tensor
        (normalGraph period hPeriod displacement parameter point)
        (normalGraphMetricNormalFromClass period hPeriod metric displacement
          parameter hNonNull point normalClass)
        (mfderiv throatCoverModelWithCorners coverModelWithCorners
          (normalGraph period hPeriod displacement parameter) point tangent) =
      0 := by
  induction normalClass using Submodule.Quotient.induction_on with
  | _ ambientVector =>
      rw [normalGraphMetricNormalFromClass_mk]
      exact normalGraphMetricNormal_orthogonal period hPeriod metric displacement
        parameter hNonNull point ambientVector tangent

/-- Metric square of a twisted moving normal class. -/
def normalGraphMetricNormalSquare
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (point : EffectiveThroat period hPeriod)
    (normalClass : MovingGraphDifferentialNormalFiber period hPeriod displacement
      parameter point) : Real :=
  metric.tensor.tensor
    (normalGraph period hPeriod displacement parameter point)
    (normalGraphMetricNormalFromClass period hPeriod metric displacement parameter
      hNonNull point normalClass)
    (normalGraphMetricNormalFromClass period hPeriod metric displacement parameter
      hNonNull point normalClass)

/-- A nonzero moving normal class is intrinsically non-null.  The proof uses
only ambient metric nondegeneracy, nondegeneracy of the induced metric and the
derived one-dimensionality of the quotient normal fiber. -/
theorem normalGraphMetricNormalSquare_ne_zero
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (point : EffectiveThroat period hPeriod)
    (normalClass : MovingGraphDifferentialNormalFiber period hPeriod displacement
      parameter point)
    (hClass : normalClass ≠ 0) :
    normalGraphMetricNormalSquare period hPeriod metric displacement parameter
      hNonNull point normalClass ≠ 0 := by
  let normalMap := normalGraphMetricNormalFromClass period hPeriod metric
    displacement parameter hNonNull point
  let normal := normalMap normalClass
  have hNormal : normal ≠ 0 :=
    normalGraphMetricNormalFromClass_ne_zero period hPeriod metric displacement
      parameter hNonNull point normalClass hClass
  intro hSquare
  have hFlatZero :
      metric.tensor.tensor
        (normalGraph period hPeriod displacement parameter point) normal = 0 := by
    apply ContinuousLinearMap.ext
    intro ambientVector
    let tangent :=
      normalGraphInducedMetricInverse period hPeriod metric displacement
        parameter hNonNull point
        (normalGraphTangentialPairing period hPeriod metric displacement parameter
          point ambientVector)
    let normalVector := normalGraphMetricNormal period hPeriod metric displacement
      parameter hNonNull point ambientVector
    let ambientClass : MovingGraphDifferentialNormalFiber period hPeriod
        displacement parameter point := Submodule.Quotient.mk ambientVector
    obtain ⟨scalar, hScalar⟩ := exists_smul_eq_of_finrank_eq_one
      (movingGraphDifferentialNormalFiber_finrank period hPeriod metric
        displacement parameter hNonNull point) hClass ambientClass
    have hNormalVector : normalVector = scalar • normal := by
      calc
        normalVector = normalMap ambientClass := by
          exact (normalGraphMetricNormalFromClass_mk period hPeriod metric
            displacement parameter hNonNull point ambientVector).symm
        _ = normalMap (scalar • normalClass) := by rw [hScalar]
        _ = scalar • normal := by
          exact map_smul normalMap scalar normalClass
    have hDecomposition :
        mfderiv throatCoverModelWithCorners coverModelWithCorners
              (normalGraph period hPeriod displacement parameter) point tangent +
            normalVector = ambientVector := by
      unfold normalVector normalGraphMetricNormal
      unfold tangent normalGraphTangentialProjection
      abel
    rw [← hDecomposition, map_add,
      normalGraphMetricNormalFromClass_orthogonal period hPeriod metric
        displacement parameter hNonNull point normalClass tangent,
      hNormalVector, map_smul]
    change 0 + scalar *
      metric.tensor.tensor
        (normalGraph period hPeriod displacement parameter point) normal normal = 0
    rw [show
      metric.tensor.tensor
          (normalGraph period hPeriod displacement parameter point) normal normal =
        normalGraphMetricNormalSquare period hPeriod metric displacement parameter
          hNonNull point normalClass by rfl,
      hSquare]
    simp
  have hNormalZero : normal = 0 :=
    (injective_iff_map_eq_zero _).mp
      (metric_nondegenerate_at period hPeriod metric
        (normalGraph period hPeriod displacement parameter point)) normal
          hFlatZero
  exact hNormal hNormalZero

/-- Causal sign of a nonzero metric-normal class. -/
def normalGraphMetricNormalCausalSign
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (point : EffectiveThroat period hPeriod)
    (normalClass : MovingGraphDifferentialNormalFiber period hPeriod displacement
      parameter point) : Real :=
  normalGraphMetricNormalSquare period hPeriod metric displacement parameter
      hNonNull point normalClass /
    |normalGraphMetricNormalSquare period hPeriod metric displacement parameter
      hNonNull point normalClass|

/-- Intrinsic unit representative of a moving twisted normal class. -/
def normalGraphMetricUnitNormal
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (point : EffectiveThroat period hPeriod)
    (normalClass : MovingGraphDifferentialNormalFiber period hPeriod displacement
      parameter point) :
    TangentSpace coverModelWithCorners
      (normalGraph period hPeriod displacement parameter point) :=
  (Real.sqrt
    |normalGraphMetricNormalSquare period hPeriod metric displacement parameter
      hNonNull point normalClass|)⁻¹ •
    normalGraphMetricNormalFromClass period hPeriod metric displacement parameter
      hNonNull point normalClass

@[simp]
theorem normalGraphMetricUnitNormal_neg
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (point : EffectiveThroat period hPeriod)
    (normalClass : MovingGraphDifferentialNormalFiber period hPeriod displacement
      parameter point) :
    normalGraphMetricUnitNormal period hPeriod metric displacement parameter
        hNonNull point (-normalClass) =
      -normalGraphMetricUnitNormal period hPeriod metric displacement parameter
        hNonNull point normalClass := by
  simp [normalGraphMetricUnitNormal, normalGraphMetricNormalSquare]

/-- The causal sign of a nonzero class is exactly `+1` or `-1`. -/
theorem normalGraphMetricNormalCausalSign_admissible
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (point : EffectiveThroat period hPeriod)
    (normalClass : MovingGraphDifferentialNormalFiber period hPeriod displacement
      parameter point)
    (hClass : normalClass ≠ 0) :
    normalGraphMetricNormalCausalSign period hPeriod metric displacement parameter
        hNonNull point normalClass = 1 ∨
      normalGraphMetricNormalCausalSign period hPeriod metric displacement parameter
        hNonNull point normalClass = -1 := by
  let square := normalGraphMetricNormalSquare period hPeriod metric displacement
    parameter hNonNull point normalClass
  have hSquare : square ≠ 0 :=
    normalGraphMetricNormalSquare_ne_zero period hPeriod metric displacement
      parameter hNonNull point normalClass hClass
  rcases lt_or_gt_of_ne hSquare with hNegative | hPositive
  · right
    unfold normalGraphMetricNormalCausalSign
    change square / |square| = -1
    rw [abs_of_neg hNegative]
    field_simp
  · left
    unfold normalGraphMetricNormalCausalSign
    change square / |square| = 1
    rw [abs_of_pos hPositive]
    exact div_self hSquare

/-- The normalized representative has the derived causal square. -/
theorem normalGraphMetricUnitNormal_square
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (point : EffectiveThroat period hPeriod)
    (normalClass : MovingGraphDifferentialNormalFiber period hPeriod displacement
      parameter point)
    (hClass : normalClass ≠ 0) :
    metric.tensor.tensor
        (normalGraph period hPeriod displacement parameter point)
        (normalGraphMetricUnitNormal period hPeriod metric displacement parameter
          hNonNull point normalClass)
        (normalGraphMetricUnitNormal period hPeriod metric displacement parameter
          hNonNull point normalClass) =
      normalGraphMetricNormalCausalSign period hPeriod metric displacement
        parameter hNonNull point normalClass := by
  let square := normalGraphMetricNormalSquare period hPeriod metric displacement
    parameter hNonNull point normalClass
  let root := Real.sqrt |square|
  have hSquare : square ≠ 0 :=
    normalGraphMetricNormalSquare_ne_zero period hPeriod metric displacement
      parameter hNonNull point normalClass hClass
  have hAbs : |square| ≠ 0 := abs_ne_zero.mpr hSquare
  have hRoot : root ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.2 (abs_pos.mpr hSquare))
  have hRootSquare : root ^ 2 = |square| := by
    exact Real.sq_sqrt (abs_nonneg square)
  unfold normalGraphMetricUnitNormal
  rw [map_smul, map_smul]
  change root⁻¹ * (root⁻¹ * square) = square / |square|
  field_simp
  nlinarith

/-- Hence the normalized square has absolute value one. -/
theorem abs_normalGraphMetricUnitNormal_square
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (point : EffectiveThroat period hPeriod)
    (normalClass : MovingGraphDifferentialNormalFiber period hPeriod displacement
      parameter point)
    (hClass : normalClass ≠ 0) :
    |metric.tensor.tensor
        (normalGraph period hPeriod displacement parameter point)
        (normalGraphMetricUnitNormal period hPeriod metric displacement parameter
          hNonNull point normalClass)
        (normalGraphMetricUnitNormal period hPeriod metric displacement parameter
          hNonNull point normalClass)| = 1 := by
  rw [normalGraphMetricUnitNormal_square period hPeriod metric displacement
    parameter hNonNull point normalClass hClass]
  rcases normalGraphMetricNormalCausalSign_admissible period hPeriod metric
      displacement parameter hNonNull point normalClass hClass with hSign | hSign
  · rw [hSign]
    norm_num
  · rw [hSign]
    norm_num

/-! ## Local nonvanishing metric-normal fields -/

/-- A local metric-normal field in one fixed tangent trivialization.  Its
coordinate vector is obtained by applying the genuine intrinsic projector to
one constant ambient coordinate vector. -/
def normalGraphLocalMetricNormalCoordinates
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (ambientCoordinate : CoverCoordinates)
    (current : EffectiveThroat period hPeriod × Real) : CoverCoordinates :=
  normalGraphMetricNormalProjectorCoordinates period hPeriod metric displacement
    base current ambientCoordinate

/-- The local coordinate field is exactly the intrinsic metric normal written
in the chosen tangent trivialization. -/
theorem normalGraphLocalMetricNormalCoordinates_eq_intrinsic
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base current : EffectiveThroat period hPeriod × Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement
      current.2)
    (hTangent : current.1 ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) base.1).baseSet)
    (hCotangent : current.1 ∈
      (trivializationAt (ThroatCoverCoordinates →L[Real] Real)
        (ThroatCotangentFiber period hPeriod) base.1).baseSet)
    (hImage : normalGraph period hPeriod displacement current.2 current.1 ∈
      (trivializationAt CoverCoordinates
        (fun point : EffectiveQuotient period hPeriod =>
          TangentSpace coverModelWithCorners point)
        (normalGraph period hPeriod displacement base.2 base.1)).baseSet)
    (ambientCoordinate : CoverCoordinates) :
    normalGraphLocalMetricNormalCoordinates period hPeriod metric displacement
        base ambientCoordinate current =
      (trivializationAt CoverCoordinates
        (fun point : EffectiveQuotient period hPeriod =>
          TangentSpace coverModelWithCorners point)
        (normalGraph period hPeriod displacement base.2 base.1)).linearMapAt
          Real
          (normalGraph period hPeriod displacement current.2 current.1)
          (normalGraphMetricNormal period hPeriod metric displacement current.2
            hNonNull current.1
            ((trivializationAt CoverCoordinates
              (fun point : EffectiveQuotient period hPeriod =>
                TangentSpace coverModelWithCorners point)
              (normalGraph period hPeriod displacement base.2 base.1)).symm
                (normalGraph period hPeriod displacement current.2 current.1)
                ambientCoordinate)) := by
  unfold normalGraphLocalMetricNormalCoordinates
  rw [normalGraphMetricNormalProjectorCoordinates_eq_inCoordinates period hPeriod
    metric displacement base current hNonNull hTangent hCotangent hImage]
  rw [ContinuousLinearMap.inCoordinates_eq hImage hImage]
  rw [Trivialization.linearMapAt_apply, if_pos hImage]
  rfl

/-- Every fixed-coordinate local metric-normal field is smooth at an
admissible base point. -/
theorem normalGraphLocalMetricNormalCoordinates_contMDiffAt
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement base.2)
    (ambientCoordinate : CoverCoordinates) :
    ContMDiffAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      𝓘(Real, CoverCoordinates) ∞
      (normalGraphLocalMetricNormalCoordinates period hPeriod metric displacement
        base ambientCoordinate) base := by
  exact
    (normalGraphMetricNormalProjectorCoordinates_contMDiffAt period hPeriod
      metric displacement base hNonNull).clm_apply contMDiffAt_const

/-- At every admissible base point some constant coordinate vector produces a
nonzero metric normal.  This is derived from the one-dimensional differential
normal quotient, not supplied as a coorientation. -/
theorem exists_normalGraphLocalMetricNormalCoordinates_ne_zero
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement base.2) :
    ∃ ambientCoordinate : CoverCoordinates,
      normalGraphLocalMetricNormalCoordinates period hPeriod metric displacement
        base ambientCoordinate base ≠ 0 := by
  have hPositive : 0 < Module.finrank Real
      (MovingGraphDifferentialNormalFiber period hPeriod displacement base.2
        base.1) := by
    rw [movingGraphDifferentialNormalFiber_finrank period hPeriod metric
      displacement base.2 hNonNull base.1]
    norm_num
  obtain ⟨normalClass, hClass⟩ :=
    (Module.finrank_pos_iff_exists_ne_zero (R := Real)
      (M := MovingGraphDifferentialNormalFiber period hPeriod displacement
        base.2 base.1)).mp hPositive
  obtain ⟨ambientVector, rfl⟩ :=
    Submodule.Quotient.mk_surjective
      (NormalGraphTangentRange period hPeriod displacement base.2 base.1)
      normalClass
  have hProjector :
      normalGraphMetricNormalLinearMap period hPeriod metric displacement base.2
        hNonNull base.1 ambientVector ≠ 0 := by
    intro hZero
    apply hClass
    apply (Submodule.Quotient.mk_eq_zero
      (NormalGraphTangentRange period hPeriod displacement base.2 base.1)).2
    exact (normalGraphMetricNormalLinearMap_eq_zero_iff period hPeriod metric
      displacement base.2 hNonNull base.1 ambientVector).1 hZero
  have hTangent : base.1 ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) base.1).baseSet :=
    mem_baseSet_trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) base.1
  have hCotangent : base.1 ∈
      (trivializationAt (ThroatCoverCoordinates →L[Real] Real)
        (ThroatCotangentFiber period hPeriod) base.1).baseSet :=
    mem_baseSet_trivializationAt (ThroatCoverCoordinates →L[Real] Real)
      (ThroatCotangentFiber period hPeriod) base.1
  have hImage : normalGraph period hPeriod displacement base.2 base.1 ∈
      (trivializationAt CoverCoordinates
        (fun point : EffectiveQuotient period hPeriod =>
          TangentSpace coverModelWithCorners point)
        (normalGraph period hPeriod displacement base.2 base.1)).baseSet :=
    mem_baseSet_trivializationAt CoverCoordinates
      (fun point : EffectiveQuotient period hPeriod =>
        TangentSpace coverModelWithCorners point)
      (normalGraph period hPeriod displacement base.2 base.1)
  let ambientEquiv :=
    (trivializationAt CoverCoordinates
      (fun point : EffectiveQuotient period hPeriod =>
        TangentSpace coverModelWithCorners point)
      (normalGraph period hPeriod displacement base.2 base.1)
      ).continuousLinearEquivAt Real
        (normalGraph period hPeriod displacement base.2 base.1) hImage
  refine ⟨ambientEquiv ambientVector, ?_⟩
  rw [show normalGraphLocalMetricNormalCoordinates period hPeriod metric
      displacement base (ambientEquiv ambientVector) base =
    normalGraphMetricNormalProjectorCoordinates period hPeriod metric
      displacement base base (ambientEquiv ambientVector) by rfl]
  rw [normalGraphMetricNormalProjectorCoordinates_eq_inCoordinates period hPeriod
    metric displacement base base hNonNull hTangent hCotangent hImage]
  rw [ContinuousLinearMap.inCoordinates_eq hImage hImage]
  change ambientEquiv
      (normalGraphMetricNormalLinearMap period hPeriod metric displacement base.2
        hNonNull base.1 (ambientEquiv.symm (ambientEquiv ambientVector))) ≠ 0
  rw [ContinuousLinearEquiv.symm_apply_apply]
  exact fun hZero => hProjector (ambientEquiv.injective (by simpa using hZero))

/-- Hence every admissible point has a neighborhood carrying a smooth,
nonvanishing local metric-normal field.  No global orientation of the normal
line is selected. -/
theorem exists_eventually_nonzero_normalGraphLocalMetricNormalCoordinates
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement base.2) :
    ∃ ambientCoordinate : CoverCoordinates,
      ContMDiffAt
          (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
          𝓘(Real, CoverCoordinates) ∞
          (normalGraphLocalMetricNormalCoordinates period hPeriod metric
            displacement base ambientCoordinate) base ∧
        ∀ᶠ current in 𝓝 base,
          normalGraphLocalMetricNormalCoordinates period hPeriod metric
            displacement base ambientCoordinate current ≠ 0 := by
  obtain ⟨ambientCoordinate, hNonzero⟩ :=
    exists_normalGraphLocalMetricNormalCoordinates_ne_zero period hPeriod metric
      displacement base hNonNull
  refine ⟨ambientCoordinate,
    normalGraphLocalMetricNormalCoordinates_contMDiffAt period hPeriod metric
      displacement base hNonNull ambientCoordinate, ?_⟩
  exact
    (normalGraphLocalMetricNormalCoordinates_contMDiffAt period hPeriod metric
      displacement base hNonNull ambientCoordinate).continuousAt.eventually_ne
        hNonzero

/-- Metric square of one local metric-normal coordinate field. -/
def normalGraphLocalMetricNormalSquareCoordinates
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (ambientCoordinate : CoverCoordinates)
    (current : EffectiveThroat period hPeriod × Real) : Real :=
  normalGraphFamilyAmbientTensorCoordinates period hPeriod metric displacement
    base current
    (normalGraphLocalMetricNormalCoordinates period hPeriod metric displacement
      base ambientCoordinate current)
    (normalGraphLocalMetricNormalCoordinates period hPeriod metric displacement
      base ambientCoordinate current)

/-- The local normal square is smooth at every admissible base point. -/
theorem normalGraphLocalMetricNormalSquareCoordinates_contMDiffAt
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement base.2)
    (ambientCoordinate : CoverCoordinates) :
    ContMDiffAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      𝓘(Real, Real) ∞
      (normalGraphLocalMetricNormalSquareCoordinates period hPeriod metric
        displacement base ambientCoordinate) base := by
  have hAmbient :=
    normalGraphFamilyAmbientTensorCoordinates_contMDiffAt period hPeriod metric
      displacement base
  have hNormal :=
    normalGraphLocalMetricNormalCoordinates_contMDiffAt period hPeriod metric
      displacement base hNonNull ambientCoordinate
  exact (hAmbient.clm_apply hNormal).clm_apply hNormal

/-- A nonzero local metric-normal coordinate at the base has nonzero metric
square. -/
theorem normalGraphLocalMetricNormalSquareCoordinates_ne_zero
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement base.2)
    (ambientCoordinate : CoverCoordinates)
    (hCoordinate :
      normalGraphLocalMetricNormalCoordinates period hPeriod metric displacement
        base ambientCoordinate base ≠ 0) :
    normalGraphLocalMetricNormalSquareCoordinates period hPeriod metric
      displacement base ambientCoordinate base ≠ 0 := by
  have hTangent : base.1 ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) base.1).baseSet :=
    mem_baseSet_trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) base.1
  have hCotangent : base.1 ∈
      (trivializationAt (ThroatCoverCoordinates →L[Real] Real)
        (ThroatCotangentFiber period hPeriod) base.1).baseSet :=
    mem_baseSet_trivializationAt (ThroatCoverCoordinates →L[Real] Real)
      (ThroatCotangentFiber period hPeriod) base.1
  have hImage : normalGraph period hPeriod displacement base.2 base.1 ∈
      (trivializationAt CoverCoordinates
        (fun point : EffectiveQuotient period hPeriod =>
          TangentSpace coverModelWithCorners point)
        (normalGraph period hPeriod displacement base.2 base.1)).baseSet :=
    mem_baseSet_trivializationAt CoverCoordinates
      (fun point : EffectiveQuotient period hPeriod =>
        TangentSpace coverModelWithCorners point)
      (normalGraph period hPeriod displacement base.2 base.1)
  let ambientVector :=
    (trivializationAt CoverCoordinates
      (fun point : EffectiveQuotient period hPeriod =>
        TangentSpace coverModelWithCorners point)
      (normalGraph period hPeriod displacement base.2 base.1)).symm
        (normalGraph period hPeriod displacement base.2 base.1)
        ambientCoordinate
  let normalClass : MovingGraphDifferentialNormalFiber period hPeriod
      displacement base.2 base.1 := Submodule.Quotient.mk ambientVector
  have hClass : normalClass ≠ 0 := by
    intro hZero
    have hTangentRange : ambientVector ∈
        NormalGraphTangentRange period hPeriod displacement base.2 base.1 :=
      (Submodule.Quotient.mk_eq_zero
        (NormalGraphTangentRange period hPeriod displacement base.2 base.1)).1
        hZero
    have hProjectedZero :=
      (normalGraphMetricNormalLinearMap_eq_zero_iff period hPeriod metric
        displacement base.2 hNonNull base.1 ambientVector).2 hTangentRange
    apply hCoordinate
    rw [normalGraphLocalMetricNormalCoordinates_eq_intrinsic period hPeriod
      metric displacement base base hNonNull hTangent hCotangent hImage]
    rw [← normalGraphMetricNormalLinearMap_apply, hProjectedZero, map_zero]
  have hSquare := normalGraphMetricNormalSquare_ne_zero period hPeriod metric
    displacement base.2 hNonNull base.1 normalClass hClass
  have hSquareCoordinates :
      normalGraphLocalMetricNormalSquareCoordinates period hPeriod metric
          displacement base ambientCoordinate base =
        normalGraphMetricNormalSquare period hPeriod metric displacement base.2
          hNonNull base.1 normalClass := by
    unfold normalGraphMetricNormalSquare normalClass
    rw [normalGraphMetricNormalFromClass_mk]
    unfold normalGraphLocalMetricNormalSquareCoordinates
    rw [normalGraphLocalMetricNormalCoordinates_eq_intrinsic period hPeriod
      metric displacement base base hNonNull hTangent hCotangent hImage]
    rw [show normalGraphFamilyAmbientTensorCoordinates period hPeriod metric
        displacement base base =
      ContinuousLinearMap.inCoordinates CoverCoordinates
        (fun point : EffectiveQuotient period hPeriod =>
          TangentSpace coverModelWithCorners point)
        (CoverCoordinates →L[Real] Real)
        (fun point : EffectiveQuotient period hPeriod =>
          TangentSpace coverModelWithCorners point →L[Real] Real)
        (normalGraph period hPeriod displacement base.2 base.1)
        (normalGraph period hPeriod displacement base.2 base.1)
        (normalGraph period hPeriod displacement base.2 base.1)
        (normalGraph period hPeriod displacement base.2 base.1)
        (metric.tensor.tensor
          (normalGraph period hPeriod displacement base.2 base.1)) by rfl]
    rw [inCoordinates_apply_eq₂ hImage hImage (Set.mem_univ _)]
    simp only [Trivialization.symm_linearMapAt _ hImage]
    simp [ambientVector]
  intro hZero
  rw [hSquareCoordinates] at hZero
  exact hSquare hZero

/-- Unit normalization of a local metric-normal coordinate field. -/
def normalGraphLocalMetricUnitNormalCoordinates
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (ambientCoordinate : CoverCoordinates)
    (current : EffectiveThroat period hPeriod × Real) : CoverCoordinates :=
  (Real.sqrt
    |normalGraphLocalMetricNormalSquareCoordinates period hPeriod metric
      displacement base ambientCoordinate current|)⁻¹ •
    normalGraphLocalMetricNormalCoordinates period hPeriod metric displacement
      base ambientCoordinate current

@[simp]
theorem normalGraphLocalMetricNormalCoordinates_neg
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base current : EffectiveThroat period hPeriod × Real)
    (ambientCoordinate : CoverCoordinates) :
    normalGraphLocalMetricNormalCoordinates period hPeriod metric displacement
        base (-ambientCoordinate) current =
      -normalGraphLocalMetricNormalCoordinates period hPeriod metric displacement
        base ambientCoordinate current := by
  simp [normalGraphLocalMetricNormalCoordinates]

@[simp]
theorem normalGraphLocalMetricNormalSquareCoordinates_neg
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base current : EffectiveThroat period hPeriod × Real)
    (ambientCoordinate : CoverCoordinates) :
    normalGraphLocalMetricNormalSquareCoordinates period hPeriod metric
        displacement base (-ambientCoordinate) current =
      normalGraphLocalMetricNormalSquareCoordinates period hPeriod metric
        displacement base ambientCoordinate current := by
  simp [normalGraphLocalMetricNormalSquareCoordinates]

@[simp]
theorem normalGraphLocalMetricUnitNormalCoordinates_neg
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base current : EffectiveThroat period hPeriod × Real)
    (ambientCoordinate : CoverCoordinates) :
    normalGraphLocalMetricUnitNormalCoordinates period hPeriod metric displacement
        base (-ambientCoordinate) current =
      -normalGraphLocalMetricUnitNormalCoordinates period hPeriod metric
        displacement base ambientCoordinate current := by
  simp [normalGraphLocalMetricUnitNormalCoordinates]

/-- Unit normalization remains smooth wherever the base normal square is
nonzero. -/
theorem normalGraphLocalMetricUnitNormalCoordinates_contMDiffAt
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement base.2)
    (ambientCoordinate : CoverCoordinates)
    (hSquare : normalGraphLocalMetricNormalSquareCoordinates period hPeriod
      metric displacement base ambientCoordinate base ≠ 0) :
    ContMDiffAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      𝓘(Real, CoverCoordinates) ∞
      (normalGraphLocalMetricUnitNormalCoordinates period hPeriod metric
        displacement base ambientCoordinate) base := by
  have hNormal :=
    normalGraphLocalMetricNormalCoordinates_contMDiffAt period hPeriod metric
      displacement base hNonNull ambientCoordinate
  have hSquareSmooth :=
    normalGraphLocalMetricNormalSquareCoordinates_contMDiffAt period hPeriod
      metric displacement base hNonNull ambientCoordinate
  have hAbs : ContMDiffAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      𝓘(Real, Real) ∞
      (fun current =>
        |normalGraphLocalMetricNormalSquareCoordinates period hPeriod metric
          displacement base ambientCoordinate current|) base := by
    simpa [Function.comp_def] using
      (contDiffAt_abs hSquare).comp_contMDiffAt hSquareSmooth
  have hAbsPositive : 0 <
      |normalGraphLocalMetricNormalSquareCoordinates period hPeriod metric
        displacement base ambientCoordinate base| := abs_pos.mpr hSquare
  have hRoot : ContMDiffAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      𝓘(Real, Real) ∞
      (fun current => Real.sqrt
        |normalGraphLocalMetricNormalSquareCoordinates period hPeriod metric
          displacement base ambientCoordinate current|) base := by
    simpa [Function.comp_def] using
      (Real.contDiffAt_sqrt (ne_of_gt hAbsPositive)).comp_contMDiffAt
        (I := throatCoverModelWithCorners.prod
          (modelWithCornersSelf Real Real))
        (f := fun current =>
          |normalGraphLocalMetricNormalSquareCoordinates period hPeriod metric
            displacement base ambientCoordinate current|)
        (x := base) hAbs
  have hInverse := hRoot.inv₀ (Real.sqrt_ne_zero'.mpr hAbsPositive)
  exact hInverse.smul hNormal

/-- Every admissible point therefore admits a smooth local unit-normal
coordinate field. -/
theorem exists_normalGraphLocalMetricUnitNormalCoordinates_contMDiffAt
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement base.2) :
    ∃ ambientCoordinate : CoverCoordinates,
      ContMDiffAt
        (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
        𝓘(Real, CoverCoordinates) ∞
        (normalGraphLocalMetricUnitNormalCoordinates period hPeriod metric
          displacement base ambientCoordinate) base := by
  obtain ⟨ambientCoordinate, hCoordinate⟩ :=
    exists_normalGraphLocalMetricNormalCoordinates_ne_zero period hPeriod metric
      displacement base hNonNull
  exact ⟨ambientCoordinate,
    normalGraphLocalMetricUnitNormalCoordinates_contMDiffAt period hPeriod metric
      displacement base hNonNull ambientCoordinate
      (normalGraphLocalMetricNormalSquareCoordinates_ne_zero period hPeriod
        metric displacement base hNonNull ambientCoordinate hCoordinate)⟩

/-- The coordinate unit normal has metric square of absolute value one at its
base point. -/
theorem abs_normalGraphLocalMetricUnitNormalCoordinates_square
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (ambientCoordinate : CoverCoordinates)
    (hSquare : normalGraphLocalMetricNormalSquareCoordinates period hPeriod
      metric displacement base ambientCoordinate base ≠ 0) :
    |normalGraphFamilyAmbientTensorCoordinates period hPeriod metric displacement
        base base
        (normalGraphLocalMetricUnitNormalCoordinates period hPeriod metric
          displacement base ambientCoordinate base)
        (normalGraphLocalMetricUnitNormalCoordinates period hPeriod metric
          displacement base ambientCoordinate base)| = 1 := by
  let square := normalGraphLocalMetricNormalSquareCoordinates period hPeriod
    metric displacement base ambientCoordinate base
  let root := Real.sqrt |square|
  have hAbs : |square| ≠ 0 := abs_ne_zero.mpr hSquare
  have hRoot : root ≠ 0 := Real.sqrt_ne_zero'.mpr (abs_pos.mpr hSquare)
  have hRootSquare : root ^ 2 = |square| :=
    Real.sq_sqrt (abs_nonneg square)
  have hNormalized :
      normalGraphFamilyAmbientTensorCoordinates period hPeriod metric displacement
          base base
          (normalGraphLocalMetricUnitNormalCoordinates period hPeriod metric
            displacement base ambientCoordinate base)
          (normalGraphLocalMetricUnitNormalCoordinates period hPeriod metric
            displacement base ambientCoordinate base) =
        square / |square| := by
    unfold normalGraphLocalMetricUnitNormalCoordinates
    rw [map_smul, map_smul]
    change root⁻¹ * (root⁻¹ * square) = square / |square|
    rw [← hRootSquare]
    field_simp [hRoot]
  rw [hNormalized]
  rw [abs_div, abs_abs]
  exact div_self hAbs

/-! ## Existing holonomic-atlas bridge -/

private abbrev HolonomicVector4 :=
  P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D.Vector4

set_option backward.isDefEq.respectTransparency false in
private theorem holonomic_fromTangentSpace_apply
    (point : HolonomicVector4)
    (vector : TangentSpace
      (modelWithCornersSelf Real HolonomicVector4) point) :
    NormedSpace.fromTangentSpace point vector = vector :=
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem holonomicProduct_fromTangentSpace_apply
    (point : HolonomicVector4 × HolonomicVector4)
    (vector : TangentSpace
      (modelWithCornersSelf Real (HolonomicVector4 × HolonomicVector4)) point) :
    NormedSpace.fromTangentSpace point vector = vector :=
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem holonomicProduct_fromTangentSpace_prod_apply
    {domain : Type*} [TopologicalSpace domain] [AddCommMonoid domain]
    [Module Real domain]
    (firstPoint secondPoint : HolonomicVector4)
    (first : domain →L[Real] TangentSpace
      (modelWithCornersSelf Real HolonomicVector4) firstPoint)
    (second : domain →L[Real] TangentSpace
      (modelWithCornersSelf Real HolonomicVector4) secondPoint)
    (vector : domain) :
    NormedSpace.fromTangentSpace (𝕜 := Real) (firstPoint, secondPoint)
        ((first.prod second) vector) =
      (NormedSpace.fromTangentSpace (𝕜 := Real) firstPoint (first vector),
        NormedSpace.fromTangentSpace (𝕜 := Real) secondPoint (second vector)) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem holonomic_fromTangentSpace_fderiv_apply
    (outer : (HolonomicVector4 × HolonomicVector4) → HolonomicVector4)
    (point : HolonomicVector4 × HolonomicVector4)
    (vector : TangentSpace
      (modelWithCornersSelf Real (HolonomicVector4 × HolonomicVector4)) point) :
    NormedSpace.fromTangentSpace (𝕜 := Real) (outer point)
        (fderiv Real outer point vector) =
      fderiv Real outer point
        (NormedSpace.fromTangentSpace (𝕜 := Real) point vector) :=
  rfl

/-- Product rule for applying the varying Jacobian of a `C²` coordinate
transition to a varying vector. -/
private theorem fderiv_transitionDerivative_apply_pair
    (transition : HolonomicVector4 → HolonomicVector4)
    (point vector pointDirection vectorDirection : HolonomicVector4)
    (hTransitionDerivative :
      DifferentiableAt Real (fderiv Real transition) point) :
    fderiv Real
        (fun pair : HolonomicVector4 × HolonomicVector4 =>
          fderiv Real transition pair.1 pair.2)
        (point, vector) (pointDirection, vectorDirection) =
      fderiv Real (fderiv Real transition) point pointDirection vector +
        fderiv Real transition point vectorDirection := by
  let jacobian : HolonomicVector4 × HolonomicVector4 →
      HolonomicVector4 →L[Real] HolonomicVector4 :=
    fun pair => fderiv Real transition pair.1
  let varyingVector : HolonomicVector4 × HolonomicVector4 →
      HolonomicVector4 := Prod.snd
  have hJacobian : DifferentiableAt Real jacobian (point, vector) :=
    hTransitionDerivative.comp (point, vector) differentiableAt_fst
  have hVector : DifferentiableAt Real varyingVector (point, vector) :=
    differentiableAt_snd
  have hProduct := fderiv_clm_apply hJacobian hVector
  have hApplied := congrArg
    (fun derivative :
        (HolonomicVector4 × HolonomicVector4) →L[Real] HolonomicVector4 =>
      derivative (pointDirection, vectorDirection)) hProduct
  have hJacobianDerivative :
      fderiv Real jacobian (point, vector) (pointDirection, vectorDirection) =
        fderiv Real (fderiv Real transition) point pointDirection := by
    have hComp := fderiv_comp (𝕜 := Real) (x := (point, vector))
      (f := (Prod.fst : HolonomicVector4 × HolonomicVector4 →
        HolonomicVector4))
      (g := fderiv Real transition)
      hTransitionDerivative differentiableAt_fst
    have hApply := congrArg
      (fun derivative :
          (HolonomicVector4 × HolonomicVector4) →L[Real]
            (HolonomicVector4 →L[Real] HolonomicVector4) =>
        derivative (pointDirection, vectorDirection)) hComp
    simpa [jacobian, Function.comp_def, fderiv_fst] using hApply
  calc
    fderiv Real
          (fun pair : HolonomicVector4 × HolonomicVector4 =>
            fderiv Real transition pair.1 pair.2)
          (point, vector) (pointDirection, vectorDirection) =
        fderiv Real transition point vectorDirection +
          fderiv Real (fderiv Real transition) point pointDirection vector := by
      simpa [jacobian, varyingVector, hJacobianDerivative, fderiv_snd] using hApplied
    _ = fderiv Real (fderiv Real transition) point pointDirection vector +
          fderiv Real transition point vectorDirection := add_comm _ _

private theorem differentiableAt_transitionDerivative_apply_pair
    (transition : HolonomicVector4 → HolonomicVector4)
    (point vector : HolonomicVector4)
    (hTransitionDerivative :
      DifferentiableAt Real (fderiv Real transition) point) :
    DifferentiableAt Real
      (fun pair : HolonomicVector4 × HolonomicVector4 =>
        fderiv Real transition pair.1 pair.2)
      (point, vector) :=
  (hTransitionDerivative.comp (point, vector) differentiableAt_fst).clm_apply
    differentiableAt_snd

/-- Local holonomic representative of the moving graph.  It is obtained from
the genuine inverse germ of an existing atlas patch, not supplied as a second
embedding. -/
def normalGraphHolonomicCoordinateGerm
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (current : EffectiveThroat period hPeriod × Real) : HolonomicVector4 :=
  (patch.coordinateMap_isLocalDiffeomorph coordinate).localInverse
    (normalGraph period hPeriod displacement current.2 current.1)

@[simp]
theorem normalGraphHolonomicCoordinateGerm_base
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraph period hPeriod displacement base.2 base.1) :
    normalGraphHolonomicCoordinateGerm period hPeriod displacement base patch
        coordinate base = coordinate := by
  unfold normalGraphHolonomicCoordinateGerm
  rw [← hAt]
  exact (patch.coordinateMap_isLocalDiffeomorph coordinate).localInverse_left_inv
    (patch.coordinateMap_isLocalDiffeomorph coordinate).localInverse_mem_target

theorem normalGraphHolonomicCoordinateGerm_contMDiffAt
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraph period hPeriod displacement base.2 base.1) :
    ContMDiffAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real HolonomicVector4) ∞
      (normalGraphHolonomicCoordinateGerm period hPeriod displacement base
        patch coordinate) base := by
  have hInverse : ContMDiffAt coverModelWithCorners
      (modelWithCornersSelf Real HolonomicVector4) ∞
      (patch.coordinateMap_isLocalDiffeomorph coordinate).localInverse
      (normalGraph period hPeriod displacement base.2 base.1) := by
    rw [← hAt]
    exact (patch.coordinateMap_isLocalDiffeomorph coordinate)
      |>.localInverse_contMDiffAt
  exact hInverse.comp base
    (normalGraph_joint_contMDiff period hPeriod displacement).contMDiffAt

/-- On its inverse germ the representative reconstructs the actual normal
graph. -/
theorem normalGraphHolonomicCoordinateGerm_eventually_reconstructs
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraph period hPeriod displacement base.2 base.1) :
    (fun current => patch.coordinateMap
      (normalGraphHolonomicCoordinateGerm period hPeriod displacement base patch
        coordinate current)) =ᶠ[𝓝 base]
      fun current =>
        normalGraph period hPeriod displacement current.2 current.1 := by
  have hTendsto : Tendsto
      (fun current : EffectiveThroat period hPeriod × Real =>
        normalGraph period hPeriod displacement current.2 current.1)
      (𝓝 base) (𝓝 (patch.coordinateMap coordinate)) := by
    rw [hAt]
    exact (normalGraph_joint_contMDiff period hPeriod displacement).continuous
      |>.continuousAt
  simpa only [normalGraphHolonomicCoordinateGerm, Function.comp_def, id_eq]
    using (patch.coordinateMap_isLocalDiffeomorph coordinate)
      |>.localInverse_eventuallyEq_right.comp_tendsto hTendsto

/-- Two genuine holonomic inverse germs of the same moving graph are related
by the actual atlas transition near their common anchor. -/
theorem normalGraphHolonomicCoordinateGerm_transition_eventuallyEq
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : HolonomicVector4)
    (hFirst : firstPatch.coordinateMap firstCoordinate =
      normalGraph period hPeriod displacement base.2 base.1)
    (hSecond : secondPatch.coordinateMap secondCoordinate =
      normalGraph period hPeriod displacement base.2 base.1) :
    let transition := holonomicCoordinateTransitionAt period hPeriod firstPatch
      secondPatch firstCoordinate secondCoordinate (hFirst.trans hSecond.symm)
    (fun current => transition
      (normalGraphHolonomicCoordinateGerm period hPeriod displacement base
        firstPatch firstCoordinate current)) =ᶠ[𝓝 base]
      normalGraphHolonomicCoordinateGerm period hPeriod displacement base
        secondPatch secondCoordinate := by
  dsimp only
  filter_upwards [normalGraphHolonomicCoordinateGerm_eventually_reconstructs
    period hPeriod displacement base firstPatch firstCoordinate hFirst] with
      current hReconstruct
  have hApply := congrArg
    (secondPatch.coordinateMap_isLocalDiffeomorph secondCoordinate).localInverse
    hReconstruct
  simpa only [holonomicCoordinateTransitionAt,
    normalGraphHolonomicCoordinateGerm, Function.comp_apply] using hApply

/-- Every point of the moving graph has such a genuine holonomic inverse
germ.  This discharges chart existence using the canonical atlas already in
the repository. -/
theorem exists_normalGraphHolonomicCoordinateGerm
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real) :
    ∃ patch : SmoothHolonomicFrameChart4 period hPeriod,
      ∃ coordinate : HolonomicVector4,
        patch.coordinateMap coordinate =
            normalGraph period hPeriod displacement base.2 base.1 ∧
          ContMDiffAt
            (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
            (modelWithCornersSelf Real HolonomicVector4) ∞
            (normalGraphHolonomicCoordinateGerm period hPeriod displacement base
              patch coordinate) base ∧
          (fun current => patch.coordinateMap
            (normalGraphHolonomicCoordinateGerm period hPeriod displacement base
              patch coordinate current)) =ᶠ[𝓝 base]
            fun current => normalGraph period hPeriod displacement current.2
              current.1 := by
  rcases canonicalHolonomicChartThroughEveryPoint period hPeriod
      (normalGraph period hPeriod displacement base.2 base.1) with
    ⟨patch, coordinate, hAt⟩
  exact ⟨patch, coordinate, hAt,
    normalGraphHolonomicCoordinateGerm_contMDiffAt period hPeriod displacement
      base patch coordinate hAt,
    normalGraphHolonomicCoordinateGerm_eventually_reconstructs period hPeriod
      displacement base patch coordinate hAt⟩

/-- Spatial differential of the holonomic graph germ, kept jointly in the
normal-family parameter and the throat point. -/
def normalGraphHolonomicFamilyDerivativeCoordinates
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (current : EffectiveThroat period hPeriod × Real) :
    ThroatCoverCoordinates →L[Real] HolonomicVector4 :=
  let representative :=
    normalGraphHolonomicCoordinateGerm period hPeriod displacement base patch
      coordinate
  inTangentCoordinates throatCoverModelWithCorners
    (modelWithCornersSelf Real HolonomicVector4)
    Prod.fst representative
    (fun point => mfderiv throatCoverModelWithCorners
      (modelWithCornersSelf Real HolonomicVector4)
      (fun throatPoint => representative (throatPoint, point.2)) point.1)
    base current

private theorem normalGraphHolonomicFamilyDerivativeCoordinates_apply_base
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (vector : ThroatCoverCoordinates) :
    normalGraphHolonomicFamilyDerivativeCoordinates period hPeriod displacement
        base patch coordinate base vector =
      (trivializationAt HolonomicVector4
        (fun point : HolonomicVector4 =>
          TangentSpace (modelWithCornersSelf Real HolonomicVector4) point)
        (normalGraphHolonomicCoordinateGerm period hPeriod displacement base
          patch coordinate base)).linearMapAt Real
          (normalGraphHolonomicCoordinateGerm period hPeriod displacement base
            patch coordinate base)
          (mfderiv throatCoverModelWithCorners
            (modelWithCornersSelf Real HolonomicVector4)
            (fun point => normalGraphHolonomicCoordinateGerm period hPeriod
              displacement base patch coordinate (point, base.2)) base.1
            ((trivializationAt ThroatCoverCoordinates
              (ThroatTangentFiber period hPeriod) base.1).symm base.1
                vector)) := by
  have hThroat : base.1 ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) base.1).baseSet :=
    mem_baseSet_trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) base.1
  have hTarget : normalGraphHolonomicCoordinateGerm period hPeriod displacement
      base patch coordinate base ∈
      (trivializationAt HolonomicVector4
        (fun point : HolonomicVector4 =>
          TangentSpace (modelWithCornersSelf Real HolonomicVector4) point)
        (normalGraphHolonomicCoordinateGerm period hPeriod displacement base
          patch coordinate base)).baseSet :=
    mem_baseSet_trivializationAt HolonomicVector4
      (fun point : HolonomicVector4 =>
        TangentSpace (modelWithCornersSelf Real HolonomicVector4) point)
      (normalGraphHolonomicCoordinateGerm period hPeriod displacement base patch
        coordinate base)
  rw [show normalGraphHolonomicFamilyDerivativeCoordinates period hPeriod
      displacement base patch coordinate base =
    ContinuousLinearMap.inCoordinates ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) HolonomicVector4
      (fun point : HolonomicVector4 =>
        TangentSpace (modelWithCornersSelf Real HolonomicVector4) point)
      base.1 base.1
      (normalGraphHolonomicCoordinateGerm period hPeriod displacement base patch
        coordinate base)
      (normalGraphHolonomicCoordinateGerm period hPeriod displacement base patch
        coordinate base)
      (mfderiv throatCoverModelWithCorners
        (modelWithCornersSelf Real HolonomicVector4)
        (fun point => normalGraphHolonomicCoordinateGerm period hPeriod
          displacement base patch coordinate (point, base.2)) base.1) by rfl]
  rw [ContinuousLinearMap.inCoordinates_eq hThroat hTarget]
  rw [Trivialization.linearMapAt_apply, if_pos hTarget]
  rfl

theorem normalGraphHolonomicFamilyDerivativeCoordinates_apply_base_eq_mfderiv
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (vector : ThroatCoverCoordinates) :
    normalGraphHolonomicFamilyDerivativeCoordinates period hPeriod displacement
        base patch coordinate base vector =
      mfderiv throatCoverModelWithCorners
        (modelWithCornersSelf Real HolonomicVector4)
        (fun point => normalGraphHolonomicCoordinateGerm period hPeriod
          displacement base patch coordinate (point, base.2)) base.1
        ((trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) base.1).symm base.1 vector) := by
  rw [normalGraphHolonomicFamilyDerivativeCoordinates_apply_base]
  simp

theorem normalGraphHolonomicFamilyDerivativeCoordinates_contMDiffAt
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraph period hPeriod displacement base.2 base.1) :
    ContMDiffAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      𝓘(Real,
        ThroatCoverCoordinates →L[Real] HolonomicVector4) ∞
      (normalGraphHolonomicFamilyDerivativeCoordinates period hPeriod
        displacement base patch coordinate) base := by
  let representative :=
    normalGraphHolonomicCoordinateGerm period hPeriod displacement base patch
      coordinate
  let f : (EffectiveThroat period hPeriod × Real) →
      EffectiveThroat period hPeriod → HolonomicVector4 :=
    fun parameterPoint point => representative (point, parameterPoint.2)
  let g : (EffectiveThroat period hPeriod × Real) →
      EffectiveThroat period hPeriod := Prod.fst
  have hRepresentative : ContMDiffAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real HolonomicVector4) ∞ representative base := by
    simpa [representative] using
      (normalGraphHolonomicCoordinateGerm_contMDiffAt period hPeriod
        displacement base patch coordinate hAt)
  have hReorder : ContMDiffAt
      ((throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real)).prod
        throatCoverModelWithCorners)
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real)) ∞
      (fun point : (EffectiveThroat period hPeriod × Real) ×
          EffectiveThroat period hPeriod => (point.2, point.1.2))
      (base, base.1) :=
    (contMDiff_snd.prodMk (contMDiff_snd.comp contMDiff_fst)).contMDiffAt
  have hg : ContMDiffAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      throatCoverModelWithCorners ∞ g base := by
    simpa [g] using
      (contMDiff_fst : ContMDiff
        (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
        throatCoverModelWithCorners ∞
        (Prod.fst : EffectiveThroat period hPeriod × Real →
          EffectiveThroat period hPeriod)).contMDiffAt
  have hJoint : ContMDiffAt
      ((throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real)).prod
        throatCoverModelWithCorners)
      (modelWithCornersSelf Real HolonomicVector4) ∞
      (fun point : (EffectiveThroat period hPeriod × Real) ×
          EffectiveThroat period hPeriod => representative (point.2, point.1.2))
      (base, base.1) :=
    ContMDiffAt.comp (f := fun point :
        (EffectiveThroat period hPeriod × Real) ×
          EffectiveThroat period hPeriod => (point.2, point.1.2))
      (g := representative) (base, base.1) hRepresentative hReorder
  change ContMDiffAt
    (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
    𝓘(Real, ThroatCoverCoordinates →L[Real] HolonomicVector4) ∞
    (inTangentCoordinates throatCoverModelWithCorners
      (modelWithCornersSelf Real HolonomicVector4) g representative
      (fun point => mfderiv throatCoverModelWithCorners
        (modelWithCornersSelf Real HolonomicVector4) (f point) (g point))
      base) base
  exact hJoint.mfderiv f g hg (by simp)

/-- The holonomic spatial differential represents exactly the intrinsic
differential of the moving graph at the anchor. -/
theorem normalGraphHolonomicFamilyDerivativeCoordinates_reconstructs
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraph period hPeriod displacement base.2 base.1)
    (vector : ThroatCoverCoordinates) :
    mfderiv (modelWithCornersSelf Real HolonomicVector4)
        coverModelWithCorners patch.coordinateMap coordinate
        (normalGraphHolonomicFamilyDerivativeCoordinates period hPeriod
          displacement base patch coordinate base vector) =
      mfderiv throatCoverModelWithCorners coverModelWithCorners
        (normalGraph period hPeriod displacement base.2) base.1
        ((trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) base.1).symm base.1 vector) := by
  let representative := fun point : EffectiveThroat period hPeriod =>
    normalGraphHolonomicCoordinateGerm period hPeriod displacement base patch
      coordinate (point, base.2)
  have hSection : ContMDiffAt throatCoverModelWithCorners
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real)) ∞
      (fun point : EffectiveThroat period hPeriod => (point, base.2)) base.1 :=
    (contMDiff_id.prodMk contMDiff_const).contMDiffAt
  have hRepresentative : ContMDiffAt throatCoverModelWithCorners
      (modelWithCornersSelf Real HolonomicVector4) ∞ representative base.1 := by
    exact ContMDiffAt.comp
      (f := fun point : EffectiveThroat period hPeriod => (point, base.2))
      (g := normalGraphHolonomicCoordinateGerm period hPeriod displacement base
        patch coordinate) base.1
      (normalGraphHolonomicCoordinateGerm_contMDiffAt period hPeriod
        displacement base patch coordinate hAt) hSection
  let sectionMap :=
    fun point : EffectiveThroat period hPeriod => (point, base.2)
  have hTendsto : Tendsto sectionMap (𝓝 base.1) (𝓝 base) :=
    hSection.continuousAt
  have hReconstruct :=
    (normalGraphHolonomicCoordinateGerm_eventually_reconstructs period hPeriod
      displacement base patch coordinate hAt).comp_tendsto hTendsto
  have hDerivativeReconstruct :=
    Filter.EventuallyEq.mfderiv_eq
      (I := throatCoverModelWithCorners) (I' := coverModelWithCorners)
      hReconstruct
  let tangent :=
    (trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) base.1).symm base.1 vector
  have hChain := mfderiv_comp_apply base.1
    (patch.coordinateMap_contMDiff.mdifferentiable (by simp)
      (representative base.1))
    (hRepresentative.mdifferentiableAt (by simp)) tangent
  rw [normalGraphHolonomicFamilyDerivativeCoordinates_apply_base_eq_mfderiv]
  change mfderiv (modelWithCornersSelf Real HolonomicVector4)
      coverModelWithCorners patch.coordinateMap coordinate
      (mfderiv throatCoverModelWithCorners
        (modelWithCornersSelf Real HolonomicVector4) representative base.1
        tangent) = _
  have hBase : representative base.1 = coordinate := by
    exact normalGraphHolonomicCoordinateGerm_base period hPeriod displacement
      base patch coordinate hAt
  rw [← hBase]
  rw [← hChain]
  have hApply :=
    congrArg (fun derivative => derivative tangent) hDerivativeReconstruct
  change mfderiv throatCoverModelWithCorners coverModelWithCorners
      (fun point => patch.coordinateMap (representative point)) base.1 tangent =
    mfderiv throatCoverModelWithCorners coverModelWithCorners
      (normalGraph period hPeriod displacement base.2) base.1 tangent at hApply
  exact hApply

/-- The spatial differential of the moving graph obeys the genuine
holonomic-coordinate transition law.  Both sides reconstruct the same
intrinsic graph tangent; no extra frame or embedding is introduced. -/
theorem normalGraphHolonomicFamilyDerivativeCoordinates_transition
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : HolonomicVector4)
    (hFirst : firstPatch.coordinateMap firstCoordinate =
      normalGraph period hPeriod displacement base.2 base.1)
    (hSecond : secondPatch.coordinateMap secondCoordinate =
      normalGraph period hPeriod displacement base.2 base.1)
    (vector : ThroatCoverCoordinates) :
    holonomicCoordinateTransitionLinearEquivAt period hPeriod firstPatch
        secondPatch firstCoordinate secondCoordinate (hFirst.trans hSecond.symm)
        (normalGraphHolonomicFamilyDerivativeCoordinates period hPeriod
          displacement base firstPatch firstCoordinate base vector) =
      normalGraphHolonomicFamilyDerivativeCoordinates period hPeriod
        displacement base secondPatch secondCoordinate base vector := by
  let transition :=
    holonomicCoordinateTransitionLinearEquivAt period hPeriod firstPatch
      secondPatch firstCoordinate secondCoordinate (hFirst.trans hSecond.symm)
  let secondDerivative :=
    (secondPatch.coordinateMap_isLocalDiffeomorph secondCoordinate)
      |>.mfderivToContinuousLinearEquiv (by simp)
  apply secondDerivative.injective
  change
    mfderiv (modelWithCornersSelf Real HolonomicVector4) coverModelWithCorners
        secondPatch.coordinateMap secondCoordinate
        (transition
          (normalGraphHolonomicFamilyDerivativeCoordinates period hPeriod
            displacement base firstPatch firstCoordinate base vector)) =
      mfderiv (modelWithCornersSelf Real HolonomicVector4) coverModelWithCorners
        secondPatch.coordinateMap secondCoordinate
        (normalGraphHolonomicFamilyDerivativeCoordinates period hPeriod
          displacement base secondPatch secondCoordinate base vector)
  apply eq_of_heq
  exact
    (holonomicCoordinateMap_mfderiv_transition_heq period hPeriod
      firstPatch secondPatch firstCoordinate secondCoordinate
      (normalGraphHolonomicFamilyDerivativeCoordinates period hPeriod
        displacement base firstPatch firstCoordinate base vector)
      (hFirst.trans hSecond.symm)).symm.trans
        ((normalGraphHolonomicFamilyDerivativeCoordinates_reconstructs period
          hPeriod displacement base firstPatch firstCoordinate hFirst vector).heq.trans
        (normalGraphHolonomicFamilyDerivativeCoordinates_reconstructs period
          hPeriod displacement base secondPatch secondCoordinate hSecond vector).symm.heq)

/-- Spatial second derivative of the genuine holonomic graph germ, retained
jointly in the graph parameter and throat point. -/
def normalGraphHolonomicFamilySecondDerivativeBundleCoordinates
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (current : EffectiveThroat period hPeriod × Real) :
    ThroatCoverCoordinates →L[Real]
      ThroatCoverCoordinates →L[Real] HolonomicVector4 :=
  let representative :=
    normalGraphHolonomicFamilyDerivativeCoordinates period hPeriod displacement
      base patch coordinate
  inTangentCoordinates throatCoverModelWithCorners
    (modelWithCornersSelf Real
      (ThroatCoverCoordinates →L[Real] HolonomicVector4))
    Prod.fst representative
    (fun point => mfderiv throatCoverModelWithCorners
      (modelWithCornersSelf Real
        (ThroatCoverCoordinates →L[Real] HolonomicVector4))
      (fun throatPoint => representative (throatPoint, point.2)) point.1)
    base current

/-- The graph second jet has the expected joint smoothness at every
holonomic anchor. -/
theorem normalGraphHolonomicFamilySecondDerivativeBundleCoordinates_contMDiffAt
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraph period hPeriod displacement base.2 base.1) :
    ContMDiffAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      𝓘(Real, ThroatCoverCoordinates →L[Real]
        ThroatCoverCoordinates →L[Real] HolonomicVector4) ∞
      (normalGraphHolonomicFamilySecondDerivativeBundleCoordinates period hPeriod
        displacement base patch coordinate) base := by
  let target := ThroatCoverCoordinates →L[Real] HolonomicVector4
  let representative :=
    normalGraphHolonomicFamilyDerivativeCoordinates period hPeriod displacement
      base patch coordinate
  let f : (EffectiveThroat period hPeriod × Real) →
      EffectiveThroat period hPeriod → target :=
    fun parameterPoint point => representative (point, parameterPoint.2)
  let g : (EffectiveThroat period hPeriod × Real) →
      EffectiveThroat period hPeriod := Prod.fst
  have hRepresentative : ContMDiffAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real target) ∞ representative base := by
    simpa [representative, target] using
      (normalGraphHolonomicFamilyDerivativeCoordinates_contMDiffAt period
        hPeriod displacement base patch coordinate hAt)
  have hReorder : ContMDiffAt
      ((throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real)).prod
        throatCoverModelWithCorners)
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real)) ∞
      (fun point : (EffectiveThroat period hPeriod × Real) ×
          EffectiveThroat period hPeriod => (point.2, point.1.2))
      (base, base.1) :=
    (contMDiff_snd.prodMk (contMDiff_snd.comp contMDiff_fst)).contMDiffAt
  have hg : ContMDiffAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      throatCoverModelWithCorners ∞ g base := by
    simpa [g] using
      (contMDiff_fst : ContMDiff
        (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
        throatCoverModelWithCorners ∞
        (Prod.fst : EffectiveThroat period hPeriod × Real →
          EffectiveThroat period hPeriod)).contMDiffAt
  have hJoint : ContMDiffAt
      ((throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real)).prod
        throatCoverModelWithCorners)
      (modelWithCornersSelf Real target) ∞
      (fun point : (EffectiveThroat period hPeriod × Real) ×
          EffectiveThroat period hPeriod => representative (point.2, point.1.2))
      (base, base.1) :=
    ContMDiffAt.comp (f := fun point :
        (EffectiveThroat period hPeriod × Real) ×
          EffectiveThroat period hPeriod => (point.2, point.1.2))
      (g := representative) (base, base.1) hRepresentative hReorder
  change ContMDiffAt
    (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
    𝓘(Real, ThroatCoverCoordinates →L[Real] target) ∞
    (inTangentCoordinates throatCoverModelWithCorners
      (modelWithCornersSelf Real target) g representative
      (fun point => mfderiv throatCoverModelWithCorners
        (modelWithCornersSelf Real target) (f point) (g point)) base) base
  exact hJoint.mfderiv f g hg (by simp)

/-- Genuine coordinate second derivative at one holonomic anchor.  Unlike the
bundle-coordinate family above, the target tangent is converted by the
canonical normed-space equivalence, so this is the raw second derivative used
in the Gauss formula. -/
def normalGraphHolonomicFamilyRawSecondDerivativeCoordinatesAt
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4) :
    ThroatCoverCoordinates →L[Real]
      ThroatCoverCoordinates →L[Real] HolonomicVector4 :=
  let throatTrivialization := trivializationAt ThroatCoverCoordinates
    (ThroatTangentFiber period hPeriod) base.1
  let hThroat : base.1 ∈ throatTrivialization.baseSet :=
    mem_baseSet_trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) base.1
  (mvfderiv throatCoverModelWithCorners
      (fun point =>
        normalGraphHolonomicFamilyDerivativeCoordinates period hPeriod
          displacement base patch coordinate (point, base.2)) base.1).comp
    ((throatTrivialization.continuousLinearEquivAt Real base.1 hThroat).symm
      |>.toContinuousLinearMap)

/-! ### Canonical source-chart second jet -/

/-- The same holonomic graph germ written in Mathlib's canonical source chart
at the throat point.  The chart is selected by the installed manifold atlas;
it is not additional boundary data. -/
def normalGraphHolonomicSourceChartGerm
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (sourceCoordinate : ThroatCoverCoordinates) : HolonomicVector4 :=
  normalGraphHolonomicCoordinateGerm period hPeriod displacement base patch
    coordinate
    ((extChartAt throatCoverModelWithCorners base.1).symm sourceCoordinate,
      base.2)

@[simp]
theorem normalGraphHolonomicSourceChartGerm_base
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraph period hPeriod displacement base.2 base.1) :
    normalGraphHolonomicSourceChartGerm period hPeriod displacement base patch
        coordinate (extChartAt throatCoverModelWithCorners base.1 base.1) =
      coordinate := by
  unfold normalGraphHolonomicSourceChartGerm
  rw [extChartAt_to_inv]
  exact normalGraphHolonomicCoordinateGerm_base period hPeriod displacement base
    patch coordinate hAt

/-- The source-chart representative is genuinely smooth at its anchor. -/
theorem normalGraphHolonomicSourceChartGerm_contDiffAt
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraph period hPeriod displacement base.2 base.1) :
    ContDiffAt Real ∞
      (normalGraphHolonomicSourceChartGerm period hPeriod displacement base
        patch coordinate)
      (extChartAt throatCoverModelWithCorners base.1 base.1) := by
  let slice := fun point : EffectiveThroat period hPeriod =>
    normalGraphHolonomicCoordinateGerm period hPeriod displacement base patch
      coordinate (point, base.2)
  have hSection : ContMDiffAt throatCoverModelWithCorners
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real)) ∞
      (fun point : EffectiveThroat period hPeriod => (point, base.2)) base.1 :=
    (contMDiff_id.prodMk contMDiff_const).contMDiffAt
  have hSlice : ContMDiffAt throatCoverModelWithCorners
      (modelWithCornersSelf Real HolonomicVector4) ∞ slice base.1 :=
    ContMDiffAt.comp
      (f := fun point : EffectiveThroat period hPeriod => (point, base.2))
      (g := normalGraphHolonomicCoordinateGerm period hPeriod displacement base
        patch coordinate) base.1
      (normalGraphHolonomicCoordinateGerm_contMDiffAt period hPeriod
        displacement base patch coordinate hAt) hSection
  have hSource := (contMDiffAt_iff_source).mp hSlice
  have hRange : Set.range throatCoverModelWithCorners = Set.univ := by
    ext sourceCoordinate
    simp
  rw [hRange, contMDiffWithinAt_univ] at hSource
  have hFunction :
      slice ∘ (extChartAt throatCoverModelWithCorners base.1).symm =
        normalGraphHolonomicSourceChartGerm period hPeriod displacement base
          patch coordinate := by
    rfl
  rw [hFunction] at hSource
  exact hSource.contDiffAt

/-- First derivative of the graph in the canonical source chart and a genuine
ambient holonomic chart. -/
def normalGraphHolonomicSourceFirstDerivativeCoordinatesAt
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4) :
    ThroatCoverCoordinates →L[Real] HolonomicVector4 :=
  fderiv Real
    (normalGraphHolonomicSourceChartGerm period hPeriod displacement base patch
      coordinate)
    (extChartAt throatCoverModelWithCorners base.1 base.1)

/-- The canonical source-chart first jet is exactly the fixed tangent-coordinate
jet already used by the induced metric and its intrinsic inverse.  Thus the
Gauss form below needs no second metric representation. -/
theorem normalGraphHolonomicSourceFirstDerivativeCoordinatesAt_eq_family
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraph period hPeriod displacement base.2 base.1) :
    normalGraphHolonomicSourceFirstDerivativeCoordinatesAt period hPeriod
        displacement base patch coordinate =
      normalGraphHolonomicFamilyDerivativeCoordinates period hPeriod
        displacement base patch coordinate base := by
  apply ContinuousLinearMap.ext
  intro vector
  rw [normalGraphHolonomicFamilyDerivativeCoordinates_apply_base_eq_mfderiv]
  unfold normalGraphHolonomicSourceFirstDerivativeCoordinatesAt
    normalGraphHolonomicSourceChartGerm
  let slice := fun point : EffectiveThroat period hPeriod =>
    normalGraphHolonomicCoordinateGerm period hPeriod displacement base patch
      coordinate (point, base.2)
  have hSection : ContMDiffAt throatCoverModelWithCorners
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real)) ∞
      (fun point : EffectiveThroat period hPeriod => (point, base.2)) base.1 :=
    (contMDiff_id.prodMk contMDiff_const).contMDiffAt
  have hSlice : ContMDiffAt throatCoverModelWithCorners
      (modelWithCornersSelf Real HolonomicVector4) ∞ slice base.1 :=
    ContMDiffAt.comp
      (f := fun point : EffectiveThroat period hPeriod => (point, base.2))
      (g := normalGraphHolonomicCoordinateGerm period hPeriod displacement base
        patch coordinate) base.1
      (normalGraphHolonomicCoordinateGerm_contMDiffAt period hPeriod
        displacement base patch coordinate hAt) hSection
  have hChart : base.1 ∈ (chartAt ThroatCoverModel base.1).source :=
    mem_chart_source ThroatCoverModel base.1
  have hVector :
      (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) base.1).symm base.1 vector =
        vector := by
    change
      (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) base.1).symmL Real base.1 vector =
        vector
    rw [TangentBundle.symmL_trivializationAt hChart,
      mfderivWithin_range_extChartAt_symm]
    rfl
  rw [hVector]
  rw [(hSlice.mdifferentiableAt (by simp)).mfderiv]
  have hRange : Set.range throatCoverModelWithCorners = Set.univ := by
    ext sourceCoordinate
    simp
  rw [hRange, fderivWithin_univ]
  simp [writtenInExtChartAt, Function.comp_def, slice]
  rfl

/-- Second derivative of that same source-chart representative. -/
def normalGraphHolonomicSourceSecondDerivativeCoordinatesAt
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4) :
    ThroatCoverCoordinates →L[Real]
      ThroatCoverCoordinates →L[Real] HolonomicVector4 :=
  fderiv Real
    (fderiv Real
      (normalGraphHolonomicSourceChartGerm period hPeriod displacement base
        patch coordinate))
    (extChartAt throatCoverModelWithCorners base.1 base.1)

/-- The source-chart representatives inherit the already proved genuine
ambient transition relation. -/
theorem normalGraphHolonomicSourceChartGerm_transition_eventuallyEq
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : HolonomicVector4)
    (hFirst : firstPatch.coordinateMap firstCoordinate =
      normalGraph period hPeriod displacement base.2 base.1)
    (hSecond : secondPatch.coordinateMap secondCoordinate =
      normalGraph period hPeriod displacement base.2 base.1) :
    let transition := holonomicCoordinateTransitionAt period hPeriod firstPatch
      secondPatch firstCoordinate secondCoordinate (hFirst.trans hSecond.symm)
    (transition ∘ normalGraphHolonomicSourceChartGerm period hPeriod displacement
      base firstPatch firstCoordinate) =ᶠ[
        𝓝 (extChartAt throatCoverModelWithCorners base.1 base.1)]
      normalGraphHolonomicSourceChartGerm period hPeriod displacement base
        secondPatch secondCoordinate := by
  dsimp only
  have hTransition :=
    normalGraphHolonomicCoordinateGerm_transition_eventuallyEq period hPeriod
      displacement base firstPatch secondPatch firstCoordinate secondCoordinate
        hFirst hSecond
  have hInverse : ContinuousAt
      (extChartAt throatCoverModelWithCorners base.1).symm
      (extChartAt throatCoverModelWithCorners base.1 base.1) :=
    continuousAt_extChartAt_symm base.1
  have hConstant : ContinuousAt
      (fun _ : ThroatCoverCoordinates => base.2)
      (extChartAt throatCoverModelWithCorners base.1 base.1) :=
    continuousAt_const
  have hSection : Tendsto
      (fun sourceCoordinate : ThroatCoverCoordinates =>
        ((extChartAt throatCoverModelWithCorners base.1).symm sourceCoordinate,
          base.2))
      (𝓝 (extChartAt throatCoverModelWithCorners base.1 base.1)) (𝓝 base) := by
    have hPair := hInverse.prodMk hConstant
    have hBase :
        ((extChartAt throatCoverModelWithCorners base.1).symm
            (extChartAt throatCoverModelWithCorners base.1 base.1), base.2) =
      base := by
      rw [extChartAt_to_inv]
    change Tendsto
      (fun sourceCoordinate : ThroatCoverCoordinates =>
        ((extChartAt throatCoverModelWithCorners base.1).symm sourceCoordinate,
          base.2))
      (𝓝 (extChartAt throatCoverModelWithCorners base.1 base.1))
      (𝓝 ((extChartAt throatCoverModelWithCorners base.1).symm
        (extChartAt throatCoverModelWithCorners base.1 base.1), base.2)) at hPair
    rw [hBase] at hPair
    exact hPair
  change
    (fun sourceCoordinate =>
      holonomicCoordinateTransitionAt period hPeriod firstPatch secondPatch
          firstCoordinate secondCoordinate (hFirst.trans hSecond.symm)
        (normalGraphHolonomicCoordinateGerm period hPeriod displacement base
          firstPatch firstCoordinate
            ((extChartAt throatCoverModelWithCorners base.1).symm
              sourceCoordinate, base.2))) =ᶠ[
        𝓝 (extChartAt throatCoverModelWithCorners base.1 base.1)]
      fun sourceCoordinate =>
        normalGraphHolonomicCoordinateGerm period hPeriod displacement base
          secondPatch secondCoordinate
            ((extChartAt throatCoverModelWithCorners base.1).symm
              sourceCoordinate, base.2)
  exact hTransition.comp_tendsto hSection

/-- Pointwise second-order chain rule used for the canonical source chart.
It only requires smooth germs at the anchor. -/
private theorem sourceChart_secondFDeriv_comp_apply
    {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E]
    [NormedAddCommGroup F] [NormedSpace Real F]
    [NormedAddCommGroup G] [NormedSpace Real G]
    (inner : E → F) (outer : F → G) (point : E)
    (hInner : ContDiffAt Real 2 inner point)
    (hOuter : ContDiffAt Real 2 outer (inner point))
    (first second : E) :
    fderiv Real (fderiv Real (outer ∘ inner)) point first second =
      fderiv Real (fderiv Real outer) (inner point)
          (fderiv Real inner point first)
          (fderiv Real inner point second) +
        fderiv Real outer (inner point)
          (fderiv Real (fderiv Real inner) point first second) := by
  have hInnerDiff : DifferentiableAt Real inner point :=
    hInner.differentiableAt (by norm_num)
  have hInnerNear := hInner.eventually (by norm_num)
  have hOuterNearAt := hOuter.eventually (by norm_num)
  have hOuterNear := hInner.continuousAt.eventually hOuterNearAt
  have hFirstDerivative :
      Filter.EventuallyEq (𝓝 point)
        (fderiv Real (outer ∘ inner))
        (fun current =>
          (fderiv Real outer (inner current)).comp
            (fderiv Real inner current)) := by
    filter_upwards [hInnerNear, hOuterNear] with current hCurrentInner
      hCurrentOuter
    exact fderiv_comp current
      (hCurrentOuter.differentiableAt (by norm_num))
      (hCurrentInner.differentiableAt (by norm_num))
  have hSecondDerivative :
      fderiv Real (fderiv Real (outer ∘ inner)) point =
        fderiv Real
          (fun current =>
            (fderiv Real outer (inner current)).comp
              (fderiv Real inner current)) point :=
    Filter.EventuallyEq.fderiv_eq hFirstDerivative
  rw [hSecondDerivative]
  have hOuterDerivative :
      ContDiffAt Real 1 (fderiv Real outer) (inner point) :=
    hOuter.fderiv_right (m := 1) (by norm_num)
  have hInnerDerivative :
      ContDiffAt Real 1 (fderiv Real inner) point :=
    hInner.fderiv_right (m := 1) (by norm_num)
  have hComposedOuterDerivative : DifferentiableAt Real
      (fun current => fderiv Real outer (inner current)) point :=
    (hOuterDerivative.differentiableAt (by norm_num)).comp point hInnerDiff
  have hInnerDerivativeDiff :
      DifferentiableAt Real (fderiv Real inner) point :=
    hInnerDerivative.differentiableAt (by norm_num)
  rw [fderiv_clm_comp hComposedOuterDerivative hInnerDerivativeDiff]
  have hComposedOuterFDeriv :
      fderiv Real (fun current => fderiv Real outer (inner current)) point =
        (fderiv Real (fderiv Real outer) (inner point)).comp
          (fderiv Real inner point) :=
    fderiv_comp point
      (hOuterDerivative.differentiableAt (by norm_num)) hInnerDiff
  rw [hComposedOuterFDeriv]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply]
  abel

/-- First source derivative transforms by the genuine ambient Jacobian. -/
theorem normalGraphHolonomicSourceFirstDerivativeCoordinatesAt_transition
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : HolonomicVector4)
    (hFirst : firstPatch.coordinateMap firstCoordinate =
      normalGraph period hPeriod displacement base.2 base.1)
    (hSecond : secondPatch.coordinateMap secondCoordinate =
      normalGraph period hPeriod displacement base.2 base.1)
    (vector : ThroatCoverCoordinates) :
    let transition := holonomicCoordinateTransitionAt period hPeriod firstPatch
      secondPatch firstCoordinate secondCoordinate (hFirst.trans hSecond.symm)
    fderiv Real transition firstCoordinate
        (normalGraphHolonomicSourceFirstDerivativeCoordinatesAt period hPeriod
          displacement base firstPatch firstCoordinate vector) =
      normalGraphHolonomicSourceFirstDerivativeCoordinatesAt period hPeriod
        displacement base secondPatch secondCoordinate vector := by
  dsimp only
  let transition := holonomicCoordinateTransitionAt period hPeriod firstPatch
    secondPatch firstCoordinate secondCoordinate (hFirst.trans hSecond.symm)
  let sourceBase := extChartAt throatCoverModelWithCorners base.1 base.1
  let firstGerm := normalGraphHolonomicSourceChartGerm period hPeriod
    displacement base firstPatch firstCoordinate
  let secondGerm := normalGraphHolonomicSourceChartGerm period hPeriod
    displacement base secondPatch secondCoordinate
  have hGerms : (transition ∘ firstGerm) =ᶠ[𝓝 sourceBase] secondGerm := by
    simpa [transition, sourceBase, firstGerm, secondGerm] using
      (normalGraphHolonomicSourceChartGerm_transition_eventuallyEq period
        hPeriod displacement base firstPatch secondPatch firstCoordinate
          secondCoordinate hFirst hSecond)
  have hDerivative :=
    Filter.EventuallyEq.fderiv_eq (𝕜 := Real) hGerms
  have hFirstSmooth :=
    normalGraphHolonomicSourceChartGerm_contDiffAt period hPeriod displacement
      base firstPatch firstCoordinate hFirst
  have hTransitionSmooth :=
    holonomicCoordinateTransitionAt_contDiffAt_three period hPeriod firstPatch
      secondPatch firstCoordinate secondCoordinate (hFirst.trans hSecond.symm)
  have hBase : firstGerm sourceBase = firstCoordinate := by
    simpa [firstGerm, sourceBase] using
      (normalGraphHolonomicSourceChartGerm_base period hPeriod displacement base
        firstPatch firstCoordinate hFirst)
  have hTransitionDiff : DifferentiableAt Real transition
      (firstGerm sourceBase) := by
    rw [hBase]
    exact hTransitionSmooth.differentiableAt (by norm_num)
  have hChain := fderiv_comp sourceBase hTransitionDiff
    (hFirstSmooth.differentiableAt (by simp))
  have hApply := congrArg
    (fun derivative : ThroatCoverCoordinates →L[Real] HolonomicVector4 =>
      derivative vector) hDerivative
  rw [hChain] at hApply
  simp only [ContinuousLinearMap.comp_apply] at hApply
  rw [hBase] at hApply
  simpa [transition, sourceBase, firstGerm, secondGerm,
    normalGraphHolonomicSourceFirstDerivativeCoordinatesAt] using hApply

/-- The source second derivative has the exact inhomogeneous transition law.
Its Hessian term is the one cancelled by the Levi--Civita connection. -/
theorem normalGraphHolonomicSourceSecondDerivativeCoordinatesAt_transition
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : HolonomicVector4)
    (hFirst : firstPatch.coordinateMap firstCoordinate =
      normalGraph period hPeriod displacement base.2 base.1)
    (hSecond : secondPatch.coordinateMap secondCoordinate =
      normalGraph period hPeriod displacement base.2 base.1)
    (first second : ThroatCoverCoordinates) :
    let transition := holonomicCoordinateTransitionAt period hPeriod firstPatch
      secondPatch firstCoordinate secondCoordinate (hFirst.trans hSecond.symm)
    normalGraphHolonomicSourceSecondDerivativeCoordinatesAt period hPeriod
        displacement base secondPatch secondCoordinate first second =
      fderiv Real (fderiv Real transition) firstCoordinate
          (normalGraphHolonomicSourceFirstDerivativeCoordinatesAt period hPeriod
            displacement base firstPatch firstCoordinate first)
          (normalGraphHolonomicSourceFirstDerivativeCoordinatesAt period hPeriod
            displacement base firstPatch firstCoordinate second) +
        fderiv Real transition firstCoordinate
          (normalGraphHolonomicSourceSecondDerivativeCoordinatesAt period
            hPeriod displacement base firstPatch firstCoordinate first second) := by
  dsimp only
  let transition := holonomicCoordinateTransitionAt period hPeriod firstPatch
    secondPatch firstCoordinate secondCoordinate (hFirst.trans hSecond.symm)
  let sourceBase := extChartAt throatCoverModelWithCorners base.1 base.1
  let firstGerm := normalGraphHolonomicSourceChartGerm period hPeriod
    displacement base firstPatch firstCoordinate
  let secondGerm := normalGraphHolonomicSourceChartGerm period hPeriod
    displacement base secondPatch secondCoordinate
  have hGerms : (transition ∘ firstGerm) =ᶠ[𝓝 sourceBase] secondGerm := by
    simpa [transition, sourceBase, firstGerm, secondGerm] using
      (normalGraphHolonomicSourceChartGerm_transition_eventuallyEq period
        hPeriod displacement base firstPatch secondPatch firstCoordinate
          secondCoordinate hFirst hSecond)
  have hFirstDerivativeGerms :=
    Filter.EventuallyEq.fderiv (𝕜 := Real) hGerms
  have hSecondDerivative :=
    Filter.EventuallyEq.fderiv_eq (𝕜 := Real) hFirstDerivativeGerms
  have hSecondApply := congrArg
    (fun derivative : ThroatCoverCoordinates →L[Real]
        ThroatCoverCoordinates →L[Real] HolonomicVector4 =>
      derivative first second) hSecondDerivative
  have hFirstSmooth :=
    normalGraphHolonomicSourceChartGerm_contDiffAt period hPeriod displacement
      base firstPatch firstCoordinate hFirst
  have hFirstSmoothGerm : ContDiffAt Real ∞ firstGerm sourceBase := by
    simpa [firstGerm, sourceBase] using hFirstSmooth
  have hFirstTwo : ContDiffAt Real 2 firstGerm sourceBase :=
    hFirstSmoothGerm.of_le (by
      change ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
      exact WithTop.coe_le_coe.mpr le_top)
  have hBase : firstGerm sourceBase = firstCoordinate := by
    simpa [firstGerm, sourceBase] using
      (normalGraphHolonomicSourceChartGerm_base period hPeriod displacement base
        firstPatch firstCoordinate hFirst)
  have hTransitionSmooth :=
    holonomicCoordinateTransitionAt_contDiffAt_three period hPeriod firstPatch
      secondPatch firstCoordinate secondCoordinate (hFirst.trans hSecond.symm)
  have hTransitionTwo : ContDiffAt Real 2 transition (firstGerm sourceBase) := by
    rw [hBase]
    exact hTransitionSmooth.of_le (by norm_num)
  have hChain := sourceChart_secondFDeriv_comp_apply firstGerm transition
    sourceBase hFirstTwo hTransitionTwo first second
  rw [hChain] at hSecondApply
  rw [hBase] at hSecondApply
  simpa [transition, sourceBase, firstGerm, secondGerm,
    normalGraphHolonomicSourceFirstDerivativeCoordinatesAt,
    normalGraphHolonomicSourceSecondDerivativeCoordinatesAt] using
      hSecondApply.symm

/-- Pullback metric written in a genuine holonomic inverse germ. -/
def normalGraphHolonomicInducedMetricCoordinates
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (current : EffectiveThroat period hPeriod × Real)
    (first second : ThroatCoverCoordinates) : Real :=
  localMetricCoordinateForm period hPeriod metric patch
    (normalGraphHolonomicCoordinateGerm period hPeriod displacement base patch
      coordinate current)
    (normalGraphHolonomicFamilyDerivativeCoordinates period hPeriod displacement
      base patch coordinate current first)
    (normalGraphHolonomicFamilyDerivativeCoordinates period hPeriod displacement
      base patch coordinate current second)

theorem normalGraphHolonomicInducedMetricCoordinates_symmetric
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (current : EffectiveThroat period hPeriod × Real)
    (first second : ThroatCoverCoordinates) :
    normalGraphHolonomicInducedMetricCoordinates period hPeriod metric
        displacement base patch coordinate current first second =
      normalGraphHolonomicInducedMetricCoordinates period hPeriod metric
        displacement base patch coordinate current second first := by
  unfold normalGraphHolonomicInducedMetricCoordinates
  rw [localMetricCoordinateForm_apply, localMetricCoordinateForm_apply]
  exact metric.tensor.symmetric _ _ _

/-- At the anchor the holonomic expression is exactly the intrinsic induced
metric already constructed above. -/
theorem normalGraphHolonomicInducedMetricCoordinates_eq_intrinsic
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraph period hPeriod displacement base.2 base.1)
    (first second : ThroatCoverCoordinates) :
    normalGraphHolonomicInducedMetricCoordinates period hPeriod metric
        displacement base patch coordinate base first second =
      normalGraphInducedMetricValue period hPeriod metric displacement base.2
        base.1
        ((trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) base.1).symm base.1 first)
        ((trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) base.1).symm base.1 second) := by
  unfold normalGraphHolonomicInducedMetricCoordinates
  rw [normalGraphHolonomicCoordinateGerm_base period hPeriod displacement base
    patch coordinate hAt]
  rw [localMetricCoordinateForm_apply]
  rw [normalGraphHolonomicFamilyDerivativeCoordinates_reconstructs period
      hPeriod displacement base patch coordinate hAt first,
    normalGraphHolonomicFamilyDerivativeCoordinates_reconstructs period
      hPeriod displacement base patch coordinate hAt second]
  rw [hAt]
  rfl

theorem normalGraphHolonomicInducedMetricCoordinates_eq_traceCoordinates
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraph period hPeriod displacement base.2 base.1)
    (first second : ThroatCoverCoordinates) :
    normalGraphHolonomicInducedMetricCoordinates period hPeriod metric
        displacement base patch coordinate base first second =
      normalGraphFamilyTraceTensorCoordinates period hPeriod metric displacement
        base base first second := by
  rw [normalGraphHolonomicInducedMetricCoordinates_eq_intrinsic period hPeriod
    metric displacement base patch coordinate hAt first second]
  have hTangent : base.1 ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) base.1).baseSet :=
    mem_baseSet_trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) base.1
  unfold normalGraphFamilyTraceTensorCoordinates
  rw [inCoordinates_apply_eq₂ hTangent hTangent (Set.mem_univ _)]
  simp

/-- The induced metric obtained from the genuine graph germ is independent
of the holonomic chart at the anchor. -/
theorem normalGraphHolonomicInducedMetricCoordinates_chart_independent
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : HolonomicVector4)
    (hFirst : firstPatch.coordinateMap firstCoordinate =
      normalGraph period hPeriod displacement base.2 base.1)
    (hSecond : secondPatch.coordinateMap secondCoordinate =
      normalGraph period hPeriod displacement base.2 base.1)
    (first second : ThroatCoverCoordinates) :
    normalGraphHolonomicInducedMetricCoordinates period hPeriod metric
        displacement base firstPatch firstCoordinate base first second =
      normalGraphHolonomicInducedMetricCoordinates period hPeriod metric
        displacement base secondPatch secondCoordinate base first second := by
  rw [normalGraphHolonomicInducedMetricCoordinates_eq_traceCoordinates period
      hPeriod metric displacement base firstPatch firstCoordinate hFirst,
    normalGraphHolonomicInducedMetricCoordinates_eq_traceCoordinates period
      hPeriod metric displacement base secondPatch secondCoordinate hSecond]

theorem normalGraphHolonomicInducedMetricCoordinates_contMDiffAt
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraph period hPeriod displacement base.2 base.1)
    (first second : ThroatCoverCoordinates) :
    ContMDiffAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      𝓘(Real, Real) ∞
      (fun current => normalGraphHolonomicInducedMetricCoordinates period
        hPeriod metric displacement base patch coordinate current first second)
      base := by
  have hCoordinate :=
    normalGraphHolonomicCoordinateGerm_contMDiffAt period hPeriod displacement
      base patch coordinate hAt
  have hDerivative :=
    normalGraphHolonomicFamilyDerivativeCoordinates_contMDiffAt period hPeriod
      displacement base patch coordinate hAt
  have hFirstVector : ContMDiffAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      𝓘(Real, HolonomicVector4) ∞
      (fun current =>
        normalGraphHolonomicFamilyDerivativeCoordinates period hPeriod
          displacement base patch coordinate current first) base :=
    hDerivative.clm_apply (contMDiffAt_const (c := first))
  have hSecondVector : ContMDiffAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      𝓘(Real, HolonomicVector4) ∞
      (fun current =>
        normalGraphHolonomicFamilyDerivativeCoordinates period hPeriod
          displacement base patch coordinate current second) base :=
    hDerivative.clm_apply (contMDiffAt_const (c := second))
  have hFirstComponent : ∀ index,
      ContMDiffAt
        (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
        𝓘(Real, Real) ∞
        (fun current =>
          normalGraphHolonomicFamilyDerivativeCoordinates period hPeriod
            displacement base patch coordinate current first index) base := by
    intro index
    exact contMDiffAt_pi_space.mp hFirstVector index
  have hSecondComponent : ∀ index,
      ContMDiffAt
        (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
        𝓘(Real, Real) ∞
        (fun current =>
          normalGraphHolonomicFamilyDerivativeCoordinates period hPeriod
            displacement base patch coordinate current second index) base := by
    intro index
    exact contMDiffAt_pi_space.mp hSecondVector index
  have hMetricEntry : ∀ firstIndex secondIndex,
      ContMDiffAt
        (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
        𝓘(Real, Real) ∞
        (fun current => localMetricMatrix period hPeriod metric patch
          (normalGraphHolonomicCoordinateGerm period hPeriod displacement base
            patch coordinate current) firstIndex secondIndex) base := by
    intro firstIndex secondIndex
    have hEntry := ContDiff.comp_contMDiffAt
      (localMetricCoefficient_contDiff period hPeriod metric patch firstIndex
        secondIndex) hCoordinate
    apply hEntry.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall (fun _ => rfl)
  unfold normalGraphHolonomicInducedMetricCoordinates
    localMetricCoordinateForm
  simp only [Matrix.toBilin'_apply]
  apply ContMDiffAt.sum
  intro firstIndex _
  apply ContMDiffAt.sum
  intro secondIndex _
  exact ((hFirstComponent firstIndex).mul
    (hMetricEntry firstIndex secondIndex)).mul
      (hSecondComponent secondIndex)

theorem normalGraphHolonomicMetricEvaluation_contMDiffAt
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraph period hPeriod displacement base.2 base.1)
    (firstField secondField :
      EffectiveThroat period hPeriod × Real → HolonomicVector4)
    (hFirst : ContMDiffAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      𝓘(Real, HolonomicVector4) ∞ firstField base)
    (hSecond : ContMDiffAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      𝓘(Real, HolonomicVector4) ∞ secondField base) :
    ContMDiffAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      𝓘(Real, Real) ∞
      (fun current => localMetricCoordinateForm period hPeriod metric patch
        (normalGraphHolonomicCoordinateGerm period hPeriod displacement base
          patch coordinate current) (firstField current) (secondField current))
      base := by
  have hCoordinate :=
    normalGraphHolonomicCoordinateGerm_contMDiffAt period hPeriod displacement
      base patch coordinate hAt
  have hFirstComponent : ∀ index,
      ContMDiffAt
        (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
        𝓘(Real, Real) ∞ (fun current => firstField current index) base := by
    intro index
    exact contMDiffAt_pi_space.mp hFirst index
  have hSecondComponent : ∀ index,
      ContMDiffAt
        (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
        𝓘(Real, Real) ∞ (fun current => secondField current index) base := by
    intro index
    exact contMDiffAt_pi_space.mp hSecond index
  have hMetricEntry : ∀ firstIndex secondIndex,
      ContMDiffAt
        (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
        𝓘(Real, Real) ∞
        (fun current => localMetricMatrix period hPeriod metric patch
          (normalGraphHolonomicCoordinateGerm period hPeriod displacement base
            patch coordinate current) firstIndex secondIndex) base := by
    intro firstIndex secondIndex
    have hEntry := ContDiff.comp_contMDiffAt
      (localMetricCoefficient_contDiff period hPeriod metric patch firstIndex
        secondIndex) hCoordinate
    apply hEntry.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall (fun _ => rfl)
  unfold localMetricCoordinateForm
  simp only [Matrix.toBilin'_apply]
  apply ContMDiffAt.sum
  intro firstIndex _
  apply ContMDiffAt.sum
  intro secondIndex _
  exact ((hFirstComponent firstIndex).mul
    (hMetricEntry firstIndex secondIndex)).mul
      (hSecondComponent secondIndex)

/-! ## Fixed-trivialization algebra and GHY adapter -/

private abbrev AmbientMetricCoordinateModel :=
  CoverCoordinates →L[Real] CoverCoordinates →L[Real] Real

/-- The ambient metric in the same fixed tangent trivialization used by the
normal projector. -/
private def normalGraphAmbientMetricCoordinates
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (base current : EffectiveQuotient period hPeriod) :
    AmbientMetricCoordinateModel :=
  ContinuousLinearMap.inCoordinates CoverCoordinates
    (fun point : EffectiveQuotient period hPeriod =>
      TangentSpace coverModelWithCorners point)
    (CoverCoordinates →L[Real] Real)
    (fun point : EffectiveQuotient period hPeriod =>
      TangentSpace coverModelWithCorners point →L[Real] Real)
    base current base current (metric.tensor.tensor current)

private theorem normalGraphAmbientMetricCoordinates_contMDiffAt
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (base : EffectiveQuotient period hPeriod) :
    ContMDiffAt coverModelWithCorners
      (modelWithCornersSelf Real AmbientMetricCoordinateModel) ∞
      (normalGraphAmbientMetricCoordinates period hPeriod metric base) base := by
  have hTensor := metric.tensor.tensor.contMDiff base
  rw [contMDiffAt_hom_bundle] at hTensor
  exact hTensor.2

/-- First coordinate derivative of the genuine ambient metric. -/
def normalGraphAmbientMetricDerivativeCoordinates
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (base : EffectiveQuotient period hPeriod) :
    CoverCoordinates →L[Real] AmbientMetricCoordinateModel :=
  (mfderiv coverModelWithCorners
      (modelWithCornersSelf Real AmbientMetricCoordinateModel)
      (normalGraphAmbientMetricCoordinates period hPeriod metric base) base).comp
    ((trivializationAt CoverCoordinates
      (fun point : EffectiveQuotient period hPeriod =>
        TangentSpace coverModelWithCorners point) base).symmL Real base)

/-- Koszul covector in the fixed tangent chart. The last two metric slots are
symmetrized explicitly; this is definitionally faithful to a symmetric metric
and avoids introducing a separate connection datum. -/
def normalGraphAmbientLeviCivitaKoszulCovector
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (base : EffectiveQuotient period hPeriod)
    (first second : CoverCoordinates) : CoverCoordinates →L[Real] Real where
  toFun contracted := (1 / 2 : Real) *
    (normalGraphAmbientMetricDerivativeCoordinates period hPeriod metric base
        first second contracted +
      normalGraphAmbientMetricDerivativeCoordinates period hPeriod metric base
        second first contracted -
      (1 / 2 : Real) *
        (normalGraphAmbientMetricDerivativeCoordinates period hPeriod metric base
            contracted first second +
          normalGraphAmbientMetricDerivativeCoordinates period hPeriod metric base
            contracted second first))
  map_add' left right := by simp; ring
  map_smul' scalar vector := by simp; ring

/-- Levi--Civita Christoffel application reconstructed by the Koszul formula
and the inverse musical map of the same ambient metric. -/
def normalGraphAmbientLeviCivitaChristoffelCoordinates
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (base : EffectiveQuotient period hPeriod)
    (first second : CoverCoordinates) : CoverCoordinates :=
  let hBase := mem_baseSet_trivializationAt CoverCoordinates
    (fun point : EffectiveQuotient period hPeriod =>
      TangentSpace coverModelWithCorners point) base
  let tangentEquiv :=
    (trivializationAt CoverCoordinates
      (fun point : EffectiveQuotient period hPeriod =>
        TangentSpace coverModelWithCorners point) base).continuousLinearEquivAt
          Real base hBase
  tangentEquiv
    (inverseMetricSharp period hPeriod metric base
      ((normalGraphAmbientLeviCivitaKoszulCovector period hPeriod metric base
          first second).comp tangentEquiv.toContinuousLinearMap))

theorem normalGraphAmbientLeviCivitaChristoffelCoordinates_symmetric
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (base : EffectiveQuotient period hPeriod)
    (first second : CoverCoordinates) :
    normalGraphAmbientLeviCivitaChristoffelCoordinates period hPeriod metric base
        first second =
      normalGraphAmbientLeviCivitaChristoffelCoordinates period hPeriod metric
        base second first := by
  have hCovector :
      normalGraphAmbientLeviCivitaKoszulCovector period hPeriod metric base
          first second =
        normalGraphAmbientLeviCivitaKoszulCovector period hPeriod metric base
          second first := by
    apply ContinuousLinearMap.ext
    intro contracted
    simp [normalGraphAmbientLeviCivitaKoszulCovector]
    ring
  rw [normalGraphAmbientLeviCivitaChristoffelCoordinates,
    normalGraphAmbientLeviCivitaChristoffelCoordinates, hCovector]

@[simp]
theorem normalGraphAmbientLeviCivitaChristoffelCoordinates_neg_right
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (base : EffectiveQuotient period hPeriod)
    (first second : CoverCoordinates) :
    normalGraphAmbientLeviCivitaChristoffelCoordinates period hPeriod metric base
        first (-second) =
      -normalGraphAmbientLeviCivitaChristoffelCoordinates period hPeriod metric
        base first second := by
  have hCovector :
      normalGraphAmbientLeviCivitaKoszulCovector period hPeriod metric base
          first (-second) =
        -normalGraphAmbientLeviCivitaKoszulCovector period hPeriod metric base
          first second := by
    apply ContinuousLinearMap.ext
    intro contracted
    simp [normalGraphAmbientLeviCivitaKoszulCovector]
    ring
  let hBase := mem_baseSet_trivializationAt CoverCoordinates
    (fun point : EffectiveQuotient period hPeriod =>
      TangentSpace coverModelWithCorners point) base
  let tangentEquiv :=
    (trivializationAt CoverCoordinates
      (fun point : EffectiveQuotient period hPeriod =>
        TangentSpace coverModelWithCorners point) base).continuousLinearEquivAt
          Real base hBase
  change tangentEquiv
      (inverseMetricSharp period hPeriod metric base
        ((normalGraphAmbientLeviCivitaKoszulCovector period hPeriod metric base
          first (-second)).comp tangentEquiv.toContinuousLinearMap)) =
    -tangentEquiv
      (inverseMetricSharp period hPeriod metric base
        ((normalGraphAmbientLeviCivitaKoszulCovector period hPeriod metric base
          first second).comp tangentEquiv.toContinuousLinearMap))
  rw [hCovector]
  simp

private def normalGraphLocalUnitNormalAtParameterCoordinates
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (ambientCoordinate : CoverCoordinates)
    (point : EffectiveThroat period hPeriod) : CoverCoordinates :=
  normalGraphLocalMetricUnitNormalCoordinates period hPeriod metric displacement
    base ambientCoordinate (point, base.2)

private theorem normalGraphLocalUnitNormalAtParameterCoordinates_contMDiffAt
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement base.2)
    (ambientCoordinate : CoverCoordinates)
    (hSquare : normalGraphLocalMetricNormalSquareCoordinates period hPeriod
      metric displacement base ambientCoordinate base ≠ 0) :
    ContMDiffAt throatCoverModelWithCorners
      (modelWithCornersSelf Real CoverCoordinates) ∞
      (normalGraphLocalUnitNormalAtParameterCoordinates period hPeriod metric
        displacement base ambientCoordinate) base.1 := by
  have hJoint :=
    normalGraphLocalMetricUnitNormalCoordinates_contMDiffAt period hPeriod metric
      displacement base hNonNull ambientCoordinate hSquare
  have hInsert : ContMDiffAt throatCoverModelWithCorners
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real)) ∞
      (fun point : EffectiveThroat period hPeriod => (point, base.2)) base.1 :=
    contMDiffAt_id.prodMk contMDiffAt_const
  exact hJoint.comp base.1 hInsert

/-- Derivative of the actual local unit-normal field along the displaced
hypersurface. -/
def normalGraphLocalUnitNormalDerivativeCoordinates
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (ambientCoordinate : CoverCoordinates) :
    ThroatCoverCoordinates →L[Real] CoverCoordinates :=
  (mfderiv throatCoverModelWithCorners
      (modelWithCornersSelf Real CoverCoordinates)
      (normalGraphLocalUnitNormalAtParameterCoordinates period hPeriod metric
        displacement base ambientCoordinate) base.1).comp
    ((trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) base.1).symmL Real base.1)

@[simp]
theorem normalGraphLocalUnitNormalDerivativeCoordinates_neg
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (ambientCoordinate : CoverCoordinates) :
    normalGraphLocalUnitNormalDerivativeCoordinates period hPeriod metric
        displacement base (-ambientCoordinate) =
      -normalGraphLocalUnitNormalDerivativeCoordinates period hPeriod metric
        displacement base ambientCoordinate := by
  unfold normalGraphLocalUnitNormalDerivativeCoordinates
  rw [show normalGraphLocalUnitNormalAtParameterCoordinates period hPeriod metric
      displacement base (-ambientCoordinate) =
        -normalGraphLocalUnitNormalAtParameterCoordinates period hPeriod metric
          displacement base ambientCoordinate by
    funext point
    exact normalGraphLocalMetricUnitNormalCoordinates_neg period hPeriod metric
      displacement base (point, base.2) ambientCoordinate]
  rw [mfderiv_neg]
  rfl

/-- Raw Weingarten pairing from the same graph, metric, local unit normal and
Koszul-derived Levi--Civita connection. -/
def normalGraphRawLocalExtrinsicCurvatureCoordinates
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (ambientCoordinate : CoverCoordinates)
    (first second : ThroatCoverCoordinates) : Real :=
  let image := normalGraph period hPeriod displacement base.2 base.1
  let ambientMetric :=
    normalGraphAmbientMetricCoordinates period hPeriod metric image image
  let derivative :=
    normalGraphFamilyDerivativeCoordinates period hPeriod displacement base base
  let normal := normalGraphLocalUnitNormalAtParameterCoordinates period hPeriod
    metric displacement base ambientCoordinate base.1
  let normalDerivative :=
    normalGraphLocalUnitNormalDerivativeCoordinates period hPeriod metric
      displacement base ambientCoordinate
  ambientMetric
    (normalDerivative first +
      normalGraphAmbientLeviCivitaChristoffelCoordinates period hPeriod metric
        image (derivative first) normal)
    (derivative second)

@[simp]
theorem normalGraphRawLocalExtrinsicCurvatureCoordinates_neg
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (ambientCoordinate : CoverCoordinates)
    (first second : ThroatCoverCoordinates) :
    normalGraphRawLocalExtrinsicCurvatureCoordinates period hPeriod metric
        displacement base (-ambientCoordinate) first second =
      -normalGraphRawLocalExtrinsicCurvatureCoordinates period hPeriod metric
        displacement base ambientCoordinate first second := by
  simp [normalGraphRawLocalExtrinsicCurvatureCoordinates,
    normalGraphLocalUnitNormalAtParameterCoordinates]
  ring

/-- Symmetric second fundamental form. It is the canonical symmetric part of
the genuine Weingarten pairing, so its induced trace is unchanged. -/
def normalGraphLocalExtrinsicCurvatureCoordinates
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (ambientCoordinate : CoverCoordinates)
    (first second : ThroatCoverCoordinates) : Real :=
  (1 / 2 : Real) *
    (normalGraphRawLocalExtrinsicCurvatureCoordinates period hPeriod metric
        displacement base ambientCoordinate first second +
      normalGraphRawLocalExtrinsicCurvatureCoordinates period hPeriod metric
        displacement base ambientCoordinate second first)

theorem normalGraphLocalExtrinsicCurvatureCoordinates_symmetric
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (ambientCoordinate : CoverCoordinates)
    (first second : ThroatCoverCoordinates) :
    normalGraphLocalExtrinsicCurvatureCoordinates period hPeriod metric
        displacement base ambientCoordinate first second =
      normalGraphLocalExtrinsicCurvatureCoordinates period hPeriod metric
        displacement base ambientCoordinate second first := by
  unfold normalGraphLocalExtrinsicCurvatureCoordinates
  ring

@[simp]
theorem normalGraphLocalExtrinsicCurvatureCoordinates_neg
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (ambientCoordinate : CoverCoordinates)
    (first second : ThroatCoverCoordinates) :
    normalGraphLocalExtrinsicCurvatureCoordinates period hPeriod metric
        displacement base (-ambientCoordinate) first second =
      -normalGraphLocalExtrinsicCurvatureCoordinates period hPeriod metric
        displacement base ambientCoordinate first second := by
  simp [normalGraphLocalExtrinsicCurvatureCoordinates]
  ring

/-! ## Exact adapter to the existing non-null GHY ledger -/

/-- A fixed basis of the three-dimensional throat coordinate model. This is
only the matrix adapter required by the pre-existing GHY ledger; the geometric
metric and second fundamental form above remain frame-free. -/
private def throatCoordinateBasis :
    Basis (Fin 3) Real ThroatCoverCoordinates := by
  let basis := Module.finBasis Real ThroatCoverCoordinates
  have hDimension : Module.finrank Real ThroatCoverCoordinates = 3 := by
    simp [ThroatCoverCoordinates]
  simpa [hDimension] using basis

private def throatContinuousDualBasis :
    Basis (Fin 3) Real (ThroatCoverCoordinates →L[Real] Real) :=
  throatCoordinateBasis.dualBasis.map
    (LinearMap.toContinuousLinearMap :
      Module.Dual Real ThroatCoverCoordinates ≃ₗ[Real]
        (ThroatCoverCoordinates →L[Real] Real))

/-- Matrix of the genuinely induced metric in the fixed ledger adapter. -/
def normalGraphInducedMetricMatrix
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real) : Matrix3 :=
  LinearMap.toMatrix throatCoordinateBasis throatContinuousDualBasis
    (normalGraphFamilyTraceTensorCoordinates period hPeriod metric displacement
      base base).toLinearMap

/-- Matrix of the already constructed intrinsic inverse metric. -/
def normalGraphInducedInverseMatrix
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real) : Matrix3 :=
  LinearMap.toMatrix throatContinuousDualBasis throatCoordinateBasis
    (normalGraphInducedMetricInverseCoordinates period hPeriod metric
      displacement base base).toLinearMap

/-- The holonomic pullback in the same fixed three-dimensional ledger basis. -/
def normalGraphHolonomicInducedMetricMatrix
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (current : EffectiveThroat period hPeriod × Real) : Matrix3 :=
  fun first second =>
    normalGraphHolonomicInducedMetricCoordinates period hPeriod metric
      displacement base patch coordinate current (throatCoordinateBasis first)
        (throatCoordinateBasis second)

theorem normalGraphHolonomicInducedMetricMatrix_base_eq
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraph period hPeriod displacement base.2 base.1) :
    normalGraphHolonomicInducedMetricMatrix period hPeriod metric displacement
        base patch coordinate base =
      normalGraphInducedMetricMatrix period hPeriod metric displacement base := by
  ext first second
  rw [normalGraphHolonomicInducedMetricMatrix,
    normalGraphHolonomicInducedMetricCoordinates_eq_traceCoordinates period
      hPeriod metric displacement base patch coordinate hAt]
  simp only [normalGraphInducedMetricMatrix, LinearMap.toMatrix_apply,
    throatContinuousDualBasis, Basis.map_repr, LinearEquiv.trans_apply,
    Basis.dualBasis_repr]
  change normalGraphFamilyTraceTensorCoordinates period hPeriod metric
      displacement base base (throatCoordinateBasis first)
        (throatCoordinateBasis second) =
    normalGraphFamilyTraceTensorCoordinates period hPeriod metric displacement
      base base (throatCoordinateBasis second) (throatCoordinateBasis first)
  rw [← normalGraphHolonomicInducedMetricCoordinates_eq_traceCoordinates period
      hPeriod metric displacement base patch coordinate hAt,
    ← normalGraphHolonomicInducedMetricCoordinates_eq_traceCoordinates period
      hPeriod metric displacement base patch coordinate hAt]
  exact normalGraphHolonomicInducedMetricCoordinates_symmetric period hPeriod
    metric displacement base patch coordinate base _ _

private theorem normalGraphFamilyTraceTensorCoordinates_symmetric
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (first second : ThroatCoverCoordinates) :
    normalGraphFamilyTraceTensorCoordinates period hPeriod metric displacement
        base base first second =
      normalGraphFamilyTraceTensorCoordinates period hPeriod metric displacement
        base base second first := by
  have hTangent : base.1 ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) base.1).baseSet :=
    mem_baseSet_trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) base.1
  unfold normalGraphFamilyTraceTensorCoordinates
  rw [inCoordinates_apply_eq₂ hTangent hTangent (Set.mem_univ _),
    inCoordinates_apply_eq₂ hTangent hTangent (Set.mem_univ _)]
  apply congrArg
    ((trivializationAt Real
      (fun _ : EffectiveThroat period hPeriod => Real) base.1).linearMapAt
        Real base.1)
  exact normalGraphInducedMetricValue_symmetric period hPeriod metric
    displacement base.2 base.1 _ _

theorem normalGraphInducedMetricMatrix_symmetric
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real) :
    (normalGraphInducedMetricMatrix period hPeriod metric displacement
      base).transpose =
      normalGraphInducedMetricMatrix period hPeriod metric displacement base := by
  ext first second
  simp only [Matrix.transpose_apply, normalGraphInducedMetricMatrix,
    LinearMap.toMatrix_apply, throatContinuousDualBasis, Basis.map_repr,
    LinearEquiv.trans_apply, Basis.dualBasis_repr]
  exact normalGraphFamilyTraceTensorCoordinates_symmetric period hPeriod metric
    displacement base _ _

theorem normalGraphInducedInverseMatrix_mul_metric
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement base.2) :
    normalGraphInducedInverseMatrix period hPeriod metric displacement base *
        normalGraphInducedMetricMatrix period hPeriod metric displacement base =
      1 := by
  rw [normalGraphInducedInverseMatrix, normalGraphInducedMetricMatrix,
    ← LinearMap.toMatrix_comp]
  change LinearMap.toMatrix throatCoordinateBasis throatCoordinateBasis
      (((normalGraphFamilyTraceTensorCoordinates period hPeriod metric
          displacement base base).inverse.comp
        (normalGraphFamilyTraceTensorCoordinates period hPeriod metric
          displacement base base)).toLinearMap) = 1
  rw [(normalGraphFamilyTraceTensorCoordinates_isInvertible period hPeriod metric
    displacement base hNonNull).inverse_comp_self]
  exact LinearMap.toMatrix_id _

theorem normalGraphInducedMetricMatrix_mul_inverse
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement base.2) :
    normalGraphInducedMetricMatrix period hPeriod metric displacement base *
        normalGraphInducedInverseMatrix period hPeriod metric displacement base =
      1 := by
  rw [normalGraphInducedInverseMatrix, normalGraphInducedMetricMatrix,
    ← LinearMap.toMatrix_comp]
  change LinearMap.toMatrix throatContinuousDualBasis throatContinuousDualBasis
      (((normalGraphFamilyTraceTensorCoordinates period hPeriod metric
          displacement base base).comp
        (normalGraphFamilyTraceTensorCoordinates period hPeriod metric
          displacement base base).inverse).toLinearMap) = 1
  rw [(normalGraphFamilyTraceTensorCoordinates_isInvertible period hPeriod metric
    displacement base hNonNull).self_comp_inverse]
  exact LinearMap.toMatrix_id _

theorem normalGraphInducedInverseMatrix_symmetric
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement base.2) :
    (normalGraphInducedInverseMatrix period hPeriod metric displacement
      base).transpose =
      normalGraphInducedInverseMatrix period hPeriod metric displacement base := by
  let data : Matrix3InverseWitness
      (normalGraphInducedMetricMatrix period hPeriod metric displacement base)
      (normalGraphInducedInverseMatrix period hPeriod metric displacement base) :=
    { inverse_mul := normalGraphInducedInverseMatrix_mul_metric period hPeriod
        metric displacement base hNonNull
      mul_inverse := normalGraphInducedMetricMatrix_mul_inverse period hPeriod
        metric displacement base hNonNull }
  have hRightTranspose :
      normalGraphInducedMetricMatrix period hPeriod metric displacement base *
          (normalGraphInducedInverseMatrix period hPeriod metric displacement
            base).transpose = 1 := by
    have hTranspose := congrArg Matrix.transpose data.inverse_mul
    simpa [Matrix.transpose_mul,
      normalGraphInducedMetricMatrix_symmetric period hPeriod metric displacement
        base] using hTranspose
  calc
    (normalGraphInducedInverseMatrix period hPeriod metric displacement
        base).transpose =
        1 * (normalGraphInducedInverseMatrix period hPeriod metric displacement
          base).transpose := by rw [one_mul]
    _ = (normalGraphInducedInverseMatrix period hPeriod metric displacement base *
          normalGraphInducedMetricMatrix period hPeriod metric displacement base) *
          (normalGraphInducedInverseMatrix period hPeriod metric displacement
            base).transpose := by rw [data.inverse_mul]
    _ = normalGraphInducedInverseMatrix period hPeriod metric displacement base *
          (normalGraphInducedMetricMatrix period hPeriod metric displacement base *
            (normalGraphInducedInverseMatrix period hPeriod metric displacement
              base).transpose) := by rw [Matrix.mul_assoc]
    _ = normalGraphInducedInverseMatrix period hPeriod metric displacement base *
          1 := by rw [hRightTranspose]
    _ = normalGraphInducedInverseMatrix period hPeriod metric displacement base :=
      by rw [mul_one]

/-! ### Genuine holonomic metric normal -/

def normalGraphHolonomicTangentialPairingCoefficient
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate ambient : HolonomicVector4)
    (current : EffectiveThroat period hPeriod × Real)
    (index : Fin 3) : Real :=
  localMetricCoordinateForm period hPeriod metric patch
    (normalGraphHolonomicCoordinateGerm period hPeriod displacement base patch
      coordinate current) ambient
    (normalGraphHolonomicFamilyDerivativeCoordinates period hPeriod displacement
      base patch coordinate current (throatCoordinateBasis index))

/-- Coordinate covector pairing an ambient vector with graph tangents. -/
def normalGraphHolonomicTangentialPairingCoordinates
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate ambient : HolonomicVector4)
    (current : EffectiveThroat period hPeriod × Real) :
    ThroatCoverCoordinates →L[Real] Real :=
  ∑ index : Fin 3,
    normalGraphHolonomicTangentialPairingCoefficient period hPeriod metric
      displacement base patch coordinate ambient current index •
        throatContinuousDualBasis index

theorem normalGraphHolonomicTangentialPairingCoordinates_apply
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate ambient : HolonomicVector4)
    (current : EffectiveThroat period hPeriod × Real)
    (tangent : ThroatCoverCoordinates) :
    normalGraphHolonomicTangentialPairingCoordinates period hPeriod metric
        displacement base patch coordinate ambient current tangent =
      localMetricCoordinateForm period hPeriod metric patch
        (normalGraphHolonomicCoordinateGerm period hPeriod displacement base
          patch coordinate current) ambient
        (normalGraphHolonomicFamilyDerivativeCoordinates period hPeriod
          displacement base patch coordinate current tangent) := by
  rw [← throatCoordinateBasis.sum_repr tangent]
  simp [normalGraphHolonomicTangentialPairingCoordinates,
    normalGraphHolonomicTangentialPairingCoefficient,
    throatContinuousDualBasis]
  calc
    (∑ index : Fin 3,
        localMetricCoordinateForm period hPeriod metric patch
            (normalGraphHolonomicCoordinateGerm period hPeriod displacement
              base patch coordinate current) ambient
            (normalGraphHolonomicFamilyDerivativeCoordinates period hPeriod
              displacement base patch coordinate current
                (throatCoordinateBasis index)) *
          throatCoordinateBasis.repr tangent index) =
      ∑ index : Fin 3, throatCoordinateBasis.repr tangent index *
        localMetricCoordinateForm period hPeriod metric patch
            (normalGraphHolonomicCoordinateGerm period hPeriod displacement
              base patch coordinate current) ambient
            (normalGraphHolonomicFamilyDerivativeCoordinates period hPeriod
              displacement base patch coordinate current
                (throatCoordinateBasis index)) := by
          apply Finset.sum_congr rfl
          intro index _
          ring
    _ = localMetricCoordinateForm period hPeriod metric patch
          (normalGraphHolonomicCoordinateGerm period hPeriod displacement base
            patch coordinate current) ambient
          (normalGraphHolonomicFamilyDerivativeCoordinates period hPeriod
            displacement base patch coordinate current
            (∑ index : Fin 3, throatCoordinateBasis.repr tangent index •
              throatCoordinateBasis index)) := by
        simp only [map_sum, map_smul, smul_eq_mul]
    _ = _ := by rw [throatCoordinateBasis.sum_repr]

/-- Pairing with graph tangents obeys the same genuine holonomic transition
law as the ambient metric and graph differential. -/
theorem normalGraphHolonomicTangentialPairingCoordinates_transition
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate ambient : HolonomicVector4)
    (hFirst : firstPatch.coordinateMap firstCoordinate =
      normalGraph period hPeriod displacement base.2 base.1)
    (hSecond : secondPatch.coordinateMap secondCoordinate =
      normalGraph period hPeriod displacement base.2 base.1) :
    normalGraphHolonomicTangentialPairingCoordinates period hPeriod metric
        displacement base firstPatch firstCoordinate ambient base =
      normalGraphHolonomicTangentialPairingCoordinates period hPeriod metric
        displacement base secondPatch secondCoordinate
        (holonomicCoordinateTransitionLinearEquivAt period hPeriod firstPatch
          secondPatch firstCoordinate secondCoordinate
          (hFirst.trans hSecond.symm) ambient) base := by
  apply ContinuousLinearMap.ext
  intro tangent
  rw [normalGraphHolonomicTangentialPairingCoordinates_apply,
    normalGraphHolonomicTangentialPairingCoordinates_apply,
    normalGraphHolonomicCoordinateGerm_base period hPeriod displacement base
      firstPatch firstCoordinate hFirst,
    normalGraphHolonomicCoordinateGerm_base period hPeriod displacement base
      secondPatch secondCoordinate hSecond,
    ← normalGraphHolonomicFamilyDerivativeCoordinates_transition period hPeriod
      displacement base firstPatch secondPatch firstCoordinate secondCoordinate
      hFirst hSecond tangent]
  exact localMetricCoordinateForm_transition period hPeriod metric firstPatch
    secondPatch firstCoordinate secondCoordinate ambient
      (normalGraphHolonomicFamilyDerivativeCoordinates period hPeriod
        displacement base firstPatch firstCoordinate base tangent)
      (hFirst.trans hSecond.symm)

theorem normalGraphHolonomicTangentialPairingCoefficient_contMDiffAt
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate ambient : HolonomicVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraph period hPeriod displacement base.2 base.1)
    (index : Fin 3) :
    ContMDiffAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      𝓘(Real, Real) ∞
      (fun current => normalGraphHolonomicTangentialPairingCoefficient period
        hPeriod metric displacement base patch coordinate ambient current index)
      base := by
  have hCoordinate :=
    normalGraphHolonomicCoordinateGerm_contMDiffAt period hPeriod displacement
      base patch coordinate hAt
  have hDerivative :=
    normalGraphHolonomicFamilyDerivativeCoordinates_contMDiffAt period hPeriod
      displacement base patch coordinate hAt
  have hTangentVector : ContMDiffAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      𝓘(Real, HolonomicVector4) ∞
      (fun current =>
        normalGraphHolonomicFamilyDerivativeCoordinates period hPeriod
          displacement base patch coordinate current
            (throatCoordinateBasis index)) base :=
    hDerivative.clm_apply
      (contMDiffAt_const (c := throatCoordinateBasis index))
  have hTangentComponent : ∀ component,
      ContMDiffAt
        (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
        𝓘(Real, Real) ∞
        (fun current =>
          normalGraphHolonomicFamilyDerivativeCoordinates period hPeriod
            displacement base patch coordinate current
              (throatCoordinateBasis index) component) base := by
    intro component
    exact contMDiffAt_pi_space.mp hTangentVector component
  have hMetricEntry : ∀ firstIndex secondIndex,
      ContMDiffAt
        (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
        𝓘(Real, Real) ∞
        (fun current => localMetricMatrix period hPeriod metric patch
          (normalGraphHolonomicCoordinateGerm period hPeriod displacement base
            patch coordinate current) firstIndex secondIndex) base := by
    intro firstIndex secondIndex
    have hEntry := ContDiff.comp_contMDiffAt
      (localMetricCoefficient_contDiff period hPeriod metric patch firstIndex
        secondIndex) hCoordinate
    apply hEntry.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall (fun _ => rfl)
  unfold normalGraphHolonomicTangentialPairingCoefficient
    localMetricCoordinateForm
  simp only [Matrix.toBilin'_apply]
  apply ContMDiffAt.sum
  intro firstIndex _
  apply ContMDiffAt.sum
  intro secondIndex _
  exact (contMDiffAt_const.mul
    (hMetricEntry firstIndex secondIndex)).mul
      (hTangentComponent secondIndex)

theorem normalGraphHolonomicTangentialPairingCoordinates_contMDiffAt
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate ambient : HolonomicVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraph period hPeriod displacement base.2 base.1) :
    ContMDiffAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      𝓘(Real, ThroatCoverCoordinates →L[Real] Real) ∞
      (normalGraphHolonomicTangentialPairingCoordinates period hPeriod metric
        displacement base patch coordinate ambient) base := by
  unfold normalGraphHolonomicTangentialPairingCoordinates
  apply ContMDiffAt.sum
  intro index _
  exact
    (normalGraphHolonomicTangentialPairingCoefficient_contMDiffAt period hPeriod
      metric displacement base patch coordinate ambient hAt index).smul
        contMDiffAt_const

/-- Orthogonal projection in a genuine holonomic coordinate germ.  It reuses
the intrinsic induced inverse; no second inverse metric is introduced. -/
def normalGraphHolonomicMetricNormalCoordinates
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate ambient : HolonomicVector4)
    (current : EffectiveThroat period hPeriod × Real) : HolonomicVector4 :=
  ambient -
    normalGraphHolonomicFamilyDerivativeCoordinates period hPeriod displacement
      base patch coordinate current
      (normalGraphInducedMetricInverseCoordinates period hPeriod metric
        displacement base current
      (normalGraphHolonomicTangentialPairingCoordinates period hPeriod metric
          displacement base patch coordinate ambient current))

/-- The metric-normal projector is intrinsic: changing holonomic chart and
transporting the ambient vector by the true Jacobian transports the projected
normal by that same Jacobian. -/
theorem normalGraphHolonomicMetricNormalCoordinates_transition
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate ambient : HolonomicVector4)
    (hFirst : firstPatch.coordinateMap firstCoordinate =
      normalGraph period hPeriod displacement base.2 base.1)
    (hSecond : secondPatch.coordinateMap secondCoordinate =
      normalGraph period hPeriod displacement base.2 base.1) :
    holonomicCoordinateTransitionLinearEquivAt period hPeriod firstPatch
        secondPatch firstCoordinate secondCoordinate (hFirst.trans hSecond.symm)
        (normalGraphHolonomicMetricNormalCoordinates period hPeriod metric
          displacement base firstPatch firstCoordinate ambient base) =
      normalGraphHolonomicMetricNormalCoordinates period hPeriod metric
        displacement base secondPatch secondCoordinate
        (holonomicCoordinateTransitionLinearEquivAt period hPeriod firstPatch
          secondPatch firstCoordinate secondCoordinate
          (hFirst.trans hSecond.symm) ambient) base := by
  unfold normalGraphHolonomicMetricNormalCoordinates
  rw [map_sub,
    normalGraphHolonomicTangentialPairingCoordinates_transition period hPeriod
      metric displacement base firstPatch secondPatch firstCoordinate
      secondCoordinate ambient hFirst hSecond,
    normalGraphHolonomicFamilyDerivativeCoordinates_transition period hPeriod
      displacement base firstPatch secondPatch firstCoordinate secondCoordinate
      hFirst hSecond]

theorem normalGraphHolonomicMetricNormalCoordinates_contMDiffAt
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement base.2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate ambient : HolonomicVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraph period hPeriod displacement base.2 base.1) :
    ContMDiffAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      𝓘(Real, HolonomicVector4) ∞
      (normalGraphHolonomicMetricNormalCoordinates period hPeriod metric
        displacement base patch coordinate ambient) base := by
  have hDerivative :=
    normalGraphHolonomicFamilyDerivativeCoordinates_contMDiffAt period hPeriod
      displacement base patch coordinate hAt
  have hInverse :=
    normalGraphInducedMetricInverseCoordinates_contMDiffAt period hPeriod metric
      displacement base hNonNull
  have hPairing :=
    normalGraphHolonomicTangentialPairingCoordinates_contMDiffAt period hPeriod
      metric displacement base patch coordinate ambient hAt
  have hSharp := hInverse.clm_apply hPairing
  exact contMDiffAt_const.sub (hDerivative.clm_apply hSharp)

theorem normalGraphHolonomicMetricNormalCoordinates_orthogonal
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement base.2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate ambient : HolonomicVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraph period hPeriod displacement base.2 base.1)
    (tangent : ThroatCoverCoordinates) :
    localMetricCoordinateForm period hPeriod metric patch coordinate
        (normalGraphHolonomicMetricNormalCoordinates period hPeriod metric
          displacement base patch coordinate ambient base)
        (normalGraphHolonomicFamilyDerivativeCoordinates period hPeriod
          displacement base patch coordinate base tangent) = 0 := by
  let pairing :=
    normalGraphHolonomicTangentialPairingCoordinates period hPeriod metric
      displacement base patch coordinate ambient base
  let sharp :=
    normalGraphInducedMetricInverseCoordinates period hPeriod metric displacement
      base base pairing
  have hPairingApply :=
    normalGraphHolonomicTangentialPairingCoordinates_apply period hPeriod metric
      displacement base patch coordinate ambient base tangent
  rw [normalGraphHolonomicCoordinateGerm_base period hPeriod displacement base
    patch coordinate hAt] at hPairingApply
  have hInverse :=
    (normalGraphFamilyTraceTensorCoordinates_isInvertible period hPeriod metric
      displacement base hNonNull).self_comp_inverse
  have hCovector :
      normalGraphFamilyTraceTensorCoordinates period hPeriod metric displacement
          base base sharp = pairing := by
    have hApply := congrArg
      (fun map : (ThroatCoverCoordinates →L[Real] Real) →L[Real]
          (ThroatCoverCoordinates →L[Real] Real) => map pairing) hInverse
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      sharp, pairing, normalGraphInducedMetricInverseCoordinates] using hApply
  unfold normalGraphHolonomicMetricNormalCoordinates
  rw [map_sub]
  rw [show
    ((localMetricCoordinateForm period hPeriod metric patch coordinate) ambient -
        (localMetricCoordinateForm period hPeriod metric patch coordinate)
          (normalGraphHolonomicFamilyDerivativeCoordinates period hPeriod
            displacement base patch coordinate base sharp))
        (normalGraphHolonomicFamilyDerivativeCoordinates period hPeriod
          displacement base patch coordinate base tangent) =
      localMetricCoordinateForm period hPeriod metric patch coordinate ambient
          (normalGraphHolonomicFamilyDerivativeCoordinates period hPeriod
            displacement base patch coordinate base tangent) -
        localMetricCoordinateForm period hPeriod metric patch coordinate
          (normalGraphHolonomicFamilyDerivativeCoordinates period hPeriod
            displacement base patch coordinate base sharp)
          (normalGraphHolonomicFamilyDerivativeCoordinates period hPeriod
            displacement base patch coordinate base tangent) by rfl]
  have hHolonomicMetric :
      localMetricCoordinateForm period hPeriod metric patch coordinate
          (normalGraphHolonomicFamilyDerivativeCoordinates period hPeriod
            displacement base patch coordinate base sharp)
          (normalGraphHolonomicFamilyDerivativeCoordinates period hPeriod
            displacement base patch coordinate base tangent) =
        normalGraphHolonomicInducedMetricCoordinates period hPeriod metric
          displacement base patch coordinate base sharp tangent := by
    unfold normalGraphHolonomicInducedMetricCoordinates
    rw [normalGraphHolonomicCoordinateGerm_base period hPeriod displacement base
      patch coordinate hAt]
  rw [hHolonomicMetric]
  rw [← hPairingApply]
  rw [normalGraphHolonomicInducedMetricCoordinates_eq_traceCoordinates period
    hPeriod metric displacement base patch coordinate hAt]
  rw [hCovector]
  exact sub_self _

theorem exists_normalGraphHolonomicMetricNormalCoordinates_ne_zero
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4) :
    ∃ ambient : HolonomicVector4,
      normalGraphHolonomicMetricNormalCoordinates period hPeriod metric
        displacement base patch coordinate ambient base ≠ 0 := by
  by_contra hExists
  push Not at hExists
  let derivative :=
    normalGraphHolonomicFamilyDerivativeCoordinates period hPeriod displacement
      base patch coordinate base
  have hSurjective : Function.Surjective derivative := by
    intro ambient
    let pairing :=
      normalGraphHolonomicTangentialPairingCoordinates period hPeriod metric
        displacement base patch coordinate ambient base
    let sharp :=
      normalGraphInducedMetricInverseCoordinates period hPeriod metric
        displacement base base pairing
    refine ⟨sharp, ?_⟩
    have hZero := hExists ambient
    unfold normalGraphHolonomicMetricNormalCoordinates at hZero
    exact (sub_eq_zero.mp hZero).symm
  have hDimension :=
    LinearMap.finrank_le_finrank_of_surjective hSurjective
  have hAmbientDimension : Module.finrank Real HolonomicVector4 = 4 := by
    simp [HolonomicVector4]
  have hThroatDimension : Module.finrank Real ThroatCoverCoordinates = 3 := by
    simp [ThroatCoverCoordinates]
  rw [hAmbientDimension, hThroatDimension] at hDimension
  omega

@[simp]
theorem normalGraphHolonomicTangentialPairingCoordinates_neg
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate ambient : HolonomicVector4)
    (current : EffectiveThroat period hPeriod × Real) :
    normalGraphHolonomicTangentialPairingCoordinates period hPeriod metric
        displacement base patch coordinate (-ambient) current =
      -normalGraphHolonomicTangentialPairingCoordinates period hPeriod metric
        displacement base patch coordinate ambient current := by
  apply ContinuousLinearMap.ext
  intro tangent
  simp only [normalGraphHolonomicTangentialPairingCoordinates_apply]
  simp
  exact
    (normalGraphHolonomicTangentialPairingCoordinates_apply period hPeriod metric
      displacement base patch coordinate ambient current tangent).symm

@[simp]
theorem normalGraphHolonomicMetricNormalCoordinates_neg
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate ambient : HolonomicVector4)
    (current : EffectiveThroat period hPeriod × Real) :
    normalGraphHolonomicMetricNormalCoordinates period hPeriod metric
        displacement base patch coordinate (-ambient) current =
      -normalGraphHolonomicMetricNormalCoordinates period hPeriod metric
        displacement base patch coordinate ambient current := by
  simp [normalGraphHolonomicMetricNormalCoordinates]
  abel

def normalGraphHolonomicMetricNormalSquareCoordinates
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate ambient : HolonomicVector4)
    (current : EffectiveThroat period hPeriod × Real) : Real :=
  localMetricCoordinateForm period hPeriod metric patch
    (normalGraphHolonomicCoordinateGerm period hPeriod displacement base patch
      coordinate current)
    (normalGraphHolonomicMetricNormalCoordinates period hPeriod metric
      displacement base patch coordinate ambient current)
    (normalGraphHolonomicMetricNormalCoordinates period hPeriod metric
      displacement base patch coordinate ambient current)

/-- The squared length of the projected normal is a chart-independent scalar
at the graph anchor. -/
theorem normalGraphHolonomicMetricNormalSquareCoordinates_transition
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate ambient : HolonomicVector4)
    (hFirst : firstPatch.coordinateMap firstCoordinate =
      normalGraph period hPeriod displacement base.2 base.1)
    (hSecond : secondPatch.coordinateMap secondCoordinate =
      normalGraph period hPeriod displacement base.2 base.1) :
    normalGraphHolonomicMetricNormalSquareCoordinates period hPeriod metric
        displacement base firstPatch firstCoordinate ambient base =
      normalGraphHolonomicMetricNormalSquareCoordinates period hPeriod metric
        displacement base secondPatch secondCoordinate
        (holonomicCoordinateTransitionLinearEquivAt period hPeriod firstPatch
          secondPatch firstCoordinate secondCoordinate
          (hFirst.trans hSecond.symm) ambient) base := by
  unfold normalGraphHolonomicMetricNormalSquareCoordinates
  rw [normalGraphHolonomicCoordinateGerm_base period hPeriod displacement base
      firstPatch firstCoordinate hFirst,
    normalGraphHolonomicCoordinateGerm_base period hPeriod displacement base
      secondPatch secondCoordinate hSecond,
    localMetricCoordinateForm_transition period hPeriod metric firstPatch
      secondPatch firstCoordinate secondCoordinate
      (normalGraphHolonomicMetricNormalCoordinates period hPeriod metric
        displacement base firstPatch firstCoordinate ambient base)
      (normalGraphHolonomicMetricNormalCoordinates period hPeriod metric
        displacement base firstPatch firstCoordinate ambient base)
      (hFirst.trans hSecond.symm),
    normalGraphHolonomicMetricNormalCoordinates_transition period hPeriod metric
      displacement base firstPatch secondPatch firstCoordinate secondCoordinate
      ambient hFirst hSecond]

theorem normalGraphHolonomicMetricNormalSquareCoordinates_contMDiffAt
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement base.2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate ambient : HolonomicVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraph period hPeriod displacement base.2 base.1) :
    ContMDiffAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      𝓘(Real, Real) ∞
      (normalGraphHolonomicMetricNormalSquareCoordinates period hPeriod metric
        displacement base patch coordinate ambient) base := by
  have hNormal :=
    normalGraphHolonomicMetricNormalCoordinates_contMDiffAt period hPeriod
      metric displacement base hNonNull patch coordinate ambient hAt
  exact normalGraphHolonomicMetricEvaluation_contMDiffAt period hPeriod metric
    displacement base patch coordinate hAt _ _ hNormal hNormal

/-- A nonzero holonomic metric normal is intrinsically non-null.  This is the
coordinate version of the already-proved quotient-normal result: the tangent
metric is invertible, its orthogonal complement has dimension one, and the
ambient coordinate metric is nondegenerate. -/
theorem normalGraphHolonomicMetricNormalSquareCoordinates_ne_zero
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement base.2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate ambient : HolonomicVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraph period hPeriod displacement base.2 base.1)
    (hNormal : normalGraphHolonomicMetricNormalCoordinates period hPeriod metric
      displacement base patch coordinate ambient base ≠ 0) :
    normalGraphHolonomicMetricNormalSquareCoordinates period hPeriod metric
      displacement base patch coordinate ambient base ≠ 0 := by
  let derivative :=
    normalGraphHolonomicFamilyDerivativeCoordinates period hPeriod displacement
      base patch coordinate base
  let normal :=
    normalGraphHolonomicMetricNormalCoordinates period hPeriod metric
      displacement base patch coordinate ambient base
  let adapted : (ThroatCoverCoordinates × Real) →ₗ[Real] HolonomicVector4 :=
    derivative.toLinearMap.coprod
      (LinearMap.toSpanSingleton Real _ normal)
  have hNormalNe : normal ≠ 0 := hNormal
  have hOrthogonal : ∀ tangent : ThroatCoverCoordinates,
      localMetricCoordinateForm period hPeriod metric patch coordinate normal
        (derivative tangent) = 0 := by
    intro tangent
    exact normalGraphHolonomicMetricNormalCoordinates_orthogonal period hPeriod
      metric displacement base hNonNull patch coordinate ambient hAt tangent
  have hAdaptedInjective : Function.Injective adapted := by
    suffices hKernel : ∀ pair, adapted pair = 0 → pair = 0 by
      intro first second hEqual
      apply sub_eq_zero.mp
      apply hKernel (first - second)
      rw [map_sub, hEqual, sub_self]
    intro pair hPairZero
    have hPair : derivative pair.1 + pair.2 • normal = 0 := by
      simpa [adapted] using hPairZero
    have hTraceZero :
        normalGraphFamilyTraceTensorCoordinates period hPeriod metric
          displacement base base pair.1 = 0 := by
      apply ContinuousLinearMap.ext
      intro tangent
      have hApplied := congrArg
        (fun vector => localMetricCoordinateForm period hPeriod metric patch
          coordinate vector (derivative tangent)) hPair
      have hInducedZero :
          normalGraphHolonomicInducedMetricCoordinates period hPeriod metric
            displacement base patch coordinate base pair.1 tangent = 0 := by
        unfold normalGraphHolonomicInducedMetricCoordinates
        rw [normalGraphHolonomicCoordinateGerm_base period hPeriod displacement
          base patch coordinate hAt]
        simpa [map_add, hOrthogonal tangent] using hApplied
      rw [normalGraphHolonomicInducedMetricCoordinates_eq_traceCoordinates
        period hPeriod metric displacement base patch coordinate hAt] at hInducedZero
      exact hInducedZero
    have hTangentZero : pair.1 = 0 :=
      (normalGraphFamilyTraceTensorCoordinates_isInvertible period hPeriod metric
        displacement base hNonNull).injective (by simpa using hTraceZero)
    have hScalarNormal : pair.2 • normal = 0 := by
      simpa [hTangentZero] using hPair
    have hScalarZero : pair.2 = 0 :=
      (smul_eq_zero.mp hScalarNormal).resolve_right hNormalNe
    exact Prod.ext hTangentZero hScalarZero
  have hRank : Module.finrank Real (ThroatCoverCoordinates × Real) =
      Module.finrank Real HolonomicVector4 := by
    simp [ThroatCoverCoordinates, HolonomicVector4]
  have hAdaptedSurjective : Function.Surjective adapted :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hRank).mp
      hAdaptedInjective
  intro hSquare
  have hNormalSquare :
      localMetricCoordinateForm period hPeriod metric patch coordinate normal
        normal = 0 := by
    simpa only [normalGraphHolonomicMetricNormalSquareCoordinates,
      normalGraphHolonomicCoordinateGerm_base period hPeriod displacement base
        patch coordinate hAt, normal] using hSquare
  have hFlatZero :
      localMetricCoordinateForm period hPeriod metric patch coordinate normal =
        0 := by
    apply LinearMap.ext
    intro vector
    obtain ⟨pair, rfl⟩ := hAdaptedSurjective vector
    simp only [adapted, LinearMap.coprod_apply,
      LinearMap.toSpanSingleton_apply]
    change localMetricCoordinateForm period hPeriod metric patch coordinate
      normal (derivative pair.1 + pair.2 • normal) = 0
    rw [map_add, hOrthogonal pair.1, map_smul, hNormalSquare]
    simp
  have hCoordinateNondegenerate :
      (localMetricCoordinateForm period hPeriod metric patch
        coordinate).Nondegenerate := by
    unfold localMetricCoordinateForm
    exact LinearMap.BilinForm.nondegenerate_toBilin'_of_det_ne_zero'
      (localMetricMatrix period hPeriod metric patch coordinate)
      (localMetricMatrix_det_ne_zero period hPeriod metric patch coordinate)
  exact hNormalNe (hCoordinateNondegenerate.1 normal (by
    intro vector
    exact LinearMap.congr_fun hFlatZero vector))

@[simp]
theorem normalGraphHolonomicMetricNormalSquareCoordinates_neg
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate ambient : HolonomicVector4)
    (current : EffectiveThroat period hPeriod × Real) :
    normalGraphHolonomicMetricNormalSquareCoordinates period hPeriod metric
        displacement base patch coordinate (-ambient) current =
      normalGraphHolonomicMetricNormalSquareCoordinates period hPeriod metric
        displacement base patch coordinate ambient current := by
  simp [normalGraphHolonomicMetricNormalSquareCoordinates]

def normalGraphHolonomicMetricUnitNormalCoordinates
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate ambient : HolonomicVector4)
    (current : EffectiveThroat period hPeriod × Real) : HolonomicVector4 :=
  (Real.sqrt
    |normalGraphHolonomicMetricNormalSquareCoordinates period hPeriod metric
      displacement base patch coordinate ambient current|)⁻¹ •
    normalGraphHolonomicMetricNormalCoordinates period hPeriod metric
      displacement base patch coordinate ambient current

/-- Unit normalization commutes with a genuine holonomic-coordinate change. -/
theorem normalGraphHolonomicMetricUnitNormalCoordinates_transition
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate ambient : HolonomicVector4)
    (hFirst : firstPatch.coordinateMap firstCoordinate =
      normalGraph period hPeriod displacement base.2 base.1)
    (hSecond : secondPatch.coordinateMap secondCoordinate =
      normalGraph period hPeriod displacement base.2 base.1) :
    holonomicCoordinateTransitionLinearEquivAt period hPeriod firstPatch
        secondPatch firstCoordinate secondCoordinate (hFirst.trans hSecond.symm)
        (normalGraphHolonomicMetricUnitNormalCoordinates period hPeriod metric
          displacement base firstPatch firstCoordinate ambient base) =
      normalGraphHolonomicMetricUnitNormalCoordinates period hPeriod metric
        displacement base secondPatch secondCoordinate
        (holonomicCoordinateTransitionLinearEquivAt period hPeriod firstPatch
          secondPatch firstCoordinate secondCoordinate
          (hFirst.trans hSecond.symm) ambient) base := by
  unfold normalGraphHolonomicMetricUnitNormalCoordinates
  rw [map_smul,
    normalGraphHolonomicMetricNormalSquareCoordinates_transition period hPeriod
      metric displacement base firstPatch secondPatch firstCoordinate
      secondCoordinate ambient hFirst hSecond,
    normalGraphHolonomicMetricNormalCoordinates_transition period hPeriod metric
      displacement base firstPatch secondPatch firstCoordinate secondCoordinate
      ambient hFirst hSecond]

/-- The first-chart unit-normal germ transported by the genuine varying
Jacobian of a holonomic coordinate change.  This is the same normal field in
second coordinates, not a separately supplied normal. -/
def normalGraphHolonomicTransportedMetricUnitNormalCoordinates
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : HolonomicVector4)
    (samePoint : firstPatch.coordinateMap firstCoordinate =
      secondPatch.coordinateMap secondCoordinate)
    (ambient : HolonomicVector4)
    (current : EffectiveThroat period hPeriod × Real) : HolonomicVector4 :=
  fderiv Real
      (holonomicCoordinateTransitionAt period hPeriod firstPatch secondPatch
        firstCoordinate secondCoordinate samePoint)
      (normalGraphHolonomicCoordinateGerm period hPeriod displacement base
        firstPatch firstCoordinate current)
      (normalGraphHolonomicMetricUnitNormalCoordinates period hPeriod metric
        displacement base firstPatch firstCoordinate ambient current)

/-- At the overlap anchor, the varying-Jacobian transport is exactly the
already constructed second-chart unit normal. -/
theorem normalGraphHolonomicTransportedMetricUnitNormalCoordinates_base
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate ambient : HolonomicVector4)
    (hFirst : firstPatch.coordinateMap firstCoordinate =
      normalGraph period hPeriod displacement base.2 base.1)
    (hSecond : secondPatch.coordinateMap secondCoordinate =
      normalGraph period hPeriod displacement base.2 base.1) :
    normalGraphHolonomicTransportedMetricUnitNormalCoordinates period hPeriod
        metric displacement base firstPatch secondPatch firstCoordinate
          secondCoordinate (hFirst.trans hSecond.symm) ambient base =
      normalGraphHolonomicMetricUnitNormalCoordinates period hPeriod metric
        displacement base secondPatch secondCoordinate
          (holonomicCoordinateTransitionLinearEquivAt period hPeriod firstPatch
            secondPatch firstCoordinate secondCoordinate
            (hFirst.trans hSecond.symm) ambient) base := by
  unfold normalGraphHolonomicTransportedMetricUnitNormalCoordinates
  rw [normalGraphHolonomicCoordinateGerm_base period hPeriod displacement base
      firstPatch firstCoordinate hFirst,
    ← holonomicCoordinateTransitionLinearEquivAt_coe period hPeriod firstPatch
      secondPatch firstCoordinate secondCoordinate (hFirst.trans hSecond.symm)]
  exact normalGraphHolonomicMetricUnitNormalCoordinates_transition period
    hPeriod metric displacement base firstPatch secondPatch firstCoordinate
      secondCoordinate ambient hFirst hSecond

/-- The Levi--Civita term evaluated on the graph tangent and its unit normal
has the exact non-tensorial transition law.  The displayed second derivative
is the term that cancels the coordinate derivative of the transported normal. -/
theorem normalGraphHolonomicLeviCivitaNormalTerm_transition
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate ambient : HolonomicVector4)
    (hFirst : firstPatch.coordinateMap firstCoordinate =
      normalGraph period hPeriod displacement base.2 base.1)
    (hSecond : secondPatch.coordinateMap secondCoordinate =
      normalGraph period hPeriod displacement base.2 base.1)
    (tangent : ThroatCoverCoordinates) :
    let samePoint := hFirst.trans hSecond.symm
    let transition := holonomicCoordinateTransitionAt period hPeriod firstPatch
      secondPatch firstCoordinate secondCoordinate samePoint
    let transitionLinear :=
      holonomicCoordinateTransitionLinearEquivAt period hPeriod firstPatch
        secondPatch firstCoordinate secondCoordinate samePoint
    let firstTangent :=
      normalGraphHolonomicFamilyDerivativeCoordinates period hPeriod
        displacement base firstPatch firstCoordinate base tangent
    let firstNormal :=
      normalGraphHolonomicMetricUnitNormalCoordinates period hPeriod metric
        displacement base firstPatch firstCoordinate ambient base
    transitionLinear
        (localLeviCivitaChristoffelApply period hPeriod metric firstPatch
          firstCoordinate firstTangent firstNormal) =
      localLeviCivitaChristoffelApply period hPeriod metric secondPatch
          secondCoordinate
          (normalGraphHolonomicFamilyDerivativeCoordinates period hPeriod
            displacement base secondPatch secondCoordinate base tangent)
          (normalGraphHolonomicMetricUnitNormalCoordinates period hPeriod metric
            displacement base secondPatch secondCoordinate
            (transitionLinear ambient) base) +
        fderiv Real (fderiv Real transition) firstCoordinate firstTangent
          firstNormal := by
  dsimp only
  let samePoint := hFirst.trans hSecond.symm
  let transition := holonomicCoordinateTransitionAt period hPeriod firstPatch
    secondPatch firstCoordinate secondCoordinate samePoint
  let transitionLinear :=
    holonomicCoordinateTransitionLinearEquivAt period hPeriod firstPatch
      secondPatch firstCoordinate secondCoordinate samePoint
  let firstTangent :=
    normalGraphHolonomicFamilyDerivativeCoordinates period hPeriod displacement
      base firstPatch firstCoordinate base tangent
  let firstNormal :=
    normalGraphHolonomicMetricUnitNormalCoordinates period hPeriod metric
      displacement base firstPatch firstCoordinate ambient base
  have hConnection :=
    (fixedHolonomicTransition_leviCivita_eventuallyEq_vectors period hPeriod
      metric firstPatch secondPatch firstCoordinate secondCoordinate samePoint
      firstTangent firstNormal).eq_of_nhds
  rw [holonomicCoordinateTransitionAt_apply period hPeriod firstPatch
      secondPatch firstCoordinate secondCoordinate samePoint,
    ← holonomicCoordinateTransitionLinearEquivAt_coe period hPeriod firstPatch
      secondPatch firstCoordinate secondCoordinate samePoint] at hConnection
  dsimp [firstTangent, firstNormal, transitionLinear, transition, samePoint]
    at hConnection
  rw [normalGraphHolonomicFamilyDerivativeCoordinates_transition period hPeriod
      displacement base firstPatch secondPatch firstCoordinate secondCoordinate
      hFirst hSecond tangent,
    normalGraphHolonomicMetricUnitNormalCoordinates_transition period hPeriod
      metric displacement base firstPatch secondPatch firstCoordinate
      secondCoordinate ambient hFirst hSecond] at hConnection
  exact hConnection

theorem normalGraphHolonomicMetricUnitNormalCoordinates_contMDiffAt
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement base.2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate ambient : HolonomicVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraph period hPeriod displacement base.2 base.1)
    (hSquare : normalGraphHolonomicMetricNormalSquareCoordinates period hPeriod
      metric displacement base patch coordinate ambient base ≠ 0) :
    ContMDiffAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      𝓘(Real, HolonomicVector4) ∞
      (normalGraphHolonomicMetricUnitNormalCoordinates period hPeriod metric
        displacement base patch coordinate ambient) base := by
  have hNormal :=
    normalGraphHolonomicMetricNormalCoordinates_contMDiffAt period hPeriod
      metric displacement base hNonNull patch coordinate ambient hAt
  have hSquareSmooth :=
    normalGraphHolonomicMetricNormalSquareCoordinates_contMDiffAt period hPeriod
      metric displacement base hNonNull patch coordinate ambient hAt
  have hAbs : ContMDiffAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      𝓘(Real, Real) ∞
      (fun current =>
        |normalGraphHolonomicMetricNormalSquareCoordinates period hPeriod metric
          displacement base patch coordinate ambient current|) base := by
    simpa [Function.comp_def] using
      (contDiffAt_abs hSquare).comp_contMDiffAt hSquareSmooth
  have hAbsPositive : 0 <
      |normalGraphHolonomicMetricNormalSquareCoordinates period hPeriod metric
        displacement base patch coordinate ambient base| := abs_pos.mpr hSquare
  have hRoot : ContMDiffAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      𝓘(Real, Real) ∞
      (fun current => Real.sqrt
        |normalGraphHolonomicMetricNormalSquareCoordinates period hPeriod metric
          displacement base patch coordinate ambient current|) base := by
    simpa [Function.comp_def] using
      (Real.contDiffAt_sqrt (ne_of_gt hAbsPositive)).comp_contMDiffAt
        (I := throatCoverModelWithCorners.prod
          (modelWithCornersSelf Real Real))
        (f := fun current =>
          |normalGraphHolonomicMetricNormalSquareCoordinates period hPeriod
            metric displacement base patch coordinate ambient current|)
        (x := base) hAbs
  exact (hRoot.inv₀ (Real.sqrt_ne_zero'.mpr hAbsPositive)).smul hNormal

/-- Every admissible graph point therefore has a smooth unit-normal germ in
an already existing holonomic chart.  No coorientation is added: the ambient
coordinate selecting one of the two signs is obtained existentially. -/
theorem exists_normalGraphHolonomicMetricUnitNormalCoordinates_contMDiffAt
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement base.2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraph period hPeriod displacement base.2 base.1) :
    ∃ ambient : HolonomicVector4,
      normalGraphHolonomicMetricNormalSquareCoordinates period hPeriod metric
          displacement base patch coordinate ambient base ≠ 0 ∧
        ContMDiffAt
          (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
          𝓘(Real, HolonomicVector4) ∞
          (normalGraphHolonomicMetricUnitNormalCoordinates period hPeriod metric
            displacement base patch coordinate ambient) base := by
  rcases exists_normalGraphHolonomicMetricNormalCoordinates_ne_zero period
      hPeriod metric displacement base patch coordinate with ⟨ambient, hNormal⟩
  have hSquare :=
    normalGraphHolonomicMetricNormalSquareCoordinates_ne_zero period hPeriod
      metric displacement base hNonNull patch coordinate ambient hAt hNormal
  exact ⟨ambient, hSquare,
    normalGraphHolonomicMetricUnitNormalCoordinates_contMDiffAt period hPeriod
      metric displacement base hNonNull patch coordinate ambient hAt hSquare⟩

/-- Spatial derivative of the unit-normal germ, kept jointly in the graph
parameter and the throat point. -/
def normalGraphHolonomicMetricUnitNormalDerivativeCoordinates
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate ambient : HolonomicVector4)
    (current : EffectiveThroat period hPeriod × Real) :
    ThroatCoverCoordinates →L[Real] HolonomicVector4 :=
  let representative :=
    normalGraphHolonomicMetricUnitNormalCoordinates period hPeriod metric
      displacement base patch coordinate ambient
  inTangentCoordinates throatCoverModelWithCorners
    (modelWithCornersSelf Real HolonomicVector4)
    Prod.fst representative
    (fun point => mfderiv throatCoverModelWithCorners
      (modelWithCornersSelf Real HolonomicVector4)
      (fun throatPoint => representative (throatPoint, point.2)) point.1)
    base current

/-- At the anchor, the stored coordinate derivative is exactly the genuine
manifold derivative of the unit-normal germ in a throat direction. -/
theorem normalGraphHolonomicMetricUnitNormalDerivativeCoordinates_apply_base_eq_mfderiv
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate ambient : HolonomicVector4)
    (vector : ThroatCoverCoordinates) :
    normalGraphHolonomicMetricUnitNormalDerivativeCoordinates period hPeriod
        metric displacement base patch coordinate ambient base vector =
      mfderiv throatCoverModelWithCorners
        (modelWithCornersSelf Real HolonomicVector4)
        (fun point =>
          normalGraphHolonomicMetricUnitNormalCoordinates period hPeriod metric
            displacement base patch coordinate ambient (point, base.2)) base.1
        ((trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) base.1).symm base.1 vector) := by
  have hThroat : base.1 ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) base.1).baseSet :=
    mem_baseSet_trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) base.1
  have hTarget :
      normalGraphHolonomicMetricUnitNormalCoordinates period hPeriod metric
          displacement base patch coordinate ambient base ∈
        (trivializationAt HolonomicVector4
          (fun point : HolonomicVector4 =>
            TangentSpace (modelWithCornersSelf Real HolonomicVector4) point)
          (normalGraphHolonomicMetricUnitNormalCoordinates period hPeriod metric
            displacement base patch coordinate ambient base)).baseSet :=
    mem_baseSet_trivializationAt HolonomicVector4
      (fun point : HolonomicVector4 =>
        TangentSpace (modelWithCornersSelf Real HolonomicVector4) point)
      (normalGraphHolonomicMetricUnitNormalCoordinates period hPeriod metric
        displacement base patch coordinate ambient base)
  rw [show normalGraphHolonomicMetricUnitNormalDerivativeCoordinates period
      hPeriod metric displacement base patch coordinate ambient base =
    ContinuousLinearMap.inCoordinates ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) HolonomicVector4
      (fun point : HolonomicVector4 =>
        TangentSpace (modelWithCornersSelf Real HolonomicVector4) point)
      base.1 base.1
      (normalGraphHolonomicMetricUnitNormalCoordinates period hPeriod metric
        displacement base patch coordinate ambient base)
      (normalGraphHolonomicMetricUnitNormalCoordinates period hPeriod metric
        displacement base patch coordinate ambient base)
      (mfderiv throatCoverModelWithCorners
        (modelWithCornersSelf Real HolonomicVector4)
        (fun point =>
          normalGraphHolonomicMetricUnitNormalCoordinates period hPeriod metric
            displacement base patch coordinate ambient (point, base.2)) base.1)
      by rfl]
  rw [ContinuousLinearMap.inCoordinates_eq hThroat hTarget]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- Differentiating the genuinely transported unit normal gives the Hessian
correction of the coordinate change plus the transported first-chart normal
derivative. -/
theorem normalGraphHolonomicTransportedMetricUnitNormalDerivative_transition
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement base.2)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate ambient : HolonomicVector4)
    (hFirst : firstPatch.coordinateMap firstCoordinate =
      normalGraph period hPeriod displacement base.2 base.1)
    (hSecond : secondPatch.coordinateMap secondCoordinate =
      normalGraph period hPeriod displacement base.2 base.1)
    (hSquare : normalGraphHolonomicMetricNormalSquareCoordinates period hPeriod
      metric displacement base firstPatch firstCoordinate ambient base ≠ 0)
    (tangent : ThroatCoverCoordinates) :
    let samePoint := hFirst.trans hSecond.symm
    let transition := holonomicCoordinateTransitionAt period hPeriod firstPatch
      secondPatch firstCoordinate secondCoordinate samePoint
    let transitionLinear :=
      holonomicCoordinateTransitionLinearEquivAt period hPeriod firstPatch
        secondPatch firstCoordinate secondCoordinate samePoint
    let firstTangent :=
      normalGraphHolonomicFamilyDerivativeCoordinates period hPeriod
        displacement base firstPatch firstCoordinate base tangent
    let firstNormal :=
      normalGraphHolonomicMetricUnitNormalCoordinates period hPeriod metric
        displacement base firstPatch firstCoordinate ambient base
    let firstNormalDerivative :=
      normalGraphHolonomicMetricUnitNormalDerivativeCoordinates period hPeriod
        metric displacement base firstPatch firstCoordinate ambient base tangent
    NormedSpace.fromTangentSpace
        (normalGraphHolonomicTransportedMetricUnitNormalCoordinates period
          hPeriod metric displacement base firstPatch secondPatch
            firstCoordinate secondCoordinate samePoint ambient base)
        (mfderiv throatCoverModelWithCorners
          (modelWithCornersSelf Real HolonomicVector4)
          (fun point =>
            normalGraphHolonomicTransportedMetricUnitNormalCoordinates period
              hPeriod metric displacement base firstPatch secondPatch
                firstCoordinate secondCoordinate samePoint ambient
                  (point, base.2))
          base.1
          ((trivializationAt ThroatCoverCoordinates
            (ThroatTangentFiber period hPeriod) base.1).symm base.1 tangent)) =
      fderiv Real (fderiv Real transition) firstCoordinate firstTangent
          firstNormal +
        transitionLinear firstNormalDerivative := by
  dsimp only
  let samePoint := hFirst.trans hSecond.symm
  let transition := holonomicCoordinateTransitionAt period hPeriod firstPatch
    secondPatch firstCoordinate secondCoordinate samePoint
  let transitionLinear :=
    holonomicCoordinateTransitionLinearEquivAt period hPeriod firstPatch
      secondPatch firstCoordinate secondCoordinate samePoint
  let firstCoordinateGerm := fun point : EffectiveThroat period hPeriod =>
    normalGraphHolonomicCoordinateGerm period hPeriod displacement base
      firstPatch firstCoordinate (point, base.2)
  let firstNormalGerm := fun point : EffectiveThroat period hPeriod =>
    normalGraphHolonomicMetricUnitNormalCoordinates period hPeriod metric
      displacement base firstPatch firstCoordinate ambient (point, base.2)
  let outer := fun pair : HolonomicVector4 × HolonomicVector4 =>
    fderiv Real transition pair.1 pair.2
  let tangentVector :=
    (trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) base.1).symm base.1 tangent
  have hSection : ContMDiffAt throatCoverModelWithCorners
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real)) ∞
      (fun point : EffectiveThroat period hPeriod => (point, base.2)) base.1 :=
    (contMDiff_id.prodMk contMDiff_const).contMDiffAt
  have hCoordinate : MDifferentiableAt throatCoverModelWithCorners
      (modelWithCornersSelf Real HolonomicVector4) firstCoordinateGerm base.1 :=
    (ContMDiffAt.comp
      (f := fun point : EffectiveThroat period hPeriod => (point, base.2))
      (g := normalGraphHolonomicCoordinateGerm period hPeriod displacement base
        firstPatch firstCoordinate) base.1
      (normalGraphHolonomicCoordinateGerm_contMDiffAt period hPeriod
        displacement base firstPatch firstCoordinate hFirst) hSection)
      |>.mdifferentiableAt (by simp)
  have hNormal : MDifferentiableAt throatCoverModelWithCorners
      (modelWithCornersSelf Real HolonomicVector4) firstNormalGerm base.1 :=
    (ContMDiffAt.comp
      (f := fun point : EffectiveThroat period hPeriod => (point, base.2))
      (g := normalGraphHolonomicMetricUnitNormalCoordinates period hPeriod
        metric displacement base firstPatch firstCoordinate ambient) base.1
      (normalGraphHolonomicMetricUnitNormalCoordinates_contMDiffAt period hPeriod
        metric displacement base hNonNull firstPatch firstCoordinate ambient
          hFirst hSquare) hSection)
      |>.mdifferentiableAt (by simp)
  have hInner := hCoordinate.prodMk_space hNormal
  have hInnerDerivative := mfderiv_prodMk hCoordinate hNormal
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hInnerDerivative
  have hCoordinateBase : firstCoordinateGerm base.1 = firstCoordinate :=
    normalGraphHolonomicCoordinateGerm_base period hPeriod displacement base
      firstPatch firstCoordinate hFirst
  have hTransitionFirstDerivative : ContDiffAt Real 2
      (fderiv Real transition) firstCoordinate := by
    simpa [transition] using
      ((holonomicCoordinateTransitionAt_contDiffAt_three period hPeriod
        firstPatch secondPatch firstCoordinate secondCoordinate samePoint)
          |>.fderiv_right (m := 2) (by norm_num))
  have hTransitionDerivative : DifferentiableAt Real
      (fderiv Real transition) firstCoordinate :=
    hTransitionFirstDerivative.differentiableAt (by norm_num)
  have hOuter : MDifferentiableAt
      (modelWithCornersSelf Real (HolonomicVector4 × HolonomicVector4))
      (modelWithCornersSelf Real HolonomicVector4) outer
      (firstCoordinate, firstNormalGerm base.1) :=
    (differentiableAt_transitionDerivative_apply_pair transition firstCoordinate
      (firstNormalGerm base.1) hTransitionDerivative).mdifferentiableAt
  have hOuterAtInner : MDifferentiableAt
      (modelWithCornersSelf Real (HolonomicVector4 × HolonomicVector4))
      (modelWithCornersSelf Real HolonomicVector4) outer
      (firstCoordinateGerm base.1, firstNormalGerm base.1) := by
    rw [hCoordinateBase]
    exact hOuter
  have hChain := mfderiv_comp_apply base.1 hOuterAtInner hInner tangentVector
  have hInnerApply := congrArg
    (fun derivative => derivative tangentVector) hInnerDerivative
  have hCoordinateDerivative :
      mfderiv throatCoverModelWithCorners
          (modelWithCornersSelf Real HolonomicVector4) firstCoordinateGerm
          base.1 tangentVector =
        normalGraphHolonomicFamilyDerivativeCoordinates period hPeriod
          displacement base firstPatch firstCoordinate base tangent := by
    exact (normalGraphHolonomicFamilyDerivativeCoordinates_apply_base_eq_mfderiv
      period hPeriod displacement base firstPatch firstCoordinate tangent).symm
  have hNormalDerivative :
      mfderiv throatCoverModelWithCorners
          (modelWithCornersSelf Real HolonomicVector4) firstNormalGerm base.1
          tangentVector =
        normalGraphHolonomicMetricUnitNormalDerivativeCoordinates period hPeriod
          metric displacement base firstPatch firstCoordinate ambient base
            tangent := by
    exact
      (normalGraphHolonomicMetricUnitNormalDerivativeCoordinates_apply_base_eq_mfderiv
        period hPeriod metric displacement base firstPatch firstCoordinate
          ambient tangent).symm
  have hCoordinateVectorDerivative :
      mvfderiv throatCoverModelWithCorners firstCoordinateGerm base.1
          tangentVector =
        normalGraphHolonomicFamilyDerivativeCoordinates period hPeriod
          displacement base firstPatch firstCoordinate base tangent := by
    unfold mvfderiv
    rw [ContinuousLinearMap.comp_apply, hCoordinateDerivative]
    exact holonomic_fromTangentSpace_apply _ _
  have hNormalVectorDerivative :
      mvfderiv throatCoverModelWithCorners firstNormalGerm base.1
          tangentVector =
        normalGraphHolonomicMetricUnitNormalDerivativeCoordinates period hPeriod
          metric displacement base firstPatch firstCoordinate ambient base
            tangent := by
    unfold mvfderiv
    rw [ContinuousLinearMap.comp_apply, hNormalDerivative]
    exact holonomic_fromTangentSpace_apply _ _
  have hChainMV :
      mvfderiv throatCoverModelWithCorners
          (outer ∘ fun point =>
            (firstCoordinateGerm point, firstNormalGerm point)) base.1
          tangentVector =
        fderiv Real outer
          (firstCoordinateGerm base.1, firstNormalGerm base.1)
          (mvfderiv throatCoverModelWithCorners
            (fun point =>
              (firstCoordinateGerm point, firstNormalGerm point)) base.1
            tangentVector) := by
    unfold mvfderiv
    simp only [ContinuousLinearMap.comp_apply]
    erw [hChain]
    rw [mfderiv_eq_fderiv]
    exact holonomic_fromTangentSpace_fderiv_apply _ _ _
  have hInnerVector :
      mvfderiv throatCoverModelWithCorners
          (fun point =>
            (firstCoordinateGerm point, firstNormalGerm point)) base.1
          tangentVector =
        (mvfderiv throatCoverModelWithCorners firstCoordinateGerm base.1
            tangentVector,
          mvfderiv throatCoverModelWithCorners firstNormalGerm base.1
            tangentVector) := by
    unfold mvfderiv
    simp only [ContinuousLinearMap.comp_apply]
    erw [hInnerApply]
    exact holonomicProduct_fromTangentSpace_prod_apply
      (domain := TangentSpace throatCoverModelWithCorners base.1)
      (firstCoordinateGerm base.1) (firstNormalGerm base.1)
      (mfderiv throatCoverModelWithCorners
        (modelWithCornersSelf Real HolonomicVector4) firstCoordinateGerm base.1)
      (mfderiv throatCoverModelWithCorners
        (modelWithCornersSelf Real HolonomicVector4) firstNormalGerm base.1)
      tangentVector
  rw [hInnerVector, hCoordinateVectorDerivative, hNormalVectorDerivative,
    hCoordinateBase] at hChainMV
  have hProduct := fderiv_transitionDerivative_apply_pair transition
    firstCoordinate (firstNormalGerm base.1)
    (normalGraphHolonomicFamilyDerivativeCoordinates period hPeriod displacement
      base firstPatch firstCoordinate base tangent)
    (normalGraphHolonomicMetricUnitNormalDerivativeCoordinates period hPeriod
      metric displacement base firstPatch firstCoordinate ambient base tangent)
    hTransitionDerivative
  rw [show outer = fun pair : HolonomicVector4 × HolonomicVector4 =>
      fderiv Real transition pair.1 pair.2 by rfl, hProduct] at hChainMV
  rw [← holonomicCoordinateTransitionLinearEquivAt_coe period hPeriod firstPatch
    secondPatch firstCoordinate secondCoordinate samePoint] at hChainMV
  simpa [samePoint, transition, transitionLinear, firstCoordinateGerm,
    firstNormalGerm, outer, tangentVector, Function.comp_def,
    mvfderiv, normalGraphHolonomicTransportedMetricUnitNormalCoordinates] using
      hChainMV

/-- The Hessian correction in the transported normal derivative cancels the
non-tensorial correction in the Levi--Civita transition law.  Thus the full
covariant derivative of the same unit normal is a genuine vector. -/
theorem normalGraphHolonomicTransportedMetricUnitNormalCovariantDerivative_transition
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement base.2)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate ambient : HolonomicVector4)
    (hFirst : firstPatch.coordinateMap firstCoordinate =
      normalGraph period hPeriod displacement base.2 base.1)
    (hSecond : secondPatch.coordinateMap secondCoordinate =
      normalGraph period hPeriod displacement base.2 base.1)
    (hSquare : normalGraphHolonomicMetricNormalSquareCoordinates period hPeriod
      metric displacement base firstPatch firstCoordinate ambient base ≠ 0)
    (tangent : ThroatCoverCoordinates) :
    let samePoint := hFirst.trans hSecond.symm
    let transitionLinear :=
      holonomicCoordinateTransitionLinearEquivAt period hPeriod firstPatch
        secondPatch firstCoordinate secondCoordinate samePoint
    let firstTangent :=
      normalGraphHolonomicFamilyDerivativeCoordinates period hPeriod
        displacement base firstPatch firstCoordinate base tangent
    let firstNormal :=
      normalGraphHolonomicMetricUnitNormalCoordinates period hPeriod metric
        displacement base firstPatch firstCoordinate ambient base
    let firstNormalDerivative :=
      normalGraphHolonomicMetricUnitNormalDerivativeCoordinates period hPeriod
        metric displacement base firstPatch firstCoordinate ambient base tangent
    let secondTangent :=
      normalGraphHolonomicFamilyDerivativeCoordinates period hPeriod
        displacement base secondPatch secondCoordinate base tangent
    let secondNormal :=
      normalGraphHolonomicMetricUnitNormalCoordinates period hPeriod metric
        displacement base secondPatch secondCoordinate
          (transitionLinear ambient) base
    let transportedDerivative :=
      NormedSpace.fromTangentSpace
        (normalGraphHolonomicTransportedMetricUnitNormalCoordinates period
          hPeriod metric displacement base firstPatch secondPatch firstCoordinate
            secondCoordinate samePoint ambient base)
        (mfderiv throatCoverModelWithCorners
          (modelWithCornersSelf Real HolonomicVector4)
          (fun point =>
            normalGraphHolonomicTransportedMetricUnitNormalCoordinates period
              hPeriod metric displacement base firstPatch secondPatch
                firstCoordinate secondCoordinate samePoint ambient
                  (point, base.2))
          base.1
          ((trivializationAt ThroatCoverCoordinates
            (ThroatTangentFiber period hPeriod) base.1).symm base.1 tangent))
    transportedDerivative +
        localLeviCivitaChristoffelApply period hPeriod metric secondPatch
          secondCoordinate secondTangent secondNormal =
      transitionLinear
        (firstNormalDerivative +
          localLeviCivitaChristoffelApply period hPeriod metric firstPatch
            firstCoordinate firstTangent firstNormal) := by
  dsimp only
  have hDerivative :=
    normalGraphHolonomicTransportedMetricUnitNormalDerivative_transition period
      hPeriod metric displacement base hNonNull firstPatch secondPatch
        firstCoordinate secondCoordinate ambient hFirst hSecond hSquare tangent
  dsimp only at hDerivative
  have hConnection :=
    normalGraphHolonomicLeviCivitaNormalTerm_transition period hPeriod metric
      displacement base firstPatch secondPatch firstCoordinate secondCoordinate
        ambient hFirst hSecond tangent
  dsimp only at hConnection
  rw [hDerivative, map_add, hConnection]
  abel

theorem normalGraphHolonomicMetricUnitNormalDerivativeCoordinates_contMDiffAt
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement base.2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate ambient : HolonomicVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraph period hPeriod displacement base.2 base.1)
    (hSquare : normalGraphHolonomicMetricNormalSquareCoordinates period hPeriod
      metric displacement base patch coordinate ambient base ≠ 0) :
    ContMDiffAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      𝓘(Real,
        ThroatCoverCoordinates →L[Real] HolonomicVector4) ∞
      (normalGraphHolonomicMetricUnitNormalDerivativeCoordinates period hPeriod
        metric displacement base patch coordinate ambient) base := by
  let representative :=
    normalGraphHolonomicMetricUnitNormalCoordinates period hPeriod metric
      displacement base patch coordinate ambient
  let f : (EffectiveThroat period hPeriod × Real) →
      EffectiveThroat period hPeriod → HolonomicVector4 :=
    fun parameterPoint point => representative (point, parameterPoint.2)
  let g : (EffectiveThroat period hPeriod × Real) →
      EffectiveThroat period hPeriod := Prod.fst
  have hRepresentative : ContMDiffAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real HolonomicVector4) ∞ representative base := by
    simpa [representative] using
      (normalGraphHolonomicMetricUnitNormalCoordinates_contMDiffAt period hPeriod
        metric displacement base hNonNull patch coordinate ambient hAt hSquare)
  have hReorder : ContMDiffAt
      ((throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real)).prod
        throatCoverModelWithCorners)
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real)) ∞
      (fun point : (EffectiveThroat period hPeriod × Real) ×
          EffectiveThroat period hPeriod => (point.2, point.1.2))
      (base, base.1) :=
    (contMDiff_snd.prodMk (contMDiff_snd.comp contMDiff_fst)).contMDiffAt
  have hg : ContMDiffAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      throatCoverModelWithCorners ∞ g base := by
    simpa [g] using
      (contMDiff_fst : ContMDiff
        (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
        throatCoverModelWithCorners ∞
        (Prod.fst : EffectiveThroat period hPeriod × Real →
          EffectiveThroat period hPeriod)).contMDiffAt
  have hJoint : ContMDiffAt
      ((throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real)).prod
        throatCoverModelWithCorners)
      (modelWithCornersSelf Real HolonomicVector4) ∞
      (fun point : (EffectiveThroat period hPeriod × Real) ×
          EffectiveThroat period hPeriod => representative (point.2, point.1.2))
      (base, base.1) :=
    ContMDiffAt.comp (f := fun point :
        (EffectiveThroat period hPeriod × Real) ×
          EffectiveThroat period hPeriod => (point.2, point.1.2))
      (g := representative) (base, base.1) hRepresentative hReorder
  change ContMDiffAt
    (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
    𝓘(Real, ThroatCoverCoordinates →L[Real] HolonomicVector4) ∞
    (inTangentCoordinates throatCoverModelWithCorners
      (modelWithCornersSelf Real HolonomicVector4) g representative
      (fun point => mfderiv throatCoverModelWithCorners
        (modelWithCornersSelf Real HolonomicVector4) (f point) (g point))
      base) base
  exact hJoint.mfderiv f g hg (by simp)

/-- Smoothness of the existing holonomic Levi--Civita coefficients after
evaluation on two jointly smooth coordinate-vector fields. -/
theorem normalGraphHolonomicLeviCivitaApply_contMDiffAt
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraph period hPeriod displacement base.2 base.1)
    (firstField secondField :
      EffectiveThroat period hPeriod × Real → HolonomicVector4)
    (hFirst : ContMDiffAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      𝓘(Real, HolonomicVector4) ∞ firstField base)
    (hSecond : ContMDiffAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      𝓘(Real, HolonomicVector4) ∞ secondField base) :
    ContMDiffAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      𝓘(Real, HolonomicVector4) ∞
      (fun current => localLeviCivitaChristoffelApply period hPeriod metric patch
        (normalGraphHolonomicCoordinateGerm period hPeriod displacement base
          patch coordinate current) (firstField current) (secondField current))
      base := by
  have hCoordinate :=
    normalGraphHolonomicCoordinateGerm_contMDiffAt period hPeriod displacement
      base patch coordinate hAt
  have hFirstComponent : ∀ index,
      ContMDiffAt
        (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
        𝓘(Real, Real) ∞ (fun current => firstField current index) base := by
    intro index
    exact contMDiffAt_pi_space.mp hFirst index
  have hSecondComponent : ∀ index,
      ContMDiffAt
        (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
        𝓘(Real, Real) ∞ (fun current => secondField current index) base := by
    intro index
    exact contMDiffAt_pi_space.mp hSecond index
  apply contMDiffAt_pi_space.mpr
  intro upper
  unfold localLeviCivitaChristoffelApply localLeviCivitaChristoffelMatrix
  simp only [Matrix.toBilin'_apply]
  apply ContMDiffAt.sum
  intro firstIndex _
  apply ContMDiffAt.sum
  intro secondIndex _
  have hChristoffel := ContDiff.comp_contMDiffAt
    (localLeviCivitaChristoffel_contDiff period hPeriod metric patch upper
      firstIndex secondIndex) hCoordinate
  exact ((hFirstComponent firstIndex).mul hChristoffel).mul
    (hSecondComponent secondIndex)

/-- The genuine Weingarten pairing in a holonomic chart.  Its connection term
is the pre-existing Levi--Civita Christoffel map, not the earlier fixed-frame
algebraic adapter. -/
def normalGraphHolonomicRawExtrinsicCurvatureCoordinates
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate ambient : HolonomicVector4)
    (first second : ThroatCoverCoordinates)
    (current : EffectiveThroat period hPeriod × Real) : Real :=
  let graphDerivative :=
    normalGraphHolonomicFamilyDerivativeCoordinates period hPeriod displacement
      base patch coordinate current
  let normal :=
    normalGraphHolonomicMetricUnitNormalCoordinates period hPeriod metric
      displacement base patch coordinate ambient current
  let normalDerivative :=
    normalGraphHolonomicMetricUnitNormalDerivativeCoordinates period hPeriod
      metric displacement base patch coordinate ambient current
  localMetricCoordinateForm period hPeriod metric patch
    (normalGraphHolonomicCoordinateGerm period hPeriod displacement base patch
      coordinate current)
    (normalDerivative first +
      localLeviCivitaChristoffelApply period hPeriod metric patch
        (normalGraphHolonomicCoordinateGerm period hPeriod displacement base
          patch coordinate current) (graphDerivative first) normal)
    (graphDerivative second)

/-- The raw Weingarten scalar computed from one chart equals the second-chart
metric contraction of the genuinely transported normal germ.  Hence no
coordinate-dependent connection residue remains. -/
theorem normalGraphHolonomicRawExtrinsicCurvatureCoordinates_chart_independent_transport
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement base.2)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate ambient : HolonomicVector4)
    (hFirst : firstPatch.coordinateMap firstCoordinate =
      normalGraph period hPeriod displacement base.2 base.1)
    (hSecond : secondPatch.coordinateMap secondCoordinate =
      normalGraph period hPeriod displacement base.2 base.1)
    (hSquare : normalGraphHolonomicMetricNormalSquareCoordinates period hPeriod
      metric displacement base firstPatch firstCoordinate ambient base ≠ 0)
    (first second : ThroatCoverCoordinates) :
    let samePoint := hFirst.trans hSecond.symm
    let transitionLinear :=
      holonomicCoordinateTransitionLinearEquivAt period hPeriod firstPatch
        secondPatch firstCoordinate secondCoordinate samePoint
    let secondTangent := fun tangent =>
      normalGraphHolonomicFamilyDerivativeCoordinates period hPeriod
        displacement base secondPatch secondCoordinate base tangent
    let secondNormal :=
      normalGraphHolonomicMetricUnitNormalCoordinates period hPeriod metric
        displacement base secondPatch secondCoordinate
          (transitionLinear ambient) base
    let transportedDerivative :=
      NormedSpace.fromTangentSpace
        (normalGraphHolonomicTransportedMetricUnitNormalCoordinates period
          hPeriod metric displacement base firstPatch secondPatch firstCoordinate
            secondCoordinate samePoint ambient base)
        (mfderiv throatCoverModelWithCorners
          (modelWithCornersSelf Real HolonomicVector4)
          (fun point =>
            normalGraphHolonomicTransportedMetricUnitNormalCoordinates period
              hPeriod metric displacement base firstPatch secondPatch
                firstCoordinate secondCoordinate samePoint ambient
                  (point, base.2))
          base.1
          ((trivializationAt ThroatCoverCoordinates
            (ThroatTangentFiber period hPeriod) base.1).symm base.1 first))
    normalGraphHolonomicRawExtrinsicCurvatureCoordinates period hPeriod metric
        displacement base firstPatch firstCoordinate ambient first second base =
      localMetricCoordinateForm period hPeriod metric secondPatch
        secondCoordinate
        (transportedDerivative +
          localLeviCivitaChristoffelApply period hPeriod metric secondPatch
            secondCoordinate (secondTangent first) secondNormal)
        (secondTangent second) := by
  dsimp only
  unfold normalGraphHolonomicRawExtrinsicCurvatureCoordinates
  dsimp only
  rw [normalGraphHolonomicCoordinateGerm_base period hPeriod displacement base
    firstPatch firstCoordinate hFirst]
  rw [localMetricCoordinateForm_transition period hPeriod metric firstPatch
    secondPatch firstCoordinate secondCoordinate _ _ (hFirst.trans hSecond.symm)]
  have hCovariant :=
    normalGraphHolonomicTransportedMetricUnitNormalCovariantDerivative_transition
      period hPeriod metric displacement base hNonNull firstPatch secondPatch
        firstCoordinate secondCoordinate ambient hFirst hSecond hSquare first
  dsimp only at hCovariant
  rw [← hCovariant]
  rw [normalGraphHolonomicFamilyDerivativeCoordinates_transition period hPeriod
    displacement base firstPatch secondPatch firstCoordinate secondCoordinate
      hFirst hSecond second]

theorem normalGraphHolonomicRawExtrinsicCurvatureCoordinates_contMDiffAt
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement base.2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate ambient : HolonomicVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraph period hPeriod displacement base.2 base.1)
    (hSquare : normalGraphHolonomicMetricNormalSquareCoordinates period hPeriod
      metric displacement base patch coordinate ambient base ≠ 0)
    (first second : ThroatCoverCoordinates) :
    ContMDiffAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      𝓘(Real, Real) ∞
      (normalGraphHolonomicRawExtrinsicCurvatureCoordinates period hPeriod metric
        displacement base patch coordinate ambient first second) base := by
  have hGraphDerivative :=
    normalGraphHolonomicFamilyDerivativeCoordinates_contMDiffAt period hPeriod
      displacement base patch coordinate hAt
  have hNormal :=
    normalGraphHolonomicMetricUnitNormalCoordinates_contMDiffAt period hPeriod
      metric displacement base hNonNull patch coordinate ambient hAt hSquare
  have hNormalDerivative :=
    normalGraphHolonomicMetricUnitNormalDerivativeCoordinates_contMDiffAt period
      hPeriod metric displacement base hNonNull patch coordinate ambient hAt
        hSquare
  have hGraphFirst := hGraphDerivative.clm_apply
    (contMDiffAt_const (c := first))
  have hGraphSecond := hGraphDerivative.clm_apply
    (contMDiffAt_const (c := second))
  have hNormalDerivativeFirst := hNormalDerivative.clm_apply
    (contMDiffAt_const (c := first))
  have hConnection :=
    normalGraphHolonomicLeviCivitaApply_contMDiffAt period hPeriod metric
      displacement base patch coordinate hAt _ _ hGraphFirst hNormal
  exact normalGraphHolonomicMetricEvaluation_contMDiffAt period hPeriod metric
    displacement base patch coordinate hAt _ _
      (hNormalDerivativeFirst.add hConnection) hGraphSecond

/-- Symmetric second fundamental form obtained from the genuine holonomic
Weingarten pairing. -/
def normalGraphHolonomicExtrinsicCurvatureCoordinates
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate ambient : HolonomicVector4)
    (first second : ThroatCoverCoordinates)
    (current : EffectiveThroat period hPeriod × Real) : Real :=
  (1 / 2 : Real) *
    (normalGraphHolonomicRawExtrinsicCurvatureCoordinates period hPeriod metric
        displacement base patch coordinate ambient first second current +
      normalGraphHolonomicRawExtrinsicCurvatureCoordinates period hPeriod metric
        displacement base patch coordinate ambient second first current)

theorem normalGraphHolonomicExtrinsicCurvatureCoordinates_symmetric
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate ambient : HolonomicVector4)
    (first second : ThroatCoverCoordinates)
    (current : EffectiveThroat period hPeriod × Real) :
    normalGraphHolonomicExtrinsicCurvatureCoordinates period hPeriod metric
        displacement base patch coordinate ambient first second current =
      normalGraphHolonomicExtrinsicCurvatureCoordinates period hPeriod metric
        displacement base patch coordinate ambient second first current := by
  unfold normalGraphHolonomicExtrinsicCurvatureCoordinates
  ring

theorem normalGraphHolonomicExtrinsicCurvatureCoordinates_contMDiffAt
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement base.2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate ambient : HolonomicVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraph period hPeriod displacement base.2 base.1)
    (hSquare : normalGraphHolonomicMetricNormalSquareCoordinates period hPeriod
      metric displacement base patch coordinate ambient base ≠ 0)
    (first second : ThroatCoverCoordinates) :
    ContMDiffAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      𝓘(Real, Real) ∞
      (normalGraphHolonomicExtrinsicCurvatureCoordinates period hPeriod metric
        displacement base patch coordinate ambient first second) base := by
  exact contMDiffAt_const.mul
    ((normalGraphHolonomicRawExtrinsicCurvatureCoordinates_contMDiffAt period
      hPeriod metric displacement base hNonNull patch coordinate ambient hAt
        hSquare first second).add
      (normalGraphHolonomicRawExtrinsicCurvatureCoordinates_contMDiffAt period
        hPeriod metric displacement base hNonNull patch coordinate ambient hAt
          hSquare second first))

/-- Matrix adapter for the holonomic second fundamental form. -/
def normalGraphHolonomicExtrinsicCurvatureMatrix
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate ambient : HolonomicVector4)
    (current : EffectiveThroat period hPeriod × Real) : Matrix3 :=
  fun first second =>
    normalGraphHolonomicExtrinsicCurvatureCoordinates period hPeriod metric
      displacement base patch coordinate ambient (throatCoordinateBasis first)
        (throatCoordinateBasis second) current

def normalGraphHolonomicRawExtrinsicCurvatureMatrix
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate ambient : HolonomicVector4)
    (current : EffectiveThroat period hPeriod × Real) : Matrix3 :=
  fun first second =>
    normalGraphHolonomicRawExtrinsicCurvatureCoordinates period hPeriod metric
      displacement base patch coordinate ambient (throatCoordinateBasis first)
        (throatCoordinateBasis second) current

theorem normalGraphHolonomicExtrinsicCurvatureMatrix_eq_symmetrized_raw
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate ambient : HolonomicVector4)
    (current : EffectiveThroat period hPeriod × Real) :
    normalGraphHolonomicExtrinsicCurvatureMatrix period hPeriod metric
        displacement base patch coordinate ambient current =
      (1 / 2 : Real) •
        (normalGraphHolonomicRawExtrinsicCurvatureMatrix period hPeriod metric
            displacement base patch coordinate ambient current +
          (normalGraphHolonomicRawExtrinsicCurvatureMatrix period hPeriod metric
            displacement base patch coordinate ambient current).transpose) := by
  ext first second
  simp [normalGraphHolonomicExtrinsicCurvatureMatrix,
    normalGraphHolonomicRawExtrinsicCurvatureMatrix,
    normalGraphHolonomicExtrinsicCurvatureCoordinates]

theorem normalGraphHolonomicExtrinsicCurvatureMatrix_symmetric
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate ambient : HolonomicVector4)
    (current : EffectiveThroat period hPeriod × Real) :
    (normalGraphHolonomicExtrinsicCurvatureMatrix period hPeriod metric
      displacement base patch coordinate ambient current).transpose =
      normalGraphHolonomicExtrinsicCurvatureMatrix period hPeriod metric
        displacement base patch coordinate ambient current := by
  ext first second
  exact normalGraphHolonomicExtrinsicCurvatureCoordinates_symmetric period
    hPeriod metric displacement base patch coordinate ambient _ _ current

/-- Joint inverse-metric matrix; this is only a matrix view of the intrinsic
inverse already used by the normal projector. -/
def normalGraphInducedInverseMatrixFamily
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base current : EffectiveThroat period hPeriod × Real) : Matrix3 :=
  LinearMap.toMatrix throatContinuousDualBasis throatCoordinateBasis
    (normalGraphInducedMetricInverseCoordinates period hPeriod metric
      displacement base current).toLinearMap

@[simp]
theorem normalGraphInducedInverseMatrixFamily_base
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real) :
    normalGraphInducedInverseMatrixFamily period hPeriod metric displacement
        base base =
      normalGraphInducedInverseMatrix period hPeriod metric displacement base :=
  rfl

/-- Symmetrization leaves the GHY trace unchanged for the holonomic (K). -/
theorem normalGraphHolonomicExtrinsicCurvature_trace_eq_raw
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement base.2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate ambient : HolonomicVector4) :
    Matrix.trace
        (normalGraphInducedInverseMatrix period hPeriod metric displacement base *
          normalGraphHolonomicExtrinsicCurvatureMatrix period hPeriod metric
            displacement base patch coordinate ambient base) =
      Matrix.trace
        (normalGraphInducedInverseMatrix period hPeriod metric displacement base *
          normalGraphHolonomicRawExtrinsicCurvatureMatrix period hPeriod metric
            displacement base patch coordinate ambient base) := by
  let inverse :=
    normalGraphInducedInverseMatrix period hPeriod metric displacement base
  let raw := normalGraphHolonomicRawExtrinsicCurvatureMatrix period hPeriod
    metric displacement base patch coordinate ambient base
  have hInverse : inverse.transpose = inverse :=
    normalGraphInducedInverseMatrix_symmetric period hPeriod metric displacement
      base hNonNull
  have hTransposeTrace : Matrix.trace (inverse * raw.transpose) =
      Matrix.trace (inverse * raw) := by
    calc
      Matrix.trace (inverse * raw.transpose) =
          Matrix.trace ((inverse * raw.transpose).transpose) := by
            rw [Matrix.trace_transpose]
      _ = Matrix.trace (raw * inverse) := by
        rw [Matrix.transpose_mul, Matrix.transpose_transpose, hInverse]
      _ = Matrix.trace (inverse * raw) := Matrix.trace_mul_comm raw inverse
  rw [normalGraphHolonomicExtrinsicCurvatureMatrix_eq_symmetrized_raw]
  change Matrix.trace (inverse * ((1 / 2 : Real) • (raw + raw.transpose))) = _
  rw [Matrix.mul_smul, Matrix.mul_add, Matrix.trace_smul, Matrix.trace_add,
    hTransposeTrace]
  ring

@[simp]
theorem normalGraphHolonomicMetricUnitNormalCoordinates_neg
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate ambient : HolonomicVector4)
    (current : EffectiveThroat period hPeriod × Real) :
    normalGraphHolonomicMetricUnitNormalCoordinates period hPeriod metric
        displacement base patch coordinate (-ambient) current =
      -normalGraphHolonomicMetricUnitNormalCoordinates period hPeriod metric
        displacement base patch coordinate ambient current := by
  simp [normalGraphHolonomicMetricUnitNormalCoordinates]

@[simp]
theorem normalGraphHolonomicMetricUnitNormalDerivativeCoordinates_neg
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate ambient : HolonomicVector4)
    (current : EffectiveThroat period hPeriod × Real) :
    normalGraphHolonomicMetricUnitNormalDerivativeCoordinates period hPeriod
        metric displacement base patch coordinate (-ambient) current =
      -normalGraphHolonomicMetricUnitNormalDerivativeCoordinates period hPeriod
        metric displacement base patch coordinate ambient current := by
  simp [normalGraphHolonomicMetricUnitNormalDerivativeCoordinates,
    inTangentCoordinates, ContinuousLinearMap.inCoordinates]
  rw [show (fun throatPoint =>
      normalGraphHolonomicMetricUnitNormalCoordinates period hPeriod metric
        displacement base patch coordinate (-ambient) (throatPoint, current.2)) =
      -(fun throatPoint =>
        normalGraphHolonomicMetricUnitNormalCoordinates period hPeriod metric
          displacement base patch coordinate ambient (throatPoint, current.2)) by
    funext throatPoint
    exact normalGraphHolonomicMetricUnitNormalCoordinates_neg period hPeriod
      metric displacement base patch coordinate ambient (throatPoint, current.2)]
  rw [mfderiv_neg]
  rfl

@[simp]
theorem normalGraphHolonomicRawExtrinsicCurvatureCoordinates_neg
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate ambient : HolonomicVector4)
    (first second : ThroatCoverCoordinates)
    (current : EffectiveThroat period hPeriod × Real) :
    normalGraphHolonomicRawExtrinsicCurvatureCoordinates period hPeriod metric
        displacement base patch coordinate (-ambient) first second current =
      -normalGraphHolonomicRawExtrinsicCurvatureCoordinates period hPeriod metric
        displacement base patch coordinate ambient first second current := by
  have hConnectionNeg :
      localLeviCivitaChristoffelApply period hPeriod metric patch
          (normalGraphHolonomicCoordinateGerm period hPeriod displacement base
            patch coordinate current)
          (normalGraphHolonomicFamilyDerivativeCoordinates period hPeriod
            displacement base patch coordinate current first)
          (-normalGraphHolonomicMetricUnitNormalCoordinates period hPeriod metric
            displacement base patch coordinate ambient current) =
        -localLeviCivitaChristoffelApply period hPeriod metric patch
          (normalGraphHolonomicCoordinateGerm period hPeriod displacement base
            patch coordinate current)
          (normalGraphHolonomicFamilyDerivativeCoordinates period hPeriod
            displacement base patch coordinate current first)
          (normalGraphHolonomicMetricUnitNormalCoordinates period hPeriod metric
            displacement base patch coordinate ambient current) := by
    change (localLeviCivitaChristoffelBilinearMap period hPeriod metric patch
      (normalGraphHolonomicCoordinateGerm period hPeriod displacement base patch
        coordinate current)
      (normalGraphHolonomicFamilyDerivativeCoordinates period hPeriod
        displacement base patch coordinate current first))
      (-normalGraphHolonomicMetricUnitNormalCoordinates period hPeriod metric
        displacement base patch coordinate ambient current) = _
    rw [map_neg]
    rfl
  simp only [normalGraphHolonomicRawExtrinsicCurvatureCoordinates]
  rw [normalGraphHolonomicMetricUnitNormalDerivativeCoordinates_neg,
    normalGraphHolonomicMetricUnitNormalCoordinates_neg, hConnectionNeg]
  simp only [neg_apply, LinearMap.add_apply, LinearMap.neg_apply, map_add,
    map_neg]
  ring

@[simp]
theorem normalGraphHolonomicExtrinsicCurvatureCoordinates_neg
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate ambient : HolonomicVector4)
    (first second : ThroatCoverCoordinates)
    (current : EffectiveThroat period hPeriod × Real) :
    normalGraphHolonomicExtrinsicCurvatureCoordinates period hPeriod metric
        displacement base patch coordinate (-ambient) first second current =
      -normalGraphHolonomicExtrinsicCurvatureCoordinates period hPeriod metric
        displacement base patch coordinate ambient first second current := by
  simp [normalGraphHolonomicExtrinsicCurvatureCoordinates]
  ring

@[simp]
theorem normalGraphHolonomicExtrinsicCurvatureMatrix_neg
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate ambient : HolonomicVector4)
    (current : EffectiveThroat period hPeriod × Real) :
    normalGraphHolonomicExtrinsicCurvatureMatrix period hPeriod metric
        displacement base patch coordinate (-ambient) current =
      -normalGraphHolonomicExtrinsicCurvatureMatrix period hPeriod metric
        displacement base patch coordinate ambient current := by
  ext first second
  simp [normalGraphHolonomicExtrinsicCurvatureMatrix]

/-- Matrix of the unsymmetrized Weingarten pairing. -/
def normalGraphRawLocalExtrinsicCurvatureMatrix
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (ambientCoordinate : CoverCoordinates) : Matrix3 :=
  fun first second =>
    normalGraphRawLocalExtrinsicCurvatureCoordinates period hPeriod metric
      displacement base ambientCoordinate (throatCoordinateBasis first)
        (throatCoordinateBasis second)

/-- Matrix adapter for the actual local second fundamental form. -/
def normalGraphLocalExtrinsicCurvatureMatrix
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (ambientCoordinate : CoverCoordinates) : Matrix3 :=
  fun first second =>
    normalGraphLocalExtrinsicCurvatureCoordinates period hPeriod metric
      displacement base ambientCoordinate (throatCoordinateBasis first)
        (throatCoordinateBasis second)

theorem normalGraphLocalExtrinsicCurvatureMatrix_eq_symmetrized_raw
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (ambientCoordinate : CoverCoordinates) :
    normalGraphLocalExtrinsicCurvatureMatrix period hPeriod metric displacement
        base ambientCoordinate =
      (1 / 2 : Real) •
        (normalGraphRawLocalExtrinsicCurvatureMatrix period hPeriod metric
            displacement base ambientCoordinate +
          (normalGraphRawLocalExtrinsicCurvatureMatrix period hPeriod metric
            displacement base ambientCoordinate).transpose) := by
  ext first second
  simp [normalGraphLocalExtrinsicCurvatureMatrix,
    normalGraphRawLocalExtrinsicCurvatureMatrix,
    normalGraphLocalExtrinsicCurvatureCoordinates]

theorem normalGraphLocalExtrinsicCurvatureMatrix_symmetric
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (ambientCoordinate : CoverCoordinates) :
    (normalGraphLocalExtrinsicCurvatureMatrix period hPeriod metric displacement
      base ambientCoordinate).transpose =
      normalGraphLocalExtrinsicCurvatureMatrix period hPeriod metric displacement
        base ambientCoordinate := by
  ext first second
  exact normalGraphLocalExtrinsicCurvatureCoordinates_symmetric period hPeriod
    metric displacement base ambientCoordinate _ _

@[simp]
theorem normalGraphLocalExtrinsicCurvatureMatrix_neg
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (ambientCoordinate : CoverCoordinates) :
    normalGraphLocalExtrinsicCurvatureMatrix period hPeriod metric displacement
        base (-ambientCoordinate) =
      -normalGraphLocalExtrinsicCurvatureMatrix period hPeriod metric displacement
        base ambientCoordinate := by
  ext first second
  simp [normalGraphLocalExtrinsicCurvatureMatrix]

/-- Symmetrizing the Weingarten pairing changes no GHY trace. Thus the ledger
receives its required symmetric matrix without changing the physical scalar. -/
theorem normalGraphLocalExtrinsicCurvature_trace_eq_raw
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement base.2)
    (ambientCoordinate : CoverCoordinates) :
    Matrix.trace
        (normalGraphInducedInverseMatrix period hPeriod metric displacement base *
          normalGraphLocalExtrinsicCurvatureMatrix period hPeriod metric
            displacement base ambientCoordinate) =
      Matrix.trace
        (normalGraphInducedInverseMatrix period hPeriod metric displacement base *
          normalGraphRawLocalExtrinsicCurvatureMatrix period hPeriod metric
            displacement base ambientCoordinate) := by
  let inverse :=
    normalGraphInducedInverseMatrix period hPeriod metric displacement base
  let raw := normalGraphRawLocalExtrinsicCurvatureMatrix period hPeriod metric
    displacement base ambientCoordinate
  have hInverse : inverse.transpose = inverse :=
    normalGraphInducedInverseMatrix_symmetric period hPeriod metric displacement
      base hNonNull
  have hTransposeTrace : Matrix.trace (inverse * raw.transpose) =
      Matrix.trace (inverse * raw) := by
    calc
      Matrix.trace (inverse * raw.transpose) =
          Matrix.trace ((inverse * raw.transpose).transpose) := by
            rw [Matrix.trace_transpose]
      _ = Matrix.trace (raw * inverse) := by
        rw [Matrix.transpose_mul, Matrix.transpose_transpose, hInverse]
      _ = Matrix.trace (inverse * raw) := Matrix.trace_mul_comm raw inverse
  rw [normalGraphLocalExtrinsicCurvatureMatrix_eq_symmetrized_raw]
  change Matrix.trace (inverse * ((1 / 2 : Real) • (raw + raw.transpose))) = _
  rw [Matrix.mul_smul, Matrix.mul_add, Matrix.trace_smul, Matrix.trace_add,
    hTransposeTrace]
  ring

/-- The mobile graph supplies exactly the point-data type consumed by the
unchanged non-null GHY density ledger. The normal, metric and curvature are
all derived above; only the already existing boundary-orientation sign is
passed through. -/
def normalGraphLocalNonNullBoundaryPointData
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement base.2)
    (ambientCoordinate : CoverCoordinates)
    (_hSquare : normalGraphLocalMetricNormalSquareCoordinates period hPeriod
      metric displacement base ambientCoordinate base ≠ 0)
    (orientationSign : Real) (hOrientation : IsOrientationSign orientationSign) :
    NonNullBoundaryPointData where
  inducedMetric :=
    normalGraphInducedMetricMatrix period hPeriod metric displacement base
  inducedInverse :=
    normalGraphInducedInverseMatrix period hPeriod metric displacement base
  extrinsicCurvature :=
    normalGraphLocalExtrinsicCurvatureMatrix period hPeriod metric displacement
      base ambientCoordinate
  orientationSign := orientationSign
  inverseWitness :=
    { inverse_mul := normalGraphInducedInverseMatrix_mul_metric period hPeriod
        metric displacement base hNonNull
      mul_inverse := normalGraphInducedMetricMatrix_mul_inverse period hPeriod
        metric displacement base hNonNull }
  inducedMetricSymmetric :=
    normalGraphInducedMetricMatrix_symmetric period hPeriod metric displacement
      base
  extrinsicCurvatureSymmetric :=
    normalGraphLocalExtrinsicCurvatureMatrix_symmetric period hPeriod metric
      displacement base ambientCoordinate
  orientationSignAdmissible := hOrientation

theorem isOrientationSign_neg
    (orientationSign : Real) (hOrientation : IsOrientationSign orientationSign) :
    IsOrientationSign (-orientationSign) := by
  rcases hOrientation with hPositive | hNegative
  · right
    rw [hPositive]
  · left
    rw [hNegative]
    norm_num

/-- The unchanged GHY ledger evaluated on the geometry derived from the mobile
normal graph. -/
def normalGraphLocalGHYDensity
    (einsteinScale : Real)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement base.2)
    (ambientCoordinate : CoverCoordinates)
    (hSquare : normalGraphLocalMetricNormalSquareCoordinates period hPeriod
      metric displacement base ambientCoordinate base ≠ 0)
    (orientationSign : Real) (hOrientation : IsOrientationSign orientationSign) :
    Real :=
  nonNullGHYDensity einsteinScale
    (normalGraphLocalNonNullBoundaryPointData period hPeriod metric displacement
      base hNonNull ambientCoordinate hSquare orientationSign hOrientation)

/-- Reversing a local unit normal and the corresponding outward-orientation
sign leaves the physical GHY density unchanged. This is the descent law needed
on the existing orientation-double cut boundary. -/
theorem normalGraphLocalGHYDensity_neg_normal_orientation
    (einsteinScale : Real)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement base.2)
    (ambientCoordinate : CoverCoordinates)
    (hSquare : normalGraphLocalMetricNormalSquareCoordinates period hPeriod
      metric displacement base ambientCoordinate base ≠ 0)
    (orientationSign : Real) (hOrientation : IsOrientationSign orientationSign)
    (hSquareNeg : normalGraphLocalMetricNormalSquareCoordinates period hPeriod
      metric displacement base (-ambientCoordinate) base ≠ 0)
    (hOrientationNeg : IsOrientationSign (-orientationSign)) :
    normalGraphLocalGHYDensity period hPeriod einsteinScale metric displacement
        base hNonNull (-ambientCoordinate) hSquareNeg (-orientationSign)
          hOrientationNeg =
      normalGraphLocalGHYDensity period hPeriod einsteinScale metric displacement
        base hNonNull ambientCoordinate hSquare orientationSign hOrientation := by
  unfold normalGraphLocalGHYDensity normalGraphLocalNonNullBoundaryPointData
    nonNullGHYDensity meanCurvatureTrace
  change einsteinScale * (-orientationSign) *
        Real.sqrt
          |Matrix.det (normalGraphInducedMetricMatrix period hPeriod metric
            displacement base)| *
        Matrix.trace
          (normalGraphInducedInverseMatrix period hPeriod metric displacement
              base *
            normalGraphLocalExtrinsicCurvatureMatrix period hPeriod metric
              displacement base (-ambientCoordinate)) =
      einsteinScale * orientationSign *
        Real.sqrt
          |Matrix.det (normalGraphInducedMetricMatrix period hPeriod metric
            displacement base)| *
        Matrix.trace
          (normalGraphInducedInverseMatrix period hPeriod metric displacement
              base *
            normalGraphLocalExtrinsicCurvatureMatrix period hPeriod metric
              displacement base ambientCoordinate)
  rw [normalGraphLocalExtrinsicCurvatureMatrix_neg]
  simp

/-! ### Holonomic Levi--Civita adapter to the unchanged GHY ledger -/

/-- Point data for the mobile graph using the genuine holonomic
Levi--Civita second fundamental form constructed above. -/
def normalGraphHolonomicNonNullBoundaryPointData
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement base.2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate ambient : HolonomicVector4)
    (_hAt : patch.coordinateMap coordinate =
      normalGraph period hPeriod displacement base.2 base.1)
    (_hSquare : normalGraphHolonomicMetricNormalSquareCoordinates period hPeriod
      metric displacement base patch coordinate ambient base ≠ 0)
    (orientationSign : Real) (hOrientation : IsOrientationSign orientationSign) :
    NonNullBoundaryPointData where
  inducedMetric :=
    normalGraphInducedMetricMatrix period hPeriod metric displacement base
  inducedInverse :=
    normalGraphInducedInverseMatrix period hPeriod metric displacement base
  extrinsicCurvature :=
    normalGraphHolonomicExtrinsicCurvatureMatrix period hPeriod metric
      displacement base patch coordinate ambient base
  orientationSign := orientationSign
  inverseWitness :=
    { inverse_mul := normalGraphInducedInverseMatrix_mul_metric period hPeriod
        metric displacement base hNonNull
      mul_inverse := normalGraphInducedMetricMatrix_mul_inverse period hPeriod
        metric displacement base hNonNull }
  inducedMetricSymmetric :=
    normalGraphInducedMetricMatrix_symmetric period hPeriod metric displacement
      base
  extrinsicCurvatureSymmetric :=
    normalGraphHolonomicExtrinsicCurvatureMatrix_symmetric period hPeriod metric
      displacement base patch coordinate ambient base
  orientationSignAdmissible := hOrientation

/-- The pre-existing GHY density ledger evaluated on the genuine holonomic
Levi--Civita geometry of the moving graph. -/
def normalGraphHolonomicGHYDensity
    (einsteinScale : Real)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement base.2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate ambient : HolonomicVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraph period hPeriod displacement base.2 base.1)
    (hSquare : normalGraphHolonomicMetricNormalSquareCoordinates period hPeriod
      metric displacement base patch coordinate ambient base ≠ 0)
    (orientationSign : Real) (hOrientation : IsOrientationSign orientationSign) :
    Real :=
  nonNullGHYDensity einsteinScale
    (normalGraphHolonomicNonNullBoundaryPointData period hPeriod metric
      displacement base hNonNull patch coordinate ambient hAt hSquare
        orientationSign hOrientation)

/-- The normal/orientation simultaneous reversal law now holds for the genuine
holonomic Levi--Civita (K). -/
theorem normalGraphHolonomicGHYDensity_neg_normal_orientation
    (einsteinScale : Real)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement base.2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate ambient : HolonomicVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraph period hPeriod displacement base.2 base.1)
    (hSquare : normalGraphHolonomicMetricNormalSquareCoordinates period hPeriod
      metric displacement base patch coordinate ambient base ≠ 0)
    (orientationSign : Real) (hOrientation : IsOrientationSign orientationSign) :
    normalGraphHolonomicGHYDensity period hPeriod einsteinScale metric
        displacement base hNonNull patch coordinate (-ambient) hAt
          (by simpa using hSquare) (-orientationSign)
          (isOrientationSign_neg orientationSign hOrientation) =
      normalGraphHolonomicGHYDensity period hPeriod einsteinScale metric
        displacement base hNonNull patch coordinate ambient hAt hSquare
          orientationSign hOrientation := by
  unfold normalGraphHolonomicGHYDensity
    normalGraphHolonomicNonNullBoundaryPointData nonNullGHYDensity
    meanCurvatureTrace
  change einsteinScale * (-orientationSign) *
        Real.sqrt
          |Matrix.det (normalGraphInducedMetricMatrix period hPeriod metric
            displacement base)| *
        Matrix.trace
          (normalGraphInducedInverseMatrix period hPeriod metric displacement
              base *
            normalGraphHolonomicExtrinsicCurvatureMatrix period hPeriod metric
              displacement base patch coordinate (-ambient) base) =
      einsteinScale * orientationSign *
        Real.sqrt
          |Matrix.det (normalGraphInducedMetricMatrix period hPeriod metric
            displacement base)| *
        Matrix.trace
          (normalGraphInducedInverseMatrix period hPeriod metric displacement
              base *
            normalGraphHolonomicExtrinsicCurvatureMatrix period hPeriod metric
              displacement base patch coordinate ambient base)
  rw [normalGraphHolonomicExtrinsicCurvatureMatrix_neg]
  simp

/-! ## Frame-free induced volume density -/

/-- Relative endomorphism of the induced metric with respect to the existing
intrinsic throat metric.  This is frame-free; determinants computed below are
therefore independent of any local trivialization. -/
def normalGraphRelativeEndomorphism
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (point : EffectiveThroat period hPeriod) :
    ThroatTangentFiber period hPeriod point →L[Real]
      ThroatTangentFiber period hPeriod point :=
  (intrinsicThroatInverseMusical period hPeriod point).toContinuousLinearMap.comp
    (normalGraphInducedMetricValue period hPeriod metric displacement
      parameter point)

@[simp]
theorem normalGraphRelativeEndomorphism_apply
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (point : EffectiveThroat period hPeriod)
    (vector : ThroatTangentFiber period hPeriod point) :
    normalGraphRelativeEndomorphism period hPeriod metric displacement
        parameter point vector =
      intrinsicThroatInverseMusical period hPeriod point
        (normalGraphInducedMetricValue period hPeriod metric displacement
          parameter point vector) :=
  rfl

/-- On the non-null domain the relative endomorphism is the underlying map of
a genuine continuous linear equivalence. -/
def normalGraphRelativeMetricEquiv
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (point : EffectiveThroat period hPeriod) :
    ThroatTangentFiber period hPeriod point ≃L[Real]
      ThroatTangentFiber period hPeriod point :=
  (normalGraphInducedMetricEquiv period hPeriod metric displacement parameter
      hNonNull point).trans
    (intrinsicThroatInverseMusical period hPeriod point)

theorem normalGraphRelativeMetricEquiv_toContinuousLinearMap
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (point : EffectiveThroat period hPeriod) :
    (normalGraphRelativeMetricEquiv period hPeriod metric displacement parameter
      hNonNull point : ThroatTangentFiber period hPeriod point →L[Real]
        ThroatTangentFiber period hPeriod point) =
      normalGraphRelativeEndomorphism period hPeriod metric displacement
        parameter point := by
  apply ContinuousLinearMap.ext
  intro vector
  simp [normalGraphRelativeMetricEquiv,
    normalGraphRelativeEndomorphism]

/-- Intrinsic determinant of the induced metric relative to the existing
throat metric. -/
def normalGraphRelativeDeterminant
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (point : EffectiveThroat period hPeriod) : Real :=
  LinearMap.det
    (normalGraphRelativeEndomorphism period hPeriod metric displacement
      parameter point).toLinearMap

theorem normalGraphRelativeDeterminant_ne_zero
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (point : EffectiveThroat period hPeriod) :
    normalGraphRelativeDeterminant period hPeriod metric displacement
      parameter point ≠ 0 := by
  have hDet := (LinearEquiv.isUnit_det'
    (normalGraphRelativeMetricEquiv period hPeriod metric displacement
      parameter hNonNull point).toLinearEquiv).ne_zero
  rw [normalGraphRelativeDeterminant,
    ← normalGraphRelativeMetricEquiv_toContinuousLinearMap
      period hPeriod metric displacement parameter hNonNull point]
  exact hDet

/-- Positive frame-free density `sqrt |det(g_ref⁻¹ g_parameter)|`. -/
def normalGraphRelativeVolumeDensity
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (point : EffectiveThroat period hPeriod) : Real :=
  Real.sqrt |normalGraphRelativeDeterminant period hPeriod metric displacement
    parameter point|

theorem normalGraphRelativeVolumeDensity_pos
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (point : EffectiveThroat period hPeriod) :
    0 < normalGraphRelativeVolumeDensity period hPeriod metric displacement
      parameter point := by
  exact Real.sqrt_pos.2 (abs_pos.mpr
    (normalGraphRelativeDeterminant_ne_zero period hPeriod metric displacement
      parameter hNonNull point))

private def normalGraphReferenceMetricCoordinates
    (base current : EffectiveThroat period hPeriod × Real) :
    ThroatCovariantTwoTensorModel :=
  ContinuousLinearMap.inCoordinates ThroatCoverCoordinates
    (ThroatTangentFiber period hPeriod)
    (ThroatCoverCoordinates →L[Real] Real)
    (ThroatCotangentFiber period hPeriod)
    base.1 current.1 base.1 current.1
    ((intrinsicSmoothNondegenerateThroatMetric period hPeriod).1.tensor
      current.1)

private theorem normalGraphReferenceMetricCoordinates_isInvertible
    (base : EffectiveThroat period hPeriod × Real) :
    (normalGraphReferenceMetricCoordinates period hPeriod base base).IsInvertible := by
  have hTangent : base.1 ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) base.1).baseSet :=
    mem_baseSet_trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) base.1
  have hCotangent : base.1 ∈
      (trivializationAt (ThroatCoverCoordinates →L[Real] Real)
        (ThroatCotangentFiber period hPeriod) base.1).baseSet :=
    mem_baseSet_trivializationAt (ThroatCoverCoordinates →L[Real] Real)
      (ThroatCotangentFiber period hPeriod) base.1
  have hFiber :
      (intrinsicSmoothNondegenerateThroatMetric period hPeriod).1.tensor base.1 =
        (intrinsicThroatMusical period hPeriod base.1 :
          ThroatTangentFiber period hPeriod base.1 →L[Real]
            ThroatCotangentFiber period hPeriod base.1) := by
    apply ContinuousLinearMap.ext
    intro vector
    exact (intrinsicThroatMusical_apply period hPeriod base.1 vector).symm
  unfold normalGraphReferenceMetricCoordinates
  rw [ContinuousLinearMap.inCoordinates_eq hTangent hCotangent, hFiber]
  exact isInvertible_equiv.comp
    (isInvertible_equiv.comp isInvertible_equiv)

private def normalGraphRelativeEndomorphismCoordinates
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base current : EffectiveThroat period hPeriod × Real) :
    ThroatCoverCoordinates →L[Real] ThroatCoverCoordinates :=
  (normalGraphReferenceMetricCoordinates period hPeriod base current).inverse.comp
    (normalGraphFamilyTraceTensorCoordinates period hPeriod metric displacement
      base current)

private theorem normalGraphRelativeEndomorphismCoordinates_eq_inCoordinates
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base current : EffectiveThroat period hPeriod × Real)
    (hTangent : current.1 ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) base.1).baseSet)
    (hCotangent : current.1 ∈
      (trivializationAt (ThroatCoverCoordinates →L[Real] Real)
        (ThroatCotangentFiber period hPeriod) base.1).baseSet) :
    normalGraphRelativeEndomorphismCoordinates period hPeriod metric
        displacement base current =
      ContinuousLinearMap.inCoordinates ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod)
        base.1 current.1 base.1 current.1
        (normalGraphRelativeEndomorphism period hPeriod metric displacement
          current.2 current.1) := by
  have hFiber :
      (intrinsicSmoothNondegenerateThroatMetric period hPeriod).1.tensor current.1 =
        (intrinsicThroatMusical period hPeriod current.1 :
          ThroatTangentFiber period hPeriod current.1 →L[Real]
            ThroatCotangentFiber period hPeriod current.1) := by
    apply ContinuousLinearMap.ext
    intro vector
    exact (intrinsicThroatMusical_apply period hPeriod current.1 vector).symm
  unfold normalGraphRelativeEndomorphismCoordinates
    normalGraphReferenceMetricCoordinates
    normalGraphFamilyTraceTensorCoordinates
  rw [ContinuousLinearMap.inCoordinates_eq hTangent hCotangent, hFiber,
    ContinuousLinearMap.inCoordinates_eq hTangent hCotangent,
    ContinuousLinearMap.inCoordinates_eq hTangent hTangent]
  simp only [ContinuousLinearMap.inverse_equiv_comp,
    ContinuousLinearMap.inverse_comp_equiv,
    ContinuousLinearEquiv.symm_symm]
  apply ContinuousLinearMap.ext
  intro vector
  simp only [normalGraphRelativeEndomorphism,
    intrinsicThroatInverseMusical, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe,
    ContinuousLinearMap.inverse_equiv,
    ContinuousLinearEquiv.symm_apply_apply]

private theorem normalGraphRelativeEndomorphismCoordinates_continuousAt
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real) :
    ContinuousAt
      (normalGraphRelativeEndomorphismCoordinates period hPeriod metric
        displacement base) base := by
  have hReferenceSection :=
    ((intrinsicSmoothNondegenerateThroatMetric period hPeriod).1.tensor.contMDiff.comp
      (contMDiff_fst : ContMDiff
        (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
        throatCoverModelWithCorners ∞
        (Prod.fst : EffectiveThroat period hPeriod × Real →
          EffectiveThroat period hPeriod))) base
  rw [contMDiffAt_hom_bundle] at hReferenceSection
  have hReference : ContinuousAt
      (normalGraphReferenceMetricCoordinates period hPeriod base) base :=
    hReferenceSection.2.continuousAt
  have hInverse : ContinuousAt
      (fun current =>
        (normalGraphReferenceMetricCoordinates period hPeriod base current).inverse)
      base :=
    (normalGraphReferenceMetricCoordinates_isInvertible period hPeriod base
      |>.contDiffAt_map_inverse (n := ∞)).continuousAt.comp hReference
  have hInducedSection :=
    normalGraphInducedMetricValue_joint_contMDiff period hPeriod metric
      displacement base
  rw [contMDiffAt_hom_bundle] at hInducedSection
  exact hInverse.clm_comp hInducedSection.2.continuousAt

private theorem normalGraphRelativeDeterminant_eq_coordinates
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base current : EffectiveThroat period hPeriod × Real)
    (hTangent : current.1 ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) base.1).baseSet)
    (hCotangent : current.1 ∈
      (trivializationAt (ThroatCoverCoordinates →L[Real] Real)
        (ThroatCotangentFiber period hPeriod) base.1).baseSet) :
    normalGraphRelativeDeterminant period hPeriod metric displacement
        current.2 current.1 =
      LinearMap.det
        (normalGraphRelativeEndomorphismCoordinates period hPeriod metric
          displacement base current).toLinearMap := by
  rw [normalGraphRelativeEndomorphismCoordinates_eq_inCoordinates
    period hPeriod metric displacement base current hTangent hCotangent]
  rw [ContinuousLinearMap.inCoordinates_eq hTangent hTangent]
  let equivalence :=
    (trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) base.1).continuousLinearEquivAt
        Real current.1 hTangent
  unfold normalGraphRelativeDeterminant
  change LinearMap.det
      (normalGraphRelativeEndomorphism period hPeriod metric displacement
        current.2 current.1).toLinearMap =
    LinearMap.det
      (equivalence.toLinearMap.comp
        ((normalGraphRelativeEndomorphism period hPeriod metric displacement
          current.2 current.1).toLinearMap.comp
            equivalence.symm.toLinearMap))
  simpa [LinearMap.comp_assoc] using
    (LinearMap.det_conj
      (normalGraphRelativeEndomorphism period hPeriod metric displacement
        current.2 current.1).toLinearMap equivalence.toLinearEquiv).symm

/-- The frame-free relative determinant varies continuously jointly in the
throat point and the normal-graph parameter. -/
theorem normalGraphRelativeDeterminant_joint_continuous
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod) :
    Continuous
      (fun current : EffectiveThroat period hPeriod × Real =>
        normalGraphRelativeDeterminant period hPeriod metric displacement
          current.2 current.1) := by
  rw [continuous_iff_continuousAt]
  intro base
  have hCoordinates :=
    normalGraphRelativeEndomorphismCoordinates_continuousAt
      period hPeriod metric displacement base
  have hCoordinateDeterminant : ContinuousAt
      (fun current => LinearMap.det
        (normalGraphRelativeEndomorphismCoordinates period hPeriod metric
          displacement base current).toLinearMap) base :=
    ContinuousLinearMap.continuous_det.continuousAt.comp hCoordinates
  have hTangent : ∀ᶠ current in nhds base,
      current.1 ∈
        (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) base.1).baseSet :=
    continuous_fst.continuousAt
      ((trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) base.1).open_baseSet.mem_nhds
          (mem_baseSet_trivializationAt ThroatCoverCoordinates
            (ThroatTangentFiber period hPeriod) base.1))
  have hCotangent : ∀ᶠ current in nhds base,
      current.1 ∈
        (trivializationAt (ThroatCoverCoordinates →L[Real] Real)
          (ThroatCotangentFiber period hPeriod) base.1).baseSet :=
    continuous_fst.continuousAt
      ((trivializationAt (ThroatCoverCoordinates →L[Real] Real)
        (ThroatCotangentFiber period hPeriod) base.1).open_baseSet.mem_nhds
          (mem_baseSet_trivializationAt
            (ThroatCoverCoordinates →L[Real] Real)
            (ThroatCotangentFiber period hPeriod) base.1))
  apply hCoordinateDeterminant.congr_of_eventuallyEq
  filter_upwards [hTangent, hCotangent] with current hCurrent hCurrentDual
  exact normalGraphRelativeDeterminant_eq_coordinates period hPeriod metric
    displacement base current hCurrent hCurrentDual

/-- The corresponding absolute square-root density is jointly continuous. -/
theorem normalGraphRelativeVolumeDensity_joint_continuous
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod) :
    Continuous
      (fun current : EffectiveThroat period hPeriod × Real =>
        normalGraphRelativeVolumeDensity period hPeriod metric displacement
          current.2 current.1) := by
  exact (normalGraphRelativeDeterminant_joint_continuous
    period hPeriod metric displacement).abs.sqrt

/-! ## Induced boundary-volume measure -/

/-- Restriction of the joint density family to one graph parameter. -/
def normalGraphRelativeVolumeDensityAtParameter
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) : EffectiveThroat period hPeriod → Real :=
  (fun current : EffectiveThroat period hPeriod × Real =>
      normalGraphRelativeVolumeDensity period hPeriod metric displacement
        current.2 current.1) ∘
    fun point => (point, parameter)

@[simp]
theorem normalGraphRelativeVolumeDensityAtParameter_apply
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (point : EffectiveThroat period hPeriod) :
    normalGraphRelativeVolumeDensityAtParameter period hPeriod metric
        displacement parameter point =
        normalGraphRelativeVolumeDensity period hPeriod metric displacement
          parameter point :=
  rfl

/-- At fixed graph parameter, the frame-free density is continuous on the
compact physical throat. -/
theorem normalGraphRelativeVolumeDensityAtParameter_continuous
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) :
    Continuous
      (normalGraphRelativeVolumeDensityAtParameter period hPeriod metric
        displacement parameter) := by
  unfold normalGraphRelativeVolumeDensityAtParameter
  exact (normalGraphRelativeVolumeDensity_joint_continuous
    period hPeriod metric displacement).comp
      (continuous_id.prodMk continuous_const)

/-- The genuine volume measure induced by the normal graph, expressed
relative to the already existing canonical throat measure. -/
def normalGraphInducedVolumeMeasure
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) : Measure (EffectiveThroat period hPeriod) :=
  (intrinsicCanonicalThroatVolumeMeasure period hPeriod).withDensity
    (fun point => ENNReal.ofReal
      (normalGraphRelativeVolumeDensityAtParameter period hPeriod metric
        displacement parameter point))

theorem normalGraphInducedVolumeMeasure_isFinite
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) :
    IsFiniteMeasure
      (normalGraphInducedVolumeMeasure period hPeriod metric displacement
        parameter) := by
  letI := intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod
  apply isFiniteMeasure_withDensity_ofReal
  exact (Continuous.integrable_of_hasCompactSupport
    (normalGraphRelativeVolumeDensityAtParameter_continuous period hPeriod metric
      displacement parameter)
    (HasCompactSupport.of_compactSpace _)).hasFiniteIntegral

theorem normalGraphInducedVolumeMeasure_ne_zero
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter) :
    normalGraphInducedVolumeMeasure period hPeriod metric displacement
      parameter ≠ 0 := by
  let reference := intrinsicCanonicalThroatVolumeMeasure period hPeriod
  let density := fun point : EffectiveThroat period hPeriod =>
    ENNReal.ofReal
      (normalGraphRelativeVolumeDensityAtParameter period hPeriod metric
        displacement parameter point)
  have hDensityMeasurable : AEMeasurable density reference :=
    (ENNReal.measurable_ofReal.comp
      (normalGraphRelativeVolumeDensityAtParameter_continuous period hPeriod metric
        displacement parameter).measurable).aemeasurable
  have hDensityNonzero : ∀ᵐ point ∂reference, density point ≠ 0 :=
    Filter.Eventually.of_forall fun point =>
      ENNReal.ofReal_ne_zero_iff.mpr
        (by
          simpa using
            (normalGraphRelativeVolumeDensity_pos period hPeriod metric
              displacement parameter hNonNull point))
  have hAbsolutelyContinuous :
      reference ≪ reference.withDensity density :=
    withDensity_absolutelyContinuous' hDensityMeasurable hDensityNonzero
  change reference.withDensity density ≠ 0
  intro hZero
  rw [hZero] at hAbsolutelyContinuous
  exact intrinsicCanonicalThroatVolumeMeasure_ne_zero period hPeriod
    (Measure.absolutelyContinuous_zero_iff.mp hAbsolutelyContinuous)

/-- Integration on the graph is exactly integration on the reference throat
with the intrinsic determinant ratio inserted. -/
theorem integral_normalGraphInducedVolumeMeasure_eq_reference
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (integrand : EffectiveThroat period hPeriod → Real) :
    (∫ point, integrand point
        ∂normalGraphInducedVolumeMeasure period hPeriod metric displacement
          parameter) =
      ∫ point,
        normalGraphRelativeVolumeDensity period hPeriod metric displacement
            parameter point * integrand point
          ∂intrinsicCanonicalThroatVolumeMeasure period hPeriod := by
  let density := fun point : EffectiveThroat period hPeriod =>
    ENNReal.ofReal
      (normalGraphRelativeVolumeDensityAtParameter period hPeriod metric
        displacement parameter point)
  have hDensityMeasurable : Measurable density :=
    ENNReal.measurable_ofReal.comp
      (normalGraphRelativeVolumeDensityAtParameter_continuous period hPeriod metric
        displacement parameter).measurable
  have hDensityFinite : ∀ᵐ point
      ∂intrinsicCanonicalThroatVolumeMeasure period hPeriod,
      density point < (⊤ : ENNReal) :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  change
    (∫ point, integrand point
        ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod).withDensity
          density) = _
  rw [integral_withDensity_eq_integral_toReal_smul
    hDensityMeasurable hDensityFinite]
  apply integral_congr_ae
  filter_upwards [] with point
  simp [density, normalGraphRelativeVolumeDensity,
    ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]

/-- At the intrinsic metric and zero graph parameter, the relative metric
endomorphism is exactly the identity. -/
@[simp]
theorem normalGraphRelativeEndomorphism_intrinsic_zero
    (displacement : SmoothNormalDisplacement period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    normalGraphRelativeEndomorphism period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod) displacement
        0 point =
      ContinuousLinearMap.id Real
        (ThroatTangentFiber period hPeriod point) := by
  apply ContinuousLinearMap.ext
  intro vector
  rw [normalGraphRelativeEndomorphism_apply,
    normalGraphInducedMetricValue_zero]
  change intrinsicThroatInverseMusical period hPeriod point
      (intrinsicThroatMusical period hPeriod point vector) = vector
  exact intrinsicThroatInverseMusical_apply_musical
    period hPeriod point vector

@[simp]
theorem normalGraphRelativeDeterminant_intrinsic_zero
    (displacement : SmoothNormalDisplacement period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    normalGraphRelativeDeterminant period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod) displacement
        0 point = 1 := by
  unfold normalGraphRelativeDeterminant
  rw [normalGraphRelativeEndomorphism_intrinsic_zero]
  exact LinearMap.det_id

@[simp]
theorem normalGraphRelativeVolumeDensity_intrinsic_zero
    (displacement : SmoothNormalDisplacement period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    normalGraphRelativeVolumeDensity period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod) displacement
        0 point = 1 := by
  simp [normalGraphRelativeVolumeDensity]

/-- The induced boundary measure recovers the existing canonical throat
measure at the physical intrinsic metric and zero displacement. -/
theorem normalGraphInducedVolumeMeasure_intrinsic_zero
    (displacement : SmoothNormalDisplacement period hPeriod) :
    normalGraphInducedVolumeMeasure period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod) displacement 0 =
      intrinsicCanonicalThroatVolumeMeasure period hPeriod := by
  unfold normalGraphInducedVolumeMeasure
  rw [show
      (fun point : EffectiveThroat period hPeriod =>
        ENNReal.ofReal
          (normalGraphRelativeVolumeDensityAtParameter period hPeriod
            (intrinsicSmoothGeneralLorentzMetric period hPeriod)
            displacement 0 point)) = 1 by
      funext point
      simp]
  exact withDensity_one

/-! ## Descent of the genuine normal section to the orientation double -/

attribute [local instance 30000]
  P0EFTJanusProgramPGlobalNormalDisplacementCollarJointSmooth4D.throatCoverChartedSpace
  P0EFTJanusProgramPGlobalNormalDisplacementCollarJointSmooth4D.throatCoverIsManifold
  P0EFTJanusProgramPGlobalNormalDisplacementCollarJointSmooth4D.effectiveThroatChartedSpace
  P0EFTJanusProgramPGlobalNormalDisplacementCollarJointSmooth4D.effectiveThroatIsManifold
  P0EFTJanusProgramPGlobalNormalDisplacementCollarJointSmooth4D.effectiveQuotientChartedSpace
  P0EFTJanusProgramPGlobalNormalDisplacementCollarJointSmooth4D.effectiveQuotientIsManifold

/-- The coordinate identification from the doubled cover to the original
throat cover is smooth for the already installed quotient atlases. -/
theorem orientationDoubleCoverHomeomorph_contMDiff :
    ContMDiff throatCoverModelWithCorners throatCoverModelWithCorners ∞
      (orientationDoubleCoverHomeomorph period hPeriod) := by
  have hTo := chartedSpacePullback_toFun_contMDiff
    throatCoverModelWithCorners ∞
    (coverHomeomorphProd (orientationDoubleData period hPeriod))
  have hInv := chartedSpacePullback_invFun_contMDiff
    throatCoverModelWithCorners ∞
    (coverHomeomorphProd (fixedEquatorData period hPeriod))
  change ContMDiff throatCoverModelWithCorners throatCoverModelWithCorners ∞
    ((coverHomeomorphProd (fixedEquatorData period hPeriod)).symm ∘
      coverHomeomorphProd (orientationDoubleData period hPeriod))
  exact hInv.comp hTo

/-- The inverse coordinate identification is smooth for the same two pulled
back atlases. -/
theorem orientationDoubleCoverHomeomorph_symm_contMDiff :
    ContMDiff throatCoverModelWithCorners throatCoverModelWithCorners ∞
      (orientationDoubleCoverHomeomorph period hPeriod).symm := by
  have hTo := chartedSpacePullback_toFun_contMDiff
    throatCoverModelWithCorners ∞
    (coverHomeomorphProd (fixedEquatorData period hPeriod))
  have hInv := chartedSpacePullback_invFun_contMDiff
    throatCoverModelWithCorners ∞
    (coverHomeomorphProd (orientationDoubleData period hPeriod))
  change ContMDiff throatCoverModelWithCorners throatCoverModelWithCorners ∞
    ((coverHomeomorphProd (orientationDoubleData period hPeriod)).symm ∘
      coverHomeomorphProd (fixedEquatorData period hPeriod))
  exact hInv.comp hTo

/-- Smooth upgrade of the already existing cover-coordinate homeomorphism. -/
def orientationDoubleCoverDiffeomorph :
    OrientationBoundaryCover period hPeriod ≃ₘ⟮
      throatCoverModelWithCorners, throatCoverModelWithCorners⟯
      EffectiveThroatCover period hPeriod where
  toEquiv := (orientationDoubleCoverHomeomorph period hPeriod).toEquiv
  contMDiff_toFun := orientationDoubleCoverHomeomorph_contMDiff period hPeriod
  contMDiff_invFun :=
    orientationDoubleCoverHomeomorph_symm_contMDiff period hPeriod

/-- The residual two-sheeted projection is a smooth local diffeomorphism.
This is the local-chart bridge needed to compare the global coorientation with
the pre-existing holonomic Weingarten germ. -/
theorem orientationDoubleToThroat_isLocalDiffeomorph :
    IsLocalDiffeomorph throatCoverModelWithCorners
      throatCoverModelWithCorners ∞
      (orientationDoubleToThroat period hPeriod) := by
  intro boundary
  obtain ⟨coverPoint, rfl⟩ :=
    mappingTorusMk_surjective (orientationDoubleData period hPeriod) boundary
  let sourceProjection :=
    mappingTorusMk (orientationDoubleData period hPeriod)
  let targetProjection :=
    mappingTorusMk (fixedEquatorData period hPeriod)
  let coverDiffeomorph :=
    orientationDoubleCoverDiffeomorph period hPeriod
  have hSource : IsLocalDiffeomorph throatCoverModelWithCorners
      throatCoverModelWithCorners ∞ sourceProjection :=
    fixedThroat_projection_isLocalDiffeomorph_smooth
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
  have hTarget : IsLocalDiffeomorph throatCoverModelWithCorners
      throatCoverModelWithCorners ∞ targetProjection :=
    fixedThroat_projection_isLocalDiffeomorph_smooth period hPeriod
  let hSourceAt := hSource coverPoint
  let hTargetAt := hTarget (coverDiffeomorph coverPoint)
  let localChart := hSourceAt.localInverse.trans
    (coverDiffeomorph.toPartialDiffeomorph.trans hTargetAt.choose)
  refine ⟨localChart, ?_, ?_⟩
  · change
      mappingTorusMk (orientationDoubleData period hPeriod) coverPoint ∈
        localChart.source
    rw [show localChart.source =
        hSourceAt.localInverse.source ∩
          hSourceAt.localInverse ⁻¹'
            (coverDiffeomorph.toPartialDiffeomorph.trans
              hTargetAt.choose).source by rfl]
    constructor
    · exact hSourceAt.localInverse_mem_source
    · rw [show
          (coverDiffeomorph.toPartialDiffeomorph.trans
            hTargetAt.choose).source =
          Set.univ ∩ coverDiffeomorph ⁻¹' hTargetAt.choose.source by rfl]
      refine ⟨Set.mem_univ _, ?_⟩
      rw [hSourceAt.localInverse_left_inv hSourceAt.localInverse_mem_target]
      exact hTargetAt.choose_spec.1
  · intro current hCurrent
    have hInverse : sourceProjection (hSourceAt.localInverse current) = current :=
      hSourceAt.localInverse_right_inv hCurrent.1
    have hTargetSource :
        coverDiffeomorph (hSourceAt.localInverse current) ∈
          hTargetAt.choose.source := by
      have hNested := hCurrent.2
      change hSourceAt.localInverse current ∈
        Set.univ ∩ coverDiffeomorph ⁻¹' hTargetAt.choose.source at hNested
      exact hNested.2
    calc
      orientationDoubleToThroat period hPeriod current =
          orientationDoubleToThroat period hPeriod
            (sourceProjection (hSourceAt.localInverse current)) :=
        congrArg _ hInverse.symm
      _ = targetProjection
          (coverDiffeomorph (hSourceAt.localInverse current)) := rfl
      _ = hTargetAt.choose
          (coverDiffeomorph (hSourceAt.localInverse current)) :=
        hTargetAt.choose_spec.2 hTargetSource
      _ = localChart current := rfl

/-- The topological orientation-double projection already present in D8 is
also smooth for the canonical doubled and original throat atlases. -/
theorem orientationDoubleToThroat_contMDiff :
    ContMDiff throatCoverModelWithCorners throatCoverModelWithCorners ∞
      (orientationDoubleToThroat period hPeriod) := by
  intro boundary
  obtain ⟨coverPoint, rfl⟩ :=
    mappingTorusMk_surjective (orientationDoubleData period hPeriod) boundary
  have hSource :
      IsLocalDiffeomorph throatCoverModelWithCorners throatCoverModelWithCorners ω
        (mappingTorusMk (orientationDoubleData period hPeriod)) :=
    fixedThroat_projection_isLocalDiffeomorph
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
  have hTarget :
      IsLocalDiffeomorph throatCoverModelWithCorners throatCoverModelWithCorners ω
        (mappingTorusMk (fixedEquatorData period hPeriod)) :=
    fixedThroat_projection_isLocalDiffeomorph period hPeriod
  have hAt := hSource coverPoint
  have hTargetSmooth :
      ContMDiff throatCoverModelWithCorners throatCoverModelWithCorners ∞
        (mappingTorusMk (fixedEquatorData period hPeriod)) :=
    hTarget.contMDiff.of_le (by simp)
  have hInverseAt :
      ContMDiffAt throatCoverModelWithCorners throatCoverModelWithCorners ∞
        hAt.localInverse
        (mappingTorusMk (orientationDoubleData period hPeriod) coverPoint) :=
    hAt.localInverse_contMDiffAt.of_le (by simp)
  have hCoverInverseAt :
      ContMDiffAt throatCoverModelWithCorners throatCoverModelWithCorners ∞
        (orientationDoubleCoverHomeomorph period hPeriod ∘ hAt.localInverse)
        (mappingTorusMk (orientationDoubleData period hPeriod) coverPoint) :=
    (orientationDoubleCoverHomeomorph_contMDiff period hPeriod).contMDiffAt.comp _
      hInverseAt
  have hLocal :
      ContMDiffAt throatCoverModelWithCorners throatCoverModelWithCorners ∞
        (mappingTorusMk (fixedEquatorData period hPeriod) ∘
          orientationDoubleCoverHomeomorph period hPeriod ∘ hAt.localInverse)
        (mappingTorusMk (orientationDoubleData period hPeriod) coverPoint) :=
    hTargetSmooth.contMDiffAt.comp _ hCoverInverseAt
  apply hLocal.congr_of_eventuallyEq
  filter_upwards [hAt.localInverse_eventuallyEq_right] with point hPoint
  have hPoint' :
      mappingTorusMk (orientationDoubleData period hPeriod)
          (hAt.localInverse point) = point := by
    simpa [Function.comp_def] using hPoint
  calc
    orientationDoubleToThroat period hPeriod point =
        orientationDoubleToThroat period hPeriod
          (mappingTorusMk (orientationDoubleData period hPeriod)
            (hAt.localInverse point)) := congrArg _ hPoint'.symm
    _ = mappingTorusMk (fixedEquatorData period hPeriod)
        (orientationDoubleCoverHomeomorph period hPeriod
          (hAt.localInverse point)) := rfl

/-- The moving graph pulled back to the orientation double. -/
def normalGraphOrientationDouble
    (displacement : SmoothNormalDisplacement period hPeriod)
    (current : OrientationBoundary period hPeriod × Real) :
    EffectiveQuotient period hPeriod :=
  normalGraph period hPeriod displacement current.2
    (orientationDoubleToThroat period hPeriod current.1)

theorem normalGraphOrientationDouble_contMDiff
    (displacement : SmoothNormalDisplacement period hPeriod) :
    ContMDiff
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      coverModelWithCorners ∞
      (normalGraphOrientationDouble period hPeriod displacement) := by
  change ContMDiff
    (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
    coverModelWithCorners ∞
    (fun current : OrientationBoundary period hPeriod × Real =>
      normalGraph period hPeriod displacement current.2
        (orientationDoubleToThroat period hPeriod current.1))
  have hBase : ContMDiff
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      throatCoverModelWithCorners ∞
      (fun current : OrientationBoundary period hPeriod × Real =>
        orientationDoubleToThroat period hPeriod current.1) :=
    (orientationDoubleToThroat_contMDiff period hPeriod).comp contMDiff_fst
  have hPair : ContMDiff
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real)) ∞
      (fun current : OrientationBoundary period hPeriod × Real =>
        (orientationDoubleToThroat period hPeriod current.1, current.2)) :=
    hBase.prodMk contMDiff_snd
  have hComposition :=
    (normalGraph_joint_contMDiff period hPeriod displacement).comp hPair
  simpa only [Function.comp_def] using hComposition

@[simp]
theorem normalGraphOrientationDouble_deck
    (displacement : SmoothNormalDisplacement period hPeriod)
    (boundary : OrientationBoundary period hPeriod) (parameter : Real) :
    normalGraphOrientationDouble period hPeriod displacement
        (orientationDeck period hPeriod boundary, parameter) =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter) := by
  simp [normalGraphOrientationDouble]

/-- The local coordinate of a genuine normal section transforms by the
normal-sign character under every deck winding. -/
theorem normalCoordinateLift_vadd
    (displacement : SmoothNormalDisplacement period hPeriod)
    (winding : Int)
    (anchor : MappingTorusCover (fixedEquatorData period hPeriod)) :
    normalCoordinateLift period hPeriod displacement (winding +ᵥ anchor) =
      (normalSignRepresentation winding : Real) *
        normalCoordinateLift period hPeriod displacement anchor := by
  have hMinusOne : ∀ current :
      MappingTorusCover (fixedEquatorData period hPeriod),
      normalCoordinateLift period hPeriod displacement ((-1 : Int) +ᵥ current) =
        -normalCoordinateLift period hPeriod displacement current := by
    intro current
    have hForward := normalCoordinateLift_oneLoop period hPeriod displacement
      ((-1 : Int) +ᵥ current)
    have hForward' :
        normalCoordinateLift period hPeriod displacement current =
          -normalCoordinateLift period hPeriod displacement
            ((-1 : Int) +ᵥ current) := by
      simpa [add_vadd] using hForward
    linarith
  induction winding using Int.induction_on generalizing anchor with
  | zero => simp [normalSignRepresentation]
  | succ winding ih =>
      calc
        normalCoordinateLift period hPeriod displacement
            (((winding : Int) + 1) +ᵥ anchor) =
          normalCoordinateLift period hPeriod displacement
            ((winding : Int) +ᵥ ((1 : Int) +ᵥ anchor)) := by
              rw [add_vadd]
        _ = (normalSignRepresentation (winding : Int) : Real) *
            normalCoordinateLift period hPeriod displacement
              ((1 : Int) +ᵥ anchor) := ih _
        _ = (normalSignRepresentation (winding : Int) : Real) *
            (-normalCoordinateLift period hPeriod displacement anchor) := by
              rw [normalCoordinateLift_oneLoop]
        _ = (normalSignRepresentation ((winding : Int) + 1) : Real) *
            normalCoordinateLift period hPeriod displacement anchor := by
              rw [normal_sign_add]
              simp [normalSignRepresentation]
  | pred winding ih =>
      calc
        normalCoordinateLift period hPeriod displacement
            ((-(winding : Int) - 1) +ᵥ anchor) =
          normalCoordinateLift period hPeriod displacement
            ((-(winding : Int)) +ᵥ ((-1 : Int) +ᵥ anchor)) := by
              rw [sub_eq_add_neg, add_vadd]
        _ = (normalSignRepresentation (-(winding : Int)) : Real) *
            normalCoordinateLift period hPeriod displacement
              ((-1 : Int) +ᵥ anchor) := ih _
        _ = (normalSignRepresentation (-(winding : Int)) : Real) *
            (-normalCoordinateLift period hPeriod displacement anchor) := by
              rw [hMinusOne]
        _ = (normalSignRepresentation (-(winding : Int) - 1) : Real) *
            normalCoordinateLift period hPeriod displacement anchor := by
              rw [sub_eq_add_neg, normal_sign_add]
              simp [normalSignRepresentation]

/-- Pulling a genuine twisted normal section to the orientation-double cover
turns it into an ordinary scalar. -/
def normalDisplacementOrientationCoverScalar
    (displacement : SmoothNormalDisplacement period hPeriod)
    (point : OrientationBoundaryCover period hPeriod) : Real :=
  normalCoordinateLift period hPeriod displacement
    (orientationDoubleCoverHomeomorph period hPeriod point)

theorem normalDisplacementOrientationCoverScalar_contMDiff
    (displacement : SmoothNormalDisplacement period hPeriod) :
    ContMDiff throatCoverModelWithCorners (modelWithCornersSelf Real Real) ∞
      (normalDisplacementOrientationCoverScalar period hPeriod displacement) := by
  exact (normalCoordinateLift_contMDiff period hPeriod displacement).comp
    (orientationDoubleCoverHomeomorph_contMDiff period hPeriod)

theorem normalDisplacementOrientationCoverScalar_invariant
    (displacement : SmoothNormalDisplacement period hPeriod)
    (winding : Int) (point : OrientationBoundaryCover period hPeriod) :
    normalDisplacementOrientationCoverScalar period hPeriod displacement
        (winding +ᵥ point) =
      normalDisplacementOrientationCoverScalar period hPeriod displacement point := by
  unfold normalDisplacementOrientationCoverScalar
  rw [orientationDoubleCover_even_equivariant,
    normalCoordinateLift_vadd, pulledBack_normal_sign_trivial]
  simp

/-- Global scalar representative of the pulled-back normal section on the
orientation double.  It is derived from the existing bundle section. -/
def normalDisplacementOrientationScalar
    (displacement : SmoothNormalDisplacement period hPeriod) :
    OrientationBoundary period hPeriod → Real :=
  Quotient.lift
    (normalDisplacementOrientationCoverScalar period hPeriod displacement)
    (fun first second hOrbit ↦ by
      change AddAction.orbitRel Int (OrientationBoundaryCover period hPeriod)
        first second at hOrbit
      rw [AddAction.orbitRel_apply, AddAction.mem_orbit_iff] at hOrbit
      rcases hOrbit with ⟨winding, hWinding⟩
      rw [← hWinding]
      exact normalDisplacementOrientationCoverScalar_invariant
        period hPeriod displacement winding second)

@[simp]
theorem normalDisplacementOrientationScalar_mk
    (displacement : SmoothNormalDisplacement period hPeriod)
    (point : OrientationBoundaryCover period hPeriod) :
    normalDisplacementOrientationScalar period hPeriod displacement
        (mappingTorusMk (orientationDoubleData period hPeriod) point) =
      normalDisplacementOrientationCoverScalar period hPeriod displacement point :=
  rfl

theorem normalDisplacementOrientationScalar_contMDiff
    (displacement : SmoothNormalDisplacement period hPeriod) :
    ContMDiff throatCoverModelWithCorners (modelWithCornersSelf Real Real) ∞
      (normalDisplacementOrientationScalar period hPeriod displacement) := by
  intro boundary
  obtain ⟨coverPoint, rfl⟩ :=
    mappingTorusMk_surjective (orientationDoubleData period hPeriod) boundary
  have hProjection :
      IsLocalDiffeomorph throatCoverModelWithCorners throatCoverModelWithCorners ω
        (mappingTorusMk (orientationDoubleData period hPeriod)) :=
    fixedThroat_projection_isLocalDiffeomorph
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
  have hAt := hProjection coverPoint
  have hLocal :
      ContMDiffAt throatCoverModelWithCorners (modelWithCornersSelf Real Real) ∞
        (normalDisplacementOrientationCoverScalar period hPeriod displacement ∘
          hAt.localInverse)
        (mappingTorusMk (orientationDoubleData period hPeriod) coverPoint) :=
    (normalDisplacementOrientationCoverScalar_contMDiff
      period hPeriod displacement).contMDiffAt.comp _
        (hAt.localInverse_contMDiffAt.of_le (by simp))
  apply hLocal.congr_of_eventuallyEq
  filter_upwards [hAt.localInverse_eventuallyEq_right] with point hPoint
  have hPoint' :
      mappingTorusMk (orientationDoubleData period hPeriod)
          (hAt.localInverse point) = point := by
    simpa [Function.comp_def] using hPoint
  calc
    normalDisplacementOrientationScalar period hPeriod displacement point =
        normalDisplacementOrientationScalar period hPeriod displacement
          (mappingTorusMk (orientationDoubleData period hPeriod)
            (hAt.localInverse point)) := congrArg _ hPoint'.symm
    _ = normalDisplacementOrientationCoverScalar period hPeriod displacement
        (hAt.localInverse point) := rfl

/-- The remaining deck involution reverses the scalar representative, exactly
encoding the two normal orientations. -/
theorem normalDisplacementOrientationScalar_deck
    (displacement : SmoothNormalDisplacement period hPeriod)
    (boundary : OrientationBoundary period hPeriod) :
    normalDisplacementOrientationScalar period hPeriod displacement
        (orientationDeck period hPeriod boundary) =
      -normalDisplacementOrientationScalar period hPeriod displacement boundary := by
  refine Quotient.inductionOn boundary ?_
  intro point
  have hCover :
      orientationDoubleCoverHomeomorph period hPeriod
          (orientationDeckCover period hPeriod point) =
        (1 : Int) +ᵥ orientationDoubleCoverHomeomorph period hPeriod point := by
    apply MappingTorusCover.ext
    · simp only [orientationDoubleCoverHomeomorph_fiber,
        orientationDeckCover_fiber, vadd_fiber]
      simp [fixedEquatorData]
    · simp only [orientationDoubleCoverHomeomorph_time,
        orientationDeckCover_time, vadd_time]
      simp [fixedEquatorData]
  change normalCoordinateLift period hPeriod displacement
      (orientationDoubleCoverHomeomorph period hPeriod
        (orientationDeckCover period hPeriod point)) =
    -normalCoordinateLift period hPeriod displacement
      (orientationDoubleCoverHomeomorph period hPeriod point)
  rw [hCover, normalCoordinateLift_oneLoop]

/-! ## Uniform second-jet core for genuine normal displacements -/

private theorem localNormalCoordinate_add
    (anchor : EffectiveThroatCover period hPeriod)
    (point : EffectiveThroat period hPeriod)
    (hPoint : point ∈ normalBundleBaseSet period hPeriod anchor)
    (first second : FixedThroatNormalFiber period hPeriod point) :
    localNormalCoordinate period hPeriod anchor point hPoint (first + second) =
      localNormalCoordinate period hPeriod anchor point hPoint first +
        localNormalCoordinate period hPeriod anchor point hPoint second := by
  let trivialization :=
    (fixedThroatNormalVectorBundleCore period hPeriod).localTriv anchor
  unfold localNormalCoordinate
  rw [trivialization.apply_eq_prod_continuousLinearEquivAt Real point hPoint,
    trivialization.apply_eq_prod_continuousLinearEquivAt Real point hPoint,
    trivialization.apply_eq_prod_continuousLinearEquivAt Real point hPoint]
  exact map_add _ first second

private theorem localNormalCoordinate_smul
    (anchor : EffectiveThroatCover period hPeriod)
    (point : EffectiveThroat period hPeriod)
    (hPoint : point ∈ normalBundleBaseSet period hPeriod anchor)
    (scalar : Real) (normal : FixedThroatNormalFiber period hPeriod point) :
    localNormalCoordinate period hPeriod anchor point hPoint (scalar • normal) =
      scalar * localNormalCoordinate period hPeriod anchor point hPoint normal := by
  let trivialization :=
    (fixedThroatNormalVectorBundleCore period hPeriod).localTriv anchor
  unfold localNormalCoordinate
  rw [trivialization.apply_eq_prod_continuousLinearEquivAt Real point hPoint,
    trivialization.apply_eq_prod_continuousLinearEquivAt Real point hPoint]
  exact map_smul (trivialization.continuousLinearEquivAt Real point hPoint)
    scalar normal

private theorem localNormalCoordinate_injective
    (anchor : EffectiveThroatCover period hPeriod)
    (point : EffectiveThroat period hPeriod)
    (hPoint : point ∈ normalBundleBaseSet period hPeriod anchor) :
    Function.Injective
      (localNormalCoordinate period hPeriod anchor point hPoint) := by
  intro first second hEqual
  let trivialization :=
    (fixedThroatNormalVectorBundleCore period hPeriod).localTriv anchor
  unfold localNormalCoordinate at hEqual
  rw [trivialization.apply_eq_prod_continuousLinearEquivAt Real point hPoint,
    trivialization.apply_eq_prod_continuousLinearEquivAt Real point hPoint]
    at hEqual
  exact (trivialization.continuousLinearEquivAt
    Real point hPoint).injective hEqual

theorem normalDisplacementOrientationScalar_add
    (first second : SmoothNormalDisplacement period hPeriod) :
    normalDisplacementOrientationScalar period hPeriod (first + second) =
      normalDisplacementOrientationScalar period hPeriod first +
        normalDisplacementOrientationScalar period hPeriod second := by
  funext boundary
  obtain ⟨point, rfl⟩ :=
    mappingTorusMk_surjective (orientationDoubleData period hPeriod) boundary
  rw [normalDisplacementOrientationScalar_mk]
  simp only [Pi.add_apply]
  rw [normalDisplacementOrientationScalar_mk,
    normalDisplacementOrientationScalar_mk]
  unfold normalDisplacementOrientationCoverScalar
  change normalCoordinateLift period hPeriod (first + second)
      (orientationDoubleCoverHomeomorph period hPeriod point) = _
  unfold normalCoordinateLift
  exact localNormalCoordinate_add period hPeriod _ _ _ _ _

theorem normalDisplacementOrientationScalar_smul
    (scalar : Real) (displacement : SmoothNormalDisplacement period hPeriod) :
    normalDisplacementOrientationScalar period hPeriod
        (scalar • displacement) =
      scalar • normalDisplacementOrientationScalar period hPeriod displacement := by
  funext boundary
  obtain ⟨point, rfl⟩ :=
    mappingTorusMk_surjective (orientationDoubleData period hPeriod) boundary
  rw [normalDisplacementOrientationScalar_mk]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [normalDisplacementOrientationScalar_mk]
  let anchor := orientationDoubleCoverHomeomorph period hPeriod point
  let base := mappingTorusMk (fixedEquatorData period hPeriod) anchor
  have hEvaluation : (scalar • displacement) base =
      scalar • displacement base := by
    exact congrFun (ContMDiffSection.coe_smul scalar displacement) base
  unfold normalDisplacementOrientationCoverScalar normalCoordinateLift
  change localNormalCoordinate period hPeriod anchor base _
      ((scalar • displacement) base) =
    scalar * localNormalCoordinate period hPeriod anchor base _
      (displacement base)
  rw [hEvaluation]
  exact localNormalCoordinate_smul period hPeriod anchor base _ scalar _

/-- Scalarization on the orientation double loses no genuine normal section. -/
theorem normalDisplacementOrientationScalar_injective :
    Function.Injective
      (normalDisplacementOrientationScalar period hPeriod) := by
  intro first second hEqual
  apply ContMDiffSection.ext
  intro throat
  obtain ⟨anchor, rfl⟩ :=
    mappingTorusMk_surjective (fixedEquatorData period hPeriod) throat
  let orientationPoint :=
    (orientationDoubleCoverHomeomorph period hPeriod).symm anchor
  have hCoordinate := congrFun hEqual
    (mappingTorusMk (orientationDoubleData period hPeriod) orientationPoint)
  rw [normalDisplacementOrientationScalar_mk,
    normalDisplacementOrientationScalar_mk] at hCoordinate
  unfold normalDisplacementOrientationCoverScalar at hCoordinate
  simp only [orientationPoint, Homeomorph.apply_symm_apply] at hCoordinate
  unfold normalCoordinateLift at hCoordinate
  exact localNormalCoordinate_injective period hPeriod anchor _ _ hCoordinate

private abbrev OrientationNormalFrame :=
  finiteSmoothThroatGeneratingFrame
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)

/-- Value and genuine first and ordered second tangential derivatives on the
orientation double. -/
abbrev NormalBoundaryFrameJet2 (Index : Type*) :=
  Real × ((Index → Real) × (Index → Index → Real))

private abbrev OrientationNormalJet2Fiber :=
  NormalBoundaryFrameJet2
    (Fin (OrientationNormalFrame period hPeriod).count)

/-- The scalar on the orientation double, packaged in the existing smooth
throat-field type at doubled period. -/
def normalDisplacementOrientationSmoothField
    (displacement : SmoothNormalDisplacement period hPeriod) :
    SmoothThroatField
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod) Real where
  toFun := normalDisplacementOrientationScalar period hPeriod displacement
  contMDiff_toFun :=
    normalDisplacementOrientationScalar_contMDiff period hPeriod displacement

theorem normalDisplacementOrientationSmoothField_add
    (first second : SmoothNormalDisplacement period hPeriod) :
    normalDisplacementOrientationSmoothField period hPeriod (first + second) =
      normalDisplacementOrientationSmoothField period hPeriod first +
        normalDisplacementOrientationSmoothField period hPeriod second := by
  apply SmoothThroatField.ext
  intro point
  exact congrFun
    (normalDisplacementOrientationScalar_add period hPeriod first second) point

theorem normalDisplacementOrientationSmoothField_smul
    (scalar : Real) (displacement : SmoothNormalDisplacement period hPeriod) :
    normalDisplacementOrientationSmoothField period hPeriod
        (scalar • displacement) =
      scalar • normalDisplacementOrientationSmoothField
        period hPeriod displacement := by
  apply SmoothThroatField.ext
  intro point
  exact congrFun
    (normalDisplacementOrientationScalar_smul period hPeriod scalar displacement)
    point

/-- One first derivative component, retained as a genuine smooth scalar on
the orientation double. -/
def normalBoundaryFrameDerivativeComponentField
    (frame : SmoothThroatGeneratingFrame
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
    (field : SmoothThroatField
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod) Real)
    (index : Fin frame.count) :
    SmoothThroatField
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod) Real where
  toFun := fun point =>
    throatFrameDerivative
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
      Real frame field point index
  contMDiff_toFun :=
    (contMDiff_pi_space.mp
      (throatFrameDerivative_contMDiff
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
        Real frame field)) index

theorem normalBoundaryFrameDerivativeComponentField_add
    (frame : SmoothThroatGeneratingFrame
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
    (first second : SmoothThroatField
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod) Real)
    (index : Fin frame.count) :
    normalBoundaryFrameDerivativeComponentField period hPeriod frame
        (first + second) index =
      normalBoundaryFrameDerivativeComponentField period hPeriod frame
          first index +
        normalBoundaryFrameDerivativeComponentField period hPeriod frame
          second index := by
  apply SmoothThroatField.ext
  intro point
  exact congrFun (congrFun
    (throatFrameDerivative_add
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
      Real frame first second) point) index

theorem normalBoundaryFrameDerivativeComponentField_smul
    (frame : SmoothThroatGeneratingFrame
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
    (scalar : Real)
    (field : SmoothThroatField
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod) Real)
    (index : Fin frame.count) :
    normalBoundaryFrameDerivativeComponentField period hPeriod frame
        (scalar • field) index =
      scalar • normalBoundaryFrameDerivativeComponentField period hPeriod
        frame field index := by
  apply SmoothThroatField.ext
  intro point
  exact congrFun (congrFun
    (throatFrameDerivative_smul
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
      Real frame scalar field) point) index

/-- Ordered second derivatives in the finite spanning family. -/
def normalBoundaryFrameSecondDerivative
    (frame : SmoothThroatGeneratingFrame
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
    (field : SmoothThroatField
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod) Real)
    (point : OrientationBoundary period hPeriod) :
    Fin frame.count → Fin frame.count → Real :=
  fun outer inner =>
    throatFrameDerivative
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
      Real frame
      (normalBoundaryFrameDerivativeComponentField period hPeriod frame
        field inner) point outer

theorem normalBoundaryFrameSecondDerivative_contMDiff
    (frame : SmoothThroatGeneratingFrame
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
    (field : SmoothThroatField
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod) Real) :
    ContMDiff throatCoverModelWithCorners
      𝓘(Real, Fin frame.count → Fin frame.count → Real) ∞
      (normalBoundaryFrameSecondDerivative period hPeriod frame field) := by
  rw [contMDiff_pi_space]
  intro outer
  rw [contMDiff_pi_space]
  intro inner
  exact (contMDiff_pi_space.mp
    (throatFrameDerivative_contMDiff
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
      Real frame
      (normalBoundaryFrameDerivativeComponentField period hPeriod frame
        field inner))) outer

theorem normalBoundaryFrameSecondDerivative_add
    (frame : SmoothThroatGeneratingFrame
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
    (first second : SmoothThroatField
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod) Real) :
    normalBoundaryFrameSecondDerivative period hPeriod frame (first + second) =
      normalBoundaryFrameSecondDerivative period hPeriod frame first +
        normalBoundaryFrameSecondDerivative period hPeriod frame second := by
  funext point outer inner
  change throatFrameDerivative
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
      Real frame
      (normalBoundaryFrameDerivativeComponentField period hPeriod frame
        (first + second) inner) point outer = _
  rw [normalBoundaryFrameDerivativeComponentField_add,
    throatFrameDerivative_add]
  rfl

theorem normalBoundaryFrameSecondDerivative_smul
    (frame : SmoothThroatGeneratingFrame
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
    (scalar : Real)
    (field : SmoothThroatField
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod) Real) :
    normalBoundaryFrameSecondDerivative period hPeriod frame (scalar • field) =
      scalar • normalBoundaryFrameSecondDerivative
        period hPeriod frame field := by
  funext point outer inner
  change throatFrameDerivative
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
      Real frame
      (normalBoundaryFrameDerivativeComponentField period hPeriod frame
        (scalar • field) inner) point outer = _
  rw [normalBoundaryFrameDerivativeComponentField_smul,
    throatFrameDerivative_smul]
  rfl

/-- Genuine uniform second jet of a smooth scalar on the orientation double. -/
def smoothNormalBoundaryFrameJet2
    (frame : SmoothThroatGeneratingFrame
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
    (field : SmoothThroatField
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod) Real)
    (point : OrientationBoundary period hPeriod) :
    NormalBoundaryFrameJet2 (Fin frame.count) :=
  (field point,
    (throatFrameDerivative
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
      Real frame field point,
      normalBoundaryFrameSecondDerivative period hPeriod frame field point))

theorem smoothNormalBoundaryFrameJet2_contMDiff
    (frame : SmoothThroatGeneratingFrame
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
    (field : SmoothThroatField
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod) Real) :
    ContMDiff throatCoverModelWithCorners
      𝓘(Real, NormalBoundaryFrameJet2 (Fin frame.count)) ∞
      (smoothNormalBoundaryFrameJet2 period hPeriod frame field) :=
  field.contMDiff_toFun.prodMk_space
    ((throatFrameDerivative_contMDiff
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
      Real frame field).prodMk_space
      (normalBoundaryFrameSecondDerivative_contMDiff
        period hPeriod frame field))

theorem smoothNormalBoundaryFrameJet2_add
    (frame : SmoothThroatGeneratingFrame
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
    (first second : SmoothThroatField
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod) Real) :
    smoothNormalBoundaryFrameJet2 period hPeriod frame (first + second) =
      smoothNormalBoundaryFrameJet2 period hPeriod frame first +
        smoothNormalBoundaryFrameJet2 period hPeriod frame second := by
  funext point
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · exact congrFun
        (throatFrameDerivative_add
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
          Real frame first second) point
    · exact congrFun
        (normalBoundaryFrameSecondDerivative_add period hPeriod frame
          first second) point

theorem smoothNormalBoundaryFrameJet2_smul
    (frame : SmoothThroatGeneratingFrame
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
    (scalar : Real)
    (field : SmoothThroatField
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod) Real) :
    smoothNormalBoundaryFrameJet2 period hPeriod frame (scalar • field) =
      scalar • smoothNormalBoundaryFrameJet2 period hPeriod frame field := by
  funext point
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · exact congrFun
        (throatFrameDerivative_smul
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
          Real frame scalar field) point
    · exact congrFun
        (normalBoundaryFrameSecondDerivative_smul period hPeriod frame
          scalar field) point

/-- Continuous uniform normal jets on the compact orientation double. -/
abbrev NormalBoundaryC2JetAmbient :=
  C(OrientationBoundary period hPeriod, OrientationNormalJet2Fiber period hPeriod)

/-- Exact second-jet map of the existing genuine normal sections. -/
def smoothNormalDisplacementFrameJet2LinearMap :
    SmoothNormalDisplacement period hPeriod →ₗ[Real]
      NormalBoundaryC2JetAmbient period hPeriod where
  toFun displacement :=
    ⟨smoothNormalBoundaryFrameJet2 period hPeriod
        (OrientationNormalFrame period hPeriod)
        (normalDisplacementOrientationSmoothField
          period hPeriod displacement),
      (smoothNormalBoundaryFrameJet2_contMDiff period hPeriod
        (OrientationNormalFrame period hPeriod)
        (normalDisplacementOrientationSmoothField
          period hPeriod displacement)).continuous⟩
  map_add' first second := by
    apply ContinuousMap.ext
    intro point
    rw [normalDisplacementOrientationSmoothField_add]
    exact congrFun
      (smoothNormalBoundaryFrameJet2_add period hPeriod
        (OrientationNormalFrame period hPeriod)
        (normalDisplacementOrientationSmoothField period hPeriod first)
        (normalDisplacementOrientationSmoothField period hPeriod second)) point
  map_smul' scalar displacement := by
    apply ContinuousMap.ext
    intro point
    rw [normalDisplacementOrientationSmoothField_smul]
    exact congrFun
      (smoothNormalBoundaryFrameJet2_smul period hPeriod
        (OrientationNormalFrame period hPeriod) scalar
        (normalDisplacementOrientationSmoothField
          period hPeriod displacement)) point

/-- Closed uniform `C²` normal core generated by the genuine smooth normal
sections; no independent scalar displacement is introduced. -/
def normalBoundaryC2JetCoreSubmodule :
    Submodule Real (NormalBoundaryC2JetAmbient period hPeriod) :=
  (LinearMap.range
    (smoothNormalDisplacementFrameJet2LinearMap
      period hPeriod)).topologicalClosure

/-- Complete model space controlling the moving graph pointwise through two
tangential derivatives. -/
abbrev NormalBoundaryC2JetCore :=
  normalBoundaryC2JetCoreSubmodule period hPeriod

theorem normalBoundaryC2JetCore_isClosed :
    IsClosed
      (NormalBoundaryC2JetCore period hPeriod :
        Set (NormalBoundaryC2JetAmbient period hPeriod)) :=
  Submodule.isClosed_topologicalClosure _

@[implicit_reducible]
def normalBoundaryC2JetCoreCompleteSpace :
    CompleteSpace (NormalBoundaryC2JetCore period hPeriod) :=
  Submodule.topologicalClosure.completeSpace
    (LinearMap.range
      (smoothNormalDisplacementFrameJet2LinearMap period hPeriod))

/-- Faithful lift of genuine smooth normal sections into the completed core. -/
def smoothNormalDisplacementToBoundaryC2JetCore :
    SmoothNormalDisplacement period hPeriod →ₗ[Real]
      NormalBoundaryC2JetCore period hPeriod where
  toFun displacement :=
    ⟨smoothNormalDisplacementFrameJet2LinearMap period hPeriod displacement,
      (LinearMap.range
        (smoothNormalDisplacementFrameJet2LinearMap
          period hPeriod)).le_topologicalClosure
        (LinearMap.mem_range_self
          (smoothNormalDisplacementFrameJet2LinearMap period hPeriod)
          displacement)⟩
  map_add' first second := Subtype.ext
    ((smoothNormalDisplacementFrameJet2LinearMap
      period hPeriod).map_add first second)
  map_smul' scalar displacement := Subtype.ext
    ((smoothNormalDisplacementFrameJet2LinearMap
      period hPeriod).map_smul scalar displacement)

theorem smoothNormalDisplacementToBoundaryC2JetCore_injective :
    Function.Injective
      (smoothNormalDisplacementToBoundaryC2JetCore period hPeriod) := by
  intro first second hEqual
  apply normalDisplacementOrientationScalar_injective period hPeriod
  funext point
  have hAmbient := congrArg Subtype.val hEqual
  exact congrArg (fun jet => (jet point).1) hAmbient

theorem smoothNormalDisplacementToBoundaryC2JetCore_denseRange :
    DenseRange
      (smoothNormalDisplacementToBoundaryC2JetCore period hPeriod) := by
  simp only [DenseRange]
  rw [Subtype.dense_iff]
  let inclusion := smoothNormalDisplacementFrameJet2LinearMap period hPeriod
  have hRange :
      Subtype.val '' Set.range
          (smoothNormalDisplacementToBoundaryC2JetCore period hPeriod) =
        (LinearMap.range inclusion :
          Set (NormalBoundaryC2JetAmbient period hPeriod)) := by
    ext value
    constructor
    · rintro ⟨lifted, ⟨displacement, rfl⟩, rfl⟩
      exact ⟨displacement, rfl⟩
    · rintro ⟨displacement, rfl⟩
      exact ⟨smoothNormalDisplacementToBoundaryC2JetCore
          period hPeriod displacement, ⟨displacement, rfl⟩, rfl⟩
  change closure (LinearMap.range inclusion :
      Set (NormalBoundaryC2JetAmbient period hPeriod)) ⊆
    closure (Subtype.val '' Set.range
      (smoothNormalDisplacementToBoundaryC2JetCore period hPeriod))
  rw [hRange]

/-- Continuous inclusion into the uniform second-jet ambient space. -/
def normalBoundaryC2JetCoreToAmbient :
    NormalBoundaryC2JetCore period hPeriod →L[Real]
      NormalBoundaryC2JetAmbient period hPeriod :=
  (normalBoundaryC2JetCoreSubmodule period hPeriod).subtypeL

private def normalBoundaryFrameJet2ToValue :
    OrientationNormalJet2Fiber period hPeriod →L[Real] Real :=
  ContinuousLinearMap.fst Real Real
    ((Fin (OrientationNormalFrame period hPeriod).count → Real) ×
      (Fin (OrientationNormalFrame period hPeriod).count →
        Fin (OrientationNormalFrame period hPeriod).count → Real))

/-- Continuous pointwise-value projection; this is the analytic property
missing from the pre-existing `L²` normal completion. -/
def normalBoundaryC2JetCoreToContinuous :
    NormalBoundaryC2JetCore period hPeriod →L[Real]
      C(OrientationBoundary period hPeriod, Real) :=
  ((normalBoundaryFrameJet2ToValue period hPeriod).compLeftContinuous
      Real (OrientationBoundary period hPeriod)).comp
    (normalBoundaryC2JetCoreToAmbient period hPeriod)

@[simp]
theorem normalBoundaryC2JetCoreToContinuous_smooth
    (displacement : SmoothNormalDisplacement period hPeriod) :
    normalBoundaryC2JetCoreToContinuous period hPeriod
        (smoothNormalDisplacementToBoundaryC2JetCore
          period hPeriod displacement) =
      ⟨normalDisplacementOrientationScalar period hPeriod displacement,
        (normalDisplacementOrientationScalar_contMDiff
          period hPeriod displacement).continuous⟩ := by
  apply ContinuousMap.ext
  intro point
  rfl

private def normalBoundaryContinuousValueAt
    (point : OrientationBoundary period hPeriod) :
    C(OrientationBoundary period hPeriod, Real) →L[Real] Real :=
  LinearMap.mkContinuous
    { toFun := fun field => field point
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 (fun field => by
      change ‖field point‖ ≤ 1 * ‖field‖
      simpa only [one_mul] using
        (ContinuousMap.norm_coe_le_norm field point))

/-- Continuous evaluation of a completed normal displacement. -/
def normalBoundaryC2JetCoreValueAt
    (point : OrientationBoundary period hPeriod) :
    NormalBoundaryC2JetCore period hPeriod →L[Real] Real :=
  (normalBoundaryContinuousValueAt period hPeriod point).comp
    (normalBoundaryC2JetCoreToContinuous period hPeriod)

@[simp]
theorem normalBoundaryC2JetCoreValueAt_smooth
    (displacement : SmoothNormalDisplacement period hPeriod)
    (point : OrientationBoundary period hPeriod) :
    normalBoundaryC2JetCoreValueAt period hPeriod point
        (smoothNormalDisplacementToBoundaryC2JetCore
          period hPeriod displacement) =
      normalDisplacementOrientationScalar
        period hPeriod displacement point := by
  rfl

private def normalBoundaryFrameJet2ToFirst :
    OrientationNormalJet2Fiber period hPeriod →L[Real]
      (Fin (OrientationNormalFrame period hPeriod).count → Real) :=
  (ContinuousLinearMap.fst Real
    (Fin (OrientationNormalFrame period hPeriod).count → Real)
    (Fin (OrientationNormalFrame period hPeriod).count →
      Fin (OrientationNormalFrame period hPeriod).count → Real)).comp
    (ContinuousLinearMap.snd Real Real
      ((Fin (OrientationNormalFrame period hPeriod).count → Real) ×
        (Fin (OrientationNormalFrame period hPeriod).count →
          Fin (OrientationNormalFrame period hPeriod).count → Real)))

private def normalBoundaryFrameJet2ToSecond :
    OrientationNormalJet2Fiber period hPeriod →L[Real]
      (Fin (OrientationNormalFrame period hPeriod).count →
        Fin (OrientationNormalFrame period hPeriod).count → Real) :=
  (ContinuousLinearMap.snd Real
    (Fin (OrientationNormalFrame period hPeriod).count → Real)
    (Fin (OrientationNormalFrame period hPeriod).count →
      Fin (OrientationNormalFrame period hPeriod).count → Real)).comp
    (ContinuousLinearMap.snd Real Real
      ((Fin (OrientationNormalFrame period hPeriod).count → Real) ×
        (Fin (OrientationNormalFrame period hPeriod).count →
          Fin (OrientationNormalFrame period hPeriod).count → Real)))

/-- Continuous first-jet projection on the completed normal core. -/
def normalBoundaryC2JetCoreFirstToContinuous :
    NormalBoundaryC2JetCore period hPeriod →L[Real]
      C(OrientationBoundary period hPeriod,
        Fin (OrientationNormalFrame period hPeriod).count → Real) :=
  ((normalBoundaryFrameJet2ToFirst period hPeriod).compLeftContinuous
      Real (OrientationBoundary period hPeriod)).comp
    (normalBoundaryC2JetCoreToAmbient period hPeriod)

/-- Continuous ordered second-jet projection on the completed normal core. -/
def normalBoundaryC2JetCoreSecondToContinuous :
    NormalBoundaryC2JetCore period hPeriod →L[Real]
      C(OrientationBoundary period hPeriod,
        Fin (OrientationNormalFrame period hPeriod).count →
          Fin (OrientationNormalFrame period hPeriod).count → Real) :=
  ((normalBoundaryFrameJet2ToSecond period hPeriod).compLeftContinuous
      Real (OrientationBoundary period hPeriod)).comp
    (normalBoundaryC2JetCoreToAmbient period hPeriod)

private def normalBoundaryContinuousFirstAt
    (point : OrientationBoundary period hPeriod) :
    C(OrientationBoundary period hPeriod,
      Fin (OrientationNormalFrame period hPeriod).count → Real) →L[Real]
        (Fin (OrientationNormalFrame period hPeriod).count → Real) :=
  LinearMap.mkContinuous
    { toFun := fun field => field point
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 (fun field => by
      change ‖field point‖ ≤ 1 * ‖field‖
      simpa only [one_mul] using
        (ContinuousMap.norm_coe_le_norm field point))

private def normalBoundaryContinuousSecondAt
    (point : OrientationBoundary period hPeriod) :
    C(OrientationBoundary period hPeriod,
      Fin (OrientationNormalFrame period hPeriod).count →
        Fin (OrientationNormalFrame period hPeriod).count → Real) →L[Real]
      (Fin (OrientationNormalFrame period hPeriod).count →
        Fin (OrientationNormalFrame period hPeriod).count → Real) :=
  LinearMap.mkContinuous
    { toFun := fun field => field point
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 (fun field => by
      change ‖field point‖ ≤ 1 * ‖field‖
      simpa only [one_mul] using
        (ContinuousMap.norm_coe_le_norm field point))

/-- Continuous evaluation of the first tangential jet of a completed normal. -/
def normalBoundaryC2JetCoreFirstAt
    (point : OrientationBoundary period hPeriod) :
    NormalBoundaryC2JetCore period hPeriod →L[Real]
      (Fin (OrientationNormalFrame period hPeriod).count → Real) :=
  (normalBoundaryContinuousFirstAt period hPeriod point).comp
    (normalBoundaryC2JetCoreFirstToContinuous period hPeriod)

/-- Continuous evaluation of the ordered second tangential jet. -/
def normalBoundaryC2JetCoreSecondAt
    (point : OrientationBoundary period hPeriod) :
    NormalBoundaryC2JetCore period hPeriod →L[Real]
      (Fin (OrientationNormalFrame period hPeriod).count →
        Fin (OrientationNormalFrame period hPeriod).count → Real) :=
  (normalBoundaryContinuousSecondAt period hPeriod point).comp
    (normalBoundaryC2JetCoreSecondToContinuous period hPeriod)

@[simp]
theorem normalBoundaryC2JetCoreFirstAt_smooth
    (displacement : SmoothNormalDisplacement period hPeriod)
    (point : OrientationBoundary period hPeriod) :
    normalBoundaryC2JetCoreFirstAt period hPeriod point
        (smoothNormalDisplacementToBoundaryC2JetCore
          period hPeriod displacement) =
      throatFrameDerivative
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
        Real (OrientationNormalFrame period hPeriod)
        (normalDisplacementOrientationSmoothField period hPeriod displacement)
        point := by
  rfl

/-- Intrinsic differential reconstructed from the completed redundant first
jet.  The inverse frame operator is the canonical one supplied by the already
proved intrinsic nondegenerate throat metric. -/
def normalBoundaryC2JetCoreDifferentialAt
    (normal : NormalBoundaryC2JetCore period hPeriod)
    (point : OrientationBoundary period hPeriod) :
    TangentSpace throatCoverModelWithCorners point →L[Real] Real :=
  ∑ index : Fin (OrientationNormalFrame period hPeriod).count,
    (normalBoundaryC2JetCoreFirstAt period hPeriod point normal index) •
      intrinsicThroatFiniteFrameCoefficientAt
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
        (OrientationNormalFrame period hPeriod) point index

/-- On the dense genuine-smooth core, the reconstructed differential is the
actual manifold differential of the original normal scalar. -/
theorem normalBoundaryC2JetCoreDifferentialAt_smooth
    (displacement : SmoothNormalDisplacement period hPeriod)
    (point : OrientationBoundary period hPeriod) :
    normalBoundaryC2JetCoreDifferentialAt period hPeriod
        (smoothNormalDisplacementToBoundaryC2JetCore
          period hPeriod displacement) point =
      mvfderiv throatCoverModelWithCorners
        (normalDisplacementOrientationSmoothField
          period hPeriod displacement).toFun point := by
  classical
  apply ContinuousLinearMap.ext
  intro vector
  let field := normalDisplacementOrientationSmoothField
    period hPeriod displacement
  let derivative := mvfderiv throatCoverModelWithCorners field.toFun point
  have hReconstruct :=
    intrinsicThroatFiniteFrameCoefficientAt_reconstructs
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
      (OrientationNormalFrame period hPeriod) point vector
  calc
    normalBoundaryC2JetCoreDifferentialAt period hPeriod
        (smoothNormalDisplacementToBoundaryC2JetCore
          period hPeriod displacement) point vector =
      ∑ index : Fin (OrientationNormalFrame period hPeriod).count,
        derivative
            ((OrientationNormalFrame period hPeriod).vectorAt point index) *
          intrinsicThroatFiniteFrameCoefficientAt
            (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
            (OrientationNormalFrame period hPeriod) point index vector := by
      unfold normalBoundaryC2JetCoreDifferentialAt
      rw [_root_.sum_apply]
      apply Finset.sum_congr rfl
      intro index _
      rw [normalBoundaryC2JetCoreFirstAt_smooth,
        throatFrameDerivative_eq_mvfderiv]
      rfl
    _ = derivative
        (∑ index : Fin (OrientationNormalFrame period hPeriod).count,
          intrinsicThroatFiniteFrameCoefficientAt
              (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
              (OrientationNormalFrame period hPeriod) point index vector •
            (OrientationNormalFrame period hPeriod).vectorAt point index) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro index _
      rw [map_smul]
      simpa only [smul_eq_mul] using
        (mul_comm
          (derivative
            ((OrientationNormalFrame period hPeriod).vectorAt point index))
          (intrinsicThroatFiniteFrameCoefficientAt
            (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
            (OrientationNormalFrame period hPeriod) point index vector))
    _ = derivative vector := by rw [← hReconstruct]

@[simp]
theorem normalBoundaryC2JetCoreSecondAt_smooth
    (displacement : SmoothNormalDisplacement period hPeriod)
    (point : OrientationBoundary period hPeriod) :
    normalBoundaryC2JetCoreSecondAt period hPeriod point
        (smoothNormalDisplacementToBoundaryC2JetCore
          period hPeriod displacement) =
      normalBoundaryFrameSecondDerivative period hPeriod
        (OrientationNormalFrame period hPeriod)
        (normalDisplacementOrientationSmoothField period hPeriod displacement)
        point := by
  rfl

/-- The residual deck-odd law survives completion because both point
evaluations are continuous in the uniform second-jet norm. -/
theorem normalBoundaryC2JetCoreValueAt_deck
    (normal : NormalBoundaryC2JetCore period hPeriod)
    (point : OrientationBoundary period hPeriod) :
    normalBoundaryC2JetCoreValueAt period hPeriod
        (orientationDeck period hPeriod point) normal =
      -normalBoundaryC2JetCoreValueAt period hPeriod point normal := by
  letI : CompleteSpace (NormalBoundaryC2JetCore period hPeriod) :=
    normalBoundaryC2JetCoreCompleteSpace period hPeriod
  refine DenseRange.induction_on
    (p := fun current : NormalBoundaryC2JetCore period hPeriod =>
      normalBoundaryC2JetCoreValueAt period hPeriod
          (orientationDeck period hPeriod point) current =
        -normalBoundaryC2JetCoreValueAt period hPeriod point current)
    (smoothNormalDisplacementToBoundaryC2JetCore_denseRange period hPeriod)
    normal
    (isClosed_eq
      (normalBoundaryC2JetCoreValueAt period hPeriod
        (orientationDeck period hPeriod point)).continuous
      (normalBoundaryC2JetCoreValueAt period hPeriod point).continuous.neg) ?_
  intro displacement
  rw [normalBoundaryC2JetCoreValueAt_smooth,
    normalBoundaryC2JetCoreValueAt_smooth,
    normalDisplacementOrientationScalar_deck]

private theorem normalBoundary_refl_zpow_apply
    {X : Type*} [TopologicalSpace X]
    (winding : Int) (point : X) :
    ((Homeomorph.refl X) ^ winding) point = point := by
  rw [show ((Homeomorph.refl X) ^ winding) point =
      ((Homeomorph.refl X) ^ winding).toEquiv point from rfl,
    homeomorph_toEquiv_zpow]
  rw [show (Homeomorph.refl X).toEquiv = 1 from rfl, one_zpow]
  rfl

private theorem normalBoundary_sphereReflection_even_zpow
    (winding : Int) (point : UnitThreeSphere) :
    (sphereReflection ^ (2 * winding)) point = point := by
  rw [show (sphereReflection ^ (2 * winding)) =
      (sphereReflection ^ (2 : Int)) ^ winding by
        exact zpow_mul sphereReflection 2 winding]
  have hSquare : sphereReflection ^ (2 : Int) = 1 := by
    apply Homeomorph.ext
    intro current
    exact sphereReflection.apply_symm_apply current
  rw [hSquare, one_zpow]
  rfl

private theorem normalLatitudeCover_even_equivariant
    (winding : Int)
    (anchor : EffectiveThroatCover period hPeriod) (normal : Real) :
    normalLatitudeCover period hPeriod ((2 * winding) +ᵥ anchor) normal =
      (2 * winding) +ᵥ normalLatitudeCover period hPeriod anchor normal := by
  apply MappingTorusCover.ext
  · change equatorialLatitude
        (((Homeomorph.refl EquatorialTwoSphere) ^ (2 * winding))
          anchor.fiber) normal =
      (sphereReflection ^ (2 * winding))
        (equatorialLatitude anchor.fiber normal)
    rw [normalBoundary_refl_zpow_apply,
      normalBoundary_sphereReflection_even_zpow]
  · rfl

/-- Cover-level moving graph of a completed normal displacement. -/
def normalBoundaryC2GraphCoverMap
    (normal : NormalBoundaryC2JetCore period hPeriod)
    (parameter : Real)
    (point : OrientationBoundaryCover period hPeriod) :
    MappingTorusCover (reflectedSphereData period hPeriod) :=
  normalLatitudeCover period hPeriod
    (orientationDoubleCoverHomeomorph period hPeriod point)
    (Real.arctan
      (parameter * normalBoundaryC2JetCoreValueAt period hPeriod
        (mappingTorusMk (orientationDoubleData period hPeriod) point) normal))

theorem normalBoundaryC2GraphCoverMap_equivariant
    (normal : NormalBoundaryC2JetCore period hPeriod)
    (parameter : Real) (winding : Int)
    (point : OrientationBoundaryCover period hPeriod) :
    normalBoundaryC2GraphCoverMap period hPeriod normal parameter
        (winding +ᵥ point) =
      (2 * winding) +ᵥ
        normalBoundaryC2GraphCoverMap period hPeriod normal parameter point := by
  unfold normalBoundaryC2GraphCoverMap
  rw [orientationDoubleCover_even_equivariant]
  have hProjection :
      mappingTorusMk (orientationDoubleData period hPeriod) (winding +ᵥ point) =
        mappingTorusMk (orientationDoubleData period hPeriod) point :=
    (mappingTorusMk_isAddQuotientCoveringMap
      (orientationDoubleData period hPeriod)).map_vadd winding
  rw [hProjection]
  exact normalLatitudeCover_even_equivariant
    period hPeriod winding _ _

/-- Genuine moving graph on the full completed normal `C²` model. -/
def normalBoundaryC2Graph
    (normal : NormalBoundaryC2JetCore period hPeriod)
    (parameter : Real) :
    OrientationBoundary period hPeriod → EffectiveQuotient period hPeriod :=
  Quotient.map
    (normalBoundaryC2GraphCoverMap period hPeriod normal parameter)
    (fun first second hOrbit => by
      change AddAction.orbitRel Int (OrientationBoundaryCover period hPeriod)
        first second at hOrbit
      change AddAction.orbitRel Int
        (MappingTorusCover (reflectedSphereData period hPeriod))
        (normalBoundaryC2GraphCoverMap period hPeriod normal parameter first)
        (normalBoundaryC2GraphCoverMap period hPeriod normal parameter second)
      rw [AddAction.orbitRel_apply, AddAction.mem_orbit_iff] at hOrbit ⊢
      rcases hOrbit with ⟨winding, hWinding⟩
      refine ⟨2 * winding, ?_⟩
      rw [← normalBoundaryC2GraphCoverMap_equivariant]
      exact congrArg
        (normalBoundaryC2GraphCoverMap period hPeriod normal parameter) hWinding)

@[simp]
theorem normalBoundaryC2Graph_mk
    (normal : NormalBoundaryC2JetCore period hPeriod)
    (parameter : Real) (point : OrientationBoundaryCover period hPeriod) :
    normalBoundaryC2Graph period hPeriod normal parameter
        (mappingTorusMk (orientationDoubleData period hPeriod) point) =
      mappingTorusMk (reflectedSphereData period hPeriod)
        (normalBoundaryC2GraphCoverMap
          period hPeriod normal parameter point) :=
  rfl

/-- On the dense genuine-smooth subspace, the completed graph is exactly the
already constructed moving normal graph. -/
theorem normalBoundaryC2Graph_smooth
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : OrientationBoundary period hPeriod) :
    normalBoundaryC2Graph period hPeriod
        (smoothNormalDisplacementToBoundaryC2JetCore
          period hPeriod displacement) parameter boundary =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter) := by
  refine Quotient.inductionOn boundary ?_
  intro point
  rw [normalBoundaryC2Graph_mk]
  change mappingTorusMk (reflectedSphereData period hPeriod)
      (normalBoundaryC2GraphCoverMap period hPeriod
        (smoothNormalDisplacementToBoundaryC2JetCore
          period hPeriod displacement) parameter point) =
    normalGraph period hPeriod displacement parameter
      (orientationDoubleToThroat period hPeriod
        (mappingTorusMk (orientationDoubleData period hPeriod) point))
  rw [orientationDoubleToThroat_mk, normalGraph_mk]
  unfold normalBoundaryC2GraphCoverMap normalGraphCoverMap normalGraphCoordinate
  rw [normalBoundaryC2JetCoreValueAt_smooth,
    normalDisplacementOrientationScalar_mk]
  rfl

private theorem orientationDoubleCoverHomeomorph_deck
    (point : OrientationBoundaryCover period hPeriod) :
    orientationDoubleCoverHomeomorph period hPeriod
        (orientationDeckCover period hPeriod point) =
      (1 : Int) +ᵥ orientationDoubleCoverHomeomorph period hPeriod point := by
  apply MappingTorusCover.ext
  · simp only [orientationDoubleCoverHomeomorph_fiber,
      orientationDeckCover_fiber, vadd_fiber]
    simp [fixedEquatorData]
  · simp only [orientationDoubleCoverHomeomorph_time,
      orientationDeckCover_time, vadd_time]
    simp [fixedEquatorData]

/-- The completed graph is invariant under the residual orientation deck map,
so it still represents one physical moving throat rather than two copies. -/
@[simp]
theorem normalBoundaryC2Graph_deck
    (normal : NormalBoundaryC2JetCore period hPeriod)
    (parameter : Real) (boundary : OrientationBoundary period hPeriod) :
    normalBoundaryC2Graph period hPeriod normal parameter
        (orientationDeck period hPeriod boundary) =
      normalBoundaryC2Graph period hPeriod normal parameter boundary := by
  refine Quotient.inductionOn boundary ?_
  intro point
  rw [orientationDeck_mk, normalBoundaryC2Graph_mk,
    normalBoundaryC2Graph_mk]
  unfold normalBoundaryC2GraphCoverMap
  rw [orientationDoubleCoverHomeomorph_deck]
  change mappingTorusMk (reflectedSphereData period hPeriod)
      (normalLatitudeCover period hPeriod
        ((1 : Int) +ᵥ orientationDoubleCoverHomeomorph period hPeriod point)
        (Real.arctan (parameter *
          normalBoundaryC2JetCoreValueAt period hPeriod
            (orientationDeck period hPeriod
              (mappingTorusMk (orientationDoubleData period hPeriod) point))
            normal))) = _
  rw [normalBoundaryC2JetCoreValueAt_deck]
  simp only [mul_neg, Real.arctan_neg]
  rw [normalLatitudeCover_deck_generator_twist]
  simp only [neg_neg]
  exact (mappingTorusMk_isAddQuotientCoveringMap
    (reflectedSphereData period hPeriod)).map_vadd (1 : Int)

/-- The completed graph is continuous already at cover level. -/
theorem normalBoundaryC2GraphCoverMap_continuous
    (normal : NormalBoundaryC2JetCore period hPeriod)
    (parameter : Real) :
    Continuous
      (normalBoundaryC2GraphCoverMap period hPeriod normal parameter) := by
  have hProjection : Continuous
      (mappingTorusMk (orientationDoubleData period hPeriod)) :=
    (mappingTorusMk_isCoveringMap
      (orientationDoubleData period hPeriod)).isLocalHomeomorph.continuous
  have hValue : Continuous
      (fun point : OrientationBoundaryCover period hPeriod =>
        normalBoundaryC2JetCoreValueAt period hPeriod
          (mappingTorusMk (orientationDoubleData period hPeriod) point) normal) := by
    change Continuous
      (fun point : OrientationBoundaryCover period hPeriod =>
        (normalBoundaryC2JetCoreToContinuous period hPeriod normal)
          (mappingTorusMk (orientationDoubleData period hPeriod) point))
    exact (normalBoundaryC2JetCoreToContinuous
      period hPeriod normal).continuous.comp hProjection
  have hNormal : Continuous
      (fun point : OrientationBoundaryCover period hPeriod =>
        Real.arctan (parameter *
          normalBoundaryC2JetCoreValueAt period hPeriod
            (mappingTorusMk (orientationDoubleData period hPeriod) point)
            normal)) :=
    Real.continuous_arctan.comp (continuous_const.mul hValue)
  have hAnchor :=
    (orientationDoubleCoverHomeomorph period hPeriod).continuous
  have hLatitudeInput : Continuous
      (fun point : OrientationBoundaryCover period hPeriod =>
        ((orientationDoubleCoverHomeomorph period hPeriod point).fiber,
          Real.arctan (parameter *
            normalBoundaryC2JetCoreValueAt period hPeriod
              (mappingTorusMk (orientationDoubleData period hPeriod) point)
              normal))) :=
    ((continuous_fiber _).comp hAnchor).prodMk hNormal
  have hLatitude :=
    equatorialLatitude_joint_continuous.comp hLatitudeInput
  have hTime := (continuous_time _).comp hAnchor
  have hCover :=
    (coverHomeomorphProd
      (reflectedSphereData period hPeriod)).symm.continuous.comp
      (hLatitude.prodMk hTime)
  change Continuous
    (fun point : OrientationBoundaryCover period hPeriod =>
      (coverHomeomorphProd
        (reflectedSphereData period hPeriod)).symm
        (equatorialLatitude
            (orientationDoubleCoverHomeomorph period hPeriod point).fiber
            (Real.arctan (parameter *
              normalBoundaryC2JetCoreValueAt period hPeriod
                (mappingTorusMk (orientationDoubleData period hPeriod) point)
                normal)),
          (orientationDoubleCoverHomeomorph period hPeriod point).time))
  exact hCover

/-- The completed graph descends as a continuous global moving boundary. -/
theorem normalBoundaryC2Graph_continuous
    (normal : NormalBoundaryC2JetCore period hPeriod)
    (parameter : Real) :
    Continuous (normalBoundaryC2Graph period hPeriod normal parameter) := by
  apply (continuous_quotient_mk'.comp
    (normalBoundaryC2GraphCoverMap_continuous
      period hPeriod normal parameter)).quotient_lift

/-- Joint continuity of the completed moving graph before quotienting the
orientation boundary; the target is already the physical bulk quotient. -/
theorem normalBoundaryC2GraphCoverMap_joint_continuous :
    Continuous
      (fun current :
        (NormalBoundaryC2JetCore period hPeriod × Real) ×
          OrientationBoundaryCover period hPeriod =>
        mappingTorusMk (reflectedSphereData period hPeriod)
          (normalBoundaryC2GraphCoverMap period hPeriod
            current.1.1 current.1.2 current.2)) := by
  have hProjection : Continuous
      (mappingTorusMk (orientationDoubleData period hPeriod)) :=
    (mappingTorusMk_isCoveringMap
      (orientationDoubleData period hPeriod)).isLocalHomeomorph.continuous
  have hField : Continuous
      (fun current :
        (NormalBoundaryC2JetCore period hPeriod × Real) ×
          OrientationBoundaryCover period hPeriod =>
        normalBoundaryC2JetCoreToContinuous period hPeriod current.1.1) :=
    (normalBoundaryC2JetCoreToContinuous period hPeriod).continuous.comp
      (continuous_fst.comp continuous_fst)
  have hPoint : Continuous
      (fun current :
        (NormalBoundaryC2JetCore period hPeriod × Real) ×
          OrientationBoundaryCover period hPeriod =>
        mappingTorusMk (orientationDoubleData period hPeriod) current.2) :=
    hProjection.comp continuous_snd
  have hValue : Continuous
      (fun current :
        (NormalBoundaryC2JetCore period hPeriod × Real) ×
          OrientationBoundaryCover period hPeriod =>
        normalBoundaryC2JetCoreValueAt period hPeriod
          (mappingTorusMk (orientationDoubleData period hPeriod) current.2)
          current.1.1) := by
    change Continuous
      (fun current :
        (NormalBoundaryC2JetCore period hPeriod × Real) ×
          OrientationBoundaryCover period hPeriod =>
        (normalBoundaryC2JetCoreToContinuous period hPeriod current.1.1)
          (mappingTorusMk (orientationDoubleData period hPeriod) current.2))
    exact hField.eval hPoint
  have hNormal : Continuous
      (fun current :
        (NormalBoundaryC2JetCore period hPeriod × Real) ×
          OrientationBoundaryCover period hPeriod =>
        Real.arctan (current.1.2 *
          normalBoundaryC2JetCoreValueAt period hPeriod
            (mappingTorusMk (orientationDoubleData period hPeriod) current.2)
            current.1.1)) :=
    Real.continuous_arctan.comp
      ((continuous_snd.comp continuous_fst).mul hValue)
  have hAnchor : Continuous
      (fun current :
        (NormalBoundaryC2JetCore period hPeriod × Real) ×
          OrientationBoundaryCover period hPeriod =>
        orientationDoubleCoverHomeomorph period hPeriod current.2) :=
    (orientationDoubleCoverHomeomorph period hPeriod).continuous.comp
      continuous_snd
  have hLatitudeInput : Continuous
      (fun current :
        (NormalBoundaryC2JetCore period hPeriod × Real) ×
          OrientationBoundaryCover period hPeriod =>
        ((orientationDoubleCoverHomeomorph period hPeriod current.2).fiber,
          Real.arctan (current.1.2 *
            normalBoundaryC2JetCoreValueAt period hPeriod
              (mappingTorusMk (orientationDoubleData period hPeriod) current.2)
              current.1.1))) :=
    ((continuous_fiber _).comp hAnchor).prodMk hNormal
  have hLatitude :=
    equatorialLatitude_joint_continuous.comp hLatitudeInput
  have hTime := (continuous_time _).comp hAnchor
  have hCover :=
    (coverHomeomorphProd
      (reflectedSphereData period hPeriod)).symm.continuous.comp
      (hLatitude.prodMk hTime)
  exact continuous_quotient_mk'.comp (hCover.congr fun _ => rfl)

/-- The moving boundary varies jointly continuously in the full completed
normal model, the real parameter, and the boundary point. -/
theorem normalBoundaryC2Graph_joint_continuous :
    Continuous
      (fun current :
        (NormalBoundaryC2JetCore period hPeriod × Real) ×
          OrientationBoundary period hPeriod =>
        normalBoundaryC2Graph period hPeriod
          current.1.1 current.1.2 current.2) := by
  have hParameters : IsOpenQuotientMap
      (id : (NormalBoundaryC2JetCore period hPeriod × Real) →
        NormalBoundaryC2JetCore period hPeriod × Real) :=
    IsOpenQuotientMap.id
  have hBoundary :=
    (mappingTorusMk_isAddQuotientCoveringMap
      (orientationDoubleData period hPeriod)).isOpenQuotientMap
  have hProduct := hParameters.prodMap hBoundary
  apply hProduct.continuous_comp_iff.mp
  apply (normalBoundaryC2GraphCoverMap_joint_continuous
    period hPeriod).congr
  intro current
  simp only [Function.comp_apply, Prod.map_apply, id_eq]
  exact (normalBoundaryC2Graph_mk period hPeriod
    current.1.1 current.1.2 current.2).symm

/-- The physical graph obtained by factoring the orientation-double graph
through its two-sheeted projection.  The following theorem proves that the
noncomputable representative choice is immaterial. -/
noncomputable def normalBoundaryC2ThroatGraph
    (normal : NormalBoundaryC2JetCore period hPeriod)
    (parameter : Real) :
    EffectiveThroat period hPeriod → EffectiveQuotient period hPeriod :=
  fun throat =>
    normalBoundaryC2Graph period hPeriod normal parameter
      (Function.surjInv
        (orientationDoubleToThroat_surjective period hPeriod) throat)

@[simp]
theorem normalBoundaryC2ThroatGraph_orientationDouble
    (normal : NormalBoundaryC2JetCore period hPeriod)
    (parameter : Real) (boundary : OrientationBoundary period hPeriod) :
    normalBoundaryC2ThroatGraph period hPeriod normal parameter
        (orientationDoubleToThroat period hPeriod boundary) =
      normalBoundaryC2Graph period hPeriod normal parameter boundary := by
  let chosen := Function.surjInv
    (orientationDoubleToThroat_surjective period hPeriod)
    (orientationDoubleToThroat period hPeriod boundary)
  have hChosen :
      orientationDoubleToThroat period hPeriod chosen =
        orientationDoubleToThroat period hPeriod boundary :=
    Function.surjInv_eq
      (orientationDoubleToThroat_surjective period hPeriod) _
  have hFiber := (orientationDouble_fiber_iff period hPeriod
    chosen boundary).mp hChosen
  change normalBoundaryC2Graph period hPeriod normal parameter chosen = _
  rcases hFiber with hSame | hDeck
  · rw [hSame]
  · rw [hDeck, normalBoundaryC2Graph_deck]

theorem normalBoundaryC2ThroatGraph_continuous
    (normal : NormalBoundaryC2JetCore period hPeriod)
    (parameter : Real) :
    Continuous
      (normalBoundaryC2ThroatGraph period hPeriod normal parameter) := by
  apply (orientationDoubleToThroat_isQuotientMap
    period hPeriod).continuous_iff.mpr
  apply (normalBoundaryC2Graph_continuous
    period hPeriod normal parameter).congr
  intro boundary
  exact (normalBoundaryC2ThroatGraph_orientationDouble
    period hPeriod normal parameter boundary).symm

/-- On genuine smooth normal sections, the physical descended graph is
definitionally the original graph used by the variational construction. -/
theorem normalBoundaryC2ThroatGraph_smooth
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (throat : EffectiveThroat period hPeriod) :
    normalBoundaryC2ThroatGraph period hPeriod
        (smoothNormalDisplacementToBoundaryC2JetCore
          period hPeriod displacement) parameter throat =
      normalGraph period hPeriod displacement parameter throat := by
  obtain ⟨boundary, rfl⟩ :=
    orientationDoubleToThroat_surjective period hPeriod throat
  rw [normalBoundaryC2ThroatGraph_orientationDouble,
    normalBoundaryC2Graph_smooth]
  rfl

/-- Joint continuity survives the physical descent to the original throat. -/
theorem normalBoundaryC2ThroatGraph_joint_continuous :
    Continuous
      (fun current :
        (NormalBoundaryC2JetCore period hPeriod × Real) ×
          EffectiveThroat period hPeriod =>
        normalBoundaryC2ThroatGraph period hPeriod
          current.1.1 current.1.2 current.2) := by
  have hParameters : IsOpenQuotientMap
      (id : (NormalBoundaryC2JetCore period hPeriod × Real) →
        NormalBoundaryC2JetCore period hPeriod × Real) :=
    IsOpenQuotientMap.id
  have hBoundary :=
    (orientationDoubleToThroat_isAddQuotientCoveringMap
      period hPeriod).isOpenQuotientMap
  have hProduct := hParameters.prodMap hBoundary
  apply hProduct.continuous_comp_iff.mp
  apply (normalBoundaryC2Graph_joint_continuous period hPeriod).congr
  intro current
  exact (normalBoundaryC2ThroatGraph_orientationDouble period hPeriod
    current.1.1 current.1.2 current.2).symm

/-! ## Canonical vertical lift along the genuine moving graph -/

local instance canonicalTubularSphereFinrank :
    Fact (Module.finrank Real EuclideanR3 = 2 + 1) := ⟨by simp⟩

local instance canonicalTubularTargetSphereFinrank :
    Fact (Module.finrank Real EuclideanR4 = 3 + 1) := ⟨by simp⟩

local instance canonicalTubularSphereChartedSpace :
    ChartedSpace (EuclideanSpace Real (Fin 2))
      (Metric.sphere (0 : EuclideanR3) 1) := inferInstance

local instance canonicalTubularTargetSphereChartedSpace :
    ChartedSpace (EuclideanSpace Real (Fin 3)) UnitThreeSphere := inferInstance

local instance canonicalTubularBaseChartedSpace :
    ChartedSpace CanonicalLatitudeBaseModel CanonicalLatitudeBase := inferInstance

local instance canonicalTubularParameterChartedSpace :
    ChartedSpace CanonicalLatitudeParameterModel CanonicalLatitudeParameter :=
  inferInstance

/-- Reassociate the pre-existing canonical tubular parameters with the
equatorial tubular diffeomorphism parameters. -/
private def canonicalTubularReassociation :
    (CanonicalLatitudeBase × equatorialTubularNormalOpen) ≃ₘ^∞⟮
      canonicalLatitudeParameterModelWithCorners,
      canonicalLatitudeParameterModelWithCorners⟯
      ((EquatorialTwoSphere × equatorialTubularNormalOpen) × Real) where
  toFun parameter :=
    ((equatorialTwoSphereHomeomorph.symm parameter.1.1, parameter.2),
      parameter.1.2)
  invFun parameter :=
    ((equatorialTwoSphereHomeomorph parameter.1.1, parameter.2),
      parameter.1.2)
  left_inv parameter := by
    rcases parameter with ⟨⟨sphere, time⟩, normal⟩
    simp
  right_inv parameter := by
    rcases parameter with ⟨⟨sphere, normal⟩, time⟩
    simp
  contMDiff_toFun := by
    have hSphere : ContMDiff canonicalLatitudeParameterModelWithCorners
        (modelWithCornersSelf Real (EuclideanSpace Real (Fin 2))) ∞
        (fun parameter : CanonicalLatitudeBase × equatorialTubularNormalOpen =>
          equatorialTwoSphereHomeomorph.symm parameter.1.1) :=
      (chartedSpacePullback_invFun_contMDiff
        (modelWithCornersSelf Real (EuclideanSpace Real (Fin 2))) ∞
        equatorialTwoSphereHomeomorph).comp
          (contMDiff_fst.comp contMDiff_fst)
    exact (hSphere.prodMk contMDiff_snd).prodMk
      (contMDiff_snd.comp contMDiff_fst)
  contMDiff_invFun := by
    have hSphere : ContMDiff canonicalLatitudeParameterModelWithCorners
        (modelWithCornersSelf Real (EuclideanSpace Real (Fin 2))) ∞
        (fun parameter :
          (EquatorialTwoSphere × equatorialTubularNormalOpen) × Real =>
          equatorialTwoSphereHomeomorph parameter.1.1) :=
      (chartedSpacePullback_toFun_contMDiff
        (modelWithCornersSelf Real (EuclideanSpace Real (Fin 2))) ∞
        equatorialTwoSphereHomeomorph).comp
          (contMDiff_fst.comp contMDiff_fst)
    exact (hSphere.prodMk contMDiff_snd).prodMk
      (contMDiff_snd.comp contMDiff_fst)

/-- Canonical tubular parameters mapped diffeomorphically to the already
implemented open spherical band coordinates. -/
private def canonicalTubularToBandSpacetime :
    (CanonicalLatitudeBase × equatorialTubularNormalOpen) ≃ₘ^∞⟮
      canonicalLatitudeParameterModelWithCorners, coverModelWithCorners⟯
      (equatorialSphericalBandOpen × Real) :=
  canonicalTubularReassociation.trans
    (equatorialTubularDiffeomorph.prodCongr
      (Diffeomorph.refl (modelWithCornersSelf Real Real) Real ∞))

private theorem canonicalLatitudeTubularPhysicalMap_eq_band
    (parameter : CanonicalLatitudeBase × equatorialTubularNormalOpen) :
    canonicalLatitudeTubularPhysicalMap period hPeriod parameter =
      tubularBandSpacetimeToAmbient period hPeriod
        (canonicalTubularToBandSpacetime parameter) := by
  rfl

/-- The physical canonical latitude collar is a genuine local
diffeomorphism throughout the open tubular band. -/
theorem canonicalLatitudeTubularPhysicalMap_isLocalDiffeomorph :
    IsLocalDiffeomorph canonicalLatitudeParameterModelWithCorners
      coverModelWithCorners ∞
      (fun parameter : CanonicalLatitudeBase × equatorialTubularNormalOpen =>
        canonicalLatitudeTubularPhysicalMap period hPeriod parameter) := by
  have hFunction :
      (fun parameter : CanonicalLatitudeBase × equatorialTubularNormalOpen =>
        canonicalLatitudeTubularPhysicalMap period hPeriod parameter) =
      tubularBandSpacetimeToAmbient period hPeriod ∘
        canonicalTubularToBandSpacetime := by
    funext parameter
    exact canonicalLatitudeTubularPhysicalMap_eq_band period hPeriod parameter
  rw [hFunction]
  intro parameter
  exact canonicalTubularToBandSpacetime.isLocalDiffeomorph parameter
    |>.comp coverModelWithCorners _
      (tubularBandSpacetimeToAmbient_isLocalDiffeomorph period hPeriod
        (canonicalTubularToBandSpacetime parameter))

/-- Include the open latitude normal band into the unrestricted collar. -/
def canonicalLatitudeTubularParameterInclusion
    (parameter : CanonicalLatitudeBase × equatorialTubularNormalOpen) :
    CanonicalLatitudeParameter :=
  (parameter.1, parameter.2.1)

theorem canonicalLatitudeTubularParameterInclusion_isLocalDiffeomorph :
    IsLocalDiffeomorph canonicalLatitudeParameterModelWithCorners
      canonicalLatitudeParameterModelWithCorners ∞
      canonicalLatitudeTubularParameterInclusion := by
  intro point
  let baseMap :=
    (Diffeomorph.refl canonicalLatitudeBaseModelWithCorners
      CanonicalLatitudeBase ∞).toPartialDiffeomorph
  let normalMap := openSubtypePartialDiffeomorph
    (modelWithCornersSelf Real Real) equatorialTubularNormalOpen point.2
  refine ⟨partialDiffeomorphProd baseMap normalMap,
    ⟨Set.mem_univ _, Set.mem_univ _⟩, ?_⟩
  rintro ⟨base, normal⟩ -
  rfl

/-- On the genuine tubular band the unrestricted canonical collar derivative
is injective. -/
theorem canonicalLatitudeCollarMap_mfderiv_injective_of_mem_band
    (base : CanonicalLatitudeBase) (normal : Real)
    (hNormal : normal ∈ equatorialTubularNormalOpen) :
    Function.Injective
      (mfderiv canonicalLatitudeParameterModelWithCorners
        coverModelWithCorners (canonicalLatitudeCollarMap period hPeriod)
        (base, normal)) := by
  let point : CanonicalLatitudeBase × equatorialTubularNormalOpen :=
    (base, ⟨normal, hNormal⟩)
  let inclusion := canonicalLatitudeTubularParameterInclusion
  have hInclusion :=
    canonicalLatitudeTubularParameterInclusion_isLocalDiffeomorph point
  have hCollar : MDifferentiableAt canonicalLatitudeParameterModelWithCorners
      coverModelWithCorners (canonicalLatitudeCollarMap period hPeriod)
      (inclusion point) :=
    (canonicalLatitudeCollar_contMDiff period hPeriod).mdifferentiableAt (by simp)
  have hInclusionDiff : MDifferentiableAt canonicalLatitudeParameterModelWithCorners
      canonicalLatitudeParameterModelWithCorners inclusion point :=
    hInclusion.mdifferentiableAt (by simp)
  have hComp := mfderiv_comp point hCollar hInclusionDiff
  have hMap : canonicalLatitudeCollarMap period hPeriod ∘ inclusion =
      (fun current : CanonicalLatitudeBase × equatorialTubularNormalOpen =>
        canonicalLatitudeTubularPhysicalMap period hPeriod current) := by
    rfl
  rw [hMap] at hComp
  let inclusionDerivative :=
    hInclusion.mfderivToContinuousLinearEquiv (by simp)
  have hInclusionDerivative :
      (inclusionDerivative : _ →L[Real] _) =
        mfderiv canonicalLatitudeParameterModelWithCorners
          canonicalLatitudeParameterModelWithCorners inclusion point :=
    hInclusion.mfderivToContinuousLinearEquiv_coe (by simp)
  have hRestrictedInjective : Function.Injective
      (mfderiv canonicalLatitudeParameterModelWithCorners
        coverModelWithCorners
        (fun current : CanonicalLatitudeBase × equatorialTubularNormalOpen =>
          canonicalLatitudeTubularPhysicalMap period hPeriod current) point) := by
    rw [← (canonicalLatitudeTubularPhysicalMap_isLocalDiffeomorph
      period hPeriod point).mfderivToContinuousLinearEquiv_coe (by simp)]
    exact ((canonicalLatitudeTubularPhysicalMap_isLocalDiffeomorph
      period hPeriod point).mfderivToContinuousLinearEquiv (by simp)).injective
  intro first second hEqual
  obtain ⟨firstLift, hFirstLift⟩ := inclusionDerivative.surjective first
  obtain ⟨secondLift, hSecondLift⟩ := inclusionDerivative.surjective second
  rw [← hFirstLift, ← hSecondLift]
  apply congrArg inclusionDerivative
  apply hRestrictedInjective
  rw [hComp]
  change mfderiv canonicalLatitudeParameterModelWithCorners coverModelWithCorners
      (canonicalLatitudeCollarMap period hPeriod) (inclusion point)
        (mfderiv canonicalLatitudeParameterModelWithCorners
          canonicalLatitudeParameterModelWithCorners inclusion point firstLift) =
    mfderiv canonicalLatitudeParameterModelWithCorners coverModelWithCorners
      (canonicalLatitudeCollarMap period hPeriod) (inclusion point)
        (mfderiv canonicalLatitudeParameterModelWithCorners
          canonicalLatitudeParameterModelWithCorners inclusion point secondLift)
  rw [← hInclusionDerivative]
  change inclusionDerivative.toContinuousLinearMap firstLift = first at hFirstLift
  change inclusionDerivative.toContinuousLinearMap secondLift = second at hSecondLift
  rw [hFirstLift, hSecondLift]
  rw [show inclusion point = (base, normal) by rfl]
  exact hEqual

/-- The existing latitude anchor is a smooth coordinate equivalence onto the
fixed-throat cover. -/
def canonicalLatitudeAnchorDiffeomorph :
    CanonicalLatitudeBase ≃ₘ^∞⟮canonicalLatitudeBaseModelWithCorners,
      throatCoverModelWithCorners⟯ EffectiveThroatCover period hPeriod where
  toFun := canonicalLatitudeAnchor period hPeriod
  invFun anchor :=
    (equatorialTwoSphereHomeomorph anchor.fiber, anchor.time)
  left_inv base := by
    rcases base with ⟨sphere, time⟩
    simp [canonicalLatitudeAnchor]
  right_inv anchor := by
    apply MappingTorusCover.ext
    · simp [canonicalLatitudeAnchor]
    · simp [canonicalLatitudeAnchor]
  contMDiff_toFun := by
    have hSphere : ContMDiff canonicalLatitudeBaseModelWithCorners
        (modelWithCornersSelf Real (EuclideanSpace Real (Fin 2))) ∞
        (fun base : CanonicalLatitudeBase =>
          equatorialTwoSphereHomeomorph.symm base.1) :=
      (chartedSpacePullback_invFun_contMDiff
        (modelWithCornersSelf Real (EuclideanSpace Real (Fin 2))) ∞
        equatorialTwoSphereHomeomorph).comp contMDiff_fst
    have hProduct : ContMDiff canonicalLatitudeBaseModelWithCorners
        throatCoverModelWithCorners ∞
        (fun base : CanonicalLatitudeBase =>
          (equatorialTwoSphereHomeomorph.symm base.1, base.2)) :=
      hSphere.prodMk contMDiff_snd
    exact (chartedSpacePullback_invFun_contMDiff
      throatCoverModelWithCorners ∞
      (coverHomeomorphProd (fixedEquatorData period hPeriod))).comp hProduct
  contMDiff_invFun := by
    have hCoordinates : ContMDiff throatCoverModelWithCorners
        throatCoverModelWithCorners ∞
        (coverHomeomorphProd (fixedEquatorData period hPeriod)) :=
      chartedSpacePullback_toFun_contMDiff throatCoverModelWithCorners ∞
        (coverHomeomorphProd (fixedEquatorData period hPeriod))
    have hSphere : ContMDiff throatCoverModelWithCorners
        (modelWithCornersSelf Real (EuclideanSpace Real (Fin 2))) ∞
        (fun anchor : EffectiveThroatCover period hPeriod => anchor.fiber) :=
      contMDiff_fst.comp hCoordinates
    have hTime : ContMDiff throatCoverModelWithCorners
        (modelWithCornersSelf Real Real) ∞
        (fun anchor : EffectiveThroatCover period hPeriod => anchor.time) :=
      contMDiff_snd.comp hCoordinates
    exact ((chartedSpacePullback_toFun_contMDiff
      (modelWithCornersSelf Real (EuclideanSpace Real (Fin 2))) ∞
      equatorialTwoSphereHomeomorph).comp hSphere).prodMk hTime

theorem canonicalLatitudeThroatMap_isLocalDiffeomorph :
    IsLocalDiffeomorph canonicalLatitudeBaseModelWithCorners
      throatCoverModelWithCorners ∞
      (canonicalLatitudeThroatMap period hPeriod) := by
  have hFunction : canonicalLatitudeThroatMap period hPeriod =
      mappingTorusMk (fixedEquatorData period hPeriod) ∘
        canonicalLatitudeAnchorDiffeomorph period hPeriod := by
    rfl
  rw [hFunction]
  intro base
  exact (canonicalLatitudeAnchorDiffeomorph period hPeriod).isLocalDiffeomorph base
    |>.comp throatCoverModelWithCorners _
      (fixedThroat_projection_isLocalDiffeomorph_smooth period hPeriod
        (canonicalLatitudeAnchorDiffeomorph period hPeriod base))

/-- Product collar parameter of the actual normal graph in one canonical
latitude trivialization. -/
def canonicalLatitudeNormalGraphParameter
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (base : CanonicalLatitudeBase) :
    CanonicalLatitudeParameter :=
  (base, (normalGraphCoordinate period hPeriod displacement parameter
    (canonicalLatitudeAnchor period hPeriod base)).1)

theorem canonicalLatitudeNormalGraphParameter_contMDiff
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) :
    ContMDiff canonicalLatitudeBaseModelWithCorners
      canonicalLatitudeParameterModelWithCorners ∞
      (canonicalLatitudeNormalGraphParameter period hPeriod displacement
        parameter) := by
  have hAnchor : ContMDiff canonicalLatitudeBaseModelWithCorners
      throatCoverModelWithCorners ∞
      (canonicalLatitudeAnchor period hPeriod) :=
    (canonicalLatitudeAnchorDiffeomorph period hPeriod).contMDiff
  have hInput : ContMDiff canonicalLatitudeBaseModelWithCorners
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real)) ∞
      (fun base : CanonicalLatitudeBase =>
        (canonicalLatitudeAnchor period hPeriod base, parameter)) :=
    hAnchor.prodMk contMDiff_const
  have hNormal : ContMDiff canonicalLatitudeBaseModelWithCorners
      (modelWithCornersSelf Real Real) ∞
      (fun base : CanonicalLatitudeBase =>
        (normalGraphCoordinate period hPeriod displacement parameter
          (canonicalLatitudeAnchor period hPeriod base)).1) :=
    (normalGraphCoordinateValue_joint_contMDiff period hPeriod displacement).comp
      hInput
  exact contMDiff_id.prodMk hNormal

theorem normalGraph_comp_canonicalLatitudeThroatMap
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) :
    normalGraph period hPeriod displacement parameter ∘
        canonicalLatitudeThroatMap period hPeriod =
      canonicalLatitudeCollarMap period hPeriod ∘
        canonicalLatitudeNormalGraphParameter period hPeriod displacement
          parameter := by
  funext base
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem canonicalLatitudeNormalGraphParameter_mfderiv_fst
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (base : CanonicalLatitudeBase) :
    (ContinuousLinearMap.fst Real
      (TangentSpace canonicalLatitudeBaseModelWithCorners base)
      (TangentSpace (modelWithCornersSelf Real Real)
        (normalGraphCoordinate period hPeriod displacement parameter
          (canonicalLatitudeAnchor period hPeriod base)).1)).comp
      (mfderiv canonicalLatitudeBaseModelWithCorners
        canonicalLatitudeParameterModelWithCorners
        (canonicalLatitudeNormalGraphParameter period hPeriod displacement
          parameter) base) =
      ContinuousLinearMap.id Real
        (TangentSpace canonicalLatitudeBaseModelWithCorners base) := by
  have hGraph :=
    (canonicalLatitudeNormalGraphParameter_contMDiff period hPeriod
      displacement parameter).mdifferentiableAt (x := base) (by simp)
  have hComp := mfderiv_comp base mdifferentiableAt_fst hGraph
  have hFunction : Prod.fst ∘
      canonicalLatitudeNormalGraphParameter period hPeriod displacement
        parameter = id := by
    rfl
  rw [hFunction, mfderiv_id, mfderiv_fst] at hComp
  simpa [canonicalLatitudeNormalGraphParameter] using hComp.symm

set_option backward.isDefEq.respectTransparency false in
theorem mfderiv_canonicalLatitudeCollarMap_vertical
    (base : CanonicalLatitudeBase) (normal : Real) :
    mfderiv canonicalLatitudeParameterModelWithCorners coverModelWithCorners
        (canonicalLatitudeCollarMap period hPeriod) (base, normal) (0, 1) =
      canonicalLatitudeNormalVector period hPeriod base normal := by
  have hCollar := (canonicalLatitudeCollar_contMDiff period hPeriod)
    |>.mdifferentiableAt (x := (base, normal)) (by simp)
  rw [mfderiv_prod_eq_add_apply hCollar]
  rw [map_zero, zero_add]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The canonical vertical vector cannot lie in the tangent range of the
actual moving graph. -/
theorem canonicalLatitudeNormalVector_transverse_normalGraph
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (base : CanonicalLatitudeBase) :
    NormalGraphTransverseVectorAt period hPeriod displacement parameter
      (canonicalLatitudeThroatMap period hPeriod base)
      (canonicalLatitudeNormalVector period hPeriod base
        (normalGraphCoordinate period hPeriod displacement parameter
          (canonicalLatitudeAnchor period hPeriod base)).1) := by
  unfold NormalGraphTransverseVectorAt
  rintro ⟨tangent, hTangent⟩
  let graphParameter :=
    canonicalLatitudeNormalGraphParameter period hPeriod displacement parameter
  let normal :=
    (normalGraphCoordinate period hPeriod displacement parameter
      (canonicalLatitudeAnchor period hPeriod base)).1
  let hThroat := canonicalLatitudeThroatMap_isLocalDiffeomorph
    period hPeriod base
  let throatDerivative := hThroat.mfderivToContinuousLinearEquiv (by simp)
  obtain ⟨baseTangent, hBaseTangent⟩ := throatDerivative.surjective tangent
  have hThroatDerivative :
      (throatDerivative : _ →L[Real] _) =
        mfderiv canonicalLatitudeBaseModelWithCorners
          throatCoverModelWithCorners
          (canonicalLatitudeThroatMap period hPeriod) base :=
    hThroat.mfderivToContinuousLinearEquiv_coe (by simp)
  change throatDerivative.toContinuousLinearMap baseTangent = tangent
    at hBaseTangent
  have hGraphParameterDiff : MDifferentiableAt
      canonicalLatitudeBaseModelWithCorners
      canonicalLatitudeParameterModelWithCorners graphParameter base :=
    (canonicalLatitudeNormalGraphParameter_contMDiff period hPeriod
      displacement parameter).mdifferentiableAt (by simp)
  have hCollarDiff : MDifferentiableAt
      canonicalLatitudeParameterModelWithCorners coverModelWithCorners
      (canonicalLatitudeCollarMap period hPeriod) (graphParameter base) :=
    (canonicalLatitudeCollar_contMDiff period hPeriod).mdifferentiableAt (by simp)
  have hThroatDiff : MDifferentiableAt canonicalLatitudeBaseModelWithCorners
      throatCoverModelWithCorners (canonicalLatitudeThroatMap period hPeriod)
      base := hThroat.mdifferentiableAt (by simp)
  have hNormalGraphDiff : MDifferentiableAt throatCoverModelWithCorners
      coverModelWithCorners (normalGraph period hPeriod displacement parameter)
      (canonicalLatitudeThroatMap period hPeriod base) :=
    (normalGraph_fixedParameter_contMDiff period hPeriod displacement parameter)
      |>.mdifferentiableAt (by simp)
  have hCollarComp := mfderiv_comp base hCollarDiff hGraphParameterDiff
  have hGraphComp := mfderiv_comp base hNormalGraphDiff hThroatDiff
  have hComposite :
      normalGraph period hPeriod displacement parameter ∘
          canonicalLatitudeThroatMap period hPeriod =
        canonicalLatitudeCollarMap period hPeriod ∘ graphParameter :=
    normalGraph_comp_canonicalLatitudeThroatMap period hPeriod displacement
      parameter
  have hImage :
      mfderiv canonicalLatitudeParameterModelWithCorners coverModelWithCorners
          (canonicalLatitudeCollarMap period hPeriod) (graphParameter base)
          (mfderiv canonicalLatitudeBaseModelWithCorners
            canonicalLatitudeParameterModelWithCorners graphParameter base
            baseTangent) =
        canonicalLatitudeNormalVector period hPeriod base normal := by
    calc
      _ = mfderiv canonicalLatitudeBaseModelWithCorners coverModelWithCorners
          (canonicalLatitudeCollarMap period hPeriod ∘ graphParameter) base
          baseTangent := by
            simpa using (DFunLike.congr_fun hCollarComp baseTangent).symm
      _ = mfderiv canonicalLatitudeBaseModelWithCorners coverModelWithCorners
          (normalGraph period hPeriod displacement parameter ∘
            canonicalLatitudeThroatMap period hPeriod) base baseTangent := by
            rw [hComposite]
      _ = mfderiv throatCoverModelWithCorners coverModelWithCorners
          (normalGraph period hPeriod displacement parameter)
          (canonicalLatitudeThroatMap period hPeriod base)
          (mfderiv canonicalLatitudeBaseModelWithCorners
            throatCoverModelWithCorners
            (canonicalLatitudeThroatMap period hPeriod) base baseTangent) := by
              simpa using DFunLike.congr_fun hGraphComp baseTangent
      _ = mfderiv throatCoverModelWithCorners coverModelWithCorners
          (normalGraph period hPeriod displacement parameter)
          (canonicalLatitudeThroatMap period hPeriod base) tangent := by
            rw [← hThroatDerivative, hBaseTangent]
      _ = canonicalLatitudeNormalVector period hPeriod base normal :=
        hTangent
  have hVertical :
      mfderiv canonicalLatitudeParameterModelWithCorners coverModelWithCorners
          (canonicalLatitudeCollarMap period hPeriod) (graphParameter base)
          (0, 1) =
        canonicalLatitudeNormalVector period hPeriod base normal := by
    simpa [graphParameter, normal,
      canonicalLatitudeNormalGraphParameter] using
      (mfderiv_canonicalLatitudeCollarMap_vertical period hPeriod base normal)
  have hParameterTangent :=
    canonicalLatitudeCollarMap_mfderiv_injective_of_mem_band period hPeriod
      base normal
      (normalGraphCoordinate period hPeriod displacement parameter
        (canonicalLatitudeAnchor period hPeriod base)).2
      (hImage.trans hVertical.symm)
  let firstProjection := ContinuousLinearMap.fst Real
    (TangentSpace canonicalLatitudeBaseModelWithCorners base)
    (TangentSpace (modelWithCornersSelf Real Real) normal)
  have hFirstDerivative :=
    canonicalLatitudeNormalGraphParameter_mfderiv_fst period hPeriod
      displacement parameter base
  have hProjected := congrArg firstProjection hParameterTangent
  have hProjected' :
      (firstProjection.comp
        (mfderiv canonicalLatitudeBaseModelWithCorners
          canonicalLatitudeParameterModelWithCorners graphParameter base))
          baseTangent = firstProjection (0, 1) := by
    exact hProjected
  rw [show firstProjection.comp
      (mfderiv canonicalLatitudeBaseModelWithCorners
        canonicalLatitudeParameterModelWithCorners graphParameter base) =
        ContinuousLinearMap.id Real
          (TangentSpace canonicalLatitudeBaseModelWithCorners base) by
      simpa [firstProjection, graphParameter, normal] using hFirstDerivative]
    at hProjected'
  have hBaseZero : baseTangent = 0 := by
    simpa [firstProjection] using hProjected'
  rw [hBaseZero, map_zero] at hParameterTangent
  let secondProjection := ContinuousLinearMap.snd Real
    (TangentSpace canonicalLatitudeBaseModelWithCorners base)
    (TangentSpace (modelWithCornersSelf Real Real) normal)
  have hImpossible := congrArg secondProjection hParameterTangent
  change (0 : Real) = 1 at hImpossible
  norm_num at hImpossible

/-- Existing canonical-latitude parameter selected by a point of the
orientation-double cover and the actual graph coordinate. -/
def normalGraphCanonicalLatitudeParameterCover
    (displacement : SmoothNormalDisplacement period hPeriod)
    (current : OrientationBoundaryCover period hPeriod × Real) :
    CanonicalLatitudeParameter :=
  let anchor := orientationDoubleCoverHomeomorph period hPeriod current.1
  ((equatorialTwoSphereHomeomorph anchor.fiber, anchor.time),
    (normalGraphCoordinate period hPeriod displacement current.2 anchor).1)

/-- The already existing latitude tangent, evaluated at the actual graph
coordinate and pulled to the orientation-double cover. -/
def normalGraphCanonicalLatitudeLiftCover
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (point : OrientationBoundaryCover period hPeriod) :
    TangentBundle coverModelWithCorners (EffectiveQuotient period hPeriod) :=
  let anchor := orientationDoubleCoverHomeomorph period hPeriod point
  let normal :=
    (normalGraphCoordinate period hPeriod displacement parameter anchor).1
  ⟨quotientNormalLatitude period hPeriod anchor normal,
    mfderiv (modelWithCornersSelf Real Real) coverModelWithCorners
      (quotientNormalLatitude period hPeriod anchor) normal 1⟩

/-- The direct graph lift is exactly the pre-existing jointly smooth canonical
latitude lift evaluated on the preceding parameter. -/
theorem normalGraphCanonicalLatitudeLiftCover_eq_canonical
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (point : OrientationBoundaryCover period hPeriod) :
    normalGraphCanonicalLatitudeLiftCover period hPeriod displacement parameter
        point =
      canonicalLatitudeNormalLift period hPeriod
        (normalGraphCanonicalLatitudeParameterCover period hPeriod displacement
          (point, parameter)) := by
  let anchor := orientationDoubleCoverHomeomorph period hPeriod point
  have hCanonicalAnchor :
      canonicalLatitudeAnchor period hPeriod
          (equatorialTwoSphereHomeomorph anchor.fiber, anchor.time) = anchor := by
    apply MappingTorusCover.ext
    · simp [canonicalLatitudeAnchor, anchor]
    · simp [canonicalLatitudeAnchor, anchor]
  unfold normalGraphCanonicalLatitudeLiftCover
    normalGraphCanonicalLatitudeParameterCover canonicalLatitudeNormalLift
  change
    (⟨quotientNormalLatitude period hPeriod anchor
        (normalGraphCoordinate period hPeriod displacement parameter anchor).1,
      mfderiv (modelWithCornersSelf Real Real) coverModelWithCorners
        (quotientNormalLatitude period hPeriod anchor)
        (normalGraphCoordinate period hPeriod displacement parameter anchor).1 1⟩ :
      TangentBundle coverModelWithCorners (EffectiveQuotient period hPeriod)) =
    ⟨quotientNormalLatitude period hPeriod
        (canonicalLatitudeAnchor period hPeriod
          (equatorialTwoSphereHomeomorph anchor.fiber, anchor.time))
        (normalGraphCoordinate period hPeriod displacement parameter anchor).1,
      canonicalLatitudeNormalVector period hPeriod
        (equatorialTwoSphereHomeomorph anchor.fiber, anchor.time)
        (normalGraphCoordinate period hPeriod displacement parameter anchor).1⟩
  rw [hCanonicalAnchor]
  rfl

/-- The canonical-latitude parameter varies jointly smoothly in the boundary
point and graph parameter. -/
theorem normalGraphCanonicalLatitudeParameterCover_contMDiff
    (displacement : SmoothNormalDisplacement period hPeriod) :
    ContMDiff
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      canonicalLatitudeParameterModelWithCorners ∞
      (normalGraphCanonicalLatitudeParameterCover period hPeriod displacement) := by
  have hAnchor : ContMDiff
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      throatCoverModelWithCorners ∞
      (fun current : OrientationBoundaryCover period hPeriod × Real =>
        orientationDoubleCoverHomeomorph period hPeriod current.1) :=
    (orientationDoubleCoverHomeomorph_contMDiff period hPeriod).comp contMDiff_fst
  have hCoordinates : ContMDiff
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      throatCoverModelWithCorners ∞
      (fun current : OrientationBoundaryCover period hPeriod × Real =>
        coverHomeomorphProd (fixedEquatorData period hPeriod)
          (orientationDoubleCoverHomeomorph period hPeriod current.1)) :=
    (chartedSpacePullback_toFun_contMDiff throatCoverModelWithCorners ∞
      (coverHomeomorphProd (fixedEquatorData period hPeriod))).comp hAnchor
  have hSphere : ContMDiff
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real (EuclideanSpace Real (Fin 2))) ∞
      (fun current : OrientationBoundaryCover period hPeriod × Real =>
        (orientationDoubleCoverHomeomorph period hPeriod current.1).fiber) :=
    contMDiff_fst.comp hCoordinates
  have hTime : ContMDiff
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real Real) ∞
      (fun current : OrientationBoundaryCover period hPeriod × Real =>
        (orientationDoubleCoverHomeomorph period hPeriod current.1).time) :=
    contMDiff_snd.comp hCoordinates
  have hStandardSphere : ContMDiff
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real (EuclideanSpace Real (Fin 2))) ∞
      (fun current : OrientationBoundaryCover period hPeriod × Real =>
        equatorialTwoSphereHomeomorph
          (orientationDoubleCoverHomeomorph period hPeriod current.1).fiber) :=
    (chartedSpacePullback_toFun_contMDiff
      (modelWithCornersSelf Real (EuclideanSpace Real (Fin 2))) ∞
      equatorialTwoSphereHomeomorph).comp hSphere
  have hBase : ContMDiff
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      canonicalLatitudeBaseModelWithCorners ∞
      (fun current : OrientationBoundaryCover period hPeriod × Real =>
        (equatorialTwoSphereHomeomorph
            (orientationDoubleCoverHomeomorph period hPeriod current.1).fiber,
          (orientationDoubleCoverHomeomorph period hPeriod current.1).time)) :=
    hStandardSphere.prodMk hTime
  have hAnchorParameter : ContMDiff
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real)) ∞
      (fun current : OrientationBoundaryCover period hPeriod × Real =>
        (orientationDoubleCoverHomeomorph period hPeriod current.1,
          current.2)) :=
    hAnchor.prodMk contMDiff_snd
  have hNormal : ContMDiff
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real Real) ∞
      (fun current : OrientationBoundaryCover period hPeriod × Real =>
        (normalGraphCoordinate period hPeriod displacement current.2
          (orientationDoubleCoverHomeomorph period hPeriod current.1)).1) :=
    (normalGraphCoordinateValue_joint_contMDiff period hPeriod displacement).comp
      hAnchorParameter
  exact hBase.prodMk hNormal

/-- Joint smoothness of the genuine total tangent lift follows from the
already proved smooth canonical latitude lift. -/
theorem normalGraphCanonicalLatitudeLiftCover_joint_contMDiff
    (displacement : SmoothNormalDisplacement period hPeriod) :
    ContMDiff
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      coverModelWithCorners.tangent ∞
      (fun current : OrientationBoundaryCover period hPeriod × Real =>
        normalGraphCanonicalLatitudeLiftCover period hPeriod displacement
          current.2 current.1) := by
  exact ((canonicalLatitudeNormalLift_contMDiff period hPeriod).comp
    (normalGraphCanonicalLatitudeParameterCover_contMDiff period hPeriod
      displacement)).congr fun current =>
        (normalGraphCanonicalLatitudeLiftCover_eq_canonical period hPeriod
          displacement current.2 current.1).symm

/-- Its base point is exactly the moving graph, not an independently supplied
boundary embedding. -/
theorem normalGraphCanonicalLatitudeLiftCover_base
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (point : OrientationBoundaryCover period hPeriod) :
    (normalGraphCanonicalLatitudeLiftCover period hPeriod displacement parameter
        point).1 =
      normalGraphOrientationDouble period hPeriod displacement
        (mappingTorusMk (orientationDoubleData period hPeriod) point,
          parameter) := by
  unfold normalGraphCanonicalLatitudeLiftCover normalGraphOrientationDouble
  rw [orientationDoubleToThroat_mk, normalGraph_mk]
  rfl

/-- Canonical latitude base represented by an orientation-double cover point. -/
def normalGraphCanonicalLatitudeBaseCover
    (point : OrientationBoundaryCover period hPeriod) : CanonicalLatitudeBase :=
  let anchor := orientationDoubleCoverHomeomorph period hPeriod point
  (equatorialTwoSphereHomeomorph anchor.fiber, anchor.time)

theorem canonicalLatitudeAnchor_baseCover
    (point : OrientationBoundaryCover period hPeriod) :
    canonicalLatitudeAnchor period hPeriod
        (normalGraphCanonicalLatitudeBaseCover period hPeriod point) =
      orientationDoubleCoverHomeomorph period hPeriod point := by
  apply MappingTorusCover.ext
  · simp [canonicalLatitudeAnchor, normalGraphCanonicalLatitudeBaseCover]
  · simp [canonicalLatitudeAnchor, normalGraphCanonicalLatitudeBaseCover]

theorem canonicalLatitudeThroatMap_baseCover
    (point : OrientationBoundaryCover period hPeriod) :
    canonicalLatitudeThroatMap period hPeriod
        (normalGraphCanonicalLatitudeBaseCover period hPeriod point) =
      orientationDoubleToThroat period hPeriod
        (mappingTorusMk (orientationDoubleData period hPeriod) point) := by
  rw [orientationDoubleToThroat_mk]
  unfold canonicalLatitudeThroatMap
  rw [canonicalLatitudeAnchor_baseCover period hPeriod point]

private theorem normalGraphTransverseVectorAt_transport
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (first second : EffectiveThroat period hPeriod)
    (hPoint : first = second)
    (vector : TangentSpace coverModelWithCorners
      (normalGraph period hPeriod displacement parameter first))
    (hTransverse : NormalGraphTransverseVectorAt period hPeriod displacement
      parameter first vector) :
    NormalGraphTransverseVectorAt period hPeriod displacement parameter second
      ((congrArg (normalGraph period hPeriod displacement parameter) hPoint) ▸
        vector) := by
  subst second
  simpa using hTransverse

/-- Fiber-corrected canonical latitude vector on one orientation-double cover
representative. -/
def normalGraphCanonicalLatitudeVectorCover
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (point : OrientationBoundaryCover period hPeriod) :
    TangentSpace coverModelWithCorners
      (normalGraphOrientationDouble period hPeriod displacement
        (mappingTorusMk (orientationDoubleData period hPeriod) point,
          parameter)) := by
  let base := normalGraphCanonicalLatitudeBaseCover period hPeriod point
  let normal := (normalGraphCoordinate period hPeriod displacement parameter
    (canonicalLatitudeAnchor period hPeriod base)).1
  let hPoint := canonicalLatitudeThroatMap_baseCover period hPeriod point
  change TangentSpace coverModelWithCorners
    (normalGraph period hPeriod displacement parameter
      (orientationDoubleToThroat period hPeriod
        (mappingTorusMk (orientationDoubleData period hPeriod) point)))
  exact (congrArg (normalGraph period hPeriod displacement parameter) hPoint) ▸
    canonicalLatitudeNormalVector period hPeriod base normal

/-- The canonical cover vector is transverse to the actual moving graph. -/
theorem normalGraphCanonicalLatitudeVectorCover_transverse
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (point : OrientationBoundaryCover period hPeriod) :
    NormalGraphTransverseVectorAt period hPeriod displacement parameter
      (orientationDoubleToThroat period hPeriod
        (mappingTorusMk (orientationDoubleData period hPeriod) point))
      (normalGraphCanonicalLatitudeVectorCover period hPeriod displacement
        parameter point) := by
  let base := normalGraphCanonicalLatitudeBaseCover period hPeriod point
  let hPoint := canonicalLatitudeThroatMap_baseCover period hPeriod point
  change NormalGraphTransverseVectorAt period hPeriod displacement parameter
    (orientationDoubleToThroat period hPeriod
      (mappingTorusMk (orientationDoubleData period hPeriod) point))
    ((congrArg (normalGraph period hPeriod displacement parameter) hPoint) ▸
      canonicalLatitudeNormalVector period hPeriod base
        (normalGraphCoordinate period hPeriod displacement parameter
          (canonicalLatitudeAnchor period hPeriod base)).1)
  exact normalGraphTransverseVectorAt_transport period hPeriod displacement
    parameter (canonicalLatitudeThroatMap period hPeriod base)
    (orientationDoubleToThroat period hPeriod
      (mappingTorusMk (orientationDoubleData period hPeriod) point)) hPoint
    (canonicalLatitudeNormalVector period hPeriod base
      (normalGraphCoordinate period hPeriod displacement parameter
        (canonicalLatitudeAnchor period hPeriod base)).1)
    (canonicalLatitudeNormalVector_transverse_normalGraph period hPeriod
      displacement parameter base)

set_option backward.isDefEq.respectTransparency false in
/-- The transported cover vector is the fiber component of the pre-existing
canonical total tangent lift. -/
theorem normalGraphCanonicalLatitudeVectorCover_heq_lift
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (point : OrientationBoundaryCover period hPeriod) :
    HEq (normalGraphCanonicalLatitudeVectorCover period hPeriod displacement
          parameter point)
      (normalGraphCanonicalLatitudeLiftCover period hPeriod displacement
        parameter point).2 := by
  unfold normalGraphCanonicalLatitudeVectorCover
  dsimp only
  refine (eqRec_heq _ _).trans ?_
  unfold normalGraphCanonicalLatitudeLiftCover
  dsimp only
  rw [canonicalLatitudeAnchor_baseCover period hPeriod point]
  rfl

/-- Even source windings leave the total latitude tangent unchanged.  This is
the precise tangent-bundle descent law supplied by the orientation double. -/
theorem normalGraphCanonicalLatitudeLiftCover_invariant
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (winding : Int)
    (point : OrientationBoundaryCover period hPeriod) :
    normalGraphCanonicalLatitudeLiftCover period hPeriod displacement parameter
        (winding +ᵥ point) =
      normalGraphCanonicalLatitudeLiftCover period hPeriod displacement parameter
        point := by
  let anchor := orientationDoubleCoverHomeomorph period hPeriod point
  have hAnchor :
      orientationDoubleCoverHomeomorph period hPeriod (winding +ᵥ point) =
        (2 * winding) +ᵥ anchor := by
    exact orientationDoubleCover_even_equivariant period hPeriod winding point
  have hSign :
      (normalSignRepresentation (2 * winding) : Real) = 1 := by
    simpa using congrArg (fun unit : Realˣ => (unit : Real))
      (pulledBack_normal_sign_trivial winding)
  have hCoordinate :
      (normalGraphCoordinate period hPeriod displacement parameter
          ((2 * winding) +ᵥ anchor)).1 =
        (normalGraphCoordinate period hPeriod displacement parameter anchor).1 := by
    change Real.arctan
        (parameter * normalCoordinateLift period hPeriod displacement
          ((2 * winding) +ᵥ anchor)) =
      Real.arctan
        (parameter * normalCoordinateLift period hPeriod displacement anchor)
    rw [normalCoordinateLift_vadd, hSign]
    simp
  have hCurve :
      quotientNormalLatitude period hPeriod ((2 * winding) +ᵥ anchor) =
        quotientNormalLatitude period hPeriod anchor := by
    funext normal
    simpa [hSign] using
      quotientNormalLatitude_deck_winding period hPeriod (2 * winding) anchor normal
  unfold normalGraphCanonicalLatitudeLiftCover
  rw [hAnchor]
  dsimp only
  rw [hCoordinate, hCurve]

/-- Global total tangent lift on the orientation boundary. -/
def normalGraphCanonicalLatitudeLift
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) :
    OrientationBoundary period hPeriod →
      TangentBundle coverModelWithCorners (EffectiveQuotient period hPeriod) :=
  Quotient.lift
    (normalGraphCanonicalLatitudeLiftCover period hPeriod displacement parameter)
    (fun first second hOrbit ↦ by
      change AddAction.orbitRel Int (OrientationBoundaryCover period hPeriod)
        first second at hOrbit
      rw [AddAction.orbitRel_apply, AddAction.mem_orbit_iff] at hOrbit
      rcases hOrbit with ⟨winding, hWinding⟩
      rw [← hWinding]
      exact normalGraphCanonicalLatitudeLiftCover_invariant period hPeriod
        displacement parameter winding second)

@[simp]
theorem normalGraphCanonicalLatitudeLift_mk
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (point : OrientationBoundaryCover period hPeriod) :
    normalGraphCanonicalLatitudeLift period hPeriod displacement parameter
        (mappingTorusMk (orientationDoubleData period hPeriod) point) =
      normalGraphCanonicalLatitudeLiftCover period hPeriod displacement parameter
        point :=
  rfl

/-- The descended tangent lift is a section along the descended moving graph. -/
theorem normalGraphCanonicalLatitudeLift_base
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : OrientationBoundary period hPeriod) :
    (normalGraphCanonicalLatitudeLift period hPeriod displacement parameter
        boundary).1 =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter) := by
  refine Quotient.inductionOn boundary ?_
  intro point
  rw [normalGraphCanonicalLatitudeLift_mk]
  exact normalGraphCanonicalLatitudeLiftCover_base period hPeriod displacement
    parameter point

/-- Fiber-corrected canonical latitude vector on the descended orientation
boundary. -/
def normalGraphCanonicalLatitudeVector
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : OrientationBoundary period hPeriod) :
    TangentSpace coverModelWithCorners
      (normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter)) :=
  cast (congrArg (fun point => TangentSpace coverModelWithCorners point)
    (normalGraphCanonicalLatitudeLift_base period hPeriod displacement parameter
      boundary))
    (normalGraphCanonicalLatitudeLift period hPeriod displacement parameter
      boundary).2

set_option backward.isDefEq.respectTransparency false in
theorem normalGraphCanonicalLatitudeVector_mk_heq_cover
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (point : OrientationBoundaryCover period hPeriod) :
    HEq (normalGraphCanonicalLatitudeVector period hPeriod displacement parameter
          (mappingTorusMk (orientationDoubleData period hPeriod) point))
      (normalGraphCanonicalLatitudeVectorCover period hPeriod displacement
        parameter point) := by
  unfold normalGraphCanonicalLatitudeVector
  rw [cast_heq_iff_heq]
  rw [normalGraphCanonicalLatitudeLift_mk]
  exact (normalGraphCanonicalLatitudeVectorCover_heq_lift period hPeriod
    displacement parameter point).symm

/-- The globally descended canonical latitude vector is transverse everywhere
on the orientation boundary. -/
theorem normalGraphCanonicalLatitudeVector_transverse
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : OrientationBoundary period hPeriod) :
    NormalGraphTransverseVectorAt period hPeriod displacement parameter
      (orientationDoubleToThroat period hPeriod boundary)
      (normalGraphCanonicalLatitudeVector period hPeriod displacement parameter
        boundary) := by
  refine Quotient.inductionOn boundary ?_
  intro point
  have hVector :
      normalGraphCanonicalLatitudeVector period hPeriod displacement parameter
          (mappingTorusMk (orientationDoubleData period hPeriod) point) =
        normalGraphCanonicalLatitudeVectorCover period hPeriod displacement
          parameter point :=
    eq_of_heq (normalGraphCanonicalLatitudeVector_mk_heq_cover period hPeriod
      displacement parameter point)
  rw [hVector]
  exact normalGraphCanonicalLatitudeVectorCover_transverse period hPeriod
    displacement parameter point

/-- Canonical nonzero class in the one-dimensional differential normal fiber
of the moving graph. -/
def normalGraphCanonicalNormalClass
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : OrientationBoundary period hPeriod) :
    MovingGraphDifferentialNormalFiber period hPeriod displacement parameter
      (orientationDoubleToThroat period hPeriod boundary) :=
  Submodule.Quotient.mk
    (normalGraphCanonicalLatitudeVector period hPeriod displacement parameter
      boundary)

theorem normalGraphCanonicalNormalClass_ne_zero
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : OrientationBoundary period hPeriod) :
    normalGraphCanonicalNormalClass period hPeriod displacement parameter
      boundary ≠ 0 := by
  intro hZero
  apply normalGraphCanonicalLatitudeVector_transverse period hPeriod displacement
    parameter boundary
  apply (Submodule.Quotient.mk_eq_zero
    (NormalGraphTangentRange period hPeriod displacement parameter
      (orientationDoubleToThroat period hPeriod boundary))).1
  exact hZero

/-- The canonical metric unit normal along the full moving orientation
boundary, obtained by normalizing the already descended nonzero quotient
class. -/
def normalGraphCanonicalMetricUnitNormal
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : OrientationBoundary period hPeriod) :
    TangentSpace coverModelWithCorners
      (normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter)) :=
  normalGraphMetricUnitNormal period hPeriod metric displacement parameter
    hNonNull (orientationDoubleToThroat period hPeriod boundary)
      (normalGraphCanonicalNormalClass period hPeriod displacement parameter
        boundary)

/-- The canonical global unit normal is nowhere zero. -/
theorem normalGraphCanonicalMetricUnitNormal_ne_zero
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : OrientationBoundary period hPeriod) :
    normalGraphCanonicalMetricUnitNormal period hPeriod metric displacement
      parameter hNonNull boundary ≠ 0 := by
  intro hZero
  have hSquare := abs_normalGraphMetricUnitNormal_square period hPeriod metric
    displacement parameter hNonNull
    (orientationDoubleToThroat period hPeriod boundary)
    (normalGraphCanonicalNormalClass period hPeriod displacement parameter
      boundary)
    (normalGraphCanonicalNormalClass_ne_zero period hPeriod displacement
      parameter boundary)
  change
    |metric.tensor.tensor
      (normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter))
      (normalGraphCanonicalMetricUnitNormal period hPeriod metric displacement
        parameter hNonNull boundary)
      (normalGraphCanonicalMetricUnitNormal period hPeriod metric displacement
        parameter hNonNull boundary)| = 1 at hSquare
  rw [hZero] at hSquare
  simp at hSquare

/-- Its causal square is intrinsically either `+1` or `-1`. -/
theorem normalGraphCanonicalMetricUnitNormal_causalSign_admissible
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : OrientationBoundary period hPeriod) :
    normalGraphMetricNormalCausalSign period hPeriod metric displacement
        parameter hNonNull (orientationDoubleToThroat period hPeriod boundary)
        (normalGraphCanonicalNormalClass period hPeriod displacement parameter
          boundary) = 1 ∨
      normalGraphMetricNormalCausalSign period hPeriod metric displacement
        parameter hNonNull (orientationDoubleToThroat period hPeriod boundary)
        (normalGraphCanonicalNormalClass period hPeriod displacement parameter
          boundary) = -1 :=
  normalGraphMetricNormalCausalSign_admissible period hPeriod metric
    displacement parameter hNonNull
      (orientationDoubleToThroat period hPeriod boundary)
      (normalGraphCanonicalNormalClass period hPeriod displacement parameter
        boundary)
      (normalGraphCanonicalNormalClass_ne_zero period hPeriod displacement
        parameter boundary)

/-- The canonical global unit normal is orthogonal to every tangent of the
same moving graph. -/
theorem normalGraphCanonicalMetricUnitNormal_orthogonal
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : OrientationBoundary period hPeriod)
    (tangent : ThroatTangentFiber period hPeriod
      (orientationDoubleToThroat period hPeriod boundary)) :
    metric.tensor.tensor
        (normalGraphOrientationDouble period hPeriod displacement
          (boundary, parameter))
        (normalGraphCanonicalMetricUnitNormal period hPeriod metric displacement
          parameter hNonNull boundary)
        (mfderiv throatCoverModelWithCorners coverModelWithCorners
          (normalGraph period hPeriod displacement parameter)
          (orientationDoubleToThroat period hPeriod boundary) tangent) = 0 := by
  unfold normalGraphCanonicalMetricUnitNormal normalGraphMetricUnitNormal
    normalGraphOrientationDouble
  simp only [Prod.fst, Prod.snd, map_smul, smul_apply]
  rw [normalGraphMetricNormalFromClass_orthogonal period hPeriod metric
    displacement parameter hNonNull
    (orientationDoubleToThroat period hPeriod boundary)
    (normalGraphCanonicalNormalClass period hPeriod displacement parameter
      boundary) tangent]
  simp

/-- The absolute metric square of the canonical global normal is exactly one. -/
theorem abs_normalGraphCanonicalMetricUnitNormal_square
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : OrientationBoundary period hPeriod) :
    |metric.tensor.tensor
        (normalGraphOrientationDouble period hPeriod displacement
          (boundary, parameter))
        (normalGraphCanonicalMetricUnitNormal period hPeriod metric displacement
          parameter hNonNull boundary)
        (normalGraphCanonicalMetricUnitNormal period hPeriod metric displacement
          parameter hNonNull boundary)| = 1 := by
  exact abs_normalGraphMetricUnitNormal_square period hPeriod metric displacement
    parameter hNonNull (orientationDoubleToThroat period hPeriod boundary)
      (normalGraphCanonicalNormalClass period hPeriod displacement parameter
        boundary)
      (normalGraphCanonicalNormalClass_ne_zero period hPeriod displacement
        parameter boundary)

/-- Smoothness descends through the already installed local-diffeomorphism
projection from the orientation-double cover. -/
private theorem orientationDouble_contMDiff_of_cover
    (field : OrientationBoundary period hPeriod →
      TangentBundle coverModelWithCorners (EffectiveQuotient period hPeriod))
    (hCover : ContMDiff throatCoverModelWithCorners
      coverModelWithCorners.tangent ∞
      (field ∘ mappingTorusMk (orientationDoubleData period hPeriod))) :
    ContMDiff throatCoverModelWithCorners coverModelWithCorners.tangent ∞
      field := by
  intro boundary
  obtain ⟨coverPoint, rfl⟩ :=
    mappingTorusMk_surjective (orientationDoubleData period hPeriod) boundary
  have hProjection :
      IsLocalDiffeomorph throatCoverModelWithCorners throatCoverModelWithCorners ω
        (mappingTorusMk (orientationDoubleData period hPeriod)) :=
    fixedThroat_projection_isLocalDiffeomorph
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
  have hAt := hProjection coverPoint
  have hLocal := hCover.contMDiffAt.comp _
    (hAt.localInverse_contMDiffAt.of_le (by simp))
  apply hLocal.congr_of_eventuallyEq
  filter_upwards [hAt.localInverse_eventuallyEq_right] with point hPoint
  have hPoint' :
      mappingTorusMk (orientationDoubleData period hPeriod)
          (hAt.localInverse point) = point := by
    simpa [Function.comp_def] using hPoint
  exact congrArg field hPoint'.symm

/-- The descended total tangent lift is smooth on the full orientation
boundary. -/
theorem normalGraphCanonicalLatitudeLift_contMDiff
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) :
    ContMDiff throatCoverModelWithCorners coverModelWithCorners.tangent ∞
      (fun boundary : OrientationBoundary period hPeriod =>
        normalGraphCanonicalLatitudeLift period hPeriod displacement parameter
          boundary) := by
  apply orientationDouble_contMDiff_of_cover period hPeriod
  have hPair : ContMDiff throatCoverModelWithCorners
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real)) ∞
      (fun point : OrientationBoundaryCover period hPeriod =>
        (point, parameter)) :=
    contMDiff_id.prodMk contMDiff_const
  exact ((normalGraphCanonicalLatitudeLiftCover_joint_contMDiff period hPeriod
    displacement).comp hPair).congr fun point => rfl

/-- The descended canonical latitude lift is jointly smooth in the genuine
orientation-boundary point and graph parameter.  This is the parameterized
instance of the existing invariant mapping-torus descent theorem. -/
theorem normalGraphCanonicalLatitudeLift_joint_contMDiff
    (displacement : SmoothNormalDisplacement period hPeriod) :
    ContMDiff
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      coverModelWithCorners.tangent ∞
      (fun current : OrientationBoundary period hPeriod × Real =>
        normalGraphCanonicalLatitudeLift period hPeriod displacement current.2
          current.1) := by
  let coverField := fun current :
      OrientationBoundaryCover period hPeriod × Real =>
    normalGraphCanonicalLatitudeLiftCover period hPeriod displacement current.2
      current.1
  have hInvariant : ∀ (winding : Int)
      (current : OrientationBoundaryCover period hPeriod × Real),
      coverField (winding +ᵥ current.1, current.2) = coverField current := by
    intro winding current
    exact normalGraphCanonicalLatitudeLiftCover_invariant period hPeriod
      displacement current.2 winding current.1
  have hDescended := mappingTorusInvariantMapProd_contMDiff
    (orientationDoubleData period hPeriod) throatCoverModelWithCorners ∞
    (modelWithCornersSelf Real Real) coverModelWithCorners.tangent coverField
      hInvariant
      (fixedThroat_projection_isLocalDiffeomorph_smooth
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
      (normalGraphCanonicalLatitudeLiftCover_joint_contMDiff period hPeriod
        displacement)
  exact hDescended.congr fun current => by
    obtain ⟨coverPoint, hPoint⟩ :=
      mappingTorusMk_surjective (orientationDoubleData period hPeriod) current.1
    rcases current with ⟨boundary, parameter⟩
    dsimp only at hPoint ⊢
    subst boundary
    rfl

/-- Reflection of a parameter reverses the tangent of a smooth manifold-valued
curve at every base point, not only at the origin. -/
private theorem mfderiv_precomp_neg_one_at
    (curve : Real → EffectiveQuotient period hPeriod) (normal : Real)
    (hCurve : MDifferentiableAt (modelWithCornersSelf Real Real)
      coverModelWithCorners curve normal) :
    mfderiv (modelWithCornersSelf Real Real) coverModelWithCorners
        (fun current => curve (-current)) (-normal) 1 =
      -mfderiv (modelWithCornersSelf Real Real) coverModelWithCorners
        curve normal 1 := by
  have hNeg : MDifferentiableAt (modelWithCornersSelf Real Real)
      (modelWithCornersSelf Real Real) (fun current : Real => -current)
      (-normal) :=
    (contMDiff_id.neg : ContMDiff (modelWithCornersSelf Real Real)
      (modelWithCornersSelf Real Real) ∞
      (fun current : Real => -current)).mdifferentiableAt (by simp)
  have hNegDerivative :
      mfderiv (modelWithCornersSelf Real Real)
          (modelWithCornersSelf Real Real) (fun current : Real => -current)
          (-normal) 1 = -1 := by
    rw [show (fun current : Real => -current) = -(id : Real → Real) by rfl,
      mfderiv_neg, mfderiv_id]
    rfl
  have hCurveAt : MDifferentiableAt (modelWithCornersSelf Real Real)
      coverModelWithCorners curve (-(-normal)) := by
    simpa using hCurve
  have hComp := mfderiv_comp_apply (-normal) hCurveAt hNeg 1
  rw [hNegDerivative, map_neg] at hComp
  have hFunction : curve ∘ (fun current : Real => -current) =
      fun current : Real => curve (-current) := rfl
  rw [hFunction] at hComp
  have hNegNeg : -(-normal) = normal := neg_neg normal
  rw [hNegNeg] at hComp
  exact hComp

/-- The residual deck involution fixes the graph base and reverses the
canonical latitude tangent. -/
theorem normalGraphCanonicalLatitudeLiftCover_deck
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (point : OrientationBoundaryCover period hPeriod) :
    normalGraphCanonicalLatitudeLiftCover period hPeriod displacement parameter
        (orientationDeckCover period hPeriod point) =
      ⟨(normalGraphCanonicalLatitudeLiftCover period hPeriod displacement
          parameter point).1,
        -(normalGraphCanonicalLatitudeLiftCover period hPeriod displacement
          parameter point).2⟩ := by
  let anchor := orientationDoubleCoverHomeomorph period hPeriod point
  let normal :=
    (normalGraphCoordinate period hPeriod displacement parameter anchor).1
  have hAnchor :
      orientationDoubleCoverHomeomorph period hPeriod
          (orientationDeckCover period hPeriod point) =
        (1 : Int) +ᵥ anchor :=
    orientationDoubleCoverHomeomorph_deck period hPeriod point
  have hCoordinate :
      (normalGraphCoordinate period hPeriod displacement parameter
          ((1 : Int) +ᵥ anchor)).1 = -normal := by
    have hGraph := congrArg Subtype.val
      (normalGraphCoordinate_oneLoop period hPeriod displacement parameter anchor)
    simpa [normal, canonicalLatitudeTubularNormalNeg] using hGraph
  have hCurve :
      quotientNormalLatitude period hPeriod ((1 : Int) +ᵥ anchor) =
        fun current => quotientNormalLatitude period hPeriod anchor (-current) := by
    funext current
    exact quotientNormalLatitude_deck_generator period hPeriod anchor current
  have hRegularity : MDifferentiableAt (modelWithCornersSelf Real Real)
      coverModelWithCorners (quotientNormalLatitude period hPeriod anchor)
      normal :=
    (quotientNormalLatitude_contMDiff period hPeriod anchor).mdifferentiableAt
      (by simp)
  have hDerivative := mfderiv_precomp_neg_one_at period hPeriod
    (quotientNormalLatitude period hPeriod anchor) normal hRegularity
  unfold normalGraphCanonicalLatitudeLiftCover
  rw [hAnchor]
  dsimp only
  change
    (⟨quotientNormalLatitude period hPeriod ((1 : Int) +ᵥ anchor)
        (normalGraphCoordinate period hPeriod displacement parameter
          ((1 : Int) +ᵥ anchor)).1,
      mfderiv (modelWithCornersSelf Real Real) coverModelWithCorners
        (quotientNormalLatitude period hPeriod ((1 : Int) +ᵥ anchor))
        (normalGraphCoordinate period hPeriod displacement parameter
          ((1 : Int) +ᵥ anchor)).1 1⟩ :
      TangentBundle coverModelWithCorners (EffectiveQuotient period hPeriod)) =
    ⟨quotientNormalLatitude period hPeriod anchor normal,
      -mfderiv (modelWithCornersSelf Real Real) coverModelWithCorners
        (quotientNormalLatitude period hPeriod anchor) normal 1⟩
  rw [hCoordinate, hCurve]
  have hNegNeg : -(-normal) = normal := neg_neg normal
  apply Bundle.TotalSpace.ext
  · change quotientNormalLatitude period hPeriod anchor (-(-normal)) =
      quotientNormalLatitude period hPeriod anchor normal
    rw [hNegNeg]
  · exact hDerivative.heq

/-- Hence the globally descended tangent has the required odd residual deck
law. -/
theorem normalGraphCanonicalLatitudeLift_deck
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : OrientationBoundary period hPeriod) :
    normalGraphCanonicalLatitudeLift period hPeriod displacement parameter
        (orientationDeck period hPeriod boundary) =
      ⟨(normalGraphCanonicalLatitudeLift period hPeriod displacement parameter
          boundary).1,
        -(normalGraphCanonicalLatitudeLift period hPeriod displacement parameter
          boundary).2⟩ := by
  refine Quotient.inductionOn boundary ?_
  intro point
  rw [orientationDeck_mk, normalGraphCanonicalLatitudeLift_mk,
    normalGraphCanonicalLatitudeLift_mk]
  exact normalGraphCanonicalLatitudeLiftCover_deck period hPeriod displacement
    parameter point

/-- Fiber component of the odd deck law for the descended latitude lift. -/
theorem normalGraphCanonicalLatitudeLift_deck_snd
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : OrientationBoundary period hPeriod) :
    HEq
      (normalGraphCanonicalLatitudeLift period hPeriod displacement parameter
        (orientationDeck period hPeriod boundary)).2
      (-(normalGraphCanonicalLatitudeLift period hPeriod displacement parameter
        boundary).2) := by
  rw [normalGraphCanonicalLatitudeLift_deck]

/-- The fiber-corrected canonical latitude vector is odd under the residual
deck involution. -/
theorem normalGraphCanonicalLatitudeVector_deck
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : OrientationBoundary period hPeriod) :
    HEq
      (normalGraphCanonicalLatitudeVector period hPeriod displacement parameter
        (orientationDeck period hPeriod boundary))
      (-normalGraphCanonicalLatitudeVector period hPeriod displacement parameter
        boundary) := by
  unfold normalGraphCanonicalLatitudeVector
  rw [cast_heq_iff_heq]
  refine (normalGraphCanonicalLatitudeLift_deck_snd period hPeriod displacement
    parameter boundary).trans ?_
  have hCast : HEq
      (cast (congrArg (fun point => TangentSpace coverModelWithCorners point)
        (normalGraphCanonicalLatitudeLift_base period hPeriod displacement
          parameter boundary))
        (normalGraphCanonicalLatitudeLift period hPeriod displacement parameter
          boundary).2)
      (normalGraphCanonicalLatitudeLift period hPeriod displacement parameter
        boundary).2 :=
    by rw [cast_heq_iff_heq]
  cases hCast
  rfl

/-- Repackaging the fiber-corrected vector recovers exactly the original
smooth total tangent lift. -/
theorem normalGraphCanonicalLatitudeVector_total
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : OrientationBoundary period hPeriod) :
    (⟨normalGraphOrientationDouble period hPeriod displacement
          (boundary, parameter),
        normalGraphCanonicalLatitudeVector period hPeriod displacement parameter
          boundary⟩ :
      TangentBundle coverModelWithCorners (EffectiveQuotient period hPeriod)) =
      normalGraphCanonicalLatitudeLift period hPeriod displacement parameter
        boundary := by
  apply Bundle.TotalSpace.ext
  · exact (normalGraphCanonicalLatitudeLift_base period hPeriod displacement
      parameter boundary).symm
  · unfold normalGraphCanonicalLatitudeVector
    rw [cast_heq_iff_heq]

private theorem normalGraphDependentApply_heq
    {α : Sort _} {β γ : α → Sort _}
    (f : (point : α) → β point → γ point)
    {source target : α} (hBase : source = target)
    {first : β source} {second : β target}
    (hValue : HEq first second) :
    HEq (f source first) (f target second) := by
  cases hBase
  cases hValue
  rfl

private theorem normalGraphDependentBilinApply_heq
    {α : Sort _} {β : α → Sort _}
    (f : (point : α) → β point → β point → Real)
    {source target : α} (hBase : source = target)
    {firstSource secondSource : β source}
    {firstTarget secondTarget : β target}
    (hFirst : HEq firstSource firstTarget)
    (hSecond : HEq secondSource secondTarget) :
    HEq (f source firstSource secondSource)
      (f target firstTarget secondTarget) := by
  cases hBase
  cases hFirst
  cases hSecond
  rfl

/-- The canonical differential-normal quotient class inherits the same odd
deck law. -/
theorem normalGraphCanonicalNormalClass_deck
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : OrientationBoundary period hPeriod) :
    HEq
      (normalGraphCanonicalNormalClass period hPeriod displacement parameter
        (orientationDeck period hPeriod boundary))
      (-normalGraphCanonicalNormalClass period hPeriod displacement parameter
        boundary) := by
  have hBase := orientationDoubleToThroat_deck period hPeriod boundary
  have hVector := normalGraphCanonicalLatitudeVector_deck period hPeriod
    displacement parameter boundary
  have hQuotient : HEq
      (Submodule.Quotient.mk
          (normalGraphCanonicalLatitudeVector period hPeriod displacement
            parameter (orientationDeck period hPeriod boundary)) :
        MovingGraphDifferentialNormalFiber period hPeriod displacement parameter
          (orientationDoubleToThroat period hPeriod
            (orientationDeck period hPeriod boundary)))
      (Submodule.Quotient.mk
          (-normalGraphCanonicalLatitudeVector period hPeriod displacement
            parameter boundary) :
        MovingGraphDifferentialNormalFiber period hPeriod displacement parameter
          (orientationDoubleToThroat period hPeriod boundary)) :=
    normalGraphDependentApply_heq
      (fun point vector =>
        (Submodule.Quotient.mk vector :
          MovingGraphDifferentialNormalFiber period hPeriod displacement
            parameter point))
      hBase hVector
  unfold normalGraphCanonicalNormalClass
  refine hQuotient.trans ?_
  exact (Submodule.Quotient.mk_neg
    (NormalGraphTangentRange period hPeriod displacement parameter
      (orientationDoubleToThroat period hPeriod boundary)) :
    (Submodule.Quotient.mk
        (-normalGraphCanonicalLatitudeVector period hPeriod displacement
          parameter boundary) :
      MovingGraphDifferentialNormalFiber period hPeriod displacement parameter
        (orientationDoubleToThroat period hPeriod boundary)) =
      -Submodule.Quotient.mk
        (normalGraphCanonicalLatitudeVector period hPeriod displacement
          parameter boundary)).heq

/-- The canonical metric unit normal reverses under the residual deck
involution. -/
theorem normalGraphCanonicalMetricUnitNormal_deck
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : OrientationBoundary period hPeriod) :
    HEq
      (normalGraphCanonicalMetricUnitNormal period hPeriod metric displacement
        parameter hNonNull (orientationDeck period hPeriod boundary))
      (-normalGraphCanonicalMetricUnitNormal period hPeriod metric displacement
        parameter hNonNull boundary) := by
  have hBase := orientationDoubleToThroat_deck period hPeriod boundary
  have hClass := normalGraphCanonicalNormalClass_deck period hPeriod displacement
    parameter boundary
  have hUnit : HEq
      (normalGraphMetricUnitNormal period hPeriod metric displacement parameter
        hNonNull
        (orientationDoubleToThroat period hPeriod
          (orientationDeck period hPeriod boundary))
        (normalGraphCanonicalNormalClass period hPeriod displacement parameter
          (orientationDeck period hPeriod boundary)))
      (normalGraphMetricUnitNormal period hPeriod metric displacement parameter
        hNonNull (orientationDoubleToThroat period hPeriod boundary)
        (-normalGraphCanonicalNormalClass period hPeriod displacement parameter
          boundary)) :=
    normalGraphDependentApply_heq
      (fun point normalClass =>
        normalGraphMetricUnitNormal period hPeriod metric displacement parameter
          hNonNull point normalClass)
      hBase hClass
  unfold normalGraphCanonicalMetricUnitNormal normalGraphOrientationDouble
  refine hUnit.trans ?_
  exact (normalGraphMetricUnitNormal_neg period hPeriod metric displacement
    parameter hNonNull (orientationDoubleToThroat period hPeriod boundary)
    (normalGraphCanonicalNormalClass period hPeriod displacement parameter
      boundary)).heq

/-- Total tangent-bundle form of the canonical metric unit normal. -/
def normalGraphCanonicalMetricUnitNormalLift
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter) :
    OrientationBoundary period hPeriod →
      TangentBundle coverModelWithCorners (EffectiveQuotient period hPeriod) :=
  fun boundary =>
    ⟨normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter),
      normalGraphCanonicalMetricUnitNormal period hPeriod metric displacement
        parameter hNonNull boundary⟩

/-- The unit-normal total lift is based on the same moving graph. -/
@[simp]
theorem normalGraphCanonicalMetricUnitNormalLift_base
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : OrientationBoundary period hPeriod) :
    (normalGraphCanonicalMetricUnitNormalLift period hPeriod metric displacement
      parameter hNonNull boundary).1 =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter) :=
  rfl

/-- Total-space form of the residual odd deck law. -/
theorem normalGraphCanonicalMetricUnitNormalLift_deck
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : OrientationBoundary period hPeriod) :
    normalGraphCanonicalMetricUnitNormalLift period hPeriod metric displacement
        parameter hNonNull (orientationDeck period hPeriod boundary) =
      ⟨(normalGraphCanonicalMetricUnitNormalLift period hPeriod metric
          displacement parameter hNonNull boundary).1,
        -(normalGraphCanonicalMetricUnitNormalLift period hPeriod metric
          displacement parameter hNonNull boundary).2⟩ := by
  apply Bundle.TotalSpace.ext
  · simp [normalGraphCanonicalMetricUnitNormalLift,
      normalGraphOrientationDouble]
  · exact normalGraphCanonicalMetricUnitNormal_deck period hPeriod metric
      displacement parameter hNonNull boundary

/-! ### Smoothness of the canonical global metric normal -/

private def normalGraphOrientationBoundaryParameter
    (parameter : Real) (boundary : OrientationBoundary period hPeriod) :
    EffectiveThroat period hPeriod × Real :=
  (orientationDoubleToThroat period hPeriod boundary, parameter)

private theorem normalGraphOrientationBoundaryParameter_contMDiff
    (parameter : Real) :
    ContMDiff throatCoverModelWithCorners
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real)) ∞
      (normalGraphOrientationBoundaryParameter period hPeriod parameter) :=
  (orientationDoubleToThroat_contMDiff period hPeriod).prodMk contMDiff_const

/-- Coordinates of the already smooth canonical latitude lift in the fixed
ambient tangent trivialization centered at `base`. -/
private def normalGraphCanonicalLatitudeCoordinates
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (base current : OrientationBoundary period hPeriod) :
    CoverCoordinates :=
  ((trivializationAt CoverCoordinates
      (fun point : EffectiveQuotient period hPeriod =>
        TangentSpace coverModelWithCorners point)
      (normalGraphOrientationDouble period hPeriod displacement
        (base, parameter)))
    (normalGraphCanonicalLatitudeLift period hPeriod displacement parameter
      current)).2

private theorem normalGraphCanonicalLatitudeCoordinates_contMDiffAt
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (base : OrientationBoundary period hPeriod) :
    ContMDiffAt throatCoverModelWithCorners 𝓘(Real, CoverCoordinates) ∞
      (normalGraphCanonicalLatitudeCoordinates period hPeriod displacement
        parameter base) base := by
  let trivialization := trivializationAt CoverCoordinates
    (fun point : EffectiveQuotient period hPeriod =>
      TangentSpace coverModelWithCorners point)
    (normalGraphOrientationDouble period hPeriod displacement (base, parameter))
  have hLift : ContMDiffAt throatCoverModelWithCorners
      coverModelWithCorners.tangent ∞
      (normalGraphCanonicalLatitudeLift period hPeriod displacement parameter)
      base :=
    (normalGraphCanonicalLatitudeLift_contMDiff period hPeriod displacement
      parameter).contMDiffAt
  have hMem : normalGraphCanonicalLatitudeLift period hPeriod displacement
      parameter base ∈ trivialization.source := by
    rw [trivialization.mem_source]
    change (normalGraphCanonicalLatitudeLift period hPeriod displacement
      parameter base).1 ∈ trivialization.baseSet
    rw [normalGraphCanonicalLatitudeLift_base period hPeriod displacement
      parameter base]
    exact mem_baseSet_trivializationAt CoverCoordinates
      (fun point : EffectiveQuotient period hPeriod =>
        TangentSpace coverModelWithCorners point)
      (normalGraphOrientationDouble period hPeriod displacement (base, parameter))
  exact ((trivialization.contMDiffAt_iff hMem).mp hLift).2

private def normalGraphCanonicalMetricNormalCoordinates
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (base current : OrientationBoundary period hPeriod) :
    CoverCoordinates :=
  normalGraphMetricNormalProjectorCoordinates period hPeriod metric displacement
    (normalGraphOrientationBoundaryParameter period hPeriod parameter base)
    (normalGraphOrientationBoundaryParameter period hPeriod parameter current)
    (normalGraphCanonicalLatitudeCoordinates period hPeriod displacement
      parameter base current)

private theorem normalGraphCanonicalMetricNormalCoordinates_contMDiffAt
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (base : OrientationBoundary period hPeriod) :
    ContMDiffAt throatCoverModelWithCorners 𝓘(Real, CoverCoordinates) ∞
      (normalGraphCanonicalMetricNormalCoordinates period hPeriod metric
        displacement parameter base) base := by
  let baseParameter := normalGraphOrientationBoundaryParameter period hPeriod
    parameter base
  have hCurrent : ContMDiffAt throatCoverModelWithCorners
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real)) ∞
      (normalGraphOrientationBoundaryParameter period hPeriod parameter) base :=
    (normalGraphOrientationBoundaryParameter_contMDiff period hPeriod
      parameter).contMDiffAt
  have hProjector :=
    (normalGraphMetricNormalProjectorCoordinates_contMDiffAt period hPeriod
      metric displacement baseParameter hNonNull).comp base hCurrent
  exact hProjector.clm_apply
    (normalGraphCanonicalLatitudeCoordinates_contMDiffAt period hPeriod
      displacement parameter base)

private def normalGraphCanonicalMetricNormalSquareCoordinates
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (base current : OrientationBoundary period hPeriod) : Real :=
  normalGraphFamilyAmbientTensorCoordinates period hPeriod metric displacement
    (normalGraphOrientationBoundaryParameter period hPeriod parameter base)
    (normalGraphOrientationBoundaryParameter period hPeriod parameter current)
    (normalGraphCanonicalMetricNormalCoordinates period hPeriod metric
      displacement parameter base current)
    (normalGraphCanonicalMetricNormalCoordinates period hPeriod metric
      displacement parameter base current)

private theorem normalGraphCanonicalMetricNormalSquareCoordinates_contMDiffAt
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (base : OrientationBoundary period hPeriod) :
    ContMDiffAt throatCoverModelWithCorners 𝓘(Real, Real) ∞
      (normalGraphCanonicalMetricNormalSquareCoordinates period hPeriod metric
        displacement parameter base) base := by
  let baseParameter := normalGraphOrientationBoundaryParameter period hPeriod
    parameter base
  have hCurrent : ContMDiffAt throatCoverModelWithCorners
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real)) ∞
      (normalGraphOrientationBoundaryParameter period hPeriod parameter) base :=
    (normalGraphOrientationBoundaryParameter_contMDiff period hPeriod
      parameter).contMDiffAt
  have hMetric :=
    (normalGraphFamilyAmbientTensorCoordinates_contMDiffAt period hPeriod metric
      displacement baseParameter).comp base hCurrent
  have hNormal := normalGraphCanonicalMetricNormalCoordinates_contMDiffAt period
    hPeriod metric displacement parameter hNonNull base
  exact (hMetric.clm_apply hNormal).clm_apply hNormal

private theorem normalGraphCanonicalMetricNormalSquareCoordinates_ne_zero
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (base : OrientationBoundary period hPeriod) :
    normalGraphCanonicalMetricNormalSquareCoordinates period hPeriod metric
      displacement parameter base base ≠ 0 := by
  let throat := orientationDoubleToThroat period hPeriod base
  let baseParameter : EffectiveThroat period hPeriod × Real := (throat, parameter)
  let graph := normalGraph period hPeriod displacement parameter throat
  let ambientTrivialization := trivializationAt CoverCoordinates
    (fun point : EffectiveQuotient period hPeriod =>
      TangentSpace coverModelWithCorners point) graph
  let ambientCoordinate :=
    normalGraphCanonicalLatitudeCoordinates period hPeriod displacement
      parameter base base
  have hTangent : throat ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) throat).baseSet :=
    mem_baseSet_trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) throat
  have hCotangent : throat ∈
      (trivializationAt (ThroatCoverCoordinates →L[Real] Real)
        (ThroatCotangentFiber period hPeriod) throat).baseSet :=
    mem_baseSet_trivializationAt (ThroatCoverCoordinates →L[Real] Real)
      (ThroatCotangentFiber period hPeriod) throat
  have hImage : graph ∈ ambientTrivialization.baseSet :=
    mem_baseSet_trivializationAt CoverCoordinates
      (fun point : EffectiveQuotient period hPeriod =>
        TangentSpace coverModelWithCorners point) graph
  have hAmbientCoordinate : ambientCoordinate =
      ambientTrivialization.linearMapAt Real graph
        (normalGraphCanonicalLatitudeVector period hPeriod displacement
          parameter base) := by
    unfold ambientCoordinate normalGraphCanonicalLatitudeCoordinates
    change
      (ambientTrivialization
        (normalGraphCanonicalLatitudeLift period hPeriod displacement parameter
          base)).2 = _
    rw [← normalGraphCanonicalLatitudeVector_total period hPeriod displacement
      parameter base]
    rw [Trivialization.linearMapAt_apply, if_pos hImage]
    simp [normalGraphOrientationDouble, graph, throat]
  have hAmbientInverse :
      ambientTrivialization.symm graph ambientCoordinate =
        normalGraphCanonicalLatitudeVector period hPeriod displacement parameter
          base := by
    rw [hAmbientCoordinate]
    exact ambientTrivialization.symm_linearMapAt hImage _
  have hIntrinsicNormal :
      normalGraphMetricNormal period hPeriod metric displacement parameter
          hNonNull throat
          (normalGraphCanonicalLatitudeVector period hPeriod displacement
            parameter base) ≠ 0 := by
    simpa only [normalGraphCanonicalNormalClass,
      normalGraphMetricNormalFromClass_mk] using
      (normalGraphMetricNormalFromClass_ne_zero period hPeriod metric displacement
        parameter hNonNull throat
        (normalGraphCanonicalNormalClass period hPeriod displacement parameter
          base)
        (normalGraphCanonicalNormalClass_ne_zero period hPeriod displacement
          parameter base))
  have hCoordinate :
      normalGraphLocalMetricNormalCoordinates period hPeriod metric displacement
        baseParameter ambientCoordinate baseParameter ≠ 0 := by
    intro hZero
    rw [normalGraphLocalMetricNormalCoordinates_eq_intrinsic period hPeriod
      metric displacement baseParameter baseParameter hNonNull hTangent
      hCotangent hImage] at hZero
    rw [hAmbientInverse] at hZero
    apply hIntrinsicNormal
    let ambientEquiv := ambientTrivialization.continuousLinearEquivAt Real graph
      hImage
    have hZero' : ambientEquiv
        (normalGraphMetricNormal period hPeriod metric displacement parameter
          hNonNull throat
          (normalGraphCanonicalLatitudeVector period hPeriod displacement
            parameter base)) = 0 := by
      simpa [ambientEquiv, ambientTrivialization, graph, baseParameter, throat]
        using hZero
    exact ambientEquiv.injective (by simpa using hZero')
  have hSquare := normalGraphLocalMetricNormalSquareCoordinates_ne_zero period
    hPeriod metric displacement baseParameter hNonNull ambientCoordinate
      hCoordinate
  simpa only [normalGraphCanonicalMetricNormalSquareCoordinates,
    normalGraphCanonicalMetricNormalCoordinates,
    normalGraphOrientationBoundaryParameter,
    normalGraphLocalMetricNormalSquareCoordinates,
    normalGraphLocalMetricNormalCoordinates, throat, baseParameter,
    ambientCoordinate] using hSquare

private def normalGraphCanonicalMetricUnitNormalCoordinates
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (base current : OrientationBoundary period hPeriod) :
    CoverCoordinates :=
  (Real.sqrt
    |normalGraphCanonicalMetricNormalSquareCoordinates period hPeriod metric
      displacement parameter base current|)⁻¹ •
    normalGraphCanonicalMetricNormalCoordinates period hPeriod metric
      displacement parameter base current

private theorem normalGraphCanonicalMetricUnitNormalCoordinates_contMDiffAt
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (base : OrientationBoundary period hPeriod) :
    ContMDiffAt throatCoverModelWithCorners 𝓘(Real, CoverCoordinates) ∞
      (normalGraphCanonicalMetricUnitNormalCoordinates period hPeriod metric
        displacement parameter base) base := by
  have hNormal := normalGraphCanonicalMetricNormalCoordinates_contMDiffAt period
    hPeriod metric displacement parameter hNonNull base
  have hSquare :=
    normalGraphCanonicalMetricNormalSquareCoordinates_contMDiffAt period hPeriod
      metric displacement parameter hNonNull base
  have hSquareNe :=
    normalGraphCanonicalMetricNormalSquareCoordinates_ne_zero period hPeriod
      metric displacement parameter hNonNull base
  have hAbs : ContMDiffAt throatCoverModelWithCorners 𝓘(Real, Real) ∞
      (fun current =>
        |normalGraphCanonicalMetricNormalSquareCoordinates period hPeriod metric
          displacement parameter base current|) base := by
    simpa [Function.comp_def] using
      (contDiffAt_abs hSquareNe).comp_contMDiffAt hSquare
  have hAbsPositive : 0 <
      |normalGraphCanonicalMetricNormalSquareCoordinates period hPeriod metric
        displacement parameter base base| :=
    abs_pos.mpr hSquareNe
  have hRoot : ContMDiffAt throatCoverModelWithCorners 𝓘(Real, Real) ∞
      (fun current => Real.sqrt
        |normalGraphCanonicalMetricNormalSquareCoordinates period hPeriod metric
          displacement parameter base current|) base := by
    simpa [Function.comp_def] using
      (Real.contDiffAt_sqrt (ne_of_gt hAbsPositive)).comp_contMDiffAt
        (I := throatCoverModelWithCorners)
        (f := fun current =>
          |normalGraphCanonicalMetricNormalSquareCoordinates period hPeriod
            metric displacement parameter base current|)
        (x := base) hAbs
  exact (hRoot.inv₀ (Real.sqrt_ne_zero'.mpr hAbsPositive)).smul hNormal

private theorem normalGraphCanonicalMetricNormalCoordinates_eq_intrinsic
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (base current : OrientationBoundary period hPeriod)
    (hTangent : orientationDoubleToThroat period hPeriod current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod)
        (orientationDoubleToThroat period hPeriod base)).baseSet)
    (hCotangent : orientationDoubleToThroat period hPeriod current ∈
      (trivializationAt (ThroatCoverCoordinates →L[Real] Real)
        (ThroatCotangentFiber period hPeriod)
        (orientationDoubleToThroat period hPeriod base)).baseSet)
    (hImage : normalGraphOrientationDouble period hPeriod displacement
        (current, parameter) ∈
      (trivializationAt CoverCoordinates
        (fun point : EffectiveQuotient period hPeriod =>
          TangentSpace coverModelWithCorners point)
        (normalGraphOrientationDouble period hPeriod displacement
          (base, parameter))).baseSet) :
    normalGraphCanonicalMetricNormalCoordinates period hPeriod metric
        displacement parameter base current =
      (trivializationAt CoverCoordinates
        (fun point : EffectiveQuotient period hPeriod =>
          TangentSpace coverModelWithCorners point)
        (normalGraphOrientationDouble period hPeriod displacement
          (base, parameter))).linearMapAt Real
        (normalGraphOrientationDouble period hPeriod displacement
          (current, parameter))
        (normalGraphMetricNormal period hPeriod metric displacement parameter
          hNonNull (orientationDoubleToThroat period hPeriod current)
          (normalGraphCanonicalLatitudeVector period hPeriod displacement
            parameter current)) := by
  let ambientTrivialization := trivializationAt CoverCoordinates
    (fun point : EffectiveQuotient period hPeriod =>
      TangentSpace coverModelWithCorners point)
    (normalGraphOrientationDouble period hPeriod displacement (base, parameter))
  let ambientCoordinate := normalGraphCanonicalLatitudeCoordinates period
    hPeriod displacement parameter base current
  have hAmbientCoordinate : ambientCoordinate =
      ambientTrivialization.linearMapAt Real
        (normalGraphOrientationDouble period hPeriod displacement
          (current, parameter))
        (normalGraphCanonicalLatitudeVector period hPeriod displacement
          parameter current) := by
    unfold ambientCoordinate normalGraphCanonicalLatitudeCoordinates
    change
      (ambientTrivialization
        (normalGraphCanonicalLatitudeLift period hPeriod displacement parameter
          current)).2 = _
    rw [← normalGraphCanonicalLatitudeVector_total period hPeriod displacement
      parameter current]
    rw [Trivialization.linearMapAt_apply, if_pos hImage]
  have hAmbientInverse :
      ambientTrivialization.symm
          (normalGraphOrientationDouble period hPeriod displacement
            (current, parameter)) ambientCoordinate =
        normalGraphCanonicalLatitudeVector period hPeriod displacement parameter
          current := by
    rw [hAmbientCoordinate]
    exact ambientTrivialization.symm_linearMapAt hImage _
  change normalGraphLocalMetricNormalCoordinates period hPeriod metric
      displacement
      (normalGraphOrientationBoundaryParameter period hPeriod parameter base)
      ambientCoordinate
      (normalGraphOrientationBoundaryParameter period hPeriod parameter current) =
    ambientTrivialization.linearMapAt Real
      (normalGraphOrientationDouble period hPeriod displacement
        (current, parameter))
      (normalGraphMetricNormal period hPeriod metric displacement parameter
        hNonNull (orientationDoubleToThroat period hPeriod current)
        (normalGraphCanonicalLatitudeVector period hPeriod displacement
          parameter current))
  rw [normalGraphLocalMetricNormalCoordinates_eq_intrinsic period hPeriod metric
    displacement
    (normalGraphOrientationBoundaryParameter period hPeriod parameter base)
    (normalGraphOrientationBoundaryParameter period hPeriod parameter current)
    hNonNull hTangent hCotangent hImage]
  dsimp [ambientTrivialization, normalGraphOrientationBoundaryParameter,
    normalGraphOrientationDouble] at hAmbientInverse ⊢
  rw [hAmbientInverse]
  rfl

private theorem normalGraphCanonicalMetricNormalSquareCoordinates_eq_intrinsic
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (base current : OrientationBoundary period hPeriod)
    (hTangent : orientationDoubleToThroat period hPeriod current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod)
        (orientationDoubleToThroat period hPeriod base)).baseSet)
    (hCotangent : orientationDoubleToThroat period hPeriod current ∈
      (trivializationAt (ThroatCoverCoordinates →L[Real] Real)
        (ThroatCotangentFiber period hPeriod)
        (orientationDoubleToThroat period hPeriod base)).baseSet)
    (hImage : normalGraphOrientationDouble period hPeriod displacement
        (current, parameter) ∈
      (trivializationAt CoverCoordinates
        (fun point : EffectiveQuotient period hPeriod =>
          TangentSpace coverModelWithCorners point)
        (normalGraphOrientationDouble period hPeriod displacement
          (base, parameter))).baseSet) :
    normalGraphCanonicalMetricNormalSquareCoordinates period hPeriod metric
        displacement parameter base current =
      metric.tensor.tensor
        (normalGraphOrientationDouble period hPeriod displacement
          (current, parameter))
        (normalGraphMetricNormal period hPeriod metric displacement parameter
          hNonNull (orientationDoubleToThroat period hPeriod current)
          (normalGraphCanonicalLatitudeVector period hPeriod displacement
            parameter current))
        (normalGraphMetricNormal period hPeriod metric displacement parameter
          hNonNull (orientationDoubleToThroat period hPeriod current)
          (normalGraphCanonicalLatitudeVector period hPeriod displacement
            parameter current)) := by
  unfold normalGraphCanonicalMetricNormalSquareCoordinates
  rw [normalGraphCanonicalMetricNormalCoordinates_eq_intrinsic period hPeriod
      metric displacement parameter hNonNull base current hTangent hCotangent
      hImage]
  rw [show normalGraphFamilyAmbientTensorCoordinates period hPeriod metric
      displacement
      (normalGraphOrientationBoundaryParameter period hPeriod parameter base)
      (normalGraphOrientationBoundaryParameter period hPeriod parameter current) =
    ContinuousLinearMap.inCoordinates CoverCoordinates
      (fun point : EffectiveQuotient period hPeriod =>
        TangentSpace coverModelWithCorners point)
      (CoverCoordinates →L[Real] Real)
      (fun point : EffectiveQuotient period hPeriod =>
        TangentSpace coverModelWithCorners point →L[Real] Real)
      (normalGraphOrientationDouble period hPeriod displacement
        (base, parameter))
      (normalGraphOrientationDouble period hPeriod displacement
        (current, parameter))
      (normalGraphOrientationDouble period hPeriod displacement
        (base, parameter))
      (normalGraphOrientationDouble period hPeriod displacement
        (current, parameter))
      (metric.tensor.tensor
        (normalGraphOrientationDouble period hPeriod displacement
          (current, parameter))) by
    rfl]
  rw [inCoordinates_apply_eq₂ hImage hImage (Set.mem_univ _)]
  simp only [Trivialization.symm_linearMapAt _ hImage]
  simp

private theorem normalGraphCanonicalMetricUnitNormalCoordinates_eq_intrinsic
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (base current : OrientationBoundary period hPeriod)
    (hTangent : orientationDoubleToThroat period hPeriod current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod)
        (orientationDoubleToThroat period hPeriod base)).baseSet)
    (hCotangent : orientationDoubleToThroat period hPeriod current ∈
      (trivializationAt (ThroatCoverCoordinates →L[Real] Real)
        (ThroatCotangentFiber period hPeriod)
        (orientationDoubleToThroat period hPeriod base)).baseSet)
    (hImage : normalGraphOrientationDouble period hPeriod displacement
        (current, parameter) ∈
      (trivializationAt CoverCoordinates
        (fun point : EffectiveQuotient period hPeriod =>
          TangentSpace coverModelWithCorners point)
        (normalGraphOrientationDouble period hPeriod displacement
          (base, parameter))).baseSet) :
    normalGraphCanonicalMetricUnitNormalCoordinates period hPeriod metric
        displacement parameter base current =
      (trivializationAt CoverCoordinates
        (fun point : EffectiveQuotient period hPeriod =>
          TangentSpace coverModelWithCorners point)
        (normalGraphOrientationDouble period hPeriod displacement
          (base, parameter))).linearMapAt Real
        (normalGraphOrientationDouble period hPeriod displacement
          (current, parameter))
        (normalGraphCanonicalMetricUnitNormal period hPeriod metric displacement
          parameter hNonNull current) := by
  unfold normalGraphCanonicalMetricUnitNormalCoordinates
    normalGraphCanonicalMetricUnitNormal normalGraphMetricUnitNormal
    normalGraphMetricNormalSquare normalGraphCanonicalNormalClass
  rw [normalGraphMetricNormalFromClass_mk]
  rw [normalGraphCanonicalMetricNormalCoordinates_eq_intrinsic period hPeriod
      metric displacement parameter hNonNull base current hTangent hCotangent
      hImage,
    normalGraphCanonicalMetricNormalSquareCoordinates_eq_intrinsic period hPeriod
      metric displacement parameter hNonNull base current hTangent hCotangent
      hImage]
  dsimp [normalGraphOrientationDouble]
  rw [map_smul]
  rfl

/-- The canonical metric unit normal is a genuine smooth tangent field along
the full moving orientation boundary. -/
theorem normalGraphCanonicalMetricUnitNormalLift_contMDiff
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter) :
    ContMDiff throatCoverModelWithCorners coverModelWithCorners.tangent ∞
      (normalGraphCanonicalMetricUnitNormalLift period hPeriod metric
        displacement parameter hNonNull) := by
  intro base
  rw [contMDiffAt_totalSpace]
  constructor
  · have hPair : ContMDiff throatCoverModelWithCorners
        (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real)) ∞
        (fun boundary : OrientationBoundary period hPeriod =>
          (boundary, parameter)) :=
      contMDiff_id.prodMk contMDiff_const
    exact ((normalGraphOrientationDouble_contMDiff period hPeriod displacement)
      |>.comp hPair).contMDiffAt
  · let throatTrivialization := trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod)
      (orientationDoubleToThroat period hPeriod base)
    let cotangentTrivialization :=
      trivializationAt (ThroatCoverCoordinates →L[Real] Real)
        (ThroatCotangentFiber period hPeriod)
        (orientationDoubleToThroat period hPeriod base)
    let ambientTrivialization := trivializationAt CoverCoordinates
      (fun point : EffectiveQuotient period hPeriod =>
        TangentSpace coverModelWithCorners point)
      (normalGraphOrientationDouble period hPeriod displacement
        (base, parameter))
    have hThroatBase : orientationDoubleToThroat period hPeriod base ∈
        throatTrivialization.baseSet :=
      mem_baseSet_trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod)
        (orientationDoubleToThroat period hPeriod base)
    have hCotangentBase : orientationDoubleToThroat period hPeriod base ∈
        cotangentTrivialization.baseSet :=
      mem_baseSet_trivializationAt (ThroatCoverCoordinates →L[Real] Real)
        (ThroatCotangentFiber period hPeriod)
        (orientationDoubleToThroat period hPeriod base)
    have hImageBase : normalGraphOrientationDouble period hPeriod displacement
          (base, parameter) ∈ ambientTrivialization.baseSet :=
      mem_baseSet_trivializationAt CoverCoordinates
        (fun point : EffectiveQuotient period hPeriod =>
          TangentSpace coverModelWithCorners point)
        (normalGraphOrientationDouble period hPeriod displacement
          (base, parameter))
    have hThroatEventually : ∀ᶠ current in 𝓝 base,
        orientationDoubleToThroat period hPeriod current ∈
          throatTrivialization.baseSet :=
      (orientationDoubleToThroat_contMDiff period hPeriod).continuous.continuousAt
        (throatTrivialization.open_baseSet.mem_nhds hThroatBase)
    have hCotangentEventually : ∀ᶠ current in 𝓝 base,
        orientationDoubleToThroat period hPeriod current ∈
          cotangentTrivialization.baseSet :=
      (orientationDoubleToThroat_contMDiff period hPeriod).continuous.continuousAt
        (cotangentTrivialization.open_baseSet.mem_nhds hCotangentBase)
    have hPair : ContMDiff throatCoverModelWithCorners
        (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real)) ∞
        (fun boundary : OrientationBoundary period hPeriod =>
          (boundary, parameter)) :=
      contMDiff_id.prodMk contMDiff_const
    have hGraphContinuous : Continuous
        (fun boundary : OrientationBoundary period hPeriod =>
          normalGraphOrientationDouble period hPeriod displacement
            (boundary, parameter)) :=
      ((normalGraphOrientationDouble_contMDiff period hPeriod displacement).comp
        hPair).continuous
    have hImageEventually : ∀ᶠ current in 𝓝 base,
        normalGraphOrientationDouble period hPeriod displacement
            (current, parameter) ∈ ambientTrivialization.baseSet :=
      hGraphContinuous.continuousAt
        (ambientTrivialization.open_baseSet.mem_nhds hImageBase)
    have hEventuallyEq :
        (fun current : OrientationBoundary period hPeriod =>
          (ambientTrivialization
            (normalGraphCanonicalMetricUnitNormalLift period hPeriod metric
              displacement parameter hNonNull current)).2) =ᶠ[𝓝 base]
          normalGraphCanonicalMetricUnitNormalCoordinates period hPeriod metric
            displacement parameter base := by
      filter_upwards [hThroatEventually, hCotangentEventually,
        hImageEventually] with current hTangent hCotangent hImage
      rw [normalGraphCanonicalMetricUnitNormalCoordinates_eq_intrinsic period
        hPeriod metric displacement parameter hNonNull base current hTangent
        hCotangent hImage]
      unfold normalGraphCanonicalMetricUnitNormalLift
      rw [Trivialization.linearMapAt_apply, if_pos hImage]
    exact
      (normalGraphCanonicalMetricUnitNormalCoordinates_contMDiffAt period hPeriod
        metric displacement parameter hNonNull base).congr_of_eventuallyEq
          hEventuallyEq

/-! ### Joint point--parameter local coordinates of the same physical normal -/

/-- The local inverse of the already proved orientation-double projection.
It is a germ through `boundary`, not a new global section. -/
def normalGraphOrientationLocalSection
    (boundary : OrientationBoundary period hPeriod) :
    EffectiveThroat period hPeriod → OrientationBoundary period hPeriod :=
  (orientationDoubleToThroat_isLocalDiffeomorph period hPeriod boundary)
    |>.localInverse

@[simp]
theorem normalGraphOrientationLocalSection_base
    (boundary : OrientationBoundary period hPeriod) :
    normalGraphOrientationLocalSection period hPeriod boundary
        (orientationDoubleToThroat period hPeriod boundary) = boundary := by
  let hLocal :=
    orientationDoubleToThroat_isLocalDiffeomorph period hPeriod boundary
  exact hLocal.localInverse_left_inv hLocal.localInverse_mem_target

theorem normalGraphOrientationLocalSection_contMDiffAt
    (boundary : OrientationBoundary period hPeriod) :
    ContMDiffAt throatCoverModelWithCorners throatCoverModelWithCorners ∞
      (normalGraphOrientationLocalSection period hPeriod boundary)
      (orientationDoubleToThroat period hPeriod boundary) :=
  (orientationDoubleToThroat_isLocalDiffeomorph period hPeriod boundary)
    |>.localInverse_contMDiffAt

theorem normalGraphOrientationLocalSection_eventually_reconstructs
    (boundary : OrientationBoundary period hPeriod) :
    (fun point => orientationDoubleToThroat period hPeriod
      (normalGraphOrientationLocalSection period hPeriod boundary point)) =ᶠ[
        𝓝 (orientationDoubleToThroat period hPeriod boundary)] id :=
  (orientationDoubleToThroat_isLocalDiffeomorph period hPeriod boundary)
    |>.localInverse_eventuallyEq_right

/-- Product extension of the local orientation section, preserving the graph
parameter exactly. -/
def normalGraphOrientationLocalSectionJoint
    (boundary : OrientationBoundary period hPeriod)
    (current : EffectiveThroat period hPeriod × Real) :
    OrientationBoundary period hPeriod × Real :=
  (normalGraphOrientationLocalSection period hPeriod boundary current.1,
    current.2)

@[simp]
theorem normalGraphOrientationLocalSectionJoint_base
    (boundary : OrientationBoundary period hPeriod) (parameter : Real) :
    normalGraphOrientationLocalSectionJoint period hPeriod boundary
        (orientationDoubleToThroat period hPeriod boundary, parameter) =
      (boundary, parameter) := by
  simp [normalGraphOrientationLocalSectionJoint]

theorem normalGraphOrientationLocalSectionJoint_contMDiffAt
    (boundary : OrientationBoundary period hPeriod) (parameter : Real) :
    ContMDiffAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real)) ∞
      (normalGraphOrientationLocalSectionJoint period hPeriod boundary)
      (orientationDoubleToThroat period hPeriod boundary, parameter) := by
  exact
    ((normalGraphOrientationLocalSection_contMDiffAt period hPeriod boundary)
      |>.comp
        (orientationDoubleToThroat period hPeriod boundary, parameter)
          contMDiffAt_fst).prodMk contMDiffAt_snd

private def normalGraphOrientationBoundaryJointParameter
    (current : OrientationBoundary period hPeriod × Real) :
    EffectiveThroat period hPeriod × Real :=
  (orientationDoubleToThroat period hPeriod current.1, current.2)

private theorem normalGraphOrientationBoundaryJointParameter_contMDiff :
    ContMDiff
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real)) ∞
      (normalGraphOrientationBoundaryJointParameter period hPeriod) :=
  ((orientationDoubleToThroat_contMDiff period hPeriod).comp contMDiff_fst).prodMk
    contMDiff_snd

/-- Joint coordinates of the already descended canonical latitude lift in the
fixed ambient tangent trivialization centred at `base`. -/
private def normalGraphCanonicalLatitudeJointCoordinates
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base current : OrientationBoundary period hPeriod × Real) :
    CoverCoordinates :=
  ((trivializationAt CoverCoordinates
      (fun point : EffectiveQuotient period hPeriod =>
        TangentSpace coverModelWithCorners point)
      (normalGraphOrientationDouble period hPeriod displacement base))
    (normalGraphCanonicalLatitudeLift period hPeriod displacement current.2
      current.1)).2

private theorem normalGraphCanonicalLatitudeJointCoordinates_contMDiffAt
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : OrientationBoundary period hPeriod × Real) :
    ContMDiffAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real CoverCoordinates) ∞
      (normalGraphCanonicalLatitudeJointCoordinates period hPeriod displacement
        base) base := by
  let trivialization := trivializationAt CoverCoordinates
    (fun point : EffectiveQuotient period hPeriod =>
      TangentSpace coverModelWithCorners point)
    (normalGraphOrientationDouble period hPeriod displacement base)
  have hLift : ContMDiffAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      coverModelWithCorners.tangent ∞
      (fun current : OrientationBoundary period hPeriod × Real =>
        normalGraphCanonicalLatitudeLift period hPeriod displacement current.2
          current.1) base :=
    (normalGraphCanonicalLatitudeLift_joint_contMDiff period hPeriod
      displacement).contMDiffAt
  have hMem : normalGraphCanonicalLatitudeLift period hPeriod displacement
      base.2 base.1 ∈ trivialization.source := by
    rw [trivialization.mem_source]
    change (normalGraphCanonicalLatitudeLift period hPeriod displacement
      base.2 base.1).1 ∈ trivialization.baseSet
    rw [normalGraphCanonicalLatitudeLift_base period hPeriod displacement
      base.2 base.1]
    exact mem_baseSet_trivializationAt CoverCoordinates
      (fun point : EffectiveQuotient period hPeriod =>
        TangentSpace coverModelWithCorners point)
      (normalGraphOrientationDouble period hPeriod displacement base)
  exact ((trivialization.contMDiffAt_iff
    (f := fun current : OrientationBoundary period hPeriod × Real =>
      normalGraphCanonicalLatitudeLift period hPeriod displacement current.2
        current.1) hMem).mp hLift).2

/-- The genuine intrinsic metric projector applied to the joint canonical
latitude lift.  This is a local coordinate representative, not a new normal. -/
private def normalGraphCanonicalMetricNormalJointCoordinates
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base current : OrientationBoundary period hPeriod × Real) :
    CoverCoordinates :=
  normalGraphMetricNormalProjectorCoordinates period hPeriod metric displacement
    (normalGraphOrientationBoundaryJointParameter period hPeriod base)
    (normalGraphOrientationBoundaryJointParameter period hPeriod current)
    (normalGraphCanonicalLatitudeJointCoordinates period hPeriod displacement
      base current)

private theorem normalGraphCanonicalMetricNormalJointCoordinates_contMDiffAt
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : OrientationBoundary period hPeriod × Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement base.2) :
    ContMDiffAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real CoverCoordinates) ∞
      (normalGraphCanonicalMetricNormalJointCoordinates period hPeriod metric
        displacement base) base := by
  have hParameter : ContMDiffAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real)) ∞
      (normalGraphOrientationBoundaryJointParameter period hPeriod) base :=
    (normalGraphOrientationBoundaryJointParameter_contMDiff period hPeriod)
      |>.contMDiffAt
  have hProjector :=
    (normalGraphMetricNormalProjectorCoordinates_contMDiffAt period hPeriod
      metric displacement
        (normalGraphOrientationBoundaryJointParameter period hPeriod base)
        hNonNull).comp base hParameter
  exact hProjector.clm_apply
    (normalGraphCanonicalLatitudeJointCoordinates_contMDiffAt period hPeriod
      displacement base)

private def normalGraphCanonicalMetricNormalSquareJointCoordinates
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base current : OrientationBoundary period hPeriod × Real) : Real :=
  normalGraphFamilyAmbientTensorCoordinates period hPeriod metric displacement
    (normalGraphOrientationBoundaryJointParameter period hPeriod base)
    (normalGraphOrientationBoundaryJointParameter period hPeriod current)
    (normalGraphCanonicalMetricNormalJointCoordinates period hPeriod metric
      displacement base current)
    (normalGraphCanonicalMetricNormalJointCoordinates period hPeriod metric
      displacement base current)

private theorem normalGraphCanonicalMetricNormalSquareJointCoordinates_contMDiffAt
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : OrientationBoundary period hPeriod × Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement base.2) :
    ContMDiffAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real Real) ∞
      (normalGraphCanonicalMetricNormalSquareJointCoordinates period hPeriod
        metric displacement base) base := by
  have hParameter : ContMDiffAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real)) ∞
      (normalGraphOrientationBoundaryJointParameter period hPeriod) base :=
    (normalGraphOrientationBoundaryJointParameter_contMDiff period hPeriod)
      |>.contMDiffAt
  have hMetric :=
    (normalGraphFamilyAmbientTensorCoordinates_contMDiffAt period hPeriod metric
      displacement
        (normalGraphOrientationBoundaryJointParameter period hPeriod base)).comp
      base hParameter
  have hNormal :=
    normalGraphCanonicalMetricNormalJointCoordinates_contMDiffAt period hPeriod
      metric displacement base hNonNull
  exact (hMetric.clm_apply hNormal).clm_apply hNormal

private theorem normalGraphCanonicalMetricNormalSquareJointCoordinates_ne_zero
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : OrientationBoundary period hPeriod × Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement base.2) :
    normalGraphCanonicalMetricNormalSquareJointCoordinates period hPeriod metric
      displacement base base ≠ 0 := by
  rcases base with ⟨boundary, parameter⟩
  simpa only [normalGraphCanonicalMetricNormalSquareJointCoordinates,
    normalGraphCanonicalMetricNormalJointCoordinates,
    normalGraphCanonicalLatitudeJointCoordinates,
    normalGraphOrientationBoundaryJointParameter,
    normalGraphCanonicalMetricNormalSquareCoordinates,
    normalGraphCanonicalMetricNormalCoordinates,
    normalGraphCanonicalLatitudeCoordinates,
    normalGraphOrientationBoundaryParameter] using
      (normalGraphCanonicalMetricNormalSquareCoordinates_ne_zero period hPeriod
        metric displacement parameter hNonNull boundary)

/-- Joint point--parameter coordinates of the same normalized physical normal
on the genuine non-null local germ. -/
def normalGraphCanonicalMetricUnitNormalJointCoordinates
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base current : OrientationBoundary period hPeriod × Real) :
    CoverCoordinates :=
  (Real.sqrt
    |normalGraphCanonicalMetricNormalSquareJointCoordinates period hPeriod
      metric displacement base current|)⁻¹ •
    normalGraphCanonicalMetricNormalJointCoordinates period hPeriod metric
      displacement base current

/-- The canonical physical normal has a genuinely joint smooth local
representative in boundary point and graph parameter. -/
theorem normalGraphCanonicalMetricUnitNormalJointCoordinates_contMDiffAt
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : OrientationBoundary period hPeriod × Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement base.2) :
    ContMDiffAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real CoverCoordinates) ∞
      (normalGraphCanonicalMetricUnitNormalJointCoordinates period hPeriod metric
        displacement base) base := by
  have hNormal :=
    normalGraphCanonicalMetricNormalJointCoordinates_contMDiffAt period hPeriod
      metric displacement base hNonNull
  have hSquare :=
    normalGraphCanonicalMetricNormalSquareJointCoordinates_contMDiffAt period
      hPeriod metric displacement base hNonNull
  have hSquareNe :=
    normalGraphCanonicalMetricNormalSquareJointCoordinates_ne_zero period
      hPeriod metric displacement base hNonNull
  have hAbs : ContMDiffAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real Real) ∞
      (fun current =>
        |normalGraphCanonicalMetricNormalSquareJointCoordinates period hPeriod
          metric displacement base current|) base := by
    simpa [Function.comp_def] using
      (contDiffAt_abs hSquareNe).comp_contMDiffAt hSquare
  have hAbsPositive : 0 <
      |normalGraphCanonicalMetricNormalSquareJointCoordinates period hPeriod
        metric displacement base base| :=
    abs_pos.mpr hSquareNe
  have hRoot : ContMDiffAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real Real) ∞
      (fun current => Real.sqrt
        |normalGraphCanonicalMetricNormalSquareJointCoordinates period hPeriod
          metric displacement base current|) base := by
    simpa [Function.comp_def] using
      (Real.contDiffAt_sqrt (ne_of_gt hAbsPositive)).comp_contMDiffAt
        (I := throatCoverModelWithCorners.prod
          (modelWithCornersSelf Real Real))
        (f := fun current =>
          |normalGraphCanonicalMetricNormalSquareJointCoordinates period hPeriod
            metric displacement base current|)
        (x := base) hAbs
  exact (hRoot.inv₀ (Real.sqrt_ne_zero'.mpr hAbsPositive)).smul hNormal

private theorem normalGraphCanonicalMetricNormalJointCoordinates_eq_intrinsic
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base current : OrientationBoundary period hPeriod × Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement current.2)
    (hTangent : orientationDoubleToThroat period hPeriod current.1 ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod)
        (orientationDoubleToThroat period hPeriod base.1)).baseSet)
    (hCotangent : orientationDoubleToThroat period hPeriod current.1 ∈
      (trivializationAt (ThroatCoverCoordinates →L[Real] Real)
        (ThroatCotangentFiber period hPeriod)
        (orientationDoubleToThroat period hPeriod base.1)).baseSet)
    (hImage : normalGraphOrientationDouble period hPeriod displacement current ∈
      (trivializationAt CoverCoordinates
        (fun point : EffectiveQuotient period hPeriod =>
          TangentSpace coverModelWithCorners point)
        (normalGraphOrientationDouble period hPeriod displacement base)).baseSet) :
    normalGraphCanonicalMetricNormalJointCoordinates period hPeriod metric
        displacement base current =
      (trivializationAt CoverCoordinates
        (fun point : EffectiveQuotient period hPeriod =>
          TangentSpace coverModelWithCorners point)
        (normalGraphOrientationDouble period hPeriod displacement base)).linearMapAt
          Real (normalGraphOrientationDouble period hPeriod displacement current)
          (normalGraphMetricNormal period hPeriod metric displacement current.2
            hNonNull (orientationDoubleToThroat period hPeriod current.1)
            (normalGraphCanonicalLatitudeVector period hPeriod displacement
              current.2 current.1)) := by
  let ambientTrivialization := trivializationAt CoverCoordinates
    (fun point : EffectiveQuotient period hPeriod =>
      TangentSpace coverModelWithCorners point)
    (normalGraphOrientationDouble period hPeriod displacement base)
  let ambientCoordinate :=
    normalGraphCanonicalLatitudeJointCoordinates period hPeriod displacement
      base current
  have hAmbientCoordinate : ambientCoordinate =
      ambientTrivialization.linearMapAt Real
        (normalGraphOrientationDouble period hPeriod displacement current)
        (normalGraphCanonicalLatitudeVector period hPeriod displacement
          current.2 current.1) := by
    unfold ambientCoordinate normalGraphCanonicalLatitudeJointCoordinates
    change
      (ambientTrivialization
        (normalGraphCanonicalLatitudeLift period hPeriod displacement current.2
          current.1)).2 = _
    rw [← normalGraphCanonicalLatitudeVector_total period hPeriod displacement
      current.2 current.1]
    rw [Trivialization.linearMapAt_apply, if_pos hImage]
  have hAmbientInverse :
      ambientTrivialization.symm
          (normalGraphOrientationDouble period hPeriod displacement current)
          ambientCoordinate =
        normalGraphCanonicalLatitudeVector period hPeriod displacement
          current.2 current.1 := by
    rw [hAmbientCoordinate]
    exact ambientTrivialization.symm_linearMapAt hImage _
  change normalGraphLocalMetricNormalCoordinates period hPeriod metric
      displacement
      (normalGraphOrientationBoundaryJointParameter period hPeriod base)
      ambientCoordinate
      (normalGraphOrientationBoundaryJointParameter period hPeriod current) =
    ambientTrivialization.linearMapAt Real
      (normalGraphOrientationDouble period hPeriod displacement current)
      (normalGraphMetricNormal period hPeriod metric displacement current.2
        hNonNull (orientationDoubleToThroat period hPeriod current.1)
        (normalGraphCanonicalLatitudeVector period hPeriod displacement
          current.2 current.1))
  rw [normalGraphLocalMetricNormalCoordinates_eq_intrinsic period hPeriod metric
    displacement
    (normalGraphOrientationBoundaryJointParameter period hPeriod base)
    (normalGraphOrientationBoundaryJointParameter period hPeriod current)
    hNonNull hTangent hCotangent hImage]
  dsimp [ambientTrivialization, normalGraphOrientationBoundaryJointParameter,
    normalGraphOrientationDouble] at hAmbientInverse ⊢
  rw [hAmbientInverse]
  rfl

private theorem normalGraphCanonicalMetricNormalSquareJointCoordinates_eq_intrinsic
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base current : OrientationBoundary period hPeriod × Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement current.2)
    (hTangent : orientationDoubleToThroat period hPeriod current.1 ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod)
        (orientationDoubleToThroat period hPeriod base.1)).baseSet)
    (hCotangent : orientationDoubleToThroat period hPeriod current.1 ∈
      (trivializationAt (ThroatCoverCoordinates →L[Real] Real)
        (ThroatCotangentFiber period hPeriod)
        (orientationDoubleToThroat period hPeriod base.1)).baseSet)
    (hImage : normalGraphOrientationDouble period hPeriod displacement current ∈
      (trivializationAt CoverCoordinates
        (fun point : EffectiveQuotient period hPeriod =>
          TangentSpace coverModelWithCorners point)
        (normalGraphOrientationDouble period hPeriod displacement base)).baseSet) :
    normalGraphCanonicalMetricNormalSquareJointCoordinates period hPeriod metric
        displacement base current =
      metric.tensor.tensor
        (normalGraphOrientationDouble period hPeriod displacement current)
        (normalGraphMetricNormal period hPeriod metric displacement current.2
          hNonNull (orientationDoubleToThroat period hPeriod current.1)
          (normalGraphCanonicalLatitudeVector period hPeriod displacement
            current.2 current.1))
        (normalGraphMetricNormal period hPeriod metric displacement current.2
          hNonNull (orientationDoubleToThroat period hPeriod current.1)
          (normalGraphCanonicalLatitudeVector period hPeriod displacement
            current.2 current.1)) := by
  unfold normalGraphCanonicalMetricNormalSquareJointCoordinates
  rw [normalGraphCanonicalMetricNormalJointCoordinates_eq_intrinsic period
    hPeriod metric displacement base current hNonNull hTangent hCotangent hImage]
  rw [show normalGraphFamilyAmbientTensorCoordinates period hPeriod metric
      displacement
      (normalGraphOrientationBoundaryJointParameter period hPeriod base)
      (normalGraphOrientationBoundaryJointParameter period hPeriod current) =
    ContinuousLinearMap.inCoordinates CoverCoordinates
      (fun point : EffectiveQuotient period hPeriod =>
        TangentSpace coverModelWithCorners point)
      (CoverCoordinates →L[Real] Real)
      (fun point : EffectiveQuotient period hPeriod =>
        TangentSpace coverModelWithCorners point →L[Real] Real)
      (normalGraphOrientationDouble period hPeriod displacement base)
      (normalGraphOrientationDouble period hPeriod displacement current)
      (normalGraphOrientationDouble period hPeriod displacement base)
      (normalGraphOrientationDouble period hPeriod displacement current)
      (metric.tensor.tensor
        (normalGraphOrientationDouble period hPeriod displacement current)) by
    rfl]
  rw [inCoordinates_apply_eq₂ hImage hImage (Set.mem_univ _)]
  simp only [Trivialization.symm_linearMapAt _ hImage]
  simp

/-- On every point where the fixed trivializations are valid, the joint
coordinate family is exactly the canonical physical unit normal. -/
theorem normalGraphCanonicalMetricUnitNormalJointCoordinates_eq_intrinsic
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base current : OrientationBoundary period hPeriod × Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement current.2)
    (hTangent : orientationDoubleToThroat period hPeriod current.1 ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod)
        (orientationDoubleToThroat period hPeriod base.1)).baseSet)
    (hCotangent : orientationDoubleToThroat period hPeriod current.1 ∈
      (trivializationAt (ThroatCoverCoordinates →L[Real] Real)
        (ThroatCotangentFiber period hPeriod)
        (orientationDoubleToThroat period hPeriod base.1)).baseSet)
    (hImage : normalGraphOrientationDouble period hPeriod displacement current ∈
      (trivializationAt CoverCoordinates
        (fun point : EffectiveQuotient period hPeriod =>
          TangentSpace coverModelWithCorners point)
        (normalGraphOrientationDouble period hPeriod displacement base)).baseSet) :
    normalGraphCanonicalMetricUnitNormalJointCoordinates period hPeriod metric
        displacement base current =
      (trivializationAt CoverCoordinates
        (fun point : EffectiveQuotient period hPeriod =>
          TangentSpace coverModelWithCorners point)
        (normalGraphOrientationDouble period hPeriod displacement base)).linearMapAt
          Real (normalGraphOrientationDouble period hPeriod displacement current)
          (normalGraphCanonicalMetricUnitNormal period hPeriod metric displacement
            current.2 hNonNull current.1) := by
  unfold normalGraphCanonicalMetricUnitNormalJointCoordinates
    normalGraphCanonicalMetricUnitNormal normalGraphMetricUnitNormal
    normalGraphMetricNormalSquare normalGraphCanonicalNormalClass
  rw [normalGraphMetricNormalFromClass_mk]
  rw [normalGraphCanonicalMetricNormalJointCoordinates_eq_intrinsic period
      hPeriod metric displacement base current hNonNull hTangent hCotangent
      hImage,
    normalGraphCanonicalMetricNormalSquareJointCoordinates_eq_intrinsic period
      hPeriod metric displacement base current hNonNull hTangent hCotangent
      hImage]
  dsimp [normalGraphOrientationDouble]
  rw [map_smul]
  rfl

/-- Local admissibility predicate for the fixed joint coordinate germ.  It
contains only the already installed non-null domain and trivialization opens. -/
def NormalGraphCanonicalJointCoordinateAdmissible
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base current : OrientationBoundary period hPeriod × Real) : Prop :=
  current.2 ∈ normalGraphNonNullDomain period hPeriod metric displacement ∧
    orientationDoubleToThroat period hPeriod current.1 ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod)
        (orientationDoubleToThroat period hPeriod base.1)).baseSet ∧
    orientationDoubleToThroat period hPeriod current.1 ∈
      (trivializationAt (ThroatCoverCoordinates →L[Real] Real)
        (ThroatCotangentFiber period hPeriod)
        (orientationDoubleToThroat period hPeriod base.1)).baseSet ∧
    normalGraphOrientationDouble period hPeriod displacement current ∈
      (trivializationAt CoverCoordinates
        (fun point : EffectiveQuotient period hPeriod =>
          TangentSpace coverModelWithCorners point)
        (normalGraphOrientationDouble period hPeriod displacement base)).baseSet

/-- Openness of the non-null domain and of the three fixed trivializations
gives a genuine neighborhood on which the pointwise intrinsic identity above
applies. -/
theorem normalGraphCanonicalJointCoordinateAdmissible_eventually
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : OrientationBoundary period hPeriod × Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement base.2) :
    ∀ᶠ current in 𝓝 base,
      NormalGraphCanonicalJointCoordinateAdmissible period hPeriod metric
        displacement base current := by
  let throatTrivialization := trivializationAt ThroatCoverCoordinates
    (ThroatTangentFiber period hPeriod)
    (orientationDoubleToThroat period hPeriod base.1)
  let cotangentTrivialization :=
    trivializationAt (ThroatCoverCoordinates →L[Real] Real)
      (ThroatCotangentFiber period hPeriod)
      (orientationDoubleToThroat period hPeriod base.1)
  let ambientTrivialization := trivializationAt CoverCoordinates
    (fun point : EffectiveQuotient period hPeriod =>
      TangentSpace coverModelWithCorners point)
    (normalGraphOrientationDouble period hPeriod displacement base)
  have hThroatBase : orientationDoubleToThroat period hPeriod base.1 ∈
      throatTrivialization.baseSet :=
    mem_baseSet_trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod)
      (orientationDoubleToThroat period hPeriod base.1)
  have hCotangentBase : orientationDoubleToThroat period hPeriod base.1 ∈
      cotangentTrivialization.baseSet :=
    mem_baseSet_trivializationAt (ThroatCoverCoordinates →L[Real] Real)
      (ThroatCotangentFiber period hPeriod)
      (orientationDoubleToThroat period hPeriod base.1)
  have hImageBase : normalGraphOrientationDouble period hPeriod displacement base ∈
      ambientTrivialization.baseSet :=
    mem_baseSet_trivializationAt CoverCoordinates
      (fun point : EffectiveQuotient period hPeriod =>
        TangentSpace coverModelWithCorners point)
      (normalGraphOrientationDouble period hPeriod displacement base)
  have hNonNullEventually : ∀ᶠ current in 𝓝 base,
      current.2 ∈ normalGraphNonNullDomain period hPeriod metric displacement :=
    continuous_snd.continuousAt
      ((normalGraphNonNullDomain_isOpen period hPeriod metric displacement)
        |>.mem_nhds hNonNull)
  have hThroatEventually : ∀ᶠ current in 𝓝 base,
      orientationDoubleToThroat period hPeriod current.1 ∈
        throatTrivialization.baseSet :=
    ((orientationDoubleToThroat_contMDiff period hPeriod).continuous.comp
      continuous_fst).continuousAt
        (throatTrivialization.open_baseSet.mem_nhds hThroatBase)
  have hCotangentEventually : ∀ᶠ current in 𝓝 base,
      orientationDoubleToThroat period hPeriod current.1 ∈
        cotangentTrivialization.baseSet :=
    ((orientationDoubleToThroat_contMDiff period hPeriod).continuous.comp
      continuous_fst).continuousAt
        (cotangentTrivialization.open_baseSet.mem_nhds hCotangentBase)
  have hImageEventually : ∀ᶠ current in 𝓝 base,
      normalGraphOrientationDouble period hPeriod displacement current ∈
        ambientTrivialization.baseSet :=
    (normalGraphOrientationDouble_contMDiff period hPeriod displacement)
      |>.continuous.continuousAt
        (ambientTrivialization.open_baseSet.mem_nhds hImageBase)
  filter_upwards [hNonNullEventually, hThroatEventually, hCotangentEventually,
    hImageEventually] with current hCurrent hTangent hCotangent hImage
  exact ⟨hCurrent, hTangent, hCotangent, hImage⟩

/-- At the anchor, the joint representative is definitionally the previously
proved physical canonical unit normal coordinate. -/
theorem normalGraphCanonicalMetricUnitNormalJointCoordinates_base_eq
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : OrientationBoundary period hPeriod) :
    normalGraphCanonicalMetricUnitNormalJointCoordinates period hPeriod metric
        displacement (boundary, parameter) (boundary, parameter) =
      normalGraphCanonicalMetricUnitNormalCoordinates period hPeriod metric
        displacement parameter boundary boundary :=
  rfl

/-- The anchor value of the joint coordinates reconstructs the same physical
unit normal in the ambient tangent fiber. -/
theorem normalGraphCanonicalMetricUnitNormalJointCoordinates_base_reconstructs
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : OrientationBoundary period hPeriod) :
    (trivializationAt CoverCoordinates
      (fun point : EffectiveQuotient period hPeriod =>
        TangentSpace coverModelWithCorners point)
      (normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter))).symm
        (normalGraphOrientationDouble period hPeriod displacement
          (boundary, parameter))
        (normalGraphCanonicalMetricUnitNormalJointCoordinates period hPeriod
          metric displacement (boundary, parameter) (boundary, parameter)) =
      normalGraphCanonicalMetricUnitNormal period hPeriod metric displacement
        parameter hNonNull boundary := by
  let throatTrivialization := trivializationAt ThroatCoverCoordinates
    (ThroatTangentFiber period hPeriod)
    (orientationDoubleToThroat period hPeriod boundary)
  let cotangentTrivialization :=
    trivializationAt (ThroatCoverCoordinates →L[Real] Real)
      (ThroatCotangentFiber period hPeriod)
      (orientationDoubleToThroat period hPeriod boundary)
  let ambientTrivialization := trivializationAt CoverCoordinates
    (fun point : EffectiveQuotient period hPeriod =>
      TangentSpace coverModelWithCorners point)
    (normalGraphOrientationDouble period hPeriod displacement
      (boundary, parameter))
  have hTangent : orientationDoubleToThroat period hPeriod boundary ∈
      throatTrivialization.baseSet :=
    mem_baseSet_trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod)
      (orientationDoubleToThroat period hPeriod boundary)
  have hCotangent : orientationDoubleToThroat period hPeriod boundary ∈
      cotangentTrivialization.baseSet :=
    mem_baseSet_trivializationAt (ThroatCoverCoordinates →L[Real] Real)
      (ThroatCotangentFiber period hPeriod)
      (orientationDoubleToThroat period hPeriod boundary)
  have hImage : normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter) ∈ ambientTrivialization.baseSet :=
    mem_baseSet_trivializationAt CoverCoordinates
      (fun point : EffectiveQuotient period hPeriod =>
        TangentSpace coverModelWithCorners point)
      (normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter))
  rw [normalGraphCanonicalMetricUnitNormalJointCoordinates_base_eq period
    hPeriod metric displacement parameter hNonNull boundary]
  rw [normalGraphCanonicalMetricUnitNormalCoordinates_eq_intrinsic period
    hPeriod metric displacement parameter hNonNull boundary boundary hTangent
    hCotangent hImage]
  exact ambientTrivialization.symm_linearMapAt hImage _

/-- The joint physical normal written in one fixed holonomic inverse germ.
The source tangent coordinates are exactly the joint coordinates above; the
target is a model space, so no atlas choice is added. -/
def normalGraphCanonicalHolonomicMetricUnitNormalJointCoordinates
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : OrientationBoundary period hPeriod × Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (current : OrientationBoundary period hPeriod × Real) : HolonomicVector4 :=
  let graph := fun point : OrientationBoundary period hPeriod × Real =>
    normalGraphOrientationDouble period hPeriod displacement point
  let localInverse :=
    (patch.coordinateMap_isLocalDiffeomorph coordinate).localInverse
  inTangentCoordinates coverModelWithCorners
      (modelWithCornersSelf Real HolonomicVector4) graph
      (fun point => localInverse (graph point))
      (fun point => mfderiv coverModelWithCorners
        (modelWithCornersSelf Real HolonomicVector4) localInverse (graph point))
      base current
      (normalGraphCanonicalMetricUnitNormalJointCoordinates period hPeriod metric
        displacement base current)

/-- Joint smoothness survives passage to a genuine holonomic chart. -/
theorem normalGraphCanonicalHolonomicMetricUnitNormalJointCoordinates_contMDiffAt
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : OrientationBoundary period hPeriod × Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement base.2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement base) :
    ContMDiffAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real HolonomicVector4) ∞
      (normalGraphCanonicalHolonomicMetricUnitNormalJointCoordinates period
        hPeriod metric displacement base patch coordinate) base := by
  let graph := fun point : OrientationBoundary period hPeriod × Real =>
    normalGraphOrientationDouble period hPeriod displacement point
  let localInverse :=
    (patch.coordinateMap_isLocalDiffeomorph coordinate).localInverse
  have hInverse : ContMDiffAt coverModelWithCorners
      (modelWithCornersSelf Real HolonomicVector4) ∞ localInverse (graph base) := by
    change ContMDiffAt coverModelWithCorners
      (modelWithCornersSelf Real HolonomicVector4) ∞ localInverse
      (normalGraphOrientationDouble period hPeriod displacement base)
    rw [← hAt]
    exact (patch.coordinateMap_isLocalDiffeomorph coordinate)
      |>.localInverse_contMDiffAt
  have hUncurry : ContMDiffAt
      ((throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real)).prod
        coverModelWithCorners)
      (modelWithCornersSelf Real HolonomicVector4) ∞
      (Function.uncurry (fun _ : OrientationBoundary period hPeriod × Real =>
        localInverse)) (base, graph base) := by
    change ContMDiffAt
      ((throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real)).prod
        coverModelWithCorners)
      (modelWithCornersSelf Real HolonomicVector4) ∞
      (fun current => localInverse current.2) (base, graph base)
    exact hInverse.comp (base, graph base) contMDiffAt_snd
  have hGraph : ContMDiffAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      coverModelWithCorners ∞ graph base :=
    (normalGraphOrientationDouble_contMDiff period hPeriod displacement)
      |>.contMDiffAt
  have hUnit :=
    normalGraphCanonicalMetricUnitNormalJointCoordinates_contMDiffAt period
      hPeriod metric displacement base hNonNull
  have hApplied := ContMDiffAt.mfderiv_apply
    (I := coverModelWithCorners)
    (I' := modelWithCornersSelf Real HolonomicVector4)
    (f := fun _ : OrientationBoundary period hPeriod × Real => localInverse)
    (g := graph) (g₁ := id)
    (g₂ := normalGraphCanonicalMetricUnitNormalJointCoordinates period hPeriod
      metric displacement base)
    hUncurry hGraph contMDiffAt_id hUnit (by simp)
  exact hApplied

/-- Wherever the fixed source trivialization is valid, the joint holonomic
family is the derivative of the same fixed inverse chart applied to the
canonical physical normal. -/
theorem normalGraphCanonicalHolonomicMetricUnitNormalJointCoordinates_eq_intrinsic
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base current : OrientationBoundary period hPeriod × Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement current.2)
    (hTangent : orientationDoubleToThroat period hPeriod current.1 ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod)
        (orientationDoubleToThroat period hPeriod base.1)).baseSet)
    (hCotangent : orientationDoubleToThroat period hPeriod current.1 ∈
      (trivializationAt (ThroatCoverCoordinates →L[Real] Real)
        (ThroatCotangentFiber period hPeriod)
        (orientationDoubleToThroat period hPeriod base.1)).baseSet)
    (hImage : normalGraphOrientationDouble period hPeriod displacement current ∈
      (trivializationAt CoverCoordinates
        (fun point : EffectiveQuotient period hPeriod =>
          TangentSpace coverModelWithCorners point)
        (normalGraphOrientationDouble period hPeriod displacement base)).baseSet)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4) :
    normalGraphCanonicalHolonomicMetricUnitNormalJointCoordinates period
        hPeriod metric displacement base patch coordinate current =
      mfderiv coverModelWithCorners
        (modelWithCornersSelf Real HolonomicVector4)
        (patch.coordinateMap_isLocalDiffeomorph coordinate).localInverse
        (normalGraphOrientationDouble period hPeriod displacement current)
        (normalGraphCanonicalMetricUnitNormal period hPeriod metric displacement
          current.2 hNonNull current.1) := by
  unfold normalGraphCanonicalHolonomicMetricUnitNormalJointCoordinates
    inTangentCoordinates
  rw [normalGraphCanonicalMetricUnitNormalJointCoordinates_eq_intrinsic period
    hPeriod metric displacement base current hNonNull hTangent hCotangent hImage]
  simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply,
    Trivialization.symmL_apply]
  rw [Trivialization.symm_linearMapAt _ hImage]
  rw [TangentBundle.continuousLinearMapAt_model_space]
  rfl

/-- At its anchor, the joint holonomic representative is the derivative of
the fixed local inverse applied to the reconstructed physical normal. -/
theorem normalGraphCanonicalHolonomicMetricUnitNormalJointCoordinates_base_formula
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : OrientationBoundary period hPeriod × Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4) :
    normalGraphCanonicalHolonomicMetricUnitNormalJointCoordinates period
        hPeriod metric displacement base patch coordinate base =
      mfderiv coverModelWithCorners
        (modelWithCornersSelf Real HolonomicVector4)
        (patch.coordinateMap_isLocalDiffeomorph coordinate).localInverse
        (normalGraphOrientationDouble period hPeriod displacement base)
        ((trivializationAt CoverCoordinates
          (fun point : EffectiveQuotient period hPeriod =>
            TangentSpace coverModelWithCorners point)
          (normalGraphOrientationDouble period hPeriod displacement base)).symm
            (normalGraphOrientationDouble period hPeriod displacement base)
            (normalGraphCanonicalMetricUnitNormalJointCoordinates period
              hPeriod metric displacement base base)) := by
  simp [normalGraphCanonicalHolonomicMetricUnitNormalJointCoordinates,
    inTangentCoordinates, ContinuousLinearMap.inCoordinates,
    Trivialization.symmL_apply]
  rfl

/-! ### Global coorientation in the genuine holonomic Gauss formula -/

/-- Coordinate vector of the global canonical metric unit normal in one
genuine holonomic chart through the graph point. -/
def normalGraphCanonicalHolonomicMetricUnitNormalCoordinatesAt
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : OrientationBoundary period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter)) : HolonomicVector4 :=
  let derivativeEquiv :=
    (patch.coordinateMap_isLocalDiffeomorph coordinate)
      |>.mfderivToContinuousLinearEquiv (by simp)
  derivativeEquiv.symm
    (hAt.symm ▸ normalGraphCanonicalMetricUnitNormal period hPeriod metric
      displacement parameter hNonNull boundary)

/-- At the anchor, the jointly smooth holonomic family is exactly the
previously established physical holonomic normal, including its dependent
tangent-fiber transport. -/
theorem normalGraphCanonicalHolonomicMetricUnitNormalJointCoordinates_base_eq
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : OrientationBoundary period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter)) :
    normalGraphCanonicalHolonomicMetricUnitNormalJointCoordinates period
        hPeriod metric displacement (boundary, parameter) patch coordinate
          (boundary, parameter) =
      normalGraphCanonicalHolonomicMetricUnitNormalCoordinatesAt period hPeriod
        metric displacement parameter hNonNull boundary patch coordinate hAt := by
  rw [normalGraphCanonicalHolonomicMetricUnitNormalJointCoordinates_base_formula
    period hPeriod metric displacement (boundary, parameter) patch coordinate]
  rw [normalGraphCanonicalMetricUnitNormalJointCoordinates_base_reconstructs
    period hPeriod metric displacement parameter hNonNull boundary]
  unfold normalGraphCanonicalHolonomicMetricUnitNormalCoordinatesAt
  let derivativeEquiv :=
    (patch.coordinateMap_isLocalDiffeomorph coordinate)
      |>.mfderivToContinuousLinearEquiv (by simp)
  have hTransport (point : EffectiveQuotient period hPeriod)
      (hPoint : patch.coordinateMap coordinate = point)
      (vector : TangentSpace coverModelWithCorners point) :
      mfderiv coverModelWithCorners
          (modelWithCornersSelf Real HolonomicVector4)
          (patch.coordinateMap_isLocalDiffeomorph coordinate).localInverse point
          vector =
        derivativeEquiv.symm (hPoint.symm ▸ vector) := by
    subst point
    rfl
  exact hTransport _ hAt _

/-- The holonomic coordinate vector reconstructs exactly the already proved
global normal; it is not a separately chosen local coorientation. -/
theorem normalGraphCanonicalHolonomicMetricUnitNormalCoordinatesAt_reconstructs
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : OrientationBoundary period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter)) :
    mfderiv (modelWithCornersSelf Real HolonomicVector4) coverModelWithCorners
        patch.coordinateMap coordinate
        (normalGraphCanonicalHolonomicMetricUnitNormalCoordinatesAt period
          hPeriod metric displacement parameter hNonNull boundary patch
            coordinate hAt) =
      hAt.symm ▸ normalGraphCanonicalMetricUnitNormal period hPeriod metric
        displacement parameter hNonNull boundary := by
  let derivativeEquiv :=
    (patch.coordinateMap_isLocalDiffeomorph coordinate)
      |>.mfderivToContinuousLinearEquiv (by simp)
  rw [← (patch.coordinateMap_isLocalDiffeomorph coordinate)
    |>.mfderivToContinuousLinearEquiv_coe (by simp)]
  exact derivativeEquiv.apply_symm_apply _

/-- The canonical coordinate normal is orthogonal to the source-chart
differential of the same moving graph. -/
theorem normalGraphCanonicalHolonomicMetricUnitNormalCoordinatesAt_orthogonal
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : OrientationBoundary period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter))
    (tangent : ThroatCoverCoordinates) :
    localMetricCoordinateForm period hPeriod metric patch coordinate
        (normalGraphCanonicalHolonomicMetricUnitNormalCoordinatesAt period
          hPeriod metric displacement parameter hNonNull boundary patch
            coordinate hAt)
        (normalGraphHolonomicSourceFirstDerivativeCoordinatesAt period hPeriod
          displacement
            (orientationDoubleToThroat period hPeriod boundary, parameter)
            patch coordinate tangent) = 0 := by
  let base : EffectiveThroat period hPeriod × Real :=
    (orientationDoubleToThroat period hPeriod boundary, parameter)
  have hGraph : patch.coordinateMap coordinate =
      normalGraph period hPeriod displacement base.2 base.1 := by
    simpa [base, normalGraphOrientationDouble] using hAt
  let coordinateNormal :=
    normalGraphCanonicalHolonomicMetricUnitNormalCoordinatesAt period hPeriod
      metric displacement parameter hNonNull boundary patch coordinate hAt
  let intrinsicNormal :=
    normalGraphCanonicalMetricUnitNormal period hPeriod metric displacement
      parameter hNonNull boundary
  let coordinateTangent :=
    normalGraphHolonomicSourceFirstDerivativeCoordinatesAt period hPeriod
      displacement base patch coordinate tangent
  let intrinsicTangent :=
    mfderiv throatCoverModelWithCorners coverModelWithCorners
      (normalGraph period hPeriod displacement parameter) base.1
      ((trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) base.1).symm base.1 tangent)
  have hNormalEq :=
    normalGraphCanonicalHolonomicMetricUnitNormalCoordinatesAt_reconstructs
      period hPeriod metric displacement parameter hNonNull boundary patch
        coordinate hAt
  have hNormal : HEq
      (mfderiv (modelWithCornersSelf Real HolonomicVector4)
        coverModelWithCorners patch.coordinateMap coordinate coordinateNormal)
      intrinsicNormal := by
    exact hNormalEq.heq.trans (eqRec_heq hAt.symm intrinsicNormal)
  have hSource :=
    normalGraphHolonomicSourceFirstDerivativeCoordinatesAt_eq_family
      period hPeriod displacement base patch coordinate hGraph
  have hFamily :=
    normalGraphHolonomicFamilyDerivativeCoordinates_reconstructs period hPeriod
      displacement base patch coordinate hGraph tangent
  have hTangentEq :
      mfderiv (modelWithCornersSelf Real HolonomicVector4)
          coverModelWithCorners patch.coordinateMap coordinate coordinateTangent =
        intrinsicTangent := by
    rw [show coordinateTangent =
      normalGraphHolonomicFamilyDerivativeCoordinates period hPeriod
        displacement base patch coordinate base tangent by
      exact congrArg (fun derivative => derivative tangent) hSource]
    exact hFamily
  have hTangent : HEq
      (mfderiv (modelWithCornersSelf Real HolonomicVector4)
        coverModelWithCorners patch.coordinateMap coordinate coordinateTangent)
      intrinsicTangent := hTangentEq.heq
  have hMetric := normalGraphDependentBilinApply_heq
    (fun point first second => metric.tensor.tensor point first second)
    hAt hNormal hTangent
  rw [localMetricCoordinateForm_apply]
  change metric.tensor.tensor (patch.coordinateMap coordinate)
      (mfderiv (modelWithCornersSelf Real HolonomicVector4)
        coverModelWithCorners patch.coordinateMap coordinate coordinateNormal)
      (mfderiv (modelWithCornersSelf Real HolonomicVector4)
        coverModelWithCorners patch.coordinateMap coordinate coordinateTangent) = 0
  rw [eq_of_heq hMetric]
  exact normalGraphCanonicalMetricUnitNormal_orthogonal period hPeriod metric
    displacement parameter hNonNull boundary
      ((trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) base.1).symm base.1 tangent)

/-- Projecting the canonical unit normal back to the local normal line fixes
it exactly. -/
theorem normalGraphCanonicalHolonomicMetricNormalCoordinates_projector_fixed
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : OrientationBoundary period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter)) :
    let base : EffectiveThroat period hPeriod × Real :=
      (orientationDoubleToThroat period hPeriod boundary, parameter)
    let ambient :=
      normalGraphCanonicalHolonomicMetricUnitNormalCoordinatesAt period hPeriod
        metric displacement parameter hNonNull boundary patch coordinate hAt
    normalGraphHolonomicMetricNormalCoordinates period hPeriod metric
        displacement base patch coordinate ambient base = ambient := by
  dsimp only
  let base : EffectiveThroat period hPeriod × Real :=
    (orientationDoubleToThroat period hPeriod boundary, parameter)
  let ambient :=
    normalGraphCanonicalHolonomicMetricUnitNormalCoordinatesAt period hPeriod
      metric displacement parameter hNonNull boundary patch coordinate hAt
  have hGraph : patch.coordinateMap coordinate =
      normalGraph period hPeriod displacement base.2 base.1 := by
    simpa [base, normalGraphOrientationDouble] using hAt
  have hPairing :
      normalGraphHolonomicTangentialPairingCoordinates period hPeriod metric
          displacement base patch coordinate ambient base = 0 := by
    apply ContinuousLinearMap.ext
    intro tangent
    rw [normalGraphHolonomicTangentialPairingCoordinates_apply]
    rw [normalGraphHolonomicCoordinateGerm_base period hPeriod displacement
      base patch coordinate hGraph]
    rw [← normalGraphHolonomicSourceFirstDerivativeCoordinatesAt_eq_family
      period hPeriod displacement base patch coordinate hGraph]
    change localMetricCoordinateForm period hPeriod metric patch coordinate
        ambient
          (normalGraphHolonomicSourceFirstDerivativeCoordinatesAt period hPeriod
            displacement base patch coordinate tangent) = 0
    exact
      normalGraphCanonicalHolonomicMetricUnitNormalCoordinatesAt_orthogonal
        period hPeriod metric displacement parameter hNonNull boundary patch
          coordinate hAt tangent
  unfold normalGraphHolonomicMetricNormalCoordinates
  rw [hPairing]
  simp

/-- The coordinate square of the canonical normal has absolute value one. -/
theorem normalGraphCanonicalHolonomicMetricUnitNormalCoordinatesAt_abs_square
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : OrientationBoundary period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter)) :
    let ambient :=
      normalGraphCanonicalHolonomicMetricUnitNormalCoordinatesAt period hPeriod
        metric displacement parameter hNonNull boundary patch coordinate hAt
    |localMetricCoordinateForm period hPeriod metric patch coordinate
      ambient ambient| = 1 := by
  dsimp only
  let ambient :=
    normalGraphCanonicalHolonomicMetricUnitNormalCoordinatesAt period hPeriod
      metric displacement parameter hNonNull boundary patch coordinate hAt
  let intrinsicNormal :=
    normalGraphCanonicalMetricUnitNormal period hPeriod metric displacement
      parameter hNonNull boundary
  have hNormalEq :=
    normalGraphCanonicalHolonomicMetricUnitNormalCoordinatesAt_reconstructs
      period hPeriod metric displacement parameter hNonNull boundary patch
        coordinate hAt
  have hNormal : HEq
      (mfderiv (modelWithCornersSelf Real HolonomicVector4)
        coverModelWithCorners patch.coordinateMap coordinate ambient)
      intrinsicNormal := by
    exact hNormalEq.heq.trans (eqRec_heq hAt.symm intrinsicNormal)
  have hMetric := normalGraphDependentBilinApply_heq
    (fun point first second => metric.tensor.tensor point first second)
    hAt hNormal hNormal
  rw [localMetricCoordinateForm_apply]
  rw [eq_of_heq hMetric]
  exact abs_normalGraphCanonicalMetricUnitNormal_square period hPeriod metric
    displacement parameter hNonNull boundary

/-- The previously constructed smooth local unit-normal germ, seeded by the
canonical coordinate normal, is the global canonical normal at its anchor. -/
theorem normalGraphCanonicalHolonomicLocalUnitNormalCoordinates_eq
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : OrientationBoundary period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter)) :
    let base : EffectiveThroat period hPeriod × Real :=
      (orientationDoubleToThroat period hPeriod boundary, parameter)
    let ambient :=
      normalGraphCanonicalHolonomicMetricUnitNormalCoordinatesAt period hPeriod
        metric displacement parameter hNonNull boundary patch coordinate hAt
    normalGraphHolonomicMetricUnitNormalCoordinates period hPeriod metric
        displacement base patch coordinate ambient base = ambient := by
  dsimp only
  let base : EffectiveThroat period hPeriod × Real :=
    (orientationDoubleToThroat period hPeriod boundary, parameter)
  let ambient :=
    normalGraphCanonicalHolonomicMetricUnitNormalCoordinatesAt period hPeriod
      metric displacement parameter hNonNull boundary patch coordinate hAt
  have hGraph : patch.coordinateMap coordinate =
      normalGraph period hPeriod displacement base.2 base.1 := by
    simpa [base, normalGraphOrientationDouble] using hAt
  have hProjected :=
    normalGraphCanonicalHolonomicMetricNormalCoordinates_projector_fixed
      period hPeriod metric displacement parameter hNonNull boundary patch
        coordinate hAt
  have hSquare :
      |normalGraphHolonomicMetricNormalSquareCoordinates period hPeriod metric
        displacement base patch coordinate ambient base| = 1 := by
    unfold normalGraphHolonomicMetricNormalSquareCoordinates
    rw [normalGraphHolonomicCoordinateGerm_base period hPeriod displacement
      base patch coordinate hGraph]
    rw [hProjected]
    exact
      normalGraphCanonicalHolonomicMetricUnitNormalCoordinatesAt_abs_square
        period hPeriod metric displacement parameter hNonNull boundary patch
          coordinate hAt
  unfold normalGraphHolonomicMetricUnitNormalCoordinates
  rw [hSquare]
  simp [hProjected]

/-- The genuine Weingarten germ becomes the canonical physical germ without
losing its already proved joint smoothness. -/
theorem normalGraphCanonicalHolonomicWeingartenExtrinsicCurvature_contMDiffAt
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : OrientationBoundary period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter))
    (first second : ThroatCoverCoordinates) :
    let base : EffectiveThroat period hPeriod × Real :=
      (orientationDoubleToThroat period hPeriod boundary, parameter)
    let ambient :=
      normalGraphCanonicalHolonomicMetricUnitNormalCoordinatesAt period hPeriod
        metric displacement parameter hNonNull boundary patch coordinate hAt
    ContMDiffAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      𝓘(Real, Real) ∞
      (normalGraphHolonomicExtrinsicCurvatureCoordinates period hPeriod metric
        displacement base patch coordinate ambient first second) base := by
  dsimp only
  let base : EffectiveThroat period hPeriod × Real :=
    (orientationDoubleToThroat period hPeriod boundary, parameter)
  let ambient :=
    normalGraphCanonicalHolonomicMetricUnitNormalCoordinatesAt period hPeriod
      metric displacement parameter hNonNull boundary patch coordinate hAt
  have hGraph : patch.coordinateMap coordinate =
      normalGraph period hPeriod displacement base.2 base.1 := by
    simpa [base, normalGraphOrientationDouble] using hAt
  have hProjected :=
    normalGraphCanonicalHolonomicMetricNormalCoordinates_projector_fixed
      period hPeriod metric displacement parameter hNonNull boundary patch
        coordinate hAt
  have hAbsSquare :
      |normalGraphHolonomicMetricNormalSquareCoordinates period hPeriod metric
        displacement base patch coordinate ambient base| = 1 := by
    unfold normalGraphHolonomicMetricNormalSquareCoordinates
    rw [normalGraphHolonomicCoordinateGerm_base period hPeriod displacement
      base patch coordinate hGraph]
    rw [hProjected]
    exact
      normalGraphCanonicalHolonomicMetricUnitNormalCoordinatesAt_abs_square
        period hPeriod metric displacement parameter hNonNull boundary patch
          coordinate hAt
  have hSquare :
      normalGraphHolonomicMetricNormalSquareCoordinates period hPeriod metric
        displacement base patch coordinate ambient base ≠ 0 := by
    intro hZero
    rw [hZero, abs_zero] at hAbsSquare
    norm_num at hAbsSquare
  exact normalGraphHolonomicExtrinsicCurvatureCoordinates_contMDiffAt period
    hPeriod metric displacement base hNonNull patch coordinate ambient hGraph
      hSquare first second

/-- The square used by the canonical holonomic normal germ is nonzero at its
anchor.  This packages the admissibility argument needed by source-chart
differentiation below. -/
theorem normalGraphCanonicalHolonomicMetricNormalSquareCoordinates_ne_zero
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : OrientationBoundary period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter)) :
    let base : EffectiveThroat period hPeriod × Real :=
      (orientationDoubleToThroat period hPeriod boundary, parameter)
    let ambient :=
      normalGraphCanonicalHolonomicMetricUnitNormalCoordinatesAt period hPeriod
        metric displacement parameter hNonNull boundary patch coordinate hAt
    normalGraphHolonomicMetricNormalSquareCoordinates period hPeriod metric
        displacement base patch coordinate ambient base ≠ 0 := by
  dsimp only
  let base : EffectiveThroat period hPeriod × Real :=
    (orientationDoubleToThroat period hPeriod boundary, parameter)
  let ambient :=
    normalGraphCanonicalHolonomicMetricUnitNormalCoordinatesAt period hPeriod
      metric displacement parameter hNonNull boundary patch coordinate hAt
  have hGraph : patch.coordinateMap coordinate =
      normalGraph period hPeriod displacement base.2 base.1 := by
    simpa [base, normalGraphOrientationDouble] using hAt
  have hProjected :=
    normalGraphCanonicalHolonomicMetricNormalCoordinates_projector_fixed
      period hPeriod metric displacement parameter hNonNull boundary patch
        coordinate hAt
  have hAbsSquare :
      |normalGraphHolonomicMetricNormalSquareCoordinates period hPeriod metric
        displacement base patch coordinate ambient base| = 1 := by
    unfold normalGraphHolonomicMetricNormalSquareCoordinates
    rw [normalGraphHolonomicCoordinateGerm_base period hPeriod displacement
      base patch coordinate hGraph]
    rw [hProjected]
    exact
      normalGraphCanonicalHolonomicMetricUnitNormalCoordinatesAt_abs_square
        period hPeriod metric displacement parameter hNonNull boundary patch
          coordinate hAt
  intro hZero
  rw [hZero, abs_zero] at hAbsSquare
  norm_num at hAbsSquare

/-- The existing canonical holonomic normal germ written in the canonical
source chart of the throat.  This is only a coordinate view of the same germ,
not a second normal field. -/
def normalGraphCanonicalHolonomicLocalUnitNormalSourceGerm
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate ambient : HolonomicVector4)
    (sourceCoordinate : ThroatCoverCoordinates) : HolonomicVector4 :=
  normalGraphHolonomicMetricUnitNormalCoordinates period hPeriod metric
    displacement base patch coordinate ambient
      ((extChartAt throatCoverModelWithCorners base.1).symm sourceCoordinate,
        base.2)

theorem normalGraphCanonicalHolonomicLocalUnitNormalSourceGerm_contDiffAt
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : OrientationBoundary period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter)) :
    let base : EffectiveThroat period hPeriod × Real :=
      (orientationDoubleToThroat period hPeriod boundary, parameter)
    let ambient :=
      normalGraphCanonicalHolonomicMetricUnitNormalCoordinatesAt period hPeriod
        metric displacement parameter hNonNull boundary patch coordinate hAt
    ContDiffAt Real ∞
      (normalGraphCanonicalHolonomicLocalUnitNormalSourceGerm period hPeriod
        metric displacement base patch coordinate ambient)
      (extChartAt throatCoverModelWithCorners base.1 base.1) := by
  dsimp only
  let base : EffectiveThroat period hPeriod × Real :=
    (orientationDoubleToThroat period hPeriod boundary, parameter)
  let ambient :=
    normalGraphCanonicalHolonomicMetricUnitNormalCoordinatesAt period hPeriod
      metric displacement parameter hNonNull boundary patch coordinate hAt
  let slice := fun point : EffectiveThroat period hPeriod =>
    normalGraphHolonomicMetricUnitNormalCoordinates period hPeriod metric
      displacement base patch coordinate ambient (point, base.2)
  have hGraph : patch.coordinateMap coordinate =
      normalGraph period hPeriod displacement base.2 base.1 := by
    simpa [base, normalGraphOrientationDouble] using hAt
  have hSquare :=
    normalGraphCanonicalHolonomicMetricNormalSquareCoordinates_ne_zero period
      hPeriod metric displacement parameter hNonNull boundary patch coordinate
        hAt
  have hSection : ContMDiffAt throatCoverModelWithCorners
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real)) ∞
      (fun point : EffectiveThroat period hPeriod => (point, base.2)) base.1 :=
    (contMDiff_id.prodMk contMDiff_const).contMDiffAt
  have hSlice : ContMDiffAt throatCoverModelWithCorners
      (modelWithCornersSelf Real HolonomicVector4) ∞ slice base.1 :=
    ContMDiffAt.comp
      (f := fun point : EffectiveThroat period hPeriod => (point, base.2))
      (g := normalGraphHolonomicMetricUnitNormalCoordinates period hPeriod metric
        displacement base patch coordinate ambient) base.1
      (normalGraphHolonomicMetricUnitNormalCoordinates_contMDiffAt period hPeriod
        metric displacement base hNonNull patch coordinate ambient hGraph
          hSquare) hSection
  have hSource := (contMDiffAt_iff_source).mp hSlice
  have hRange : Set.range throatCoverModelWithCorners = Set.univ := by
    ext sourceCoordinate
    simp
  rw [hRange, contMDiffWithinAt_univ] at hSource
  have hFunction :
      slice ∘ (extChartAt throatCoverModelWithCorners base.1).symm =
        normalGraphCanonicalHolonomicLocalUnitNormalSourceGerm period hPeriod
          metric displacement base patch coordinate ambient := by
    rfl
  rw [hFunction] at hSource
  exact hSource.contDiffAt

@[simp]
theorem normalGraphCanonicalHolonomicLocalUnitNormalSourceGerm_base
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : OrientationBoundary period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter)) :
    let base : EffectiveThroat period hPeriod × Real :=
      (orientationDoubleToThroat period hPeriod boundary, parameter)
    let ambient :=
      normalGraphCanonicalHolonomicMetricUnitNormalCoordinatesAt period hPeriod
        metric displacement parameter hNonNull boundary patch coordinate hAt
    normalGraphCanonicalHolonomicLocalUnitNormalSourceGerm period hPeriod metric
        displacement base patch coordinate ambient
          (extChartAt throatCoverModelWithCorners base.1 base.1) = ambient := by
  dsimp only
  rw [normalGraphCanonicalHolonomicLocalUnitNormalSourceGerm]
  rw [extChartAt_to_inv]
  exact normalGraphCanonicalHolonomicLocalUnitNormalCoordinates_eq period
    hPeriod metric displacement parameter hNonNull boundary patch coordinate hAt

/-- The source-chart derivative is exactly the already installed spatial
derivative of the canonical holonomic normal germ. -/
theorem normalGraphCanonicalHolonomicLocalUnitNormalSourceGerm_fderiv
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : OrientationBoundary period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter))
    (tangent : ThroatCoverCoordinates) :
    let base : EffectiveThroat period hPeriod × Real :=
      (orientationDoubleToThroat period hPeriod boundary, parameter)
    let ambient :=
      normalGraphCanonicalHolonomicMetricUnitNormalCoordinatesAt period hPeriod
        metric displacement parameter hNonNull boundary patch coordinate hAt
    fderiv Real
        (normalGraphCanonicalHolonomicLocalUnitNormalSourceGerm period hPeriod
          metric displacement base patch coordinate ambient)
        (extChartAt throatCoverModelWithCorners base.1 base.1) tangent =
      normalGraphHolonomicMetricUnitNormalDerivativeCoordinates period hPeriod
        metric displacement base patch coordinate ambient base tangent := by
  dsimp only
  let base : EffectiveThroat period hPeriod × Real :=
    (orientationDoubleToThroat period hPeriod boundary, parameter)
  let ambient :=
    normalGraphCanonicalHolonomicMetricUnitNormalCoordinatesAt period hPeriod
      metric displacement parameter hNonNull boundary patch coordinate hAt
  let slice := fun point : EffectiveThroat period hPeriod =>
    normalGraphHolonomicMetricUnitNormalCoordinates period hPeriod metric
      displacement base patch coordinate ambient (point, base.2)
  have hGraph : patch.coordinateMap coordinate =
      normalGraph period hPeriod displacement base.2 base.1 := by
    simpa [base, normalGraphOrientationDouble] using hAt
  have hSquare :=
    normalGraphCanonicalHolonomicMetricNormalSquareCoordinates_ne_zero period
      hPeriod metric displacement parameter hNonNull boundary patch coordinate
        hAt
  have hSection : ContMDiffAt throatCoverModelWithCorners
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real)) ∞
      (fun point : EffectiveThroat period hPeriod => (point, base.2)) base.1 :=
    (contMDiff_id.prodMk contMDiff_const).contMDiffAt
  have hSlice : ContMDiffAt throatCoverModelWithCorners
      (modelWithCornersSelf Real HolonomicVector4) ∞ slice base.1 :=
    ContMDiffAt.comp
      (f := fun point : EffectiveThroat period hPeriod => (point, base.2))
      (g := normalGraphHolonomicMetricUnitNormalCoordinates period hPeriod metric
        displacement base patch coordinate ambient) base.1
      (normalGraphHolonomicMetricUnitNormalCoordinates_contMDiffAt period hPeriod
        metric displacement base hNonNull patch coordinate ambient hGraph
          hSquare) hSection
  rw [normalGraphHolonomicMetricUnitNormalDerivativeCoordinates_apply_base_eq_mfderiv]
  have hChart : base.1 ∈ (chartAt ThroatCoverModel base.1).source :=
    mem_chart_source ThroatCoverModel base.1
  have hVector :
      (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) base.1).symm base.1 tangent =
        tangent := by
    change
      (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) base.1).symmL Real base.1 tangent =
        tangent
    rw [TangentBundle.symmL_trivializationAt hChart,
      mfderivWithin_range_extChartAt_symm]
    rfl
  rw [hVector]
  rw [(hSlice.mdifferentiableAt (by simp)).mfderiv]
  have hRange : Set.range throatCoverModelWithCorners = Set.univ := by
    ext sourceCoordinate
    simp
  rw [hRange, fderivWithin_univ]
  simp [writtenInExtChartAt, Function.comp_def, slice]
  rfl

section GaussWeingartenDifferentiation

open scoped Matrix Matrix.Norms.Frobenius

private theorem normalBoundary_fderiv_continuousLinearMap_apply_const
    {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E]
    [NormedAddCommGroup F] [NormedSpace Real F]
    [NormedAddCommGroup G] [NormedSpace Real G]
    (maps : E → F →L[Real] G) (point direction : E) (vector : F)
    (hMaps : DifferentiableAt Real maps point) :
    fderiv Real (fun current => maps current vector) point direction =
      fderiv Real maps point direction vector := by
  let evaluation : (F →L[Real] G) →L[Real] G :=
    ContinuousLinearMap.apply Real G vector
  have hDerivative :
      fderiv Real (evaluation ∘ maps) point =
        evaluation.comp (fderiv Real maps point) :=
    (evaluation.hasFDerivAt.comp point hMaps.hasFDerivAt).fderiv
  have hFunction :
      evaluation ∘ maps = fun current => maps current vector := by
    funext current
    rfl
  rw [hFunction] at hDerivative
  exact congrArg (fun derivative : E →L[Real] G => derivative direction)
    hDerivative

/-- Differentiating a local metric orthogonality identity gives the exact
Gauss--Weingarten pairing, using the existing Levi--Civita compatibility
theorem. -/
theorem localMetric_gauss_weingarten_of_eventually_orthogonal
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate normal tangent : E →
      P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D.Vector4)
    (base direction : E)
    (hCoordinate : DifferentiableAt Real coordinate base)
    (hNormal : DifferentiableAt Real normal base)
    (hTangent : DifferentiableAt Real tangent base)
    (hOrthogonal :
      (fun current => localMetricCoordinateForm period hPeriod metric patch
        (coordinate current) (normal current) (tangent current)) =ᶠ[𝓝 base]
        fun _ => 0) :
    localMetricCoordinateForm period hPeriod metric patch (coordinate base)
        (fderiv Real normal base direction +
          localLeviCivitaChristoffelApply period hPeriod metric patch
            (coordinate base) (fderiv Real coordinate base direction)
              (normal base))
        (tangent base) =
      -localMetricCoordinateForm period hPeriod metric patch (coordinate base)
        (normal base)
        (fderiv Real tangent base direction +
          localLeviCivitaChristoffelApply period hPeriod metric patch
            (coordinate base) (fderiv Real coordinate base direction)
              (tangent base)) := by
  let matrix := fun current : E =>
    localMetricMatrix period hPeriod metric patch (coordinate current)
  have hLocalMatrix : DifferentiableAt Real
      (localMetricMatrix period hPeriod metric patch) (coordinate base) := by
    exact (localMetricMatrix_contDiff period hPeriod metric patch).differentiable
      (by simp) |>.differentiableAt
  have hMatrix : DifferentiableAt Real matrix base := by
    change DifferentiableAt Real
      ((localMetricMatrix period hPeriod metric patch) ∘ coordinate) base
    exact hLocalMatrix.comp base hCoordinate
  have hDerivativeEq :=
    Filter.EventuallyEq.fderiv_eq (𝕜 := Real) hOrthogonal
  have hDerivativeZero := congrArg
    (fun derivative : E →L[Real] Real => derivative direction) hDerivativeEq
  rw [fderiv_const_apply] at hDerivativeZero
  simp only [zero_apply] at hDerivativeZero
  simp only [localMetricCoordinateForm] at hDerivativeZero
  change fderiv Real
      (fun current => Matrix.toBilin' (matrix current)
        (normal current) (tangent current)) base direction = 0
    at hDerivativeZero
  rw [fderiv_matrix_toBilin_dynamic_apply matrix normal tangent base direction
    hMatrix hNormal hTangent] at hDerivativeZero
  have hMatrixDerivative := congrArg
    (fun derivative : E →L[Real]
      P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D.Matrix4 =>
        derivative direction)
    (fderiv_comp base hLocalMatrix hCoordinate)
  change fderiv Real matrix base direction = _ at hMatrixDerivative
  rw [hMatrixDerivative] at hDerivativeZero
  change
      localMetricCoordinateForm period hPeriod metric patch (coordinate base)
          (fderiv Real normal base direction) (tangent base) +
        localMetricDerivativeTrilinearForm period hPeriod metric patch
          (coordinate base) (fderiv Real coordinate base direction)
            (normal base) (tangent base) +
        localMetricCoordinateForm period hPeriod metric patch (coordinate base)
          (normal base) (fderiv Real tangent base direction) = 0
    at hDerivativeZero
  rw [localMetricDerivativeTrilinearForm_eq_leviCivita,
    localLeviCivitaMetricCompatibilityForm_apply,
    localLeviCivitaChristoffelBilinearMap_apply,
    localLeviCivitaChristoffelBilinearMap_apply] at hDerivativeZero
  simp only [map_add, LinearMap.add_apply]
  linarith

/-- The metric normal obtained with the pre-existing inverse is orthogonal to
the stored holonomic graph differential whenever that inverse is a genuine
right inverse for the pullback metric. -/
theorem normalGraphHolonomicMetricNormalCoordinates_orthogonal_of_rightInverse
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base current : EffectiveThroat period hPeriod × Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate ambient : HolonomicVector4)
    (hInverse : ∀ covector : ThroatCoverCoordinates →L[Real] Real,
      ∀ tangent : ThroatCoverCoordinates,
        normalGraphHolonomicInducedMetricCoordinates period hPeriod metric
            displacement base patch coordinate current
            (normalGraphInducedMetricInverseCoordinates period hPeriod metric
              displacement base current covector) tangent =
          covector tangent)
    (tangent : ThroatCoverCoordinates) :
    localMetricCoordinateForm period hPeriod metric patch
        (normalGraphHolonomicCoordinateGerm period hPeriod displacement base
          patch coordinate current)
        (normalGraphHolonomicMetricNormalCoordinates period hPeriod metric
          displacement base patch coordinate ambient current)
        (normalGraphHolonomicFamilyDerivativeCoordinates period hPeriod
          displacement base patch coordinate current tangent) = 0 := by
  let pairing :=
    normalGraphHolonomicTangentialPairingCoordinates period hPeriod metric
      displacement base patch coordinate ambient current
  let sharp :=
    normalGraphInducedMetricInverseCoordinates period hPeriod metric displacement
      base current pairing
  have hPairingApply :=
    normalGraphHolonomicTangentialPairingCoordinates_apply period hPeriod metric
      displacement base patch coordinate ambient current tangent
  unfold normalGraphHolonomicMetricNormalCoordinates
  rw [map_sub]
  change
    localMetricCoordinateForm period hPeriod metric patch
          (normalGraphHolonomicCoordinateGerm period hPeriod displacement base
            patch coordinate current) ambient
          (normalGraphHolonomicFamilyDerivativeCoordinates period hPeriod
            displacement base patch coordinate current tangent) -
        normalGraphHolonomicInducedMetricCoordinates period hPeriod metric
          displacement base patch coordinate current sharp tangent = 0
  rw [hInverse pairing tangent]
  exact sub_eq_zero.mpr hPairingApply.symm

/-- Normalizing the same metric normal preserves its exact orthogonality. -/
theorem
    normalGraphHolonomicMetricUnitNormalCoordinates_orthogonal_of_rightInverse
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base current : EffectiveThroat period hPeriod × Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate ambient : HolonomicVector4)
    (hInverse : ∀ covector : ThroatCoverCoordinates →L[Real] Real,
      ∀ tangent : ThroatCoverCoordinates,
        normalGraphHolonomicInducedMetricCoordinates period hPeriod metric
            displacement base patch coordinate current
            (normalGraphInducedMetricInverseCoordinates period hPeriod metric
              displacement base current covector) tangent =
          covector tangent)
    (tangent : ThroatCoverCoordinates) :
    localMetricCoordinateForm period hPeriod metric patch
        (normalGraphHolonomicCoordinateGerm period hPeriod displacement base
          patch coordinate current)
        (normalGraphHolonomicMetricUnitNormalCoordinates period hPeriod metric
          displacement base patch coordinate ambient current)
        (normalGraphHolonomicFamilyDerivativeCoordinates period hPeriod
          displacement base patch coordinate current tangent) = 0 := by
  unfold normalGraphHolonomicMetricUnitNormalCoordinates
  rw [map_smul, LinearMap.smul_apply]
  rw [normalGraphHolonomicMetricNormalCoordinates_orthogonal_of_rightInverse
    period hPeriod metric displacement base current patch coordinate ambient
      hInverse tangent]
  simp

/-- Evaluation of the jointly stored holonomic graph differential at an
arbitrary nearby point of the fixed source trivialization. -/
theorem normalGraphHolonomicFamilyDerivativeCoordinates_apply_eq_mfderiv
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base current : EffectiveThroat period hPeriod × Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (hCurrent : current.1 ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) base.1).baseSet)
    (vector : ThroatCoverCoordinates) :
    normalGraphHolonomicFamilyDerivativeCoordinates period hPeriod displacement
        base patch coordinate current vector =
      mfderiv throatCoverModelWithCorners
        (modelWithCornersSelf Real HolonomicVector4)
        (fun point => normalGraphHolonomicCoordinateGerm period hPeriod
          displacement base patch coordinate (point, current.2)) current.1
        ((trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) base.1).symm current.1 vector) := by
  have hTarget :
      normalGraphHolonomicCoordinateGerm period hPeriod displacement base patch
          coordinate current ∈
        (trivializationAt HolonomicVector4
          (fun point : HolonomicVector4 =>
            TangentSpace (modelWithCornersSelf Real HolonomicVector4) point)
          (normalGraphHolonomicCoordinateGerm period hPeriod displacement base
            patch coordinate base)).baseSet :=
    mem_baseSet_trivializationAt HolonomicVector4
      (fun point : HolonomicVector4 =>
        TangentSpace (modelWithCornersSelf Real HolonomicVector4) point)
      (normalGraphHolonomicCoordinateGerm period hPeriod displacement base patch
        coordinate current)
  rw [show normalGraphHolonomicFamilyDerivativeCoordinates period hPeriod
      displacement base patch coordinate current =
    ContinuousLinearMap.inCoordinates ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) HolonomicVector4
      (fun point : HolonomicVector4 =>
        TangentSpace (modelWithCornersSelf Real HolonomicVector4) point)
      base.1 current.1
      (normalGraphHolonomicCoordinateGerm period hPeriod displacement base patch
        coordinate base)
      (normalGraphHolonomicCoordinateGerm period hPeriod displacement base patch
        coordinate current)
      (mfderiv throatCoverModelWithCorners
        (modelWithCornersSelf Real HolonomicVector4)
        (fun point => normalGraphHolonomicCoordinateGerm period hPeriod
          displacement base patch coordinate (point, current.2)) current.1) by
    rfl]
  rw [ContinuousLinearMap.inCoordinates_eq hCurrent hTarget]
  simp

/-- In the canonical source chart, the ordinary Fréchet derivative is exactly
the stored holonomic family differential.  The hypotheses only record that
the chart inverse and the already existing representative are valid at the
current source coordinate. -/
theorem normalGraphHolonomicSourceChartGerm_fderiv_eq_family_of_mem
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (sourceCoordinate : ThroatCoverCoordinates)
    (hTarget : sourceCoordinate ∈
      (extChartAt throatCoverModelWithCorners base.1).target)
    (hCurrent : (extChartAt throatCoverModelWithCorners base.1).symm
        sourceCoordinate ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) base.1).baseSet)
    (hRepresentative : ContMDiffAt throatCoverModelWithCorners
      (modelWithCornersSelf Real HolonomicVector4) ∞
      (fun point : EffectiveThroat period hPeriod =>
        normalGraphHolonomicCoordinateGerm period hPeriod displacement base
          patch coordinate (point, base.2))
      ((extChartAt throatCoverModelWithCorners base.1).symm sourceCoordinate))
    (vector : ThroatCoverCoordinates) :
    fderiv Real
        (normalGraphHolonomicSourceChartGerm period hPeriod displacement base
          patch coordinate) sourceCoordinate vector =
      normalGraphHolonomicFamilyDerivativeCoordinates period hPeriod
        displacement base patch coordinate
          ((extChartAt throatCoverModelWithCorners base.1).symm sourceCoordinate,
            base.2) vector := by
  let inverse := (extChartAt throatCoverModelWithCorners base.1).symm
  let current := inverse sourceCoordinate
  let representative := fun point : EffectiveThroat period hPeriod =>
    normalGraphHolonomicCoordinateGerm period hPeriod displacement base patch
      coordinate (point, base.2)
  have hRange : Set.range throatCoverModelWithCorners = Set.univ := by
    ext point
    simp
  have hInverseDiff : MDifferentiableAt
      (modelWithCornersSelf Real ThroatCoverCoordinates)
      throatCoverModelWithCorners inverse sourceCoordinate := by
    rw [← mdifferentiableWithinAt_univ]
    rw [← hRange]
    exact mdifferentiableWithinAt_extChartAt_symm hTarget
  have hChart : current ∈ (chartAt ThroatCoverModel base.1).source := by
    have hSource :=
      (extChartAt throatCoverModelWithCorners base.1).map_target hTarget
    simpa only [extChartAt_source] using hSource
  have hVector :
      (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) base.1).symm current vector =
        mfderiv (modelWithCornersSelf Real ThroatCoverCoordinates)
          throatCoverModelWithCorners inverse sourceCoordinate vector := by
    change
      (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) base.1).symmL Real current vector = _
    rw [TangentBundle.symmL_trivializationAt hChart]
    rw [show extChartAt throatCoverModelWithCorners base.1 current =
        sourceCoordinate by
      exact (extChartAt throatCoverModelWithCorners base.1).right_inv hTarget]
    rw [hRange, mfderivWithin_univ]
    rfl
  have hChain := mfderiv_comp_apply sourceCoordinate
    (hRepresentative.mdifferentiableAt (by simp)) hInverseDiff vector
  have hChainHEq : HEq
      (fderiv Real (representative ∘ inverse) sourceCoordinate vector)
      (mfderiv throatCoverModelWithCorners
        (modelWithCornersSelf Real HolonomicVector4) representative current
        (mfderiv (modelWithCornersSelf Real ThroatCoverCoordinates)
          throatCoverModelWithCorners inverse sourceCoordinate vector)) := by
    rw [← mfderiv_eq_fderiv]
    exact hChain.heq
  unfold normalGraphHolonomicSourceChartGerm
  change fderiv Real (representative ∘ inverse) sourceCoordinate vector = _
  rw [normalGraphHolonomicFamilyDerivativeCoordinates_apply_eq_mfderiv period
    hPeriod displacement base
      ((extChartAt throatCoverModelWithCorners base.1).symm sourceCoordinate,
        base.2) patch coordinate hCurrent vector]
  rw [hVector]
  exact eq_of_heq hChainHEq

/-- The fixed holonomic representative remains smooth at every sufficiently
nearby point of the source slice.  This is the local-domain fact needed to
differentiate its metric orthogonality identity. -/
theorem normalGraphHolonomicSpatialRepresentative_eventually_contMDiffAt
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraph period hPeriod displacement base.2 base.1) :
    ∀ᶠ point in 𝓝 base.1, ContMDiffAt throatCoverModelWithCorners
      (modelWithCornersSelf Real HolonomicVector4) ∞
      (fun current : EffectiveThroat period hPeriod =>
        normalGraphHolonomicCoordinateGerm period hPeriod displacement base
          patch coordinate (current, base.2)) point := by
  let localDiffeomorph := patch.coordinateMap_isLocalDiffeomorph coordinate
  have hGraphBase : normalGraph period hPeriod displacement base.2 base.1 ∈
      localDiffeomorph.localInverse.source := by
    rw [← hAt]
    exact localDiffeomorph.localInverse_mem_source
  let sectionMap := fun point : EffectiveThroat period hPeriod => (point, base.2)
  have hSection : ContMDiff throatCoverModelWithCorners
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real)) ∞
      sectionMap := contMDiff_id.prodMk contMDiff_const
  have hGraphContinuous : ContinuousAt
      (normalGraph period hPeriod displacement base.2) base.1 := by
    exact ((normalGraph_joint_contMDiff period hPeriod displacement).comp
      hSection).continuous.continuousAt
  have hGraphEventually : ∀ᶠ point in 𝓝 base.1,
      normalGraph period hPeriod displacement base.2 point ∈
        localDiffeomorph.localInverse.source :=
    hGraphContinuous
      (localDiffeomorph.localInverse.open_source.mem_nhds hGraphBase)
  filter_upwards [hGraphEventually] with point hGraphPoint
  have hInverse := localDiffeomorph.localInverse_contMDiffOn.contMDiffAt
    (localDiffeomorph.localInverse.open_source.mem_nhds hGraphPoint)
  have hCoordinateAt : ContMDiffAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real HolonomicVector4) ∞
      (normalGraphHolonomicCoordinateGerm period hPeriod displacement base patch
        coordinate) (point, base.2) := by
    exact hInverse.comp (point, base.2)
      (normalGraph_joint_contMDiff period hPeriod displacement).contMDiffAt
  exact ContMDiffAt.comp (f := sectionMap)
    (g := normalGraphHolonomicCoordinateGerm period hPeriod displacement base
      patch coordinate) point hCoordinateAt hSection.contMDiffAt

private theorem eventually_local
    {α : Type*} [TopologicalSpace α] {predicate : α → Prop} {base : α}
    (hPredicate : ∀ᶠ point in 𝓝 base, predicate point) :
    ∀ᶠ current in 𝓝 base, ∀ᶠ point in 𝓝 current, predicate point := by
  have hSet : {point | predicate point} ∈ 𝓝 base := hPredicate
  obtain ⟨neighborhood, hSubset, hOpen, hBase⟩ := mem_nhds_iff.mp hSet
  filter_upwards [hOpen.mem_nhds hBase] with current hCurrent
  exact Filter.mem_of_superset (hOpen.mem_nhds hCurrent) hSubset

private theorem eventually_local_eventuallyEq
    {α β : Type*} [TopologicalSpace α]
    {first second : α → β} {base : α}
    (hEq : first =ᶠ[𝓝 base] second) :
    ∀ᶠ current in 𝓝 base, first =ᶠ[𝓝 current] second :=
  eventually_local hEq

/-- On a whole neighborhood, the stored holonomic differential reconstructs
the differential of the actual moving graph, not merely its anchor value. -/
theorem normalGraphHolonomicFamilyDerivativeCoordinates_eventually_reconstructs
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraph period hPeriod displacement base.2 base.1) :
    ∀ᶠ current in 𝓝 base, ∀ vector : ThroatCoverCoordinates,
      mfderiv (modelWithCornersSelf Real HolonomicVector4)
          coverModelWithCorners patch.coordinateMap
          (normalGraphHolonomicCoordinateGerm period hPeriod displacement base
            patch coordinate current)
          (normalGraphHolonomicFamilyDerivativeCoordinates period hPeriod
            displacement base patch coordinate current vector) =
        mfderiv throatCoverModelWithCorners coverModelWithCorners
          (normalGraph period hPeriod displacement current.2) current.1
          ((trivializationAt ThroatCoverCoordinates
            (ThroatTangentFiber period hPeriod) base.1).symm current.1 vector) := by
  let localDiffeomorph :=
    patch.coordinateMap_isLocalDiffeomorph coordinate
  have hGraphBase : normalGraph period hPeriod displacement base.2 base.1 ∈
      localDiffeomorph.localInverse.source := by
    rw [← hAt]
    exact localDiffeomorph.localInverse_mem_source
  have hGraphEventually : ∀ᶠ current in 𝓝 base,
      normalGraph period hPeriod displacement current.2 current.1 ∈
        localDiffeomorph.localInverse.source :=
    (normalGraph_joint_contMDiff period hPeriod displacement).continuous
      |>.continuousAt
        (localDiffeomorph.localInverse.open_source.mem_nhds hGraphBase)
  have hCurrentEventually : ∀ᶠ current in 𝓝 base,
      current.1 ∈
        (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) base.1).baseSet :=
    continuous_fst.continuousAt
      ((trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) base.1).open_baseSet.mem_nhds
          (mem_baseSet_trivializationAt ThroatCoverCoordinates
            (ThroatTangentFiber period hPeriod) base.1))
  have hReconstructLocally := eventually_local_eventuallyEq
    (normalGraphHolonomicCoordinateGerm_eventually_reconstructs period hPeriod
      displacement base patch coordinate hAt)
  filter_upwards [hGraphEventually, hCurrentEventually,
    hReconstructLocally] with current hGraphCurrent hCurrent hReconstruct
  intro vector
  let representative := fun point : EffectiveThroat period hPeriod =>
    normalGraphHolonomicCoordinateGerm period hPeriod displacement base patch
      coordinate (point, current.2)
  let sectionMap := fun point : EffectiveThroat period hPeriod =>
    (point, current.2)
  have hSection : ContMDiffAt throatCoverModelWithCorners
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real)) ∞
      sectionMap current.1 :=
    (contMDiff_id.prodMk contMDiff_const).contMDiffAt
  have hCoordinateAt : ContMDiffAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real HolonomicVector4) ∞
      (normalGraphHolonomicCoordinateGerm period hPeriod displacement base patch
        coordinate) current := by
    have hInverse := localDiffeomorph.localInverse_contMDiffOn.contMDiffAt
      (localDiffeomorph.localInverse.open_source.mem_nhds hGraphCurrent)
    exact hInverse.comp current
      (normalGraph_joint_contMDiff period hPeriod displacement).contMDiffAt
  have hRepresentative : ContMDiffAt throatCoverModelWithCorners
      (modelWithCornersSelf Real HolonomicVector4) ∞ representative current.1 :=
    ContMDiffAt.comp (f := sectionMap)
      (g := normalGraphHolonomicCoordinateGerm period hPeriod displacement base
        patch coordinate) current.1 hCoordinateAt hSection
  have hReconstructSlice :
      (fun point => patch.coordinateMap (representative point)) =ᶠ[𝓝 current.1]
        normalGraph period hPeriod displacement current.2 := by
    exact hReconstruct.comp_tendsto hSection.continuousAt
  have hDerivativeReconstruct :=
    Filter.EventuallyEq.mfderiv_eq
      (I := throatCoverModelWithCorners) (I' := coverModelWithCorners)
      hReconstructSlice
  let tangent :=
    (trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) base.1).symm current.1 vector
  have hChain := mfderiv_comp_apply current.1
    (patch.coordinateMap_contMDiff.mdifferentiable (by simp)
      (representative current.1))
    (hRepresentative.mdifferentiableAt (by simp)) tangent
  rw [normalGraphHolonomicFamilyDerivativeCoordinates_apply_eq_mfderiv period
    hPeriod displacement base current patch coordinate hCurrent vector]
  change mfderiv (modelWithCornersSelf Real HolonomicVector4)
      coverModelWithCorners patch.coordinateMap (representative current.1)
      (mfderiv throatCoverModelWithCorners
        (modelWithCornersSelf Real HolonomicVector4) representative current.1
        tangent) = _
  rw [← hChain]
  have hApply := congrArg (fun derivative => derivative tangent)
    hDerivativeReconstruct
  exact hApply

private theorem normalGraphFamilyTraceTensorCoordinates_isInvertible_current
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base current : EffectiveThroat period hPeriod × Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement
      current.2)
    (hCurrent : current.1 ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) base.1).baseSet)
    (hCotangent : current.1 ∈
      (trivializationAt (ThroatCoverCoordinates →L[Real] Real)
        (ThroatCotangentFiber period hPeriod) base.1).baseSet) :
    (normalGraphFamilyTraceTensorCoordinates period hPeriod metric displacement
      base current).IsInvertible := by
  have hFiber :
      (normalGraphInducedMetricEquiv period hPeriod metric displacement
          current.2 hNonNull current.1 :
        ThroatTangentFiber period hPeriod current.1 →L[Real]
          ThroatCotangentFiber period hPeriod current.1) =
        normalGraphInducedMetricValue period hPeriod metric displacement
          current.2 current.1 := by
    apply ContinuousLinearMap.ext
    intro vector
    exact normalGraphInducedMetricEquiv_apply period hPeriod metric displacement
      current.2 hNonNull current.1 vector
  unfold normalGraphFamilyTraceTensorCoordinates
  rw [ContinuousLinearMap.inCoordinates_eq hCurrent hCotangent, ← hFiber]
  exact isInvertible_equiv.comp
    (isInvertible_equiv.comp isInvertible_equiv)

private theorem
    normalGraphHolonomicInducedMetricCoordinates_eq_trace_of_reconstructs
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base current : EffectiveThroat period hPeriod × Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (hCurrent : current.1 ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) base.1).baseSet)
    (hPoint : patch.coordinateMap
        (normalGraphHolonomicCoordinateGerm period hPeriod displacement base
          patch coordinate current) =
      normalGraph period hPeriod displacement current.2 current.1)
    (hDerivative : ∀ vector : ThroatCoverCoordinates,
      mfderiv (modelWithCornersSelf Real HolonomicVector4)
          coverModelWithCorners patch.coordinateMap
          (normalGraphHolonomicCoordinateGerm period hPeriod displacement base
            patch coordinate current)
          (normalGraphHolonomicFamilyDerivativeCoordinates period hPeriod
            displacement base patch coordinate current vector) =
        mfderiv throatCoverModelWithCorners coverModelWithCorners
          (normalGraph period hPeriod displacement current.2) current.1
          ((trivializationAt ThroatCoverCoordinates
            (ThroatTangentFiber period hPeriod) base.1).symm current.1 vector))
    (first second : ThroatCoverCoordinates) :
    normalGraphHolonomicInducedMetricCoordinates period hPeriod metric
        displacement base patch coordinate current first second =
      normalGraphFamilyTraceTensorCoordinates period hPeriod metric displacement
        base current first second := by
  rw [show normalGraphFamilyTraceTensorCoordinates period hPeriod metric
      displacement base current first second =
    ContinuousLinearMap.inCoordinates ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod)
      (ThroatCoverCoordinates →L[Real] Real)
      (ThroatCotangentFiber period hPeriod)
      base.1 current.1 base.1 current.1
      (normalGraphInducedMetricValue period hPeriod metric displacement
        current.2 current.1) first second by rfl]
  rw [inCoordinates_apply_eq₂ hCurrent hCurrent (Set.mem_univ _)]
  simp only [normalGraphInducedMetricValue_apply]
  unfold normalGraphHolonomicInducedMetricCoordinates
  rw [localMetricCoordinateForm_apply]
  rw [hDerivative first, hDerivative second]
  rw [hPoint]
  simp

/-- Near an admissible anchor, the pre-existing intrinsic inverse is a right
inverse for the holonomic pullback metric.  No second inverse is introduced. -/
theorem normalGraphHolonomicInducedMetricInverseCoordinates_eventually_rightInverse
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement base.2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraph period hPeriod displacement base.2 base.1) :
    ∀ᶠ point in 𝓝 base.1,
      ∀ covector : ThroatCoverCoordinates →L[Real] Real,
      ∀ tangent : ThroatCoverCoordinates,
        normalGraphHolonomicInducedMetricCoordinates period hPeriod metric
            displacement base patch coordinate (point, base.2)
            (normalGraphInducedMetricInverseCoordinates period hPeriod metric
              displacement base (point, base.2) covector) tangent =
          covector tangent := by
  let sectionMap := fun point : EffectiveThroat period hPeriod =>
    (point, base.2)
  have hSection : ContMDiffAt throatCoverModelWithCorners
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real)) ∞
      sectionMap base.1 :=
    (contMDiff_id.prodMk contMDiff_const).contMDiffAt
  have hPointEventually :=
    (normalGraphHolonomicCoordinateGerm_eventually_reconstructs period hPeriod
      displacement base patch coordinate hAt).comp_tendsto hSection.continuousAt
  have hDerivativeEventually :=
    hSection.continuousAt.eventually
      (normalGraphHolonomicFamilyDerivativeCoordinates_eventually_reconstructs
        period hPeriod displacement base patch coordinate hAt)
  have hCurrentEventually : ∀ᶠ point in 𝓝 base.1,
      point ∈
        (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) base.1).baseSet :=
    (trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) base.1).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) base.1)
  have hCotangentEventually : ∀ᶠ point in 𝓝 base.1,
      point ∈
        (trivializationAt (ThroatCoverCoordinates →L[Real] Real)
          (ThroatCotangentFiber period hPeriod) base.1).baseSet :=
    (trivializationAt (ThroatCoverCoordinates →L[Real] Real)
      (ThroatCotangentFiber period hPeriod) base.1).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt
          (ThroatCoverCoordinates →L[Real] Real)
          (ThroatCotangentFiber period hPeriod) base.1)
  filter_upwards [hPointEventually, hDerivativeEventually, hCurrentEventually,
    hCotangentEventually] with point hPoint hDerivative hCurrent hCotangent
  intro covector tangent
  let current : EffectiveThroat period hPeriod × Real := (point, base.2)
  have hMetric : ∀ first second : ThroatCoverCoordinates,
      normalGraphHolonomicInducedMetricCoordinates period hPeriod metric
          displacement base patch coordinate current first second =
        normalGraphFamilyTraceTensorCoordinates period hPeriod metric
          displacement base current first second := by
    intro first second
    exact
      normalGraphHolonomicInducedMetricCoordinates_eq_trace_of_reconstructs
        period hPeriod metric displacement base current patch coordinate
          hCurrent hPoint hDerivative first second
  have hInvertible :=
    normalGraphFamilyTraceTensorCoordinates_isInvertible_current period hPeriod
      metric displacement base current hNonNull hCurrent hCotangent
  rw [hMetric]
  change normalGraphFamilyTraceTensorCoordinates period hPeriod metric
      displacement base current
        ((normalGraphFamilyTraceTensorCoordinates period hPeriod metric
          displacement base current).inverse covector) tangent = covector tangent
  have hApply := congrArg (fun currentCovector => currentCovector tangent)
    (hInvertible.self_apply_inverse covector)
  exact hApply

/-- The canonical normal germ is orthogonal, on one genuine source-chart
neighborhood, to the derivative of the same moving graph germ. -/
theorem normalGraphCanonicalHolonomicLocalUnitNormalSourceGerm_eventually_orthogonal
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : OrientationBoundary period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter))
    (tangent : ThroatCoverCoordinates) :
    let base : EffectiveThroat period hPeriod × Real :=
      (orientationDoubleToThroat period hPeriod boundary, parameter)
    let ambient :=
      normalGraphCanonicalHolonomicMetricUnitNormalCoordinatesAt period hPeriod
        metric displacement parameter hNonNull boundary patch coordinate hAt
    (fun sourceCoordinate =>
      localMetricCoordinateForm period hPeriod metric patch
        (normalGraphHolonomicSourceChartGerm period hPeriod displacement base
          patch coordinate sourceCoordinate)
        (normalGraphCanonicalHolonomicLocalUnitNormalSourceGerm period hPeriod
          metric displacement base patch coordinate ambient sourceCoordinate)
        (fderiv Real
          (normalGraphHolonomicSourceChartGerm period hPeriod displacement base
            patch coordinate) sourceCoordinate tangent)) =ᶠ[
          𝓝 (extChartAt throatCoverModelWithCorners base.1 base.1)]
      fun _ => 0 := by
  dsimp only
  let base : EffectiveThroat period hPeriod × Real :=
    (orientationDoubleToThroat period hPeriod boundary, parameter)
  let ambient :=
    normalGraphCanonicalHolonomicMetricUnitNormalCoordinatesAt period hPeriod
      metric displacement parameter hNonNull boundary patch coordinate hAt
  let inverse := (extChartAt throatCoverModelWithCorners base.1).symm
  have hGraph : patch.coordinateMap coordinate =
      normalGraph period hPeriod displacement base.2 base.1 := by
    simpa [base, normalGraphOrientationDouble] using hAt
  have hInverseContinuous : ContinuousAt inverse
      (extChartAt throatCoverModelWithCorners base.1 base.1) :=
    continuousAt_extChartAt_symm base.1
  have hInverseBase :
      inverse (extChartAt throatCoverModelWithCorners base.1 base.1) =
        base.1 := by
    dsimp only [inverse]
    rw [extChartAt_to_inv]
  have hInverseTendsto : Tendsto inverse
      (𝓝 (extChartAt throatCoverModelWithCorners base.1 base.1))
      (𝓝 base.1) := by
    have hTendsto : Tendsto inverse
        (𝓝 (extChartAt throatCoverModelWithCorners base.1 base.1))
        (𝓝 (inverse
          (extChartAt throatCoverModelWithCorners base.1 base.1))) :=
      hInverseContinuous
    rw [hInverseBase] at hTendsto
    exact hTendsto
  have hTarget : ∀ᶠ sourceCoordinate in
      𝓝 (extChartAt throatCoverModelWithCorners base.1 base.1),
      sourceCoordinate ∈
        (extChartAt throatCoverModelWithCorners base.1).target :=
    extChartAt_target_mem_nhds base.1
  have hCurrentPoint : ∀ᶠ point in 𝓝 base.1, point ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) base.1).baseSet :=
    (trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) base.1).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) base.1)
  have hRepresentative :=
    normalGraphHolonomicSpatialRepresentative_eventually_contMDiffAt period
      hPeriod displacement base patch coordinate hGraph
  have hRightInverse :=
    normalGraphHolonomicInducedMetricInverseCoordinates_eventually_rightInverse
      period hPeriod metric displacement base hNonNull patch coordinate hGraph
  filter_upwards [hTarget, hInverseTendsto.eventually hCurrentPoint,
    hInverseTendsto.eventually hRepresentative,
    hInverseTendsto.eventually hRightInverse] with sourceCoordinate
      hSourceTarget hCurrent hRepresentativeAt hInverse
  have hDerivative :=
    normalGraphHolonomicSourceChartGerm_fderiv_eq_family_of_mem period hPeriod
      displacement base patch coordinate sourceCoordinate hSourceTarget hCurrent
        hRepresentativeAt tangent
  rw [hDerivative]
  exact
    normalGraphHolonomicMetricUnitNormalCoordinates_orthogonal_of_rightInverse
      period hPeriod metric displacement base (inverse sourceCoordinate, base.2)
        patch coordinate ambient hInverse tangent

end GaussWeingartenDifferentiation

/-- The coordinate vector of the global normal obeys the genuine holonomic
transition law. -/
theorem normalGraphCanonicalHolonomicMetricUnitNormalCoordinatesAt_transition
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : OrientationBoundary period hPeriod)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : HolonomicVector4)
    (hFirst : firstPatch.coordinateMap firstCoordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter))
    (hSecond : secondPatch.coordinateMap secondCoordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter)) :
    holonomicCoordinateTransitionLinearEquivAt period hPeriod firstPatch
        secondPatch firstCoordinate secondCoordinate (hFirst.trans hSecond.symm)
        (normalGraphCanonicalHolonomicMetricUnitNormalCoordinatesAt period
          hPeriod metric displacement parameter hNonNull boundary firstPatch
            firstCoordinate hFirst) =
      normalGraphCanonicalHolonomicMetricUnitNormalCoordinatesAt period hPeriod
        metric displacement parameter hNonNull boundary secondPatch
          secondCoordinate hSecond := by
  let secondDerivative :=
    (secondPatch.coordinateMap_isLocalDiffeomorph secondCoordinate)
      |>.mfderivToContinuousLinearEquiv (by simp)
  apply secondDerivative.injective
  change
    mfderiv (modelWithCornersSelf Real HolonomicVector4) coverModelWithCorners
        secondPatch.coordinateMap secondCoordinate
        (holonomicCoordinateTransitionLinearEquivAt period hPeriod firstPatch
          secondPatch firstCoordinate secondCoordinate (hFirst.trans hSecond.symm)
          (normalGraphCanonicalHolonomicMetricUnitNormalCoordinatesAt period
            hPeriod metric displacement parameter hNonNull boundary firstPatch
              firstCoordinate hFirst)) =
      mfderiv (modelWithCornersSelf Real HolonomicVector4) coverModelWithCorners
        secondPatch.coordinateMap secondCoordinate
        (normalGraphCanonicalHolonomicMetricUnitNormalCoordinatesAt period
          hPeriod metric displacement parameter hNonNull boundary secondPatch
            secondCoordinate hSecond)
  apply eq_of_heq
  have hIntrinsicNormal : HEq
      (hFirst.symm ▸ normalGraphCanonicalMetricUnitNormal period hPeriod metric
        displacement parameter hNonNull boundary)
      (hSecond.symm ▸ normalGraphCanonicalMetricUnitNormal period hPeriod metric
        displacement parameter hNonNull boundary) := by
    have hFirstTransport := eqRec_heq hFirst.symm
      (normalGraphCanonicalMetricUnitNormal period hPeriod metric displacement
        parameter hNonNull boundary)
    have hSecondTransport := eqRec_heq hSecond.symm
      (normalGraphCanonicalMetricUnitNormal period hPeriod metric displacement
        parameter hNonNull boundary)
    exact hFirstTransport.trans hSecondTransport.symm
  exact
    (holonomicCoordinateMap_mfderiv_transition_heq period hPeriod firstPatch
      secondPatch firstCoordinate secondCoordinate
      (normalGraphCanonicalHolonomicMetricUnitNormalCoordinatesAt period
        hPeriod metric displacement parameter hNonNull boundary firstPatch
          firstCoordinate hFirst) (hFirst.trans hSecond.symm)).symm.trans
      ((normalGraphCanonicalHolonomicMetricUnitNormalCoordinatesAt_reconstructs
        period hPeriod metric displacement parameter hNonNull boundary
          firstPatch firstCoordinate hFirst).heq.trans
      (hIntrinsicNormal.trans
        (normalGraphCanonicalHolonomicMetricUnitNormalCoordinatesAt_reconstructs
          period hPeriod metric displacement parameter hNonNull boundary
            secondPatch secondCoordinate hSecond).symm.heq))

set_option backward.isDefEq.respectTransparency false in
/-- In a fixed holonomic chart through the common graph point, the global
canonical normal reverses under the residual orientation deck involution. -/
theorem normalGraphCanonicalHolonomicMetricUnitNormalCoordinatesAt_deck
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : OrientationBoundary period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter))
    (hAtDeck : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (orientationDeck period hPeriod boundary, parameter)) :
    normalGraphCanonicalHolonomicMetricUnitNormalCoordinatesAt period hPeriod
        metric displacement parameter hNonNull
          (orientationDeck period hPeriod boundary) patch coordinate hAtDeck =
      -normalGraphCanonicalHolonomicMetricUnitNormalCoordinatesAt period hPeriod
        metric displacement parameter hNonNull boundary patch coordinate hAt := by
  let derivativeEquiv :=
    (patch.coordinateMap_isLocalDiffeomorph coordinate)
      |>.mfderivToContinuousLinearEquiv (by simp)
  apply derivativeEquiv.injective
  rw [map_neg]
  change
    mfderiv (modelWithCornersSelf Real HolonomicVector4) coverModelWithCorners
        patch.coordinateMap coordinate
        (normalGraphCanonicalHolonomicMetricUnitNormalCoordinatesAt period
          hPeriod metric displacement parameter hNonNull
            (orientationDeck period hPeriod boundary) patch coordinate hAtDeck) =
      -(mfderiv (modelWithCornersSelf Real HolonomicVector4)
        coverModelWithCorners patch.coordinateMap coordinate
        (normalGraphCanonicalHolonomicMetricUnitNormalCoordinatesAt period
          hPeriod metric displacement parameter hNonNull boundary patch
            coordinate hAt))
  rw [normalGraphCanonicalHolonomicMetricUnitNormalCoordinatesAt_reconstructs,
    normalGraphCanonicalHolonomicMetricUnitNormalCoordinatesAt_reconstructs]
  apply eq_of_heq
  have hDeck := normalGraphCanonicalMetricUnitNormal_deck period hPeriod metric
    displacement parameter hNonNull boundary
  have hLeft := eqRec_heq hAtDeck.symm
    (normalGraphCanonicalMetricUnitNormal period hPeriod metric displacement
      parameter hNonNull (orientationDeck period hPeriod boundary))
  have hRight := eqRec_heq hAt.symm
    (-normalGraphCanonicalMetricUnitNormal period hPeriod metric displacement
      parameter hNonNull boundary)
  have hTransportNeg :
      (hAt.symm ▸
          (-normalGraphCanonicalMetricUnitNormal period hPeriod metric
            displacement parameter hNonNull boundary)) =
        -(hAt.symm ▸ normalGraphCanonicalMetricUnitNormal period hPeriod metric
          displacement parameter hNonNull boundary) := by
    simp
  exact hLeft.trans
    (hDeck.trans (hRight.symm.trans hTransportNeg.heq))

/-- Covariant acceleration of the mobile graph in a genuine holonomic chart:
the raw second derivative plus the already constructed Levi--Civita term. -/
def normalGraphCanonicalHolonomicCovariantAccelerationCoordinatesAt
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (first second : ThroatCoverCoordinates) : HolonomicVector4 :=
  normalGraphHolonomicSourceSecondDerivativeCoordinatesAt period hPeriod
      displacement base patch coordinate first second +
    localLeviCivitaChristoffelApply period hPeriod metric patch coordinate
      (normalGraphHolonomicSourceFirstDerivativeCoordinatesAt period hPeriod
        displacement base patch coordinate first)
      (normalGraphHolonomicSourceFirstDerivativeCoordinatesAt period hPeriod
        displacement base patch coordinate second)

/-- The Hessian defect of the raw graph second derivative cancels exactly
against the inhomogeneous Levi--Civita transition term. -/
theorem normalGraphCanonicalHolonomicCovariantAccelerationCoordinatesAt_transition
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : HolonomicVector4)
    (hFirst : firstPatch.coordinateMap firstCoordinate =
      normalGraph period hPeriod displacement base.2 base.1)
    (hSecond : secondPatch.coordinateMap secondCoordinate =
      normalGraph period hPeriod displacement base.2 base.1)
    (first second : ThroatCoverCoordinates) :
    holonomicCoordinateTransitionLinearEquivAt period hPeriod firstPatch
        secondPatch firstCoordinate secondCoordinate (hFirst.trans hSecond.symm)
        (normalGraphCanonicalHolonomicCovariantAccelerationCoordinatesAt period
          hPeriod metric displacement base firstPatch firstCoordinate first
            second) =
      normalGraphCanonicalHolonomicCovariantAccelerationCoordinatesAt period
        hPeriod metric displacement base secondPatch secondCoordinate first
          second := by
  let samePoint := hFirst.trans hSecond.symm
  let transition := holonomicCoordinateTransitionAt period hPeriod firstPatch
    secondPatch firstCoordinate secondCoordinate samePoint
  let transitionLinear :=
    holonomicCoordinateTransitionLinearEquivAt period hPeriod firstPatch
      secondPatch firstCoordinate secondCoordinate samePoint
  let firstTangent :=
    normalGraphHolonomicSourceFirstDerivativeCoordinatesAt period hPeriod
      displacement base firstPatch firstCoordinate first
  let secondTangent :=
    normalGraphHolonomicSourceFirstDerivativeCoordinatesAt period hPeriod
      displacement base firstPatch firstCoordinate second
  have hFirstTangent :=
    normalGraphHolonomicSourceFirstDerivativeCoordinatesAt_transition period
      hPeriod displacement base firstPatch secondPatch firstCoordinate
        secondCoordinate hFirst hSecond first
  have hSecondTangent :=
    normalGraphHolonomicSourceFirstDerivativeCoordinatesAt_transition period
      hPeriod displacement base firstPatch secondPatch firstCoordinate
        secondCoordinate hFirst hSecond second
  dsimp only at hFirstTangent hSecondTangent
  have hSecondDerivative :=
    normalGraphHolonomicSourceSecondDerivativeCoordinatesAt_transition period
      hPeriod displacement base firstPatch secondPatch firstCoordinate
        secondCoordinate hFirst hSecond first second
  dsimp only at hSecondDerivative
  have hConnection :=
    (fixedHolonomicTransition_leviCivita_eventuallyEq_vectors period hPeriod
      metric firstPatch secondPatch firstCoordinate secondCoordinate samePoint
        firstTangent secondTangent).eq_of_nhds
  rw [holonomicCoordinateTransitionAt_apply period hPeriod firstPatch
      secondPatch firstCoordinate secondCoordinate samePoint,
    ← holonomicCoordinateTransitionLinearEquivAt_coe period hPeriod firstPatch
      secondPatch firstCoordinate secondCoordinate samePoint] at hConnection
  rw [← holonomicCoordinateTransitionLinearEquivAt_coe period hPeriod firstPatch
      secondPatch firstCoordinate secondCoordinate samePoint] at hFirstTangent hSecondTangent hSecondDerivative
  let hessianTerm := fderiv Real (fderiv Real transition) firstCoordinate
    firstTangent secondTangent
  have hFirstTangent' : transitionLinear firstTangent =
      normalGraphHolonomicSourceFirstDerivativeCoordinatesAt period hPeriod
        displacement base secondPatch secondCoordinate first := by
    simpa [transitionLinear, firstTangent] using hFirstTangent
  have hSecondTangent' : transitionLinear secondTangent =
      normalGraphHolonomicSourceFirstDerivativeCoordinatesAt period hPeriod
        displacement base secondPatch secondCoordinate second := by
    simpa [transitionLinear, secondTangent] using hSecondTangent
  have hSecondDerivative' :
      normalGraphHolonomicSourceSecondDerivativeCoordinatesAt period hPeriod
          displacement base secondPatch secondCoordinate first second =
        hessianTerm + transitionLinear
          (normalGraphHolonomicSourceSecondDerivativeCoordinatesAt period
            hPeriod displacement base firstPatch firstCoordinate first second) := by
    simpa [hessianTerm, transition, transitionLinear, firstTangent,
      secondTangent] using hSecondDerivative
  have hConnection' : transitionLinear
      (localLeviCivitaChristoffelApply period hPeriod metric firstPatch
        firstCoordinate firstTangent secondTangent) =
      localLeviCivitaChristoffelApply period hPeriod metric secondPatch
          secondCoordinate (transitionLinear firstTangent)
          (transitionLinear secondTangent) + hessianTerm := by
    simpa [hessianTerm, transition, transitionLinear] using hConnection
  unfold normalGraphCanonicalHolonomicCovariantAccelerationCoordinatesAt
  rw [map_add]
  change transitionLinear _ + transitionLinear
      (localLeviCivitaChristoffelApply period hPeriod metric firstPatch
        firstCoordinate firstTangent secondTangent) = _
  rw [hConnection', hSecondDerivative', ← hFirstTangent', ← hSecondTangent']
  abel

/-- Gauss-form Weingarten pairing for the global coorientation.  It uses only
the same graph, metric and canonical normal already constructed above. -/
def normalGraphCanonicalHolonomicGaussRawExtrinsicCurvatureCoordinatesAt
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : OrientationBoundary period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter))
    (first second : ThroatCoverCoordinates) : Real :=
  -localMetricCoordinateForm period hPeriod metric patch coordinate
    (normalGraphCanonicalHolonomicMetricUnitNormalCoordinatesAt period hPeriod
      metric displacement parameter hNonNull boundary patch coordinate hAt)
    (normalGraphCanonicalHolonomicCovariantAccelerationCoordinatesAt period
      hPeriod metric displacement
        (orientationDoubleToThroat period hPeriod boundary, parameter)
        patch coordinate first second)

/-- The historical smooth Weingarten pairing and the canonical Gauss pairing
are the same second fundamental form.  This differentiates the exact metric
orthogonality proved above and introduces neither a second normal nor a second
inverse metric. -/
theorem normalGraphCanonicalHolonomicGaussRawExtrinsicCurvatureCoordinatesAt_eq_weingarten
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : OrientationBoundary period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter))
    (first second : ThroatCoverCoordinates) :
    let base : EffectiveThroat period hPeriod × Real :=
      (orientationDoubleToThroat period hPeriod boundary, parameter)
    let ambient :=
      normalGraphCanonicalHolonomicMetricUnitNormalCoordinatesAt period hPeriod
        metric displacement parameter hNonNull boundary patch coordinate hAt
    normalGraphHolonomicRawExtrinsicCurvatureCoordinates period hPeriod metric
        displacement base patch coordinate ambient first second base =
      normalGraphCanonicalHolonomicGaussRawExtrinsicCurvatureCoordinatesAt
        period hPeriod metric displacement parameter hNonNull boundary patch
          coordinate hAt first second := by
  dsimp only
  let base : EffectiveThroat period hPeriod × Real :=
    (orientationDoubleToThroat period hPeriod boundary, parameter)
  let ambient :=
    normalGraphCanonicalHolonomicMetricUnitNormalCoordinatesAt period hPeriod
      metric displacement parameter hNonNull boundary patch coordinate hAt
  let sourceBase := extChartAt throatCoverModelWithCorners base.1 base.1
  let sourceGerm :=
    normalGraphHolonomicSourceChartGerm period hPeriod displacement base patch
      coordinate
  let normalGerm :=
    normalGraphCanonicalHolonomicLocalUnitNormalSourceGerm period hPeriod metric
      displacement base patch coordinate ambient
  let tangentGerm := fun sourceCoordinate =>
    fderiv Real sourceGerm sourceCoordinate second
  have hGraph : patch.coordinateMap coordinate =
      normalGraph period hPeriod displacement base.2 base.1 := by
    simpa [base, normalGraphOrientationDouble] using hAt
  have hSource : ContDiffAt Real ∞ sourceGerm sourceBase := by
    exact normalGraphHolonomicSourceChartGerm_contDiffAt period hPeriod
      displacement base patch coordinate hGraph
  have hNormal : ContDiffAt Real ∞ normalGerm sourceBase := by
    exact
      normalGraphCanonicalHolonomicLocalUnitNormalSourceGerm_contDiffAt period
        hPeriod metric displacement parameter hNonNull boundary patch coordinate
          hAt
  have hSourceC2 : ContDiffAt Real 2 sourceGerm sourceBase :=
    hSource.of_le (by
      change ((2 : ℕ∞) : WithTop ℕ∞) ≤
        ((⊤ : ℕ∞) : WithTop ℕ∞)
      exact WithTop.coe_le_coe.mpr le_top)
  have hFDeriv : DifferentiableAt Real (fderiv Real sourceGerm) sourceBase :=
    (hSourceC2.fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)
  have hTangent : DifferentiableAt Real tangentGerm sourceBase :=
    hFDeriv.clm_apply (differentiableAt_const second)
  have hOrthogonal :=
    normalGraphCanonicalHolonomicLocalUnitNormalSourceGerm_eventually_orthogonal
      period hPeriod metric displacement parameter hNonNull boundary patch
        coordinate hAt second
  have hGaussWeingarten :=
    localMetric_gauss_weingarten_of_eventually_orthogonal period hPeriod metric
      patch sourceGerm normalGerm tangentGerm sourceBase first
        (hSource.differentiableAt (by simp))
        (hNormal.differentiableAt (by simp)) hTangent hOrthogonal
  have hTangentDerivative :
      fderiv Real tangentGerm sourceBase first =
        normalGraphHolonomicSourceSecondDerivativeCoordinatesAt period hPeriod
          displacement base patch coordinate first second := by
    unfold normalGraphHolonomicSourceSecondDerivativeCoordinatesAt
    exact normalBoundary_fderiv_continuousLinearMap_apply_const
      (fderiv Real sourceGerm) sourceBase first second hFDeriv
  dsimp only [sourceGerm, sourceBase, normalGerm, tangentGerm]
    at hGaussWeingarten
  rw [normalGraphHolonomicSourceChartGerm_base period hPeriod displacement base
    patch coordinate hGraph] at hGaussWeingarten
  rw [normalGraphCanonicalHolonomicLocalUnitNormalSourceGerm_base period hPeriod
    metric displacement parameter hNonNull boundary patch coordinate hAt]
    at hGaussWeingarten
  rw [normalGraphCanonicalHolonomicLocalUnitNormalSourceGerm_fderiv period
    hPeriod metric displacement parameter hNonNull boundary patch coordinate hAt
      first] at hGaussWeingarten
  rw [hTangentDerivative] at hGaussWeingarten
  change
    localMetricCoordinateForm period hPeriod metric patch coordinate
        (normalGraphHolonomicMetricUnitNormalDerivativeCoordinates period hPeriod
          metric displacement base patch coordinate ambient base first +
          localLeviCivitaChristoffelApply period hPeriod metric patch coordinate
            (normalGraphHolonomicSourceFirstDerivativeCoordinatesAt period
              hPeriod displacement base patch coordinate first) ambient)
        (normalGraphHolonomicSourceFirstDerivativeCoordinatesAt period hPeriod
          displacement base patch coordinate second) =
      -localMetricCoordinateForm period hPeriod metric patch coordinate ambient
        (normalGraphHolonomicSourceSecondDerivativeCoordinatesAt period hPeriod
            displacement base patch coordinate first second +
          localLeviCivitaChristoffelApply period hPeriod metric patch coordinate
            (normalGraphHolonomicSourceFirstDerivativeCoordinatesAt period
              hPeriod displacement base patch coordinate first)
            (normalGraphHolonomicSourceFirstDerivativeCoordinatesAt period
              hPeriod displacement base patch coordinate second))
    at hGaussWeingarten
  unfold normalGraphHolonomicRawExtrinsicCurvatureCoordinates
    normalGraphCanonicalHolonomicGaussRawExtrinsicCurvatureCoordinatesAt
    normalGraphCanonicalHolonomicCovariantAccelerationCoordinatesAt
  dsimp only
  rw [normalGraphHolonomicCoordinateGerm_base period hPeriod displacement base
    patch coordinate hGraph]
  rw [normalGraphCanonicalHolonomicLocalUnitNormalCoordinates_eq period hPeriod
    metric displacement parameter hNonNull boundary patch coordinate hAt]
  rw [← normalGraphHolonomicSourceFirstDerivativeCoordinatesAt_eq_family period
    hPeriod displacement base patch coordinate hGraph]
  exact hGaussWeingarten

/-- The Gauss pairing of the global normal is independent of the ambient
holonomic chart. -/
theorem normalGraphCanonicalHolonomicGaussRawExtrinsicCurvatureCoordinatesAt_chart_independent
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : OrientationBoundary period hPeriod)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : HolonomicVector4)
    (hFirst : firstPatch.coordinateMap firstCoordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter))
    (hSecond : secondPatch.coordinateMap secondCoordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter))
    (first second : ThroatCoverCoordinates) :
    normalGraphCanonicalHolonomicGaussRawExtrinsicCurvatureCoordinatesAt period
        hPeriod metric displacement parameter hNonNull boundary firstPatch
          firstCoordinate hFirst first second =
      normalGraphCanonicalHolonomicGaussRawExtrinsicCurvatureCoordinatesAt period
        hPeriod metric displacement parameter hNonNull boundary secondPatch
          secondCoordinate hSecond first second := by
  let base : EffectiveThroat period hPeriod × Real :=
    (orientationDoubleToThroat period hPeriod boundary, parameter)
  let samePoint := hFirst.trans hSecond.symm
  let transitionLinear :=
    holonomicCoordinateTransitionLinearEquivAt period hPeriod firstPatch
      secondPatch firstCoordinate secondCoordinate samePoint
  let firstNormal :=
    normalGraphCanonicalHolonomicMetricUnitNormalCoordinatesAt period hPeriod
      metric displacement parameter hNonNull boundary firstPatch firstCoordinate
        hFirst
  let secondNormal :=
    normalGraphCanonicalHolonomicMetricUnitNormalCoordinatesAt period hPeriod
      metric displacement parameter hNonNull boundary secondPatch
        secondCoordinate hSecond
  let firstAcceleration :=
    normalGraphCanonicalHolonomicCovariantAccelerationCoordinatesAt period
      hPeriod metric displacement base firstPatch firstCoordinate first second
  let secondAcceleration :=
    normalGraphCanonicalHolonomicCovariantAccelerationCoordinatesAt period
      hPeriod metric displacement base secondPatch secondCoordinate first second
  have hFirstGraph : firstPatch.coordinateMap firstCoordinate =
      normalGraph period hPeriod displacement base.2 base.1 := by
    simpa [base, normalGraphOrientationDouble] using hFirst
  have hSecondGraph : secondPatch.coordinateMap secondCoordinate =
      normalGraph period hPeriod displacement base.2 base.1 := by
    simpa [base, normalGraphOrientationDouble] using hSecond
  have hNormal : transitionLinear firstNormal = secondNormal := by
    simpa [transitionLinear, firstNormal, secondNormal, samePoint] using
      (normalGraphCanonicalHolonomicMetricUnitNormalCoordinatesAt_transition
        period hPeriod metric displacement parameter hNonNull boundary
          firstPatch secondPatch firstCoordinate secondCoordinate hFirst hSecond)
  have hAcceleration :
      transitionLinear firstAcceleration = secondAcceleration := by
    simpa [transitionLinear, firstAcceleration, secondAcceleration, samePoint]
      using
      (normalGraphCanonicalHolonomicCovariantAccelerationCoordinatesAt_transition
        period hPeriod metric displacement base firstPatch secondPatch
          firstCoordinate secondCoordinate hFirstGraph hSecondGraph first second)
  have hMetric := localMetricCoordinateForm_transition period hPeriod metric
    firstPatch secondPatch firstCoordinate secondCoordinate firstNormal
      firstAcceleration samePoint
  rw [hNormal, hAcceleration] at hMetric
  simpa [normalGraphCanonicalHolonomicGaussRawExtrinsicCurvatureCoordinatesAt,
    base, firstNormal, secondNormal, firstAcceleration, secondAcceleration]
    using congrArg (fun value : Real => -value) hMetric

set_option backward.isDefEq.respectTransparency false in
/-- The global Gauss pairing reverses with the canonical normal under the
residual orientation deck involution. -/
theorem normalGraphCanonicalHolonomicGaussRawExtrinsicCurvatureCoordinatesAt_deck
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : OrientationBoundary period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter))
    (hAtDeck : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (orientationDeck period hPeriod boundary, parameter))
    (first second : ThroatCoverCoordinates) :
    normalGraphCanonicalHolonomicGaussRawExtrinsicCurvatureCoordinatesAt period
        hPeriod metric displacement parameter hNonNull
          (orientationDeck period hPeriod boundary) patch coordinate hAtDeck
            first second =
      -normalGraphCanonicalHolonomicGaussRawExtrinsicCurvatureCoordinatesAt
        period hPeriod metric displacement parameter hNonNull boundary patch
          coordinate hAt first second := by
  unfold normalGraphCanonicalHolonomicGaussRawExtrinsicCurvatureCoordinatesAt
  rw [normalGraphCanonicalHolonomicMetricUnitNormalCoordinatesAt_deck]
  rw [orientationDoubleToThroat_deck]
  simp [localMetricCoordinateForm]
  all_goals assumption

/-- Symmetric second fundamental form supplied to the unchanged GHY ledger. -/
def normalGraphCanonicalHolonomicGaussExtrinsicCurvatureCoordinatesAt
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : OrientationBoundary period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter))
    (first second : ThroatCoverCoordinates) : Real :=
  (1 / 2 : Real) *
    (normalGraphCanonicalHolonomicGaussRawExtrinsicCurvatureCoordinatesAt
        period hPeriod metric displacement parameter hNonNull boundary patch
          coordinate hAt first second +
      normalGraphCanonicalHolonomicGaussRawExtrinsicCurvatureCoordinatesAt
        period hPeriod metric displacement parameter hNonNull boundary patch
          coordinate hAt second first)

theorem normalGraphCanonicalHolonomicGaussExtrinsicCurvatureCoordinatesAt_symmetric
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : OrientationBoundary period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter))
    (first second : ThroatCoverCoordinates) :
    normalGraphCanonicalHolonomicGaussExtrinsicCurvatureCoordinatesAt period
        hPeriod metric displacement parameter hNonNull boundary patch coordinate
          hAt first second =
      normalGraphCanonicalHolonomicGaussExtrinsicCurvatureCoordinatesAt period
        hPeriod metric displacement parameter hNonNull boundary patch coordinate
          hAt second first := by
  unfold normalGraphCanonicalHolonomicGaussExtrinsicCurvatureCoordinatesAt
  ring

/-- The symmetric Gauss form has the same deck-odd law. -/
theorem normalGraphCanonicalHolonomicGaussExtrinsicCurvatureCoordinatesAt_deck
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : OrientationBoundary period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter))
    (hAtDeck : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (orientationDeck period hPeriod boundary, parameter))
    (first second : ThroatCoverCoordinates) :
    normalGraphCanonicalHolonomicGaussExtrinsicCurvatureCoordinatesAt period
        hPeriod metric displacement parameter hNonNull
          (orientationDeck period hPeriod boundary) patch coordinate hAtDeck
            first second =
      -normalGraphCanonicalHolonomicGaussExtrinsicCurvatureCoordinatesAt period
        hPeriod metric displacement parameter hNonNull boundary patch coordinate
          hAt first second := by
  unfold normalGraphCanonicalHolonomicGaussExtrinsicCurvatureCoordinatesAt
  rw [normalGraphCanonicalHolonomicGaussRawExtrinsicCurvatureCoordinatesAt_deck
      period hPeriod metric displacement parameter hNonNull boundary patch
        coordinate hAt hAtDeck first second,
    normalGraphCanonicalHolonomicGaussRawExtrinsicCurvatureCoordinatesAt_deck
      period hPeriod metric displacement parameter hNonNull boundary patch
        coordinate hAt hAtDeck second first]
  ring

/-- The symmetric second fundamental form inherits the same chart
independence. -/
theorem normalGraphCanonicalHolonomicGaussExtrinsicCurvatureCoordinatesAt_chart_independent
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : OrientationBoundary period hPeriod)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : HolonomicVector4)
    (hFirst : firstPatch.coordinateMap firstCoordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter))
    (hSecond : secondPatch.coordinateMap secondCoordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter))
    (first second : ThroatCoverCoordinates) :
    normalGraphCanonicalHolonomicGaussExtrinsicCurvatureCoordinatesAt period
        hPeriod metric displacement parameter hNonNull boundary firstPatch
          firstCoordinate hFirst first second =
      normalGraphCanonicalHolonomicGaussExtrinsicCurvatureCoordinatesAt period
        hPeriod metric displacement parameter hNonNull boundary secondPatch
          secondCoordinate hSecond first second := by
  unfold normalGraphCanonicalHolonomicGaussExtrinsicCurvatureCoordinatesAt
  rw [normalGraphCanonicalHolonomicGaussRawExtrinsicCurvatureCoordinatesAt_chart_independent
      period hPeriod metric displacement parameter hNonNull boundary firstPatch
        secondPatch firstCoordinate secondCoordinate hFirst hSecond first second,
    normalGraphCanonicalHolonomicGaussRawExtrinsicCurvatureCoordinatesAt_chart_independent
      period hPeriod metric displacement parameter hNonNull boundary firstPatch
        secondPatch firstCoordinate secondCoordinate hFirst hSecond second first]

/-- Matrix adapter of the global Gauss second fundamental form. -/
def normalGraphCanonicalHolonomicGaussExtrinsicCurvatureMatrixAt
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : OrientationBoundary period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter)) : Matrix3 :=
  fun first second =>
    normalGraphCanonicalHolonomicGaussExtrinsicCurvatureCoordinatesAt period
      hPeriod metric displacement parameter hNonNull boundary patch coordinate
        hAt (throatCoordinateBasis first) (throatCoordinateBasis second)

theorem normalGraphCanonicalHolonomicGaussExtrinsicCurvatureMatrixAt_symmetric
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : OrientationBoundary period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter)) :
    (normalGraphCanonicalHolonomicGaussExtrinsicCurvatureMatrixAt period hPeriod
      metric displacement parameter hNonNull boundary patch coordinate hAt).transpose =
      normalGraphCanonicalHolonomicGaussExtrinsicCurvatureMatrixAt period hPeriod
        metric displacement parameter hNonNull boundary patch coordinate hAt := by
  ext first second
  exact normalGraphCanonicalHolonomicGaussExtrinsicCurvatureCoordinatesAt_symmetric
    period hPeriod metric displacement parameter hNonNull boundary patch
      coordinate hAt _ _

/-- Matrix-level chart independence for the global second fundamental form. -/
theorem normalGraphCanonicalHolonomicGaussExtrinsicCurvatureMatrixAt_chart_independent
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : OrientationBoundary period hPeriod)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : HolonomicVector4)
    (hFirst : firstPatch.coordinateMap firstCoordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter))
    (hSecond : secondPatch.coordinateMap secondCoordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter)) :
    normalGraphCanonicalHolonomicGaussExtrinsicCurvatureMatrixAt period hPeriod
        metric displacement parameter hNonNull boundary firstPatch
          firstCoordinate hFirst =
      normalGraphCanonicalHolonomicGaussExtrinsicCurvatureMatrixAt period hPeriod
        metric displacement parameter hNonNull boundary secondPatch
          secondCoordinate hSecond := by
  ext first second
  exact
    normalGraphCanonicalHolonomicGaussExtrinsicCurvatureCoordinatesAt_chart_independent
      period hPeriod metric displacement parameter hNonNull boundary firstPatch
        secondPatch firstCoordinate secondCoordinate hFirst hSecond
          (throatCoordinateBasis first) (throatCoordinateBasis second)

/-- Matrix-level deck reversal for the global second fundamental form. -/
theorem normalGraphCanonicalHolonomicGaussExtrinsicCurvatureMatrixAt_deck
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : OrientationBoundary period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter))
    (hAtDeck : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (orientationDeck period hPeriod boundary, parameter)) :
    normalGraphCanonicalHolonomicGaussExtrinsicCurvatureMatrixAt period hPeriod
        metric displacement parameter hNonNull
          (orientationDeck period hPeriod boundary) patch coordinate hAtDeck =
      -normalGraphCanonicalHolonomicGaussExtrinsicCurvatureMatrixAt period
        hPeriod metric displacement parameter hNonNull boundary patch coordinate
          hAt := by
  ext first second
  exact normalGraphCanonicalHolonomicGaussExtrinsicCurvatureCoordinatesAt_deck
    period hPeriod metric displacement parameter hNonNull boundary patch
      coordinate hAt hAtDeck (throatCoordinateBasis first)
        (throatCoordinateBasis second)

/-- Mean curvature obtained by contracting the global Gauss form with the
already constructed inverse induced metric. -/
def normalGraphCanonicalHolonomicGaussMeanCurvatureAt
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : OrientationBoundary period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter)) : Real :=
  Matrix.trace
    (normalGraphInducedInverseMatrix period hPeriod metric displacement
        (orientationDoubleToThroat period hPeriod boundary, parameter) *
      normalGraphCanonicalHolonomicGaussExtrinsicCurvatureMatrixAt period hPeriod
        metric displacement parameter hNonNull boundary patch coordinate hAt)

/-- The mean-curvature contraction is independent of the ambient holonomic
chart. -/
theorem normalGraphCanonicalHolonomicGaussMeanCurvatureAt_chart_independent
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : OrientationBoundary period hPeriod)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : HolonomicVector4)
    (hFirst : firstPatch.coordinateMap firstCoordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter))
    (hSecond : secondPatch.coordinateMap secondCoordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter)) :
    normalGraphCanonicalHolonomicGaussMeanCurvatureAt period hPeriod metric
        displacement parameter hNonNull boundary firstPatch firstCoordinate
          hFirst =
      normalGraphCanonicalHolonomicGaussMeanCurvatureAt period hPeriod metric
        displacement parameter hNonNull boundary secondPatch secondCoordinate
          hSecond := by
  unfold normalGraphCanonicalHolonomicGaussMeanCurvatureAt
  rw [normalGraphCanonicalHolonomicGaussExtrinsicCurvatureMatrixAt_chart_independent
    period hPeriod metric displacement parameter hNonNull boundary firstPatch
      secondPatch firstCoordinate secondCoordinate hFirst hSecond]

/-- Reversing the canonical normal reverses the mean curvature. -/
theorem normalGraphCanonicalHolonomicGaussMeanCurvatureAt_deck
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : OrientationBoundary period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter))
    (hAtDeck : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (orientationDeck period hPeriod boundary, parameter)) :
    normalGraphCanonicalHolonomicGaussMeanCurvatureAt period hPeriod metric
        displacement parameter hNonNull (orientationDeck period hPeriod boundary)
          patch coordinate hAtDeck =
      -normalGraphCanonicalHolonomicGaussMeanCurvatureAt period hPeriod metric
        displacement parameter hNonNull boundary patch coordinate hAt := by
  unfold normalGraphCanonicalHolonomicGaussMeanCurvatureAt
  rw [orientationDoubleToThroat_deck,
    normalGraphCanonicalHolonomicGaussExtrinsicCurvatureMatrixAt_deck period
      hPeriod metric displacement parameter hNonNull boundary patch coordinate
        hAt hAtDeck]
  simp

/-! ### Global Gauss geometry in the unchanged GHY ledger -/

/-- The unchanged non-null boundary ledger filled by the genuinely induced
metric, its existing intrinsic inverse and the global Gauss form. -/
def normalGraphCanonicalHolonomicGaussNonNullBoundaryPointDataAt
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : OrientationBoundary period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter))
    (orientation :
      P0EFTJanusGaussianNormalEmbeddedHypersurface.NormalOrientation) :
    NonNullBoundaryPointData where
  inducedMetric := normalGraphInducedMetricMatrix period hPeriod metric
    displacement (orientationDoubleToThroat period hPeriod boundary, parameter)
  inducedInverse := normalGraphInducedInverseMatrix period hPeriod metric
    displacement (orientationDoubleToThroat period hPeriod boundary, parameter)
  extrinsicCurvature :=
    normalGraphCanonicalHolonomicGaussExtrinsicCurvatureMatrixAt period hPeriod
      metric displacement parameter hNonNull boundary patch coordinate hAt
  orientationSign := orientation.sign
  inverseWitness :=
    { inverse_mul := normalGraphInducedInverseMatrix_mul_metric period hPeriod
        metric displacement
          (orientationDoubleToThroat period hPeriod boundary, parameter) hNonNull
      mul_inverse := normalGraphInducedMetricMatrix_mul_inverse period hPeriod
        metric displacement
          (orientationDoubleToThroat period hPeriod boundary, parameter) hNonNull }
  inducedMetricSymmetric := normalGraphInducedMetricMatrix_symmetric period
    hPeriod metric displacement
      (orientationDoubleToThroat period hPeriod boundary, parameter)
  extrinsicCurvatureSymmetric :=
    normalGraphCanonicalHolonomicGaussExtrinsicCurvatureMatrixAt_symmetric
      period hPeriod metric displacement parameter hNonNull boundary patch
        coordinate hAt
  orientationSignAdmissible := by
    cases orientation <;>
      simp [P0EFTJanusGaussianNormalEmbeddedHypersurface.NormalOrientation.sign,
        IsOrientationSign]

/-- Pointwise GHY density obtained by applying the pre-existing ledger to the
global Gauss geometry. -/
def normalGraphCanonicalHolonomicGaussGHYDensityAt
    (einsteinScale : Real)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : OrientationBoundary period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter))
    (orientation :
      P0EFTJanusGaussianNormalEmbeddedHypersurface.NormalOrientation) : Real :=
  nonNullGHYDensity einsteinScale
    (normalGraphCanonicalHolonomicGaussNonNullBoundaryPointDataAt period hPeriod
      metric displacement parameter hNonNull boundary patch coordinate hAt
        orientation)

/-- Expanded scalar formula of the unchanged GHY ledger. -/
theorem normalGraphCanonicalHolonomicGaussGHYDensityAt_formula
    (einsteinScale : Real)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : OrientationBoundary period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter))
    (orientation :
      P0EFTJanusGaussianNormalEmbeddedHypersurface.NormalOrientation) :
    normalGraphCanonicalHolonomicGaussGHYDensityAt period hPeriod einsteinScale
        metric displacement parameter hNonNull boundary patch coordinate hAt
          orientation =
      einsteinScale * orientation.sign *
        Real.sqrt |Matrix.det
          (normalGraphInducedMetricMatrix period hPeriod metric displacement
            (orientationDoubleToThroat period hPeriod boundary, parameter))| *
        Matrix.trace
          (normalGraphInducedInverseMatrix period hPeriod metric displacement
              (orientationDoubleToThroat period hPeriod boundary, parameter) *
            normalGraphCanonicalHolonomicGaussExtrinsicCurvatureMatrixAt period
              hPeriod metric displacement parameter hNonNull boundary patch
                coordinate hAt) :=
  rfl

/-- The unchanged ledger is exactly its determinant density times the global
mean-curvature contraction. -/
theorem normalGraphCanonicalHolonomicGaussGHYDensityAt_eq_meanCurvature
    (einsteinScale : Real)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : OrientationBoundary period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter))
    (orientation :
      P0EFTJanusGaussianNormalEmbeddedHypersurface.NormalOrientation) :
    normalGraphCanonicalHolonomicGaussGHYDensityAt period hPeriod einsteinScale
        metric displacement parameter hNonNull boundary patch coordinate hAt
          orientation =
      einsteinScale * orientation.sign *
        Real.sqrt |Matrix.det
          (normalGraphInducedMetricMatrix period hPeriod metric displacement
            (orientationDoubleToThroat period hPeriod boundary, parameter))| *
        normalGraphCanonicalHolonomicGaussMeanCurvatureAt period hPeriod metric
          displacement parameter hNonNull boundary patch coordinate hAt :=
  rfl

/-- The Gauss GHY density is independent of the ambient holonomic chart. -/
theorem normalGraphCanonicalHolonomicGaussGHYDensityAt_chart_independent
    (einsteinScale : Real)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : OrientationBoundary period hPeriod)
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : HolonomicVector4)
    (hFirst : firstPatch.coordinateMap firstCoordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter))
    (hSecond : secondPatch.coordinateMap secondCoordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter))
    (orientation :
      P0EFTJanusGaussianNormalEmbeddedHypersurface.NormalOrientation) :
    normalGraphCanonicalHolonomicGaussGHYDensityAt period hPeriod einsteinScale
        metric displacement parameter hNonNull boundary firstPatch
          firstCoordinate hFirst orientation =
      normalGraphCanonicalHolonomicGaussGHYDensityAt period hPeriod einsteinScale
        metric displacement parameter hNonNull boundary secondPatch
          secondCoordinate hSecond orientation := by
  rw [normalGraphCanonicalHolonomicGaussGHYDensityAt_formula,
    normalGraphCanonicalHolonomicGaussGHYDensityAt_formula]
  rw [normalGraphCanonicalHolonomicGaussExtrinsicCurvatureMatrixAt_chart_independent
    period hPeriod metric displacement parameter hNonNull boundary firstPatch
      secondPatch firstCoordinate secondCoordinate hFirst hSecond]

/-- Reversing both the deck normal and the boundary orientation leaves the
physical GHY density unchanged. -/
theorem normalGraphCanonicalHolonomicGaussGHYDensityAt_deck
    (einsteinScale : Real)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : OrientationBoundary period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter))
    (hAtDeck : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (orientationDeck period hPeriod boundary, parameter)) :
    normalGraphCanonicalHolonomicGaussGHYDensityAt period hPeriod einsteinScale
        metric displacement parameter hNonNull
          (orientationDeck period hPeriod boundary) patch coordinate hAtDeck
            .decreasing =
      normalGraphCanonicalHolonomicGaussGHYDensityAt period hPeriod einsteinScale
        metric displacement parameter hNonNull boundary patch coordinate hAt
          .increasing := by
  rw [normalGraphCanonicalHolonomicGaussGHYDensityAt_formula,
    normalGraphCanonicalHolonomicGaussGHYDensityAt_formula]
  rw [orientationDoubleToThroat_deck,
    normalGraphCanonicalHolonomicGaussExtrinsicCurvatureMatrixAt_deck period
      hPeriod metric displacement parameter hNonNull boundary patch coordinate
        hAt hAtDeck]
  simp [P0EFTJanusGaussianNormalEmbeddedHypersurface.NormalOrientation.sign]

/-! ## Global chart-free Gauss--GHY density -/

/-- A canonical atlas choice at an ambient quotient point.  This is only a
presentation device: the density below is proved independent of this choice. -/
noncomputable def normalGraphCanonicalSelectedHolonomicPatchAt
    (point : EffectiveQuotient period hPeriod) :
    SmoothHolonomicFrameChart4 period hPeriod :=
  Classical.choose
    (canonicalHolonomicChartThroughEveryPoint period hPeriod point)

/-- Coordinates of the selected holonomic patch at an ambient point. -/
noncomputable def normalGraphCanonicalSelectedHolonomicCoordinateAt
    (point : EffectiveQuotient period hPeriod) : HolonomicVector4 :=
  Classical.choose (Classical.choose_spec
    (canonicalHolonomicChartThroughEveryPoint period hPeriod point))

/-- The selected holonomic coordinates reconstruct the ambient point. -/
theorem normalGraphCanonicalSelectedHolonomicPatchAt_map
    (point : EffectiveQuotient period hPeriod) :
    (normalGraphCanonicalSelectedHolonomicPatchAt period hPeriod point).coordinateMap
        (normalGraphCanonicalSelectedHolonomicCoordinateAt period hPeriod point) =
      point :=
  Classical.choose_spec (Classical.choose_spec
    (canonicalHolonomicChartThroughEveryPoint period hPeriod point))

/-- Global Gauss--GHY density on the orientation double.  Its defining atlas
choice carries no geometric data, by
`normalGraphCanonicalHolonomicGaussGHYDensityAt_chart_independent`. -/
noncomputable def normalGraphCanonicalGaussGHYDensity
    (einsteinScale : Real)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : OrientationBoundary period hPeriod)
    (orientation :
      P0EFTJanusGaussianNormalEmbeddedHypersurface.NormalOrientation) : Real :=
  let point := normalGraphOrientationDouble period hPeriod displacement
    (boundary, parameter)
  normalGraphCanonicalHolonomicGaussGHYDensityAt period hPeriod einsteinScale
    metric displacement parameter hNonNull boundary
      (normalGraphCanonicalSelectedHolonomicPatchAt period hPeriod point)
      (normalGraphCanonicalSelectedHolonomicCoordinateAt period hPeriod point)
      (normalGraphCanonicalSelectedHolonomicPatchAt_map period hPeriod point)
      orientation

/-- The global density descends across the orientation deck transformation:
the normal and the boundary orientation reverse together. -/
theorem normalGraphCanonicalGaussGHYDensity_deck
    (einsteinScale : Real)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : OrientationBoundary period hPeriod) :
    normalGraphCanonicalGaussGHYDensity period hPeriod einsteinScale metric
        displacement parameter hNonNull (orientationDeck period hPeriod boundary)
          .decreasing =
      normalGraphCanonicalGaussGHYDensity period hPeriod einsteinScale metric
        displacement parameter hNonNull boundary .increasing := by
  unfold normalGraphCanonicalGaussGHYDensity
  let point := normalGraphOrientationDouble period hPeriod displacement
    (boundary, parameter)
  let deckPoint := normalGraphOrientationDouble period hPeriod displacement
    (orientationDeck period hPeriod boundary, parameter)
  let patch := normalGraphCanonicalSelectedHolonomicPatchAt period hPeriod point
  let coordinate :=
    normalGraphCanonicalSelectedHolonomicCoordinateAt period hPeriod point
  let deckPatch :=
    normalGraphCanonicalSelectedHolonomicPatchAt period hPeriod deckPoint
  let deckCoordinate :=
    normalGraphCanonicalSelectedHolonomicCoordinateAt period hPeriod deckPoint
  have hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter) := by
    simpa [point, patch, coordinate] using
      normalGraphCanonicalSelectedHolonomicPatchAt_map period hPeriod point
  have hAtDeck : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (orientationDeck period hPeriod boundary, parameter) :=
    hAt.trans
      (normalGraphOrientationDouble_deck period hPeriod displacement boundary
        parameter).symm
  have hSelectedDeck : deckPatch.coordinateMap deckCoordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (orientationDeck period hPeriod boundary, parameter) := by
    simpa [deckPoint, deckPatch, deckCoordinate] using
      normalGraphCanonicalSelectedHolonomicPatchAt_map period hPeriod deckPoint
  have hChart :=
    normalGraphCanonicalHolonomicGaussGHYDensityAt_chart_independent period
      hPeriod einsteinScale metric displacement parameter hNonNull
        (orientationDeck period hPeriod boundary) deckPatch patch deckCoordinate
          coordinate hSelectedDeck hAtDeck .decreasing
  have hDeck :=
    normalGraphCanonicalHolonomicGaussGHYDensityAt_deck period hPeriod
      einsteinScale metric displacement parameter hNonNull boundary patch
        coordinate hAt hAtDeck
  simpa [point, deckPoint, patch, coordinate, deckPatch, deckCoordinate] using
    hChart.trans hDeck

/-- Chart-free mean curvature on the orientation double. -/
noncomputable def normalGraphCanonicalGaussMeanCurvature
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : OrientationBoundary period hPeriod) : Real :=
  let point := normalGraphOrientationDouble period hPeriod displacement
    (boundary, parameter)
  normalGraphCanonicalHolonomicGaussMeanCurvatureAt period hPeriod metric
    displacement parameter hNonNull boundary
      (normalGraphCanonicalSelectedHolonomicPatchAt period hPeriod point)
      (normalGraphCanonicalSelectedHolonomicCoordinateAt period hPeriod point)
      (normalGraphCanonicalSelectedHolonomicPatchAt_map period hPeriod point)

/-- The chart-free mean curvature is odd under reversal of the canonical
normal. -/
theorem normalGraphCanonicalGaussMeanCurvature_deck
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : OrientationBoundary period hPeriod) :
    normalGraphCanonicalGaussMeanCurvature period hPeriod metric displacement
        parameter hNonNull (orientationDeck period hPeriod boundary) =
      -normalGraphCanonicalGaussMeanCurvature period hPeriod metric displacement
        parameter hNonNull boundary := by
  unfold normalGraphCanonicalGaussMeanCurvature
  let point := normalGraphOrientationDouble period hPeriod displacement
    (boundary, parameter)
  let deckPoint := normalGraphOrientationDouble period hPeriod displacement
    (orientationDeck period hPeriod boundary, parameter)
  let patch := normalGraphCanonicalSelectedHolonomicPatchAt period hPeriod point
  let coordinate :=
    normalGraphCanonicalSelectedHolonomicCoordinateAt period hPeriod point
  let deckPatch :=
    normalGraphCanonicalSelectedHolonomicPatchAt period hPeriod deckPoint
  let deckCoordinate :=
    normalGraphCanonicalSelectedHolonomicCoordinateAt period hPeriod deckPoint
  have hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter) := by
    simpa [point, patch, coordinate] using
      normalGraphCanonicalSelectedHolonomicPatchAt_map period hPeriod point
  have hAtDeck : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (orientationDeck period hPeriod boundary, parameter) :=
    hAt.trans
      (normalGraphOrientationDouble_deck period hPeriod displacement boundary
        parameter).symm
  have hSelectedDeck : deckPatch.coordinateMap deckCoordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (orientationDeck period hPeriod boundary, parameter) := by
    simpa [deckPoint, deckPatch, deckCoordinate] using
      normalGraphCanonicalSelectedHolonomicPatchAt_map period hPeriod deckPoint
  have hChart :=
    normalGraphCanonicalHolonomicGaussMeanCurvatureAt_chart_independent period
      hPeriod metric displacement parameter hNonNull
        (orientationDeck period hPeriod boundary) deckPatch patch deckCoordinate
          coordinate hSelectedDeck hAtDeck
  have hDeck := normalGraphCanonicalHolonomicGaussMeanCurvatureAt_deck period
    hPeriod metric displacement parameter hNonNull boundary patch coordinate hAt
      hAtDeck
  simpa [point, deckPoint, patch, coordinate, deckPatch, deckCoordinate] using
    hChart.trans hDeck

/-! ## Exact reuse of the installed non-null GHY ledger -/

/-- The auxiliary Dirichlet jet is irrelevant to the value of the exact GHY
curve at its origin.  We nevertheless supply its canonical zero member so the
mobile geometry enters the already installed `NonNullFaceDatum` unchanged. -/
def normalGraphZeroGaussianDirichletJet :
    P0EFTJanusGaussianNormalEHGHYCancellation.GaussianNormalDirichletJet where
  normalMetricVariation := 0
  normalMetricVariationSymmetric := by simp

/-- The chart-free mobile boundary point datum presented in the selected
holonomic chart.  Chart independence was proved above, so the selection adds
no geometry. -/
noncomputable def normalGraphCanonicalGaussNonNullBoundaryPointData
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : OrientationBoundary period hPeriod)
    (orientation :
      P0EFTJanusGaussianNormalEmbeddedHypersurface.NormalOrientation) :
    NonNullBoundaryPointData :=
  let point := normalGraphOrientationDouble period hPeriod displacement
    (boundary, parameter)
  normalGraphCanonicalHolonomicGaussNonNullBoundaryPointDataAt period hPeriod
    metric displacement parameter hNonNull boundary
      (normalGraphCanonicalSelectedHolonomicPatchAt period hPeriod point)
      (normalGraphCanonicalSelectedHolonomicCoordinateAt period hPeriod point)
      (normalGraphCanonicalSelectedHolonomicPatchAt_map period hPeriod point)
      orientation

@[simp]
theorem normalGraphCanonicalGaussNonNullBoundaryPointData_inducedMetric
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : OrientationBoundary period hPeriod)
    (orientation :
      P0EFTJanusGaussianNormalEmbeddedHypersurface.NormalOrientation) :
    (normalGraphCanonicalGaussNonNullBoundaryPointData period hPeriod metric
      displacement parameter hNonNull boundary orientation).inducedMetric =
      normalGraphInducedMetricMatrix period hPeriod metric displacement
        (orientationDoubleToThroat period hPeriod boundary, parameter) :=
  rfl

@[simp]
theorem normalGraphCanonicalGaussNonNullBoundaryPointData_meanCurvature
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : OrientationBoundary period hPeriod)
    (orientation :
      P0EFTJanusGaussianNormalEmbeddedHypersurface.NormalOrientation) :
    meanCurvatureTrace
        (normalGraphCanonicalGaussNonNullBoundaryPointData period hPeriod metric
          displacement parameter hNonNull boundary orientation) =
      normalGraphCanonicalGaussMeanCurvature period hPeriod metric displacement
        parameter hNonNull boundary := by
  unfold meanCurvatureTrace
    normalGraphCanonicalGaussNonNullBoundaryPointData
    normalGraphCanonicalGaussMeanCurvature
  rfl

/-- Coordinate volume density of the same mobile induced metric. -/
noncomputable def normalGraphCanonicalGaussCoordinateVolumeDensity
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : OrientationBoundary period hPeriod)
    (orientation :
      P0EFTJanusGaussianNormalEmbeddedHypersurface.NormalOrientation) : Real :=
  Real.sqrt |Matrix.det
    (normalGraphCanonicalGaussNonNullBoundaryPointData period hPeriod metric
      displacement parameter hNonNull boundary orientation).inducedMetric|

theorem normalGraphCanonicalGaussCoordinateVolumeDensity_ne_zero
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : OrientationBoundary period hPeriod)
    (orientation :
      P0EFTJanusGaussianNormalEmbeddedHypersurface.NormalOrientation) :
    normalGraphCanonicalGaussCoordinateVolumeDensity period hPeriod metric
      displacement parameter hNonNull boundary orientation ≠ 0 := by
  apply ne_of_gt
  exact Real.sqrt_pos.2 (abs_pos.mpr
    (P0EFTJanusNonNullGHYMeasureVariation.inducedMetric_det_ne_zero
      (normalGraphCanonicalGaussNonNullBoundaryPointData period hPeriod metric
        displacement parameter hNonNull boundary orientation)))

/-- Radon--Nikodym conversion from the coordinate density used by the
pointwise ledger to the already installed canonical throat measure. -/
noncomputable def normalGraphCanonicalGaussLedgerWeight
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : OrientationBoundary period hPeriod)
    (orientation :
      P0EFTJanusGaussianNormalEmbeddedHypersurface.NormalOrientation) : Real :=
  normalGraphRelativeVolumeDensity period hPeriod metric displacement parameter
      (orientationDoubleToThroat period hPeriod boundary) /
    normalGraphCanonicalGaussCoordinateVolumeDensity period hPeriod metric
      displacement parameter hNonNull boundary orientation

/-- The genuine mobile graph packaged in the unchanged face-ledger type. -/
noncomputable def normalGraphCanonicalGaussNonNullFaceDatum
    (einsteinScale : Real)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : OrientationBoundary period hPeriod)
    (orientation :
      P0EFTJanusGaussianNormalEmbeddedHypersurface.NormalOrientation) :
    NonNullFaceDatum where
  weight := normalGraphCanonicalGaussLedgerWeight period hPeriod metric
    displacement parameter hNonNull boundary orientation
  einsteinScale := einsteinScale
  geometry := normalGraphCanonicalGaussNonNullBoundaryPointData period hPeriod
    metric displacement parameter hNonNull boundary orientation
  dirichletJet := normalGraphZeroGaussianDirichletJet

/-- At the origin of its exact inverse curve, the installed face ledger is
exactly the mobile induced-measure GHY integrand. -/
theorem normalGraphCanonicalGaussNonNullFaceDatum_curve_zero
    (einsteinScale : Real)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : OrientationBoundary period hPeriod)
    (orientation :
      P0EFTJanusGaussianNormalEmbeddedHypersurface.NormalOrientation) :
    nonNullGHYCurve
        (normalGraphCanonicalGaussNonNullFaceDatum period hPeriod einsteinScale
          metric displacement parameter hNonNull boundary orientation) 0 =
      einsteinScale * orientation.sign *
        normalGraphRelativeVolumeDensity period hPeriod metric displacement
          parameter (orientationDoubleToThroat period hPeriod boundary) *
        normalGraphCanonicalGaussMeanCurvature period hPeriod metric
          displacement parameter hNonNull boundary := by
  rw [nonNullGHYCurve,
    P0EFTJanusNonNullGHYExactInverseCurve.nonNullGHYExactInverseCurve_zero]
  unfold normalGraphCanonicalGaussNonNullFaceDatum
    normalGraphCanonicalGaussLedgerWeight nonNullGHYDensity
  rw [normalGraphCanonicalGaussNonNullBoundaryPointData_meanCurvature]
  have hDensity := normalGraphCanonicalGaussCoordinateVolumeDensity_ne_zero
    period hPeriod metric displacement parameter hNonNull boundary orientation
  change
    (normalGraphRelativeVolumeDensity period hPeriod metric displacement
        parameter (orientationDoubleToThroat period hPeriod boundary) /
      normalGraphCanonicalGaussCoordinateVolumeDensity period hPeriod metric
        displacement parameter hNonNull boundary orientation) *
        (einsteinScale * orientation.sign *
          normalGraphCanonicalGaussCoordinateVolumeDensity period hPeriod metric
            displacement parameter hNonNull boundary orientation *
          normalGraphCanonicalGaussMeanCurvature period hPeriod metric
            displacement parameter hNonNull boundary) = _
  field_simp

/-- GHY integrand relative to the canonical throat reference measure.  The
frame-free relative density is precisely the Radon--Nikodym factor of the
already constructed induced graph measure. -/
def normalGraphCanonicalInducedGaussGHYIntegrand
    (einsteinScale : Real)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : OrientationBoundary period hPeriod)
    (orientation :
      P0EFTJanusGaussianNormalEmbeddedHypersurface.NormalOrientation) : Real :=
  einsteinScale * orientation.sign *
    normalGraphRelativeVolumeDensity period hPeriod metric displacement parameter
      (orientationDoubleToThroat period hPeriod boundary) *
    normalGraphCanonicalGaussMeanCurvature period hPeriod metric displacement
      parameter hNonNull boundary

/-- Pointwise same-action bridge: the mobile integrand is not a new GHY
formula, but the value at zero of the pre-existing exact face curve. -/
theorem normalGraphCanonicalGaussNonNullFaceDatum_curve_zero_eq_integrand
    (einsteinScale : Real)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : OrientationBoundary period hPeriod)
    (orientation :
      P0EFTJanusGaussianNormalEmbeddedHypersurface.NormalOrientation) :
    nonNullGHYCurve
        (normalGraphCanonicalGaussNonNullFaceDatum period hPeriod einsteinScale
          metric displacement parameter hNonNull boundary orientation) 0 =
      normalGraphCanonicalInducedGaussGHYIntegrand period hPeriod einsteinScale
        metric displacement parameter hNonNull boundary orientation := by
  simpa [normalGraphCanonicalInducedGaussGHYIntegrand] using
    normalGraphCanonicalGaussNonNullFaceDatum_curve_zero period hPeriod
      einsteinScale metric displacement parameter hNonNull boundary orientation

/-- Simultaneously reversing the coorientation and boundary orientation leaves
the induced-measure GHY integrand unchanged. -/
theorem normalGraphCanonicalInducedGaussGHYIntegrand_deck
    (einsteinScale : Real)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : OrientationBoundary period hPeriod) :
    normalGraphCanonicalInducedGaussGHYIntegrand period hPeriod einsteinScale
        metric displacement parameter hNonNull
          (orientationDeck period hPeriod boundary) .decreasing =
      normalGraphCanonicalInducedGaussGHYIntegrand period hPeriod einsteinScale
        metric displacement parameter hNonNull boundary .increasing := by
  unfold normalGraphCanonicalInducedGaussGHYIntegrand
  rw [orientationDoubleToThroat_deck,
    normalGraphCanonicalGaussMeanCurvature_deck]
  simp [P0EFTJanusGaussianNormalEmbeddedHypersurface.NormalOrientation.sign]

/-- The existing first-sheet lift projects definitionally to the canonical
fundamental-domain parametrization of the physical throat. -/
theorem orientationDoubleToThroat_canonicalLatitudeCutBoundaryFirstLift
    (base : CanonicalLatitudeBase) :
    orientationDoubleToThroat period hPeriod
        (canonicalLatitudeCutBoundaryFirstLift period hPeriod base) =
      canonicalLatitudeThroatMap period hPeriod base :=
  rfl

/-- First-sheet pullback of the induced-measure GHY integrand to the existing
canonical fundamental domain. -/
def normalGraphCanonicalFirstSheetGaussGHYIntegrand
    (einsteinScale : Real)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (base : CanonicalLatitudeBase) : Real :=
  normalGraphCanonicalInducedGaussGHYIntegrand period hPeriod einsteinScale
    metric displacement parameter hNonNull
      (canonicalLatitudeCutBoundaryFirstLift period hPeriod base) .increasing

/-- Deck-related second-sheet pullback with the opposite boundary
orientation. -/
def normalGraphCanonicalSecondSheetGaussGHYIntegrand
    (einsteinScale : Real)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (base : CanonicalLatitudeBase) : Real :=
  normalGraphCanonicalInducedGaussGHYIntegrand period hPeriod einsteinScale
    metric displacement parameter hNonNull
      (canonicalLatitudeCutBoundarySecondLift period hPeriod base) .decreasing

/-- The two oriented sheets have identical physical GHY integrands. -/
theorem normalGraphCanonicalSecondSheetGaussGHYIntegrand_eq_first
    (einsteinScale : Real)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (base : CanonicalLatitudeBase) :
    normalGraphCanonicalSecondSheetGaussGHYIntegrand period hPeriod
        einsteinScale metric displacement parameter hNonNull base =
      normalGraphCanonicalFirstSheetGaussGHYIntegrand period hPeriod
        einsteinScale metric displacement parameter hNonNull base := by
  unfold normalGraphCanonicalSecondSheetGaussGHYIntegrand
    normalGraphCanonicalFirstSheetGaussGHYIntegrand
    canonicalLatitudeCutBoundarySecondLift
  exact normalGraphCanonicalInducedGaussGHYIntegrand_deck period hPeriod
    einsteinScale metric displacement parameter hNonNull
      (canonicalLatitudeCutBoundaryFirstLift period hPeriod base)

/-- First-sheet mobile GHY action, integrated against the existing canonical
reference measure with the induced graph density inserted. -/
def normalGraphCanonicalFirstSheetGaussGHYAction
    (einsteinScale : Real)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter) :
    Real :=
  ∫ base, normalGraphCanonicalFirstSheetGaussGHYIntegrand period hPeriod
    einsteinScale metric displacement parameter hNonNull base
      ∂canonicalLatitudeBaseMeasure period

/-- Second-sheet mobile GHY action. -/
def normalGraphCanonicalSecondSheetGaussGHYAction
    (einsteinScale : Real)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter) :
    Real :=
  ∫ base, normalGraphCanonicalSecondSheetGaussGHYIntegrand period hPeriod
    einsteinScale metric displacement parameter hNonNull base
      ∂canonicalLatitudeBaseMeasure period

/-- First-sheet integral written directly with the installed exact GHY face
curve and the face datum derived above from the mobile graph. -/
def normalGraphCanonicalFirstSheetGaussGHYLedgerAction
    (einsteinScale : Real)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter) :
    Real :=
  ∫ base,
    nonNullGHYCurve
      (normalGraphCanonicalGaussNonNullFaceDatum period hPeriod einsteinScale
        metric displacement parameter hNonNull
          (canonicalLatitudeCutBoundaryFirstLift period hPeriod base)
          .increasing) 0
      ∂canonicalLatitudeBaseMeasure period

/-- Second-sheet version of the same unchanged face curve. -/
def normalGraphCanonicalSecondSheetGaussGHYLedgerAction
    (einsteinScale : Real)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter) :
    Real :=
  ∫ base,
    nonNullGHYCurve
      (normalGraphCanonicalGaussNonNullFaceDatum period hPeriod einsteinScale
        metric displacement parameter hNonNull
          (canonicalLatitudeCutBoundarySecondLift period hPeriod base)
          .decreasing) 0
      ∂canonicalLatitudeBaseMeasure period

theorem normalGraphCanonicalFirstSheetGaussGHYLedgerAction_eq
    (einsteinScale : Real)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter) :
    normalGraphCanonicalFirstSheetGaussGHYLedgerAction period hPeriod
        einsteinScale metric displacement parameter hNonNull =
      normalGraphCanonicalFirstSheetGaussGHYAction period hPeriod
        einsteinScale metric displacement parameter hNonNull := by
  unfold normalGraphCanonicalFirstSheetGaussGHYLedgerAction
    normalGraphCanonicalFirstSheetGaussGHYAction
    normalGraphCanonicalFirstSheetGaussGHYIntegrand
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun base =>
    normalGraphCanonicalGaussNonNullFaceDatum_curve_zero_eq_integrand
      period hPeriod einsteinScale metric displacement parameter hNonNull
        (canonicalLatitudeCutBoundaryFirstLift period hPeriod base) .increasing

theorem normalGraphCanonicalSecondSheetGaussGHYLedgerAction_eq
    (einsteinScale : Real)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter) :
    normalGraphCanonicalSecondSheetGaussGHYLedgerAction period hPeriod
        einsteinScale metric displacement parameter hNonNull =
      normalGraphCanonicalSecondSheetGaussGHYAction period hPeriod
        einsteinScale metric displacement parameter hNonNull := by
  unfold normalGraphCanonicalSecondSheetGaussGHYLedgerAction
    normalGraphCanonicalSecondSheetGaussGHYAction
    normalGraphCanonicalSecondSheetGaussGHYIntegrand
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun base =>
    normalGraphCanonicalGaussNonNullFaceDatum_curve_zero_eq_integrand
      period hPeriod einsteinScale metric displacement parameter hNonNull
        (canonicalLatitudeCutBoundarySecondLift period hPeriod base) .decreasing

/-- Genuine oriented action of the connected two-sheet cut boundary. -/
def normalGraphCanonicalTwoSheetGaussGHYAction
    (einsteinScale : Real)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter) :
    Real :=
  normalGraphCanonicalFirstSheetGaussGHYAction period hPeriod einsteinScale
      metric displacement parameter hNonNull +
    normalGraphCanonicalSecondSheetGaussGHYAction period hPeriod einsteinScale
      metric displacement parameter hNonNull

/-- Two-sheet mobile GHY action expressed entirely through the installed face
ledger. -/
def normalGraphCanonicalTwoSheetGaussGHYLedgerAction
    (einsteinScale : Real)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter) :
    Real :=
  normalGraphCanonicalFirstSheetGaussGHYLedgerAction period hPeriod
      einsteinScale metric displacement parameter hNonNull +
    normalGraphCanonicalSecondSheetGaussGHYLedgerAction period hPeriod
      einsteinScale metric displacement parameter hNonNull

theorem normalGraphCanonicalTwoSheetGaussGHYLedgerAction_eq
    (einsteinScale : Real)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter) :
    normalGraphCanonicalTwoSheetGaussGHYLedgerAction period hPeriod
        einsteinScale metric displacement parameter hNonNull =
      normalGraphCanonicalTwoSheetGaussGHYAction period hPeriod einsteinScale
        metric displacement parameter hNonNull := by
  rw [normalGraphCanonicalTwoSheetGaussGHYLedgerAction,
    normalGraphCanonicalTwoSheetGaussGHYAction,
    normalGraphCanonicalFirstSheetGaussGHYLedgerAction_eq,
    normalGraphCanonicalSecondSheetGaussGHYLedgerAction_eq]

theorem normalGraphCanonicalSecondSheetGaussGHYAction_eq_first
    (einsteinScale : Real)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter) :
    normalGraphCanonicalSecondSheetGaussGHYAction period hPeriod einsteinScale
        metric displacement parameter hNonNull =
      normalGraphCanonicalFirstSheetGaussGHYAction period hPeriod einsteinScale
        metric displacement parameter hNonNull := by
  unfold normalGraphCanonicalSecondSheetGaussGHYAction
    normalGraphCanonicalFirstSheetGaussGHYAction
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun base =>
    normalGraphCanonicalSecondSheetGaussGHYIntegrand_eq_first period hPeriod
      einsteinScale metric displacement parameter hNonNull base

theorem normalGraphCanonicalTwoSheetGaussGHYAction_eq_two_mul_first
    (einsteinScale : Real)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter) :
    normalGraphCanonicalTwoSheetGaussGHYAction period hPeriod einsteinScale
        metric displacement parameter hNonNull =
      2 * normalGraphCanonicalFirstSheetGaussGHYAction period hPeriod
        einsteinScale metric displacement parameter hNonNull := by
  rw [normalGraphCanonicalTwoSheetGaussGHYAction,
    normalGraphCanonicalSecondSheetGaussGHYAction_eq_first]
  ring

/-! ### Candidate-A promotion of the mobile two-sheet ledger -/

/-- The concrete mobile normal graph packaged in the sole continuum-ledger
constructor accepted by the central Candidate-A action. -/
def normalGraphCanonicalCandidateANonNullBoundaryDatum
    {NonNullFace : Type*} [Fintype NonNullFace]
    (einsteinScale : Real)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull :
      NormalGraphNonNullAt period hPeriod metric displacement parameter) :
    GlobalCandidateANonNullBoundaryDatum period hPeriod NonNullFace :=
  .canonicalLatitudeTwoSheet fun sheet base =>
    Fin.cases
      (normalGraphCanonicalGaussNonNullFaceDatum period hPeriod einsteinScale
        metric displacement parameter hNonNull
          (canonicalLatitudeCutBoundaryFirstLift period hPeriod base)
          .increasing)
      (fun _ =>
        normalGraphCanonicalGaussNonNullFaceDatum period hPeriod einsteinScale
          metric displacement parameter hNonNull
            (canonicalLatitudeCutBoundarySecondLift period hPeriod base)
            .decreasing)
      sheet

/-- Central evaluation of the mobile sourced datum is exactly the installed
two-sheet continuum ledger. -/
theorem globalCandidateANonNullBoundaryAction_normalGraph_eq_ledger
    {NonNullFace : Type*} [Fintype NonNullFace]
    (einsteinScale : Real)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull :
      NormalGraphNonNullAt period hPeriod metric displacement parameter) :
    globalCandidateANonNullBoundaryAction period hPeriod
        (normalGraphCanonicalCandidateANonNullBoundaryDatum period hPeriod
          (NonNullFace := NonNullFace) einsteinScale metric displacement
            parameter hNonNull) =
      normalGraphCanonicalTwoSheetGaussGHYLedgerAction period hPeriod
        einsteinScale metric displacement parameter hNonNull := by
  rw [normalGraphCanonicalCandidateANonNullBoundaryDatum,
    globalCandidateANonNullBoundaryAction_canonicalLatitudeTwoSheet,
    Fin.sum_univ_two]
  rfl

/-- Hence the datum promoted into Candidate A is the same physical mobile GHY
action already constructed above. -/
theorem globalCandidateANonNullBoundaryAction_normalGraph_eq
    {NonNullFace : Type*} [Fintype NonNullFace]
    (einsteinScale : Real)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull :
      NormalGraphNonNullAt period hPeriod metric displacement parameter) :
    globalCandidateANonNullBoundaryAction period hPeriod
        (normalGraphCanonicalCandidateANonNullBoundaryDatum period hPeriod
          (NonNullFace := NonNullFace) einsteinScale metric displacement
            parameter hNonNull) =
      normalGraphCanonicalTwoSheetGaussGHYAction period hPeriod einsteinScale
        metric displacement parameter hNonNull := by
  rw [globalCandidateANonNullBoundaryAction_normalGraph_eq_ledger,
    normalGraphCanonicalTwoSheetGaussGHYLedgerAction_eq]

/-! ### Local smooth representative of the chart-free Gauss contraction -/

/-- The fixed-chart Weingarten contraction near an admissible graph point.
It uses the same intrinsic inverse and second fundamental form as the global
Gauss ledger, but keeps one smooth chart germ instead of differentiating the
noncomputable global chart selection. -/
def normalGraphCanonicalHolonomicLocalMeanCurvatureFamily
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate ambient : HolonomicVector4)
    (current : EffectiveThroat period hPeriod × Real) : Real :=
  Matrix.trace
    (normalGraphInducedInverseMatrixFamily period hPeriod metric displacement
        base current *
      normalGraphHolonomicExtrinsicCurvatureMatrix period hPeriod metric
        displacement base patch coordinate ambient current)

/-- Each inverse-metric matrix coefficient is smooth at an admissible graph
point.  The proof evaluates the already smooth intrinsic inverse; no matrix
manifold or additional topology is introduced. -/
theorem normalGraphInducedInverseMatrixFamily_apply_contMDiffAt
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement base.2)
    (row column : Fin 3) :
    ContMDiffAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      𝓘(Real, Real) ∞
      (fun current => normalGraphInducedInverseMatrixFamily period hPeriod metric
        displacement base current row column) base := by
  have hVector :=
    (normalGraphInducedMetricInverseCoordinates_contMDiffAt period hPeriod
      metric displacement base hNonNull).clm_apply
        (contMDiffAt_const (c := throatContinuousDualBasis column))
  have hEntry :=
    (contMDiffAt_const (c := throatContinuousDualBasis row)).clm_apply hVector
  simp only [normalGraphInducedInverseMatrixFamily, LinearMap.toMatrix_apply,
    throatContinuousDualBasis, Basis.map_apply,
    LinearMap.coe_toContinuousLinearMap', Basis.dualBasis_apply] at hEntry ⊢
  apply hEntry.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun _ => rfl

/-- Each coefficient of the fixed-chart Weingarten matrix is smooth at the
canonical physical graph point. -/
theorem normalGraphHolonomicExtrinsicCurvatureMatrix_apply_contMDiffAt
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement base.2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate ambient : HolonomicVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraph period hPeriod displacement base.2 base.1)
    (hSquare : normalGraphHolonomicMetricNormalSquareCoordinates period hPeriod
      metric displacement base patch coordinate ambient base ≠ 0)
    (row column : Fin 3) :
    ContMDiffAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      𝓘(Real, Real) ∞
      (fun current => normalGraphHolonomicExtrinsicCurvatureMatrix period hPeriod
        metric displacement base patch coordinate ambient current row column)
      base := by
  unfold normalGraphHolonomicExtrinsicCurvatureMatrix
  exact normalGraphHolonomicExtrinsicCurvatureCoordinates_contMDiffAt period
    hPeriod metric displacement base hNonNull patch coordinate ambient hAt
      hSquare (throatCoordinateBasis row) (throatCoordinateBasis column)

/-- The fixed-chart mean-curvature contraction is jointly smooth at every
admissible canonical graph point. -/
theorem normalGraphHolonomicLocalMeanCurvatureFamily_contMDiffAt
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement base.2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate ambient : HolonomicVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraph period hPeriod displacement base.2 base.1)
    (hSquare : normalGraphHolonomicMetricNormalSquareCoordinates period hPeriod
      metric displacement base patch coordinate ambient base ≠ 0) :
    ContMDiffAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      𝓘(Real, Real) ∞
      (normalGraphCanonicalHolonomicLocalMeanCurvatureFamily period hPeriod
        metric displacement base patch coordinate ambient) base := by
  unfold normalGraphCanonicalHolonomicLocalMeanCurvatureFamily Matrix.trace
  apply ContMDiffAt.sum
  intro row _
  simp only [Matrix.diag_apply, Matrix.mul_apply]
  apply ContMDiffAt.sum
  intro column _
  exact
    (normalGraphInducedInverseMatrixFamily_apply_contMDiffAt period hPeriod
      metric displacement base hNonNull row column).mul
      (normalGraphHolonomicExtrinsicCurvatureMatrix_apply_contMDiffAt period
        hPeriod metric displacement base hNonNull patch coordinate ambient hAt
          hSquare column row)

/-- At its anchor the smooth Weingarten matrix is exactly the chartwise global
Gauss matrix. -/
theorem normalGraphCanonicalHolonomicWeingartenMatrix_base_eq_gauss
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : OrientationBoundary period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter)) :
    let base : EffectiveThroat period hPeriod × Real :=
      (orientationDoubleToThroat period hPeriod boundary, parameter)
    let ambient :=
      normalGraphCanonicalHolonomicMetricUnitNormalCoordinatesAt period hPeriod
        metric displacement parameter hNonNull boundary patch coordinate hAt
    normalGraphHolonomicExtrinsicCurvatureMatrix period hPeriod metric
        displacement base patch coordinate ambient base =
      normalGraphCanonicalHolonomicGaussExtrinsicCurvatureMatrixAt period hPeriod
        metric displacement parameter hNonNull boundary patch coordinate hAt := by
  dsimp only
  ext row column
  unfold normalGraphHolonomicExtrinsicCurvatureMatrix
    normalGraphHolonomicExtrinsicCurvatureCoordinates
    normalGraphCanonicalHolonomicGaussExtrinsicCurvatureMatrixAt
    normalGraphCanonicalHolonomicGaussExtrinsicCurvatureCoordinatesAt
  rw [normalGraphCanonicalHolonomicGaussRawExtrinsicCurvatureCoordinatesAt_eq_weingarten
      period hPeriod metric displacement parameter hNonNull boundary patch
        coordinate hAt (throatCoordinateBasis row)
          (throatCoordinateBasis column),
    normalGraphCanonicalHolonomicGaussRawExtrinsicCurvatureCoordinatesAt_eq_weingarten
      period hPeriod metric displacement parameter hNonNull boundary patch
        coordinate hAt (throatCoordinateBasis column)
          (throatCoordinateBasis row)]

/-- The smooth fixed-chart contraction agrees at its anchor with the global
chart-free Gauss mean curvature.  Thus the global value is represented without
differentiating the noncomputable atlas choice. -/
theorem normalGraphCanonicalHolonomicLocalMeanCurvatureFamily_base_eq_gauss
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : OrientationBoundary period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter)) :
    let base : EffectiveThroat period hPeriod × Real :=
      (orientationDoubleToThroat period hPeriod boundary, parameter)
    let ambient :=
      normalGraphCanonicalHolonomicMetricUnitNormalCoordinatesAt period hPeriod
        metric displacement parameter hNonNull boundary patch coordinate hAt
    normalGraphCanonicalHolonomicLocalMeanCurvatureFamily period hPeriod metric
        displacement base patch coordinate ambient base =
      normalGraphCanonicalGaussMeanCurvature period hPeriod metric displacement
        parameter hNonNull boundary := by
  dsimp only
  rw [normalGraphCanonicalHolonomicLocalMeanCurvatureFamily,
    normalGraphInducedInverseMatrixFamily_base,
    normalGraphCanonicalHolonomicWeingartenMatrix_base_eq_gauss]
  unfold normalGraphCanonicalGaussMeanCurvature
  exact normalGraphCanonicalHolonomicGaussMeanCurvatureAt_chart_independent
    period hPeriod metric displacement parameter hNonNull boundary patch
      (normalGraphCanonicalSelectedHolonomicPatchAt period hPeriod
        (normalGraphOrientationDouble period hPeriod displacement
          (boundary, parameter)))
      coordinate
      (normalGraphCanonicalSelectedHolonomicCoordinateAt period hPeriod
        (normalGraphOrientationDouble period hPeriod displacement
          (boundary, parameter)))
      hAt
      (normalGraphCanonicalSelectedHolonomicPatchAt_map period hPeriod
        (normalGraphOrientationDouble period hPeriod displacement
          (boundary, parameter)))

/-! ### Smooth Gauss representative pulled through the local orientation section -/

/-- The jointly smooth physical normal pulled back to the genuine throat by
the local inverse of the orientation-double projection. -/
def normalGraphCanonicalHolonomicLocalSectionNormalCoordinates
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (boundary : OrientationBoundary period hPeriod)
    (parameter : Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (current : EffectiveThroat period hPeriod × Real) : HolonomicVector4 :=
  normalGraphCanonicalHolonomicMetricUnitNormalJointCoordinates period hPeriod
    metric displacement (boundary, parameter) patch coordinate
      (normalGraphOrientationLocalSectionJoint period hPeriod boundary current)

theorem normalGraphCanonicalHolonomicLocalSectionNormalCoordinates_contMDiffAt
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : OrientationBoundary period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter)) :
    ContMDiffAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real HolonomicVector4) ∞
      (normalGraphCanonicalHolonomicLocalSectionNormalCoordinates period hPeriod
        metric displacement boundary parameter patch coordinate)
      (orientationDoubleToThroat period hPeriod boundary, parameter) := by
  have hJoint :=
    normalGraphCanonicalHolonomicMetricUnitNormalJointCoordinates_contMDiffAt
      period hPeriod metric displacement (boundary, parameter) hNonNull patch
        coordinate hAt
  have hComp := hJoint.comp_of_eq
    (normalGraphOrientationLocalSectionJoint_contMDiffAt period hPeriod boundary
      parameter)
    (normalGraphOrientationLocalSectionJoint_base period hPeriod boundary
      parameter)
  change ContMDiffAt
    (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
    (modelWithCornersSelf Real HolonomicVector4) ∞
    (normalGraphCanonicalHolonomicMetricUnitNormalJointCoordinates period
      hPeriod metric displacement (boundary, parameter) patch coordinate ∘
        normalGraphOrientationLocalSectionJoint period hPeriod boundary)
    (orientationDoubleToThroat period hPeriod boundary, parameter)
  exact hComp

theorem normalGraphCanonicalHolonomicLocalSectionNormalCoordinates_base_eq
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : OrientationBoundary period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter)) :
    normalGraphCanonicalHolonomicLocalSectionNormalCoordinates period hPeriod
        metric displacement boundary parameter patch coordinate
          (orientationDoubleToThroat period hPeriod boundary, parameter) =
      normalGraphCanonicalHolonomicMetricUnitNormalCoordinatesAt period hPeriod
        metric displacement parameter hNonNull boundary patch coordinate hAt := by
  unfold normalGraphCanonicalHolonomicLocalSectionNormalCoordinates
  rw [normalGraphOrientationLocalSectionJoint_base]
  exact normalGraphCanonicalHolonomicMetricUnitNormalJointCoordinates_base_eq
    period hPeriod metric displacement parameter hNonNull boundary patch
      coordinate hAt

/-- Two local inverses of the same local diffeomorphism agree as germs once
the second anchor lies in the target of the first inverse. -/
private theorem localDiffeomorphLocalInverse_eventuallyEq_of_mem_target
    {𝕜 E F H₁ H₂ M N : Type*}
    [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [TopologicalSpace H₁] [TopologicalSpace H₂]
    (I : ModelWithCorners 𝕜 E H₁)
    (J : ModelWithCorners 𝕜 F H₂)
    [TopologicalSpace M] [ChartedSpace H₁ M]
    [TopologicalSpace N] [ChartedSpace H₂ N]
    {n : ℕ∞ω} {f : M → N} {x x' : M}
    (hf : IsLocalDiffeomorphAt I J n f x)
    (hg : IsLocalDiffeomorphAt I J n f x')
    (hx' : x' ∈ hf.localInverse.target) :
    hf.localInverse =ᶠ[𝓝 (f x')] hg.localInverse := by
  have hxChoose : x' ∈ hf.choose.source := hx'
  have hForward : f x' = hf.choose x' := hf.choose_spec.2 hxChoose
  have hSource : f x' ∈ hf.localInverse.source := by
    rw [hForward]
    exact hf.localInverse.map_target hx'
  have hBase : hf.localInverse (f x') = x' :=
    hf.localInverse_left_inv hx'
  have hContinuous : ContinuousAt hf.localInverse (f x') :=
    hf.localInverse_contMDiffOn.contMDiffAt
      (hf.localInverse.open_source.mem_nhds hSource) |>.continuousAt
  rw [ContinuousAt, hBase] at hContinuous
  have hTarget : ∀ᶠ point in 𝓝 (f x'),
      hf.localInverse point ∈ hg.localInverse.target :=
    hContinuous.eventually
      (hg.localInverse.open_target.mem_nhds hg.localInverse_mem_target)
  have hRight : (f ∘ hf.localInverse) =ᶠ[𝓝 (f x')] id :=
    Filter.eventuallyEq_of_mem
      (hf.localInverse.open_source.mem_nhds hSource)
      hf.localInverse_eqOn_right
  filter_upwards [hTarget, hRight] with point hPoint hPointRight
  calc
    hf.localInverse point =
        hg.localInverse (f (hf.localInverse point)) :=
      (hg.localInverse_left_inv hPoint).symm
    _ = hg.localInverse point := congrArg hg.localInverse hPointRight

/-- Reanchoring the orientation local section inside its fixed target does
not change its germ. -/
theorem normalGraphOrientationLocalSection_eventuallyEq_reanchored
    (boundary : OrientationBoundary period hPeriod) :
    let base := orientationDoubleToThroat period hPeriod boundary
    ∀ᶠ point in 𝓝 base,
      normalGraphOrientationLocalSection period hPeriod boundary =ᶠ[𝓝 point]
        normalGraphOrientationLocalSection period hPeriod
          (normalGraphOrientationLocalSection period hPeriod boundary point) := by
  dsimp only
  let hFixed :=
    orientationDoubleToThroat_isLocalDiffeomorph period hPeriod boundary
  let localSection :=
    normalGraphOrientationLocalSection period hPeriod boundary
  have hContinuous : ContinuousAt localSection
      (orientationDoubleToThroat period hPeriod boundary) :=
    (normalGraphOrientationLocalSection_contMDiffAt period hPeriod boundary)
      |>.continuousAt
  change Tendsto localSection
    (𝓝 (orientationDoubleToThroat period hPeriod boundary))
    (𝓝 (localSection
      (orientationDoubleToThroat period hPeriod boundary))) at hContinuous
  have hLocalSectionBase : localSection
      (orientationDoubleToThroat period hPeriod boundary) = boundary := by
    exact normalGraphOrientationLocalSection_base period hPeriod boundary
  rw [hLocalSectionBase] at hContinuous
  have hTarget : ∀ᶠ point in
      𝓝 (orientationDoubleToThroat period hPeriod boundary),
      localSection point ∈ hFixed.localInverse.target :=
    hContinuous.eventually
      (hFixed.localInverse.open_target.mem_nhds
        hFixed.localInverse_mem_target)
  have hReconstruct :=
    normalGraphOrientationLocalSection_eventually_reconstructs period hPeriod
      boundary
  filter_upwards [hTarget, hReconstruct] with point hPoint hPointReconstruct
  let currentBoundary := localSection point
  let hCurrent :=
    orientationDoubleToThroat_isLocalDiffeomorph period hPeriod currentBoundary
  have hUnique :=
    localDiffeomorphLocalInverse_eventuallyEq_of_mem_target
      throatCoverModelWithCorners throatCoverModelWithCorners hFixed hCurrent
        hPoint
  change hFixed.localInverse =ᶠ[𝓝 point] hCurrent.localInverse
  have hCurrentPoint :
      orientationDoubleToThroat period hPeriod currentBoundary = point := by
    simpa [currentBoundary, localSection] using hPointReconstruct
  rw [hCurrentPoint] at hUnique
  exact hUnique

/-- The fixed holonomic inverse chart and the same chart reanchored at a
nearby graph coordinate define the same germ. -/
theorem normalGraphHolonomicLocalInverse_eventuallyEq_reanchored
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraph period hPeriod displacement base.2 base.1) :
    ∀ᶠ current in 𝓝 base,
      let currentCoordinate :=
        normalGraphHolonomicCoordinateGerm period hPeriod displacement base
          patch coordinate current
      (patch.coordinateMap_isLocalDiffeomorph coordinate).localInverse =ᶠ[
        𝓝 (normalGraph period hPeriod displacement current.2 current.1)]
        (patch.coordinateMap_isLocalDiffeomorph currentCoordinate).localInverse := by
  dsimp only
  let hFixed := patch.coordinateMap_isLocalDiffeomorph coordinate
  let coordinateGerm :=
    normalGraphHolonomicCoordinateGerm period hPeriod displacement base patch
      coordinate
  have hContinuous : ContinuousAt coordinateGerm base :=
    (normalGraphHolonomicCoordinateGerm_contMDiffAt period hPeriod displacement
      base patch coordinate hAt).continuousAt
  change Tendsto coordinateGerm (𝓝 base)
    (𝓝 (coordinateGerm base)) at hContinuous
  have hCoordinateBase : coordinateGerm base = coordinate := by
    exact normalGraphHolonomicCoordinateGerm_base period hPeriod displacement
      base patch coordinate hAt
  rw [hCoordinateBase] at hContinuous
  have hTarget : ∀ᶠ current in 𝓝 base,
      coordinateGerm current ∈ hFixed.localInverse.target :=
    hContinuous.eventually
      (hFixed.localInverse.open_target.mem_nhds hFixed.localInverse_mem_target)
  have hReconstruct :=
    normalGraphHolonomicCoordinateGerm_eventually_reconstructs period hPeriod
      displacement base patch coordinate hAt
  filter_upwards [hTarget, hReconstruct] with current hCurrentTarget hReconstructAt
  let currentCoordinate := coordinateGerm current
  let hCurrent := patch.coordinateMap_isLocalDiffeomorph currentCoordinate
  have hUnique :=
    localDiffeomorphLocalInverse_eventuallyEq_of_mem_target
      (modelWithCornersSelf Real HolonomicVector4) coverModelWithCorners hFixed
        hCurrent hCurrentTarget
  change hFixed.localInverse =ᶠ[
      𝓝 (normalGraph period hPeriod displacement current.2 current.1)]
    hCurrent.localInverse
  have hCurrentPoint : patch.coordinateMap currentCoordinate =
      normalGraph period hPeriod displacement current.2 current.1 := by
    simpa [currentCoordinate, coordinateGerm, Function.comp_def] using
      hReconstructAt
  rw [hCurrentPoint] at hUnique
  exact hUnique

/-- Reanchoring the holonomic inverse at a nearby graph point gives the same
coordinate germ on a neighborhood of that point. -/
theorem normalGraphHolonomicCoordinateGerm_eventuallyEq_reanchored
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraph period hPeriod displacement base.2 base.1) :
    ∀ᶠ current in nhds base,
      let currentCoordinate :=
        normalGraphHolonomicCoordinateGerm period hPeriod displacement base
          patch coordinate current
      normalGraphHolonomicCoordinateGerm period hPeriod displacement base patch
          coordinate =ᶠ[nhds current]
        normalGraphHolonomicCoordinateGerm period hPeriod displacement current
          patch currentCoordinate := by
  have hInverse :=
    normalGraphHolonomicLocalInverse_eventuallyEq_reanchored period hPeriod
      displacement base patch coordinate hAt
  filter_upwards [hInverse] with current hInverseAt
  dsimp only
  have hGraphTendsto : Tendsto
      (fun point : EffectiveThroat period hPeriod × Real =>
        normalGraph period hPeriod displacement point.2 point.1)
      (nhds current)
      (nhds (normalGraph period hPeriod displacement current.2 current.1)) :=
    (normalGraph_joint_contMDiff period hPeriod displacement).continuous
      |>.continuousAt
  change
    ((patch.coordinateMap_isLocalDiffeomorph coordinate).localInverse ∘
      fun point : EffectiveThroat period hPeriod × Real =>
        normalGraph period hPeriod displacement point.2 point.1) =ᶠ[nhds current]
    (((patch.coordinateMap_isLocalDiffeomorph
        (normalGraphHolonomicCoordinateGerm period hPeriod displacement base
          patch coordinate current)).localInverse) ∘
      fun point : EffectiveThroat period hPeriod × Real =>
        normalGraph period hPeriod displacement point.2 point.1)
  exact hInverseAt.comp_tendsto hGraphTendsto

set_option backward.isDefEq.respectTransparency false in
/-- Equal graph germs have source-coordinate differentials related by the
existing tangent transition. -/
theorem normalGraphHolonomicFamilyDerivativeCoordinates_natural_of_eventuallyEq
    (displacement : SmoothNormalDisplacement period hPeriod)
    (firstBase secondBase current : EffectiveThroat period hPeriod × Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate currentCoordinate : HolonomicVector4)
    (hFirst : current.1 ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) firstBase.1).baseSet)
    (hSecond : current.1 ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) secondBase.1).baseSet)
    (hGerm :
      normalGraphHolonomicCoordinateGerm period hPeriod displacement firstBase patch
          coordinate =ᶠ[nhds current]
        normalGraphHolonomicCoordinateGerm period hPeriod displacement secondBase
          patch currentCoordinate) :
    (normalGraphHolonomicFamilyDerivativeCoordinates period hPeriod displacement
        secondBase patch currentCoordinate current).comp
      (normalGraphThroatTangentCoordinateTransition period hPeriod firstBase.1
        secondBase.1 current.1 hFirst hSecond :
          ThroatCoverCoordinates →L[Real] ThroatCoverCoordinates) =
      normalGraphHolonomicFamilyDerivativeCoordinates period hPeriod displacement
        firstBase patch coordinate current := by
  apply ContinuousLinearMap.ext
  intro vector
  rw [ContinuousLinearMap.comp_apply]
  rw [normalGraphHolonomicFamilyDerivativeCoordinates_apply_eq_mfderiv period
      hPeriod displacement secondBase current patch currentCoordinate hSecond,
    normalGraphHolonomicFamilyDerivativeCoordinates_apply_eq_mfderiv period
      hPeriod displacement firstBase current patch coordinate hFirst]
  let tangentFirst :=
    (trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) firstBase.1)
      |>.continuousLinearEquivAt Real current.1 hFirst
  let tangentSecond :=
    (trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) secondBase.1)
      |>.continuousLinearEquivAt Real current.1 hSecond
  have hInput :
      (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) secondBase.1).symm current.1
          (normalGraphThroatTangentCoordinateTransition period hPeriod
            firstBase.1 secondBase.1 current.1 hFirst hSecond vector) =
        (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) firstBase.1).symm current.1 vector := by
    change tangentSecond.symm (tangentSecond (tangentFirst.symm vector)) = _
    exact tangentSecond.symm_apply_apply _
  erw [hInput]
  have hSection : Tendsto
      (fun point : EffectiveThroat period hPeriod => (point, current.2))
      (nhds current.1) (nhds current) := by
    have h : Tendsto
        (fun point : EffectiveThroat period hPeriod => (point, current.2))
        (nhds current.1) (nhds (current.1, current.2)) :=
      (continuous_id.prodMk continuous_const).continuousAt
    simpa only [Prod.eta current] using h
  have hSlice := hGerm.comp_tendsto hSection
  have hDerivative := Filter.EventuallyEq.mfderiv_eq
    (I := throatCoverModelWithCorners)
    (I' := modelWithCornersSelf Real HolonomicVector4) hSlice
  exact congrArg (fun derivative => derivative
    ((trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) firstBase.1).symm current.1 vector))
    hDerivative.symm

/-- The fixed physical normal representative and the representative obtained
by reanchoring both local inverses at a nearby graph point are the same germ.
All admissibility data come from the existing open non-null domain and fixed
bundle trivializations. -/
theorem normalGraphCanonicalHolonomicLocalSectionNormalCoordinates_eventuallyEq_reanchored
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : OrientationBoundary period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter)) :
    let base : EffectiveThroat period hPeriod × Real :=
      (orientationDoubleToThroat period hPeriod boundary, parameter)
    ∀ᶠ current in 𝓝 base,
      let currentBoundary :=
        normalGraphOrientationLocalSection period hPeriod boundary current.1
      let currentCoordinate :=
        normalGraphHolonomicCoordinateGerm period hPeriod displacement base
          patch coordinate current
      normalGraphCanonicalHolonomicLocalSectionNormalCoordinates period hPeriod
          metric displacement boundary parameter patch coordinate =ᶠ[𝓝 current]
        normalGraphCanonicalHolonomicLocalSectionNormalCoordinates period hPeriod
          metric displacement currentBoundary current.2 patch currentCoordinate := by
  dsimp only
  let base : EffectiveThroat period hPeriod × Real :=
    (orientationDoubleToThroat period hPeriod boundary, parameter)
  let orientationBase : OrientationBoundary period hPeriod × Real :=
    (boundary, parameter)
  let fixedLift :=
    normalGraphOrientationLocalSectionJoint period hPeriod boundary
  have hLiftTendsto : Tendsto fixedLift (𝓝 base) (𝓝 orientationBase) := by
    have hLift :=
      (normalGraphOrientationLocalSectionJoint_contMDiffAt period hPeriod
        boundary parameter).continuousAt
    change Tendsto fixedLift (𝓝 base) (𝓝 (fixedLift base)) at hLift
    have hLiftBase : fixedLift base = orientationBase := by
      simpa [fixedLift, base, orientationBase] using
        (normalGraphOrientationLocalSectionJoint_base period hPeriod boundary
          parameter)
    rw [hLiftBase] at hLift
    exact hLift
  have hFixedAdmissible : ∀ᶠ current in 𝓝 base,
      NormalGraphCanonicalJointCoordinateAdmissible period hPeriod metric
        displacement orientationBase (fixedLift current) :=
    hLiftTendsto.eventually
      (normalGraphCanonicalJointCoordinateAdmissible_eventually period hPeriod
        metric displacement orientationBase hNonNull)
  have hFixedAdmissibleLocal := eventually_local hFixedAdmissible
  have hNonNullCurrent : ∀ᶠ current in 𝓝 base,
      current.2 ∈ normalGraphNonNullDomain period hPeriod metric displacement :=
    continuous_snd.continuousAt.eventually
      ((normalGraphNonNullDomain_isOpen period hPeriod metric displacement)
        |>.mem_nhds hNonNull)
  have hFstTendsto : Tendsto Prod.fst (𝓝 base) (𝓝 base.1) :=
    continuous_fst.continuousAt
  have hSectionReanchor :=
    hFstTendsto.eventually
      (normalGraphOrientationLocalSection_eventuallyEq_reanchored period hPeriod
        boundary)
  have hSectionReconstruct :
      (fun current : EffectiveThroat period hPeriod × Real =>
        orientationDoubleToThroat period hPeriod
          (normalGraphOrientationLocalSection period hPeriod boundary current.1))
        =ᶠ[𝓝 base] Prod.fst := by
    change ((fun point => orientationDoubleToThroat period hPeriod
      (normalGraphOrientationLocalSection period hPeriod boundary point)) ∘
        Prod.fst) =ᶠ[𝓝 base] Prod.fst
    exact (normalGraphOrientationLocalSection_eventually_reconstructs period
      hPeriod boundary).comp_tendsto hFstTendsto
  have hSectionReconstructLocal :=
    eventually_local_eventuallyEq hSectionReconstruct
  have hGraph : patch.coordinateMap coordinate =
      normalGraph period hPeriod displacement base.2 base.1 := by
    simpa [base, normalGraphOrientationDouble] using hAt
  have hInverseReanchor :=
    normalGraphHolonomicLocalInverse_eventuallyEq_reanchored period hPeriod
      displacement base patch coordinate hGraph
  filter_upwards [hFixedAdmissibleLocal, hNonNullCurrent, hSectionReanchor,
    hSectionReconstruct, hSectionReconstructLocal, hInverseReanchor] with
    current hFixedAdmissibleAt hCurrentNonNull hSectionReanchorAt
      hSectionReconstructAt hSectionReconstructAtLocal hInverseReanchorAt
  let currentBoundary :=
    normalGraphOrientationLocalSection period hPeriod boundary current.1
  let currentCoordinate :=
    normalGraphHolonomicCoordinateGerm period hPeriod displacement base patch
      coordinate current
  let currentOrientationBase : OrientationBoundary period hPeriod × Real :=
    (currentBoundary, current.2)
  let currentLift :=
    normalGraphOrientationLocalSectionJoint period hPeriod currentBoundary
  have hCurrentProjection :
      orientationDoubleToThroat period hPeriod currentBoundary = current.1 := by
    simpa [currentBoundary] using hSectionReconstructAt
  have hCurrentLiftTendsto : Tendsto currentLift (𝓝 current)
      (𝓝 currentOrientationBase) := by
    have hLift :=
      (normalGraphOrientationLocalSectionJoint_contMDiffAt period hPeriod
        currentBoundary current.2).continuousAt
    change Tendsto currentLift
      (𝓝 (orientationDoubleToThroat period hPeriod currentBoundary,
        current.2)) (𝓝 (currentLift
          (orientationDoubleToThroat period hPeriod currentBoundary,
            current.2))) at hLift
    have hLiftBase : currentLift
        (orientationDoubleToThroat period hPeriod currentBoundary, current.2) =
      currentOrientationBase := by
      simpa [currentLift, currentOrientationBase] using
        (normalGraphOrientationLocalSectionJoint_base period hPeriod
          currentBoundary current.2)
    have hAnchor :
        (orientationDoubleToThroat period hPeriod currentBoundary, current.2) =
          current := by
      exact Prod.ext hCurrentProjection rfl
    rw [hAnchor] at hLift hLiftBase
    rw [hLiftBase] at hLift
    exact hLift
  have hCurrentAdmissible : ∀ᶠ point in 𝓝 current,
      NormalGraphCanonicalJointCoordinateAdmissible period hPeriod metric
        displacement currentOrientationBase (currentLift point) :=
    hCurrentLiftTendsto.eventually
      (normalGraphCanonicalJointCoordinateAdmissible_eventually period hPeriod
        metric displacement currentOrientationBase hCurrentNonNull)
  have hLiftEq : fixedLift =ᶠ[𝓝 current] currentLift := by
    have hSection := hSectionReanchorAt.comp_tendsto
      (show Tendsto Prod.fst (𝓝 current) (𝓝 current.1) from
        continuous_fst.continuousAt)
    filter_upwards [hSection] with point hPoint
    change
      (normalGraphOrientationLocalSection period hPeriod boundary point.1,
        point.2) =
      (normalGraphOrientationLocalSection period hPeriod currentBoundary point.1,
        point.2)
    simpa [currentBoundary, Function.comp_def] using
      congrArg (fun value => (value, point.2)) hPoint
  have hGraphTendsto : Tendsto
      (fun point : EffectiveThroat period hPeriod × Real =>
        normalGraph period hPeriod displacement point.2 point.1)
      (𝓝 current)
      (𝓝 (normalGraph period hPeriod displacement current.2 current.1)) :=
    (normalGraph_joint_contMDiff period hPeriod displacement).continuous
      |>.continuousAt
  have hInverseLocal := eventually_local_eventuallyEq hInverseReanchorAt
  have hInverseAlongGraph := hGraphTendsto.eventually hInverseLocal
  filter_upwards [hFixedAdmissibleAt, hCurrentAdmissible, hLiftEq,
    hSectionReconstructAtLocal, hInverseAlongGraph] with point hFixed hCurrent
      hLift hReconstruct hInverse
  rcases hFixed with
    ⟨hFixedNonNull, hFixedTangent, hFixedCotangent, hFixedImage⟩
  rw [← hLift] at hCurrent
  rcases hCurrent with
    ⟨hReanchoredNonNull, hReanchoredTangent, hReanchoredCotangent,
      hReanchoredImage⟩
  have hFixedIntrinsic :=
    normalGraphCanonicalHolonomicMetricUnitNormalJointCoordinates_eq_intrinsic
      period hPeriod metric displacement orientationBase (fixedLift point)
        hFixedNonNull hFixedTangent hFixedCotangent hFixedImage patch coordinate
  have hCurrentIntrinsic :=
    normalGraphCanonicalHolonomicMetricUnitNormalJointCoordinates_eq_intrinsic
      period hPeriod metric displacement currentOrientationBase
        (fixedLift point) hReanchoredNonNull hReanchoredTangent
          hReanchoredCotangent hReanchoredImage patch currentCoordinate
  change
    normalGraphCanonicalHolonomicMetricUnitNormalJointCoordinates period
        hPeriod metric displacement orientationBase patch coordinate
          (fixedLift point) =
      normalGraphCanonicalHolonomicMetricUnitNormalJointCoordinates period
        hPeriod metric displacement currentOrientationBase patch
          currentCoordinate (currentLift point)
  rw [← hLift]
  rw [hFixedIntrinsic, hCurrentIntrinsic]
  have hNonNullProof : hReanchoredNonNull = hFixedNonNull :=
    Subsingleton.elim _ _
  rw [hNonNullProof]
  have hGraphPoint :
      normalGraphOrientationDouble period hPeriod displacement (fixedLift point) =
        normalGraph period hPeriod displacement point.2 point.1 := by
    change normalGraph period hPeriod displacement point.2
        (orientationDoubleToThroat period hPeriod
          (normalGraphOrientationLocalSection period hPeriod boundary point.1)) =
      normalGraph period hPeriod displacement point.2 point.1
    exact congrArg (normalGraph period hPeriod displacement point.2) hReconstruct
  rw [hGraphPoint]
  have hDerivative := Filter.EventuallyEq.mfderiv_eq
    (I := coverModelWithCorners)
    (I' := modelWithCornersSelf Real HolonomicVector4) hInverse
  exact congrArg (fun derivative => derivative
    (normalGraphCanonicalMetricUnitNormal period hPeriod metric displacement
      point.2 hFixedNonNull (fixedLift point).1)) hDerivative

set_option backward.isDefEq.respectTransparency false in
private def normalBoundaryTangentSpaceModelCoordinates
    {E H M : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E]
    [TopologicalSpace H]
    (I : ModelWithCorners Real E H)
    [TopologicalSpace M] [ChartedSpace H M]
    (point : M) : TangentSpace I point ≃L[Real] E where
  toFun vector := vector
  invFun vector := vector
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

set_option backward.isDefEq.respectTransparency false in
/-- On the fixed inverse-chart neighborhood, the differential of the chart
is a right inverse to the differential of that same inverse germ. -/
theorem normalGraphHolonomicLocalInverseDerivative_eventually_rightInverse
    (displacement : SmoothNormalDisplacement period hPeriod)
    (base : EffectiveThroat period hPeriod × Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraph period hPeriod displacement base.2 base.1) :
    ∀ᶠ current in 𝓝 base, ∀ vector : CoverCoordinates,
      normalBoundaryTangentSpaceModelCoordinates coverModelWithCorners
        (patch.coordinateMap
          (normalGraphHolonomicCoordinateGerm period hPeriod displacement base
            patch coordinate current))
        (mfderiv (modelWithCornersSelf Real HolonomicVector4)
            coverModelWithCorners patch.coordinateMap
            (normalGraphHolonomicCoordinateGerm period hPeriod displacement base
              patch coordinate current)
            (mfderiv coverModelWithCorners
              (modelWithCornersSelf Real HolonomicVector4)
              (patch.coordinateMap_isLocalDiffeomorph coordinate).localInverse
              (normalGraph period hPeriod displacement current.2 current.1)
              vector)) = vector := by
  let localDiffeomorph :=
    patch.coordinateMap_isLocalDiffeomorph coordinate
  have hGraphBase : normalGraph period hPeriod displacement base.2 base.1 ∈
      localDiffeomorph.localInverse.source := by
    rw [← hAt]
    exact localDiffeomorph.localInverse_mem_source
  have hGraphEventually : ∀ᶠ current in 𝓝 base,
      normalGraph period hPeriod displacement current.2 current.1 ∈
        localDiffeomorph.localInverse.source :=
    (normalGraph_joint_contMDiff period hPeriod displacement).continuous
      |>.continuousAt
        (localDiffeomorph.localInverse.open_source.mem_nhds hGraphBase)
  have hRightLocal := eventually_local_eventuallyEq
    localDiffeomorph.localInverse_eventuallyEq_right
  have hGraphTendsto : Tendsto
      (fun current : EffectiveThroat period hPeriod × Real =>
        normalGraph period hPeriod displacement current.2 current.1)
      (𝓝 base) (𝓝 (patch.coordinateMap coordinate)) := by
    rw [hAt]
    exact (normalGraph_joint_contMDiff period hPeriod displacement).continuous
      |>.continuousAt
  have hRightEventually : ∀ᶠ current in 𝓝 base,
      (patch.coordinateMap ∘ localDiffeomorph.localInverse) =ᶠ[
        𝓝 (normalGraph period hPeriod displacement current.2 current.1)] id :=
    hGraphTendsto.eventually hRightLocal
  filter_upwards [hGraphEventually, hRightEventually] with current hGraph hRight
  intro vector
  let graphPoint :=
    normalGraph period hPeriod displacement current.2 current.1
  have hInverse : ContMDiffAt coverModelWithCorners
      (modelWithCornersSelf Real HolonomicVector4) ∞
      localDiffeomorph.localInverse graphPoint :=
    localDiffeomorph.localInverse_contMDiffOn.contMDiffAt
      (localDiffeomorph.localInverse.open_source.mem_nhds hGraph)
  have hChain := mfderiv_comp_apply graphPoint
    (patch.coordinateMap_contMDiff.mdifferentiable (by simp)
      (localDiffeomorph.localInverse graphPoint))
    (hInverse.mdifferentiableAt (by simp)) vector
  change normalBoundaryTangentSpaceModelCoordinates coverModelWithCorners
      (patch.coordinateMap (localDiffeomorph.localInverse graphPoint))
      (mfderiv (modelWithCornersSelf Real HolonomicVector4)
        coverModelWithCorners patch.coordinateMap
          (localDiffeomorph.localInverse graphPoint)
          (mfderiv coverModelWithCorners
            (modelWithCornersSelf Real HolonomicVector4)
            localDiffeomorph.localInverse graphPoint vector)) = vector
  rw [← hChain]
  have hDerivative := Filter.EventuallyEq.mfderiv_eq
    (I := coverModelWithCorners) (I' := coverModelWithCorners) hRight
  have hApply := congrArg (fun derivative =>
    normalBoundaryTangentSpaceModelCoordinates coverModelWithCorners graphPoint
      (derivative vector)) hDerivative
  have hId :
      normalBoundaryTangentSpaceModelCoordinates coverModelWithCorners graphPoint
          ((ContinuousLinearMap.id Real
            (TangentSpace coverModelWithCorners graphPoint)) vector) = vector := by
    rfl
  rw [mfderiv_id] at hApply
  exact hApply.trans hId

set_option backward.isDefEq.respectTransparency false in
/-- The local-section representative is orthogonal, on one genuine joint
neighborhood, to the differential of the same moving graph. -/
theorem normalGraphCanonicalHolonomicLocalSectionNormalCoordinates_eventually_orthogonal
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : OrientationBoundary period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter))
    (tangent : ThroatCoverCoordinates) :
    let base : EffectiveThroat period hPeriod × Real :=
      (orientationDoubleToThroat period hPeriod boundary, parameter)
    (fun current => localMetricCoordinateForm period hPeriod metric patch
      (normalGraphHolonomicCoordinateGerm period hPeriod displacement base patch
        coordinate current)
      (normalGraphCanonicalHolonomicLocalSectionNormalCoordinates period hPeriod
        metric displacement boundary parameter patch coordinate current)
      (normalGraphHolonomicFamilyDerivativeCoordinates period hPeriod displacement
        base patch coordinate current tangent)) =ᶠ[nhds base] fun _ => 0 := by
  dsimp only
  let base : EffectiveThroat period hPeriod × Real :=
    (orientationDoubleToThroat period hPeriod boundary, parameter)
  let lifted := normalGraphOrientationLocalSectionJoint period hPeriod boundary
  have hGraph : patch.coordinateMap coordinate =
      normalGraph period hPeriod displacement base.2 base.1 := by
    simpa [base, normalGraphOrientationDouble] using hAt
  have hLiftTendsto : Tendsto lifted (nhds base) (nhds (boundary, parameter)) :=
    by
      have hLift :=
        (normalGraphOrientationLocalSectionJoint_contMDiffAt period hPeriod
          boundary parameter).continuousAt
      change Tendsto lifted (nhds base) (nhds (lifted base)) at hLift
      have hLiftBase : lifted base = (boundary, parameter) := by
        simpa [lifted, base] using
          (normalGraphOrientationLocalSectionJoint_base period hPeriod boundary
            parameter)
      rw [hLiftBase] at hLift
      exact hLift
  have hAdmissible := hLiftTendsto.eventually
    (normalGraphCanonicalJointCoordinateAdmissible_eventually period hPeriod
      metric displacement (boundary, parameter) hNonNull)
  have hFstTendsto : Tendsto Prod.fst (nhds base) (nhds base.1) :=
    continuous_fst.continuousAt
  have hSection :
      (fun current : EffectiveThroat period hPeriod × Real =>
        orientationDoubleToThroat period hPeriod
          (normalGraphOrientationLocalSection period hPeriod boundary current.1))
        =ᶠ[nhds base] Prod.fst := by
    change ((fun point => orientationDoubleToThroat period hPeriod
      (normalGraphOrientationLocalSection period hPeriod boundary point)) ∘
        Prod.fst) =ᶠ[nhds base] Prod.fst
    exact (normalGraphOrientationLocalSection_eventually_reconstructs period
      hPeriod boundary).comp_tendsto hFstTendsto
  have hCoordinate :=
    normalGraphHolonomicCoordinateGerm_eventually_reconstructs period hPeriod
      displacement base patch coordinate hGraph
  have hDerivative :=
    normalGraphHolonomicFamilyDerivativeCoordinates_eventually_reconstructs
      period hPeriod displacement base patch coordinate hGraph
  have hRight :=
    normalGraphHolonomicLocalInverseDerivative_eventually_rightInverse period
      hPeriod displacement base patch coordinate hGraph
  filter_upwards [hAdmissible, hSection, hCoordinate, hDerivative, hRight] with
    current hCurrentAdmissible hSectionCurrent hCoordinateCurrent
      hDerivativeCurrent hRightCurrent
  rcases hCurrentAdmissible with
    ⟨hCurrent, hTangent, hCotangent, hImage⟩
  let liftedCurrent := lifted current
  have hGraphPoint :
      normalGraphOrientationDouble period hPeriod displacement liftedCurrent =
        normalGraph period hPeriod displacement current.2 current.1 := by
    change normalGraph period hPeriod displacement current.2
        (orientationDoubleToThroat period hPeriod
          (normalGraphOrientationLocalSection period hPeriod boundary current.1)) =
      normalGraph period hPeriod displacement current.2 current.1
    exact congrArg (normalGraph period hPeriod displacement current.2)
      hSectionCurrent
  have hIntrinsic :=
    normalGraphCanonicalHolonomicMetricUnitNormalJointCoordinates_eq_intrinsic
      period hPeriod metric displacement (boundary, parameter) liftedCurrent
        hCurrent hTangent hCotangent hImage patch coordinate
  rw [hGraphPoint] at hIntrinsic
  let intrinsicNormal :=
    normalGraphCanonicalMetricUnitNormal period hPeriod metric displacement
      liftedCurrent.2 hCurrent liftedCurrent.1
  have hIntrinsic' :
      normalGraphCanonicalHolonomicLocalSectionNormalCoordinates period hPeriod
          metric displacement boundary parameter patch coordinate current =
        mfderiv coverModelWithCorners
          (modelWithCornersSelf Real HolonomicVector4)
          (patch.coordinateMap_isLocalDiffeomorph coordinate).localInverse
          (normalGraph period hPeriod displacement current.2 current.1)
          intrinsicNormal := by
    simpa [intrinsicNormal, liftedCurrent, lifted,
      normalGraphCanonicalHolonomicLocalSectionNormalCoordinates] using hIntrinsic
  have hNormalModel := hRightCurrent intrinsicNormal
  have hNormal : HEq
      (mfderiv (modelWithCornersSelf Real HolonomicVector4) coverModelWithCorners
        patch.coordinateMap
        (normalGraphHolonomicCoordinateGerm period hPeriod displacement base
          patch coordinate current)
        (normalGraphCanonicalHolonomicLocalSectionNormalCoordinates period
          hPeriod metric displacement boundary parameter patch coordinate current))
      intrinsicNormal := by
    rw [hIntrinsic']
    exact hNormalModel.heq
  let sourceTangent : ThroatTangentFiber period hPeriod current.1 :=
    (trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) base.1).symm current.1 tangent
  let intrinsicTangent :=
    mfderiv throatCoverModelWithCorners coverModelWithCorners
      (normalGraph period hPeriod displacement current.2) current.1 sourceTangent
  have hCoordinateTangent : HEq
      (mfderiv (modelWithCornersSelf Real HolonomicVector4) coverModelWithCorners
        patch.coordinateMap
        (normalGraphHolonomicCoordinateGerm period hPeriod displacement base
          patch coordinate current)
        (normalGraphHolonomicFamilyDerivativeCoordinates period hPeriod
          displacement base patch coordinate current tangent))
      intrinsicTangent := by
    exact (hDerivativeCurrent tangent).heq
  have hMetric := normalGraphDependentBilinApply_heq
    (fun point first second => metric.tensor.tensor point first second)
    hCoordinateCurrent hNormal hCoordinateTangent
  rw [localMetricCoordinateForm_apply]
  change metric.tensor.tensor
      (patch.coordinateMap
        (normalGraphHolonomicCoordinateGerm period hPeriod displacement base
          patch coordinate current))
      (mfderiv (modelWithCornersSelf Real HolonomicVector4) coverModelWithCorners
        patch.coordinateMap
        (normalGraphHolonomicCoordinateGerm period hPeriod displacement base
          patch coordinate current)
        (normalGraphCanonicalHolonomicLocalSectionNormalCoordinates period
          hPeriod metric displacement boundary parameter patch coordinate current))
      (mfderiv (modelWithCornersSelf Real HolonomicVector4) coverModelWithCorners
        patch.coordinateMap
        (normalGraphHolonomicCoordinateGerm period hPeriod displacement base
          patch coordinate current)
        (normalGraphHolonomicFamilyDerivativeCoordinates period hPeriod
          displacement base patch coordinate current tangent)) = 0
  rw [eq_of_heq hMetric]
  let physicalTangent : ThroatTangentFiber period hPeriod
      (orientationDoubleToThroat period hPeriod liftedCurrent.1) :=
    hSectionCurrent.symm ▸ sourceTangent
  have hPhysical := normalGraphCanonicalMetricUnitNormal_orthogonal period hPeriod
    metric displacement current.2 hCurrent liftedCurrent.1 physicalTangent
  have hThroatPoint :
      orientationDoubleToThroat period hPeriod liftedCurrent.1 = current.1 := by
    simpa [liftedCurrent, lifted, normalGraphOrientationLocalSectionJoint] using
      hSectionCurrent
  unfold normalGraphOrientationDouble at hPhysical
  rw [hThroatPoint] at hPhysical
  simpa [intrinsicNormal, intrinsicTangent, sourceTangent, physicalTangent,
    liftedCurrent, lifted, normalGraphOrientationLocalSectionJoint] using
      hPhysical

/-- Spatial derivative of that same physical local-section normal, retained
jointly in throat point and graph parameter. -/
def normalGraphCanonicalHolonomicLocalSectionNormalDerivativeCoordinates
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (boundary : OrientationBoundary period hPeriod)
    (parameter : Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (current : EffectiveThroat period hPeriod × Real) :
    ThroatCoverCoordinates →L[Real] HolonomicVector4 :=
  let representative :=
    normalGraphCanonicalHolonomicLocalSectionNormalCoordinates period hPeriod
      metric displacement boundary parameter patch coordinate
  inTangentCoordinates throatCoverModelWithCorners
    (modelWithCornersSelf Real HolonomicVector4)
    Prod.fst representative
    (fun point => mfderiv throatCoverModelWithCorners
      (modelWithCornersSelf Real HolonomicVector4)
      (fun throatPoint => representative (throatPoint, point.2)) point.1)
    (orientationDoubleToThroat period hPeriod boundary, parameter) current

theorem normalGraphCanonicalHolonomicLocalSectionNormalDerivativeCoordinates_contMDiffAt
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : OrientationBoundary period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter)) :
    ContMDiffAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real
        (ThroatCoverCoordinates →L[Real] HolonomicVector4)) ∞
      (normalGraphCanonicalHolonomicLocalSectionNormalDerivativeCoordinates
        period hPeriod metric displacement boundary parameter patch coordinate)
      (orientationDoubleToThroat period hPeriod boundary, parameter) := by
  let base : EffectiveThroat period hPeriod × Real :=
    (orientationDoubleToThroat period hPeriod boundary, parameter)
  let representative :=
    normalGraphCanonicalHolonomicLocalSectionNormalCoordinates period hPeriod
      metric displacement boundary parameter patch coordinate
  let f : (EffectiveThroat period hPeriod × Real) →
      EffectiveThroat period hPeriod → HolonomicVector4 :=
    fun parameterPoint point => representative (point, parameterPoint.2)
  let g : (EffectiveThroat period hPeriod × Real) →
      EffectiveThroat period hPeriod := Prod.fst
  have hRepresentative : ContMDiffAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real HolonomicVector4) ∞ representative base := by
    simpa [base, representative] using
      (normalGraphCanonicalHolonomicLocalSectionNormalCoordinates_contMDiffAt
        period hPeriod metric displacement parameter hNonNull boundary patch
          coordinate hAt)
  have hReorder : ContMDiffAt
      ((throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real)).prod
        throatCoverModelWithCorners)
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real)) ∞
      (fun point : (EffectiveThroat period hPeriod × Real) ×
          EffectiveThroat period hPeriod => (point.2, point.1.2))
      (base, base.1) :=
    (contMDiff_snd.prodMk (contMDiff_snd.comp contMDiff_fst)).contMDiffAt
  have hg : ContMDiffAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      throatCoverModelWithCorners ∞ g base := by
    simpa [g] using
      (contMDiff_fst : ContMDiff
        (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
        throatCoverModelWithCorners ∞
        (Prod.fst : EffectiveThroat period hPeriod × Real →
          EffectiveThroat period hPeriod)).contMDiffAt
  have hJoint : ContMDiffAt
      ((throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real)).prod
        throatCoverModelWithCorners)
      (modelWithCornersSelf Real HolonomicVector4) ∞
      (fun point : (EffectiveThroat period hPeriod × Real) ×
          EffectiveThroat period hPeriod => representative (point.2, point.1.2))
      (base, base.1) :=
    ContMDiffAt.comp
      (f := fun point : (EffectiveThroat period hPeriod × Real) ×
        EffectiveThroat period hPeriod => (point.2, point.1.2))
      (g := representative) (base, base.1) hRepresentative hReorder
  change ContMDiffAt
    (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
    (modelWithCornersSelf Real
      (ThroatCoverCoordinates →L[Real] HolonomicVector4)) ∞
    (inTangentCoordinates throatCoverModelWithCorners
      (modelWithCornersSelf Real HolonomicVector4) g representative
      (fun point => mfderiv throatCoverModelWithCorners
        (modelWithCornersSelf Real HolonomicVector4) (f point) (g point))
      base) base
  exact hJoint.mfderiv f g hg (by simp)

/-- At the anchor, the stored local-section derivative is the genuine spatial
manifold derivative of the same physical normal representative. -/
theorem normalGraphCanonicalHolonomicLocalSectionNormalDerivativeCoordinates_apply_base_eq_mfderiv
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (boundary : OrientationBoundary period hPeriod)
    (parameter : Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (vector : ThroatCoverCoordinates) :
    let base : EffectiveThroat period hPeriod × Real :=
      (orientationDoubleToThroat period hPeriod boundary, parameter)
    normalGraphCanonicalHolonomicLocalSectionNormalDerivativeCoordinates period
        hPeriod metric displacement boundary parameter patch coordinate base
          vector =
      mfderiv throatCoverModelWithCorners
        (modelWithCornersSelf Real HolonomicVector4)
        (fun point =>
          normalGraphCanonicalHolonomicLocalSectionNormalCoordinates period
            hPeriod metric displacement boundary parameter patch coordinate
              (point, parameter)) base.1
        ((trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) base.1).symm base.1 vector) := by
  dsimp only
  let base : EffectiveThroat period hPeriod × Real :=
    (orientationDoubleToThroat period hPeriod boundary, parameter)
  let representative :=
    normalGraphCanonicalHolonomicLocalSectionNormalCoordinates period hPeriod
      metric displacement boundary parameter patch coordinate
  have hThroat : base.1 ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) base.1).baseSet :=
    mem_baseSet_trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) base.1
  have hTarget : representative base ∈
      (trivializationAt HolonomicVector4
        (fun point : HolonomicVector4 =>
          TangentSpace (modelWithCornersSelf Real HolonomicVector4) point)
        (representative base)).baseSet :=
    mem_baseSet_trivializationAt HolonomicVector4
      (fun point : HolonomicVector4 =>
        TangentSpace (modelWithCornersSelf Real HolonomicVector4) point)
      (representative base)
  rw [show normalGraphCanonicalHolonomicLocalSectionNormalDerivativeCoordinates
      period hPeriod metric displacement boundary parameter patch coordinate
        base =
    ContinuousLinearMap.inCoordinates ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) HolonomicVector4
      (fun point : HolonomicVector4 =>
        TangentSpace (modelWithCornersSelf Real HolonomicVector4) point)
      base.1 base.1 (representative base) (representative base)
      (mfderiv throatCoverModelWithCorners
        (modelWithCornersSelf Real HolonomicVector4)
        (fun point => representative (point, base.2)) base.1) by rfl]
  rw [ContinuousLinearMap.inCoordinates_eq hThroat hTarget]
  simp [base, representative]

/-- Evaluation of the stored local-section normal differential at an
arbitrary point of the fixed source trivialization. -/
theorem normalGraphCanonicalHolonomicLocalSectionNormalDerivativeCoordinates_apply_eq_mfderiv
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (boundary : OrientationBoundary period hPeriod)
    (parameter : Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (current : EffectiveThroat period hPeriod × Real)
    (hCurrent : current.1 ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod)
          (orientationDoubleToThroat period hPeriod boundary)).baseSet)
    (vector : ThroatCoverCoordinates) :
    normalGraphCanonicalHolonomicLocalSectionNormalDerivativeCoordinates period
        hPeriod metric displacement boundary parameter patch coordinate current
          vector =
      mfderiv throatCoverModelWithCorners
        (modelWithCornersSelf Real HolonomicVector4)
        (fun point =>
          normalGraphCanonicalHolonomicLocalSectionNormalCoordinates period
            hPeriod metric displacement boundary parameter patch coordinate
              (point, current.2)) current.1
        ((trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod)
            (orientationDoubleToThroat period hPeriod boundary)).symm current.1
              vector) := by
  let base : EffectiveThroat period hPeriod × Real :=
    (orientationDoubleToThroat period hPeriod boundary, parameter)
  let representative :=
    normalGraphCanonicalHolonomicLocalSectionNormalCoordinates period hPeriod
      metric displacement boundary parameter patch coordinate
  have hTarget : representative current ∈
      (trivializationAt HolonomicVector4
        (fun point : HolonomicVector4 =>
          TangentSpace (modelWithCornersSelf Real HolonomicVector4) point)
        (representative base)).baseSet :=
    mem_baseSet_trivializationAt HolonomicVector4
      (fun point : HolonomicVector4 =>
        TangentSpace (modelWithCornersSelf Real HolonomicVector4) point)
      (representative current)
  rw [show normalGraphCanonicalHolonomicLocalSectionNormalDerivativeCoordinates
      period hPeriod metric displacement boundary parameter patch coordinate
        current =
    ContinuousLinearMap.inCoordinates ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) HolonomicVector4
      (fun point : HolonomicVector4 =>
        TangentSpace (modelWithCornersSelf Real HolonomicVector4) point)
      base.1 current.1 (representative base) (representative current)
      (mfderiv throatCoverModelWithCorners
        (modelWithCornersSelf Real HolonomicVector4)
        (fun point => representative (point, current.2)) current.1) by rfl]
  rw [ContinuousLinearMap.inCoordinates_eq hCurrent hTarget]
  simp [base, representative]

set_option backward.isDefEq.respectTransparency false in
/-- Equal physical normal germs have source-coordinate differentials related
by the same tangent transition as the graph. -/
theorem normalGraphCanonicalHolonomicLocalSectionNormalDerivativeCoordinates_natural_of_eventuallyEq
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (firstBoundary secondBoundary : OrientationBoundary period hPeriod)
    (firstParameter secondParameter : Real)
    (current : EffectiveThroat period hPeriod × Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : HolonomicVector4)
    (hFirst : current.1 ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod)
          (orientationDoubleToThroat period hPeriod firstBoundary)).baseSet)
    (hSecond : current.1 ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod)
          (orientationDoubleToThroat period hPeriod secondBoundary)).baseSet)
    (hGerm :
      normalGraphCanonicalHolonomicLocalSectionNormalCoordinates period hPeriod
          metric displacement firstBoundary firstParameter patch firstCoordinate
          =ᶠ[nhds current]
        normalGraphCanonicalHolonomicLocalSectionNormalCoordinates period hPeriod
          metric displacement secondBoundary secondParameter patch
            secondCoordinate) :
    (normalGraphCanonicalHolonomicLocalSectionNormalDerivativeCoordinates period
        hPeriod metric displacement secondBoundary secondParameter patch
          secondCoordinate current).comp
      (normalGraphThroatTangentCoordinateTransition period hPeriod
        (orientationDoubleToThroat period hPeriod firstBoundary)
        (orientationDoubleToThroat period hPeriod secondBoundary) current.1
          hFirst hSecond :
          ThroatCoverCoordinates →L[Real] ThroatCoverCoordinates) =
      normalGraphCanonicalHolonomicLocalSectionNormalDerivativeCoordinates period
        hPeriod metric displacement firstBoundary firstParameter patch
          firstCoordinate current := by
  apply ContinuousLinearMap.ext
  intro vector
  rw [ContinuousLinearMap.comp_apply]
  rw [normalGraphCanonicalHolonomicLocalSectionNormalDerivativeCoordinates_apply_eq_mfderiv
      period hPeriod metric displacement secondBoundary secondParameter patch
        secondCoordinate current hSecond,
    normalGraphCanonicalHolonomicLocalSectionNormalDerivativeCoordinates_apply_eq_mfderiv
      period hPeriod metric displacement firstBoundary firstParameter patch
        firstCoordinate current hFirst]
  let tangentFirst :=
    (trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod)
        (orientationDoubleToThroat period hPeriod firstBoundary))
      |>.continuousLinearEquivAt Real current.1 hFirst
  let tangentSecond :=
    (trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod)
        (orientationDoubleToThroat period hPeriod secondBoundary))
      |>.continuousLinearEquivAt Real current.1 hSecond
  have hInput :
      (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod)
            (orientationDoubleToThroat period hPeriod secondBoundary)).symm
          current.1
          (normalGraphThroatTangentCoordinateTransition period hPeriod
            (orientationDoubleToThroat period hPeriod firstBoundary)
            (orientationDoubleToThroat period hPeriod secondBoundary) current.1
              hFirst hSecond vector) =
        (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod)
            (orientationDoubleToThroat period hPeriod firstBoundary)).symm
          current.1 vector := by
    change tangentSecond.symm (tangentSecond (tangentFirst.symm vector)) = _
    exact tangentSecond.symm_apply_apply _
  erw [hInput]
  have hSection : Tendsto
      (fun point : EffectiveThroat period hPeriod => (point, current.2))
      (nhds current.1) (nhds current) := by
    have h : Tendsto
        (fun point : EffectiveThroat period hPeriod => (point, current.2))
        (nhds current.1) (nhds (current.1, current.2)) :=
      (continuous_id.prodMk continuous_const).continuousAt
    simpa only [Prod.eta current] using h
  have hSlice := hGerm.comp_tendsto hSection
  have hDerivative := Filter.EventuallyEq.mfderiv_eq
    (I := throatCoverModelWithCorners)
    (I' := modelWithCornersSelf Real HolonomicVector4) hSlice
  exact congrArg (fun derivative => derivative
    ((trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod)
        (orientationDoubleToThroat period hPeriod firstBoundary)).symm
      current.1 vector)) hDerivative.symm

/-- The physical local-section normal written in the canonical source chart
of the throat.  This is a coordinate germ of the same normal, not a new field. -/
def normalGraphCanonicalHolonomicLocalSectionNormalSourceGerm
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (boundary : OrientationBoundary period hPeriod)
    (parameter : Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (sourceCoordinate : ThroatCoverCoordinates) : HolonomicVector4 :=
  normalGraphCanonicalHolonomicLocalSectionNormalCoordinates period hPeriod
    metric displacement boundary parameter patch coordinate
      ((extChartAt throatCoverModelWithCorners
        (orientationDoubleToThroat period hPeriod boundary)).symm sourceCoordinate,
        parameter)

theorem normalGraphCanonicalHolonomicLocalSectionNormalSourceGerm_contDiffAt
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : OrientationBoundary period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter)) :
    let throatBase := orientationDoubleToThroat period hPeriod boundary
    ContDiffAt Real ∞
      (normalGraphCanonicalHolonomicLocalSectionNormalSourceGerm period hPeriod
        metric displacement boundary parameter patch coordinate)
      (extChartAt throatCoverModelWithCorners throatBase throatBase) := by
  dsimp only
  let throatBase := orientationDoubleToThroat period hPeriod boundary
  let base : EffectiveThroat period hPeriod × Real := (throatBase, parameter)
  let representative :=
    normalGraphCanonicalHolonomicLocalSectionNormalCoordinates period hPeriod
      metric displacement boundary parameter patch coordinate
  let slice := fun point : EffectiveThroat period hPeriod =>
    representative (point, parameter)
  have hRepresentative : ContMDiffAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real HolonomicVector4) ∞ representative base := by
    simpa [representative, base, throatBase] using
      (normalGraphCanonicalHolonomicLocalSectionNormalCoordinates_contMDiffAt
        period hPeriod metric displacement parameter hNonNull boundary patch
          coordinate hAt)
  have hSection : ContMDiffAt throatCoverModelWithCorners
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real)) ∞
      (fun point : EffectiveThroat period hPeriod => (point, parameter))
      throatBase :=
    (contMDiff_id.prodMk contMDiff_const).contMDiffAt
  have hSlice : ContMDiffAt throatCoverModelWithCorners
      (modelWithCornersSelf Real HolonomicVector4) ∞ slice throatBase :=
    ContMDiffAt.comp
      (f := fun point : EffectiveThroat period hPeriod => (point, parameter))
      (g := representative) throatBase hRepresentative hSection
  have hSource := (contMDiffAt_iff_source).mp hSlice
  have hRange : Set.range throatCoverModelWithCorners = Set.univ := by
    ext sourceCoordinate
    simp
  rw [hRange, contMDiffWithinAt_univ] at hSource
  have hFunction :
      slice ∘ (extChartAt throatCoverModelWithCorners throatBase).symm =
        normalGraphCanonicalHolonomicLocalSectionNormalSourceGerm period hPeriod
          metric displacement boundary parameter patch coordinate := by
    rfl
  rw [hFunction] at hSource
  exact hSource.contDiffAt

@[simp]
theorem normalGraphCanonicalHolonomicLocalSectionNormalSourceGerm_base
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : OrientationBoundary period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter)) :
    let throatBase := orientationDoubleToThroat period hPeriod boundary
    normalGraphCanonicalHolonomicLocalSectionNormalSourceGerm period hPeriod
        metric displacement boundary parameter patch coordinate
          (extChartAt throatCoverModelWithCorners throatBase throatBase) =
      normalGraphCanonicalHolonomicMetricUnitNormalCoordinatesAt period hPeriod
        metric displacement parameter hNonNull boundary patch coordinate hAt := by
  dsimp only
  unfold normalGraphCanonicalHolonomicLocalSectionNormalSourceGerm
  rw [extChartAt_to_inv]
  exact normalGraphCanonicalHolonomicLocalSectionNormalCoordinates_base_eq
    period hPeriod metric displacement parameter hNonNull boundary patch
      coordinate hAt

theorem normalGraphCanonicalHolonomicLocalSectionNormalSourceGerm_fderiv
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : OrientationBoundary period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter))
    (tangent : ThroatCoverCoordinates) :
    let throatBase := orientationDoubleToThroat period hPeriod boundary
    let base : EffectiveThroat period hPeriod × Real :=
      (throatBase, parameter)
    fderiv Real
        (normalGraphCanonicalHolonomicLocalSectionNormalSourceGerm period hPeriod
          metric displacement boundary parameter patch coordinate)
        (extChartAt throatCoverModelWithCorners throatBase throatBase) tangent =
      normalGraphCanonicalHolonomicLocalSectionNormalDerivativeCoordinates period
        hPeriod metric displacement boundary parameter patch coordinate base
          tangent := by
  dsimp only
  let throatBase := orientationDoubleToThroat period hPeriod boundary
  let base : EffectiveThroat period hPeriod × Real := (throatBase, parameter)
  let representative :=
    normalGraphCanonicalHolonomicLocalSectionNormalCoordinates period hPeriod
      metric displacement boundary parameter patch coordinate
  let slice := fun point : EffectiveThroat period hPeriod =>
    representative (point, parameter)
  have hRepresentative : ContMDiffAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real HolonomicVector4) ∞ representative base := by
    simpa [representative, base, throatBase] using
      (normalGraphCanonicalHolonomicLocalSectionNormalCoordinates_contMDiffAt
        period hPeriod metric displacement parameter hNonNull boundary patch
          coordinate hAt)
  have hSection : ContMDiffAt throatCoverModelWithCorners
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real)) ∞
      (fun point : EffectiveThroat period hPeriod => (point, parameter))
      throatBase :=
    (contMDiff_id.prodMk contMDiff_const).contMDiffAt
  have hSlice : ContMDiffAt throatCoverModelWithCorners
      (modelWithCornersSelf Real HolonomicVector4) ∞ slice throatBase :=
    ContMDiffAt.comp
      (f := fun point : EffectiveThroat period hPeriod => (point, parameter))
      (g := representative) throatBase hRepresentative hSection
  rw [normalGraphCanonicalHolonomicLocalSectionNormalDerivativeCoordinates_apply_base_eq_mfderiv
    period hPeriod metric displacement boundary parameter patch coordinate
      tangent]
  have hChart : throatBase ∈ (chartAt ThroatCoverModel throatBase).source :=
    mem_chart_source ThroatCoverModel throatBase
  have hVector :
      (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) throatBase).symm throatBase tangent =
        tangent := by
    change
      (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) throatBase).symmL Real throatBase
            tangent = tangent
    rw [TangentBundle.symmL_trivializationAt hChart,
      mfderivWithin_range_extChartAt_symm]
    rfl
  rw [hVector]
  rw [(hSlice.mdifferentiableAt (by simp)).mfderiv]
  have hRange : Set.range throatCoverModelWithCorners = Set.univ := by
    ext sourceCoordinate
    simp
  rw [hRange, fderivWithin_univ]
  simp [writtenInExtChartAt, Function.comp_def, slice, representative,
    throatBase]
  rfl

/-- Pulling the joint identity through the canonical source chart preserves
orthogonality to the genuine source derivative on one neighborhood. -/
theorem normalGraphCanonicalHolonomicLocalSectionNormalSourceGerm_eventually_orthogonal
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : OrientationBoundary period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter))
    (tangent : ThroatCoverCoordinates) :
    let base : EffectiveThroat period hPeriod × Real :=
      (orientationDoubleToThroat period hPeriod boundary, parameter)
    (fun sourceCoordinate =>
      localMetricCoordinateForm period hPeriod metric patch
        (normalGraphHolonomicSourceChartGerm period hPeriod displacement base
          patch coordinate sourceCoordinate)
        (normalGraphCanonicalHolonomicLocalSectionNormalSourceGerm period hPeriod
          metric displacement boundary parameter patch coordinate sourceCoordinate)
        (fderiv Real
          (normalGraphHolonomicSourceChartGerm period hPeriod displacement base
            patch coordinate) sourceCoordinate tangent)) =ᶠ[
          nhds (extChartAt throatCoverModelWithCorners base.1 base.1)]
      fun _ => 0 := by
  dsimp only
  let base : EffectiveThroat period hPeriod × Real :=
    (orientationDoubleToThroat period hPeriod boundary, parameter)
  let inverse := (extChartAt throatCoverModelWithCorners base.1).symm
  let sourceMap := fun sourceCoordinate : ThroatCoverCoordinates =>
    (inverse sourceCoordinate, base.2)
  have hGraph : patch.coordinateMap coordinate =
      normalGraph period hPeriod displacement base.2 base.1 := by
    simpa [base, normalGraphOrientationDouble] using hAt
  have hInverseContinuous : ContinuousAt inverse
      (extChartAt throatCoverModelWithCorners base.1 base.1) :=
    continuousAt_extChartAt_symm base.1
  have hInverseBase :
      inverse (extChartAt throatCoverModelWithCorners base.1 base.1) = base.1 := by
    dsimp only [inverse]
    rw [extChartAt_to_inv]
  have hInverseTendsto : Tendsto inverse
      (nhds (extChartAt throatCoverModelWithCorners base.1 base.1))
      (nhds base.1) := by
    have hTendsto : Tendsto inverse
        (nhds (extChartAt throatCoverModelWithCorners base.1 base.1))
        (nhds (inverse
          (extChartAt throatCoverModelWithCorners base.1 base.1))) :=
      hInverseContinuous
    rw [hInverseBase] at hTendsto
    exact hTendsto
  have hSourceMapTendsto : Tendsto sourceMap
      (nhds (extChartAt throatCoverModelWithCorners base.1 base.1))
      (nhds base) := by
    have hConst : Tendsto
        (fun _ : ThroatCoverCoordinates => base.2)
        (nhds (extChartAt throatCoverModelWithCorners base.1 base.1))
        (nhds base.2) := tendsto_const_nhds
    have hPair := hInverseTendsto.prodMk hConst
    have hBaseFilter : nhds base = nhds base.1 ×ˢ nhds base.2 := by
      rw [← Prod.eta base]
      exact nhds_prod_eq
    rw [hBaseFilter]
    simpa [sourceMap] using hPair
  have hOrthogonal :=
    (normalGraphCanonicalHolonomicLocalSectionNormalCoordinates_eventually_orthogonal
      period hPeriod metric displacement parameter hNonNull boundary patch
        coordinate hAt tangent).comp_tendsto hSourceMapTendsto
  have hTarget : ∀ᶠ sourceCoordinate in
      nhds (extChartAt throatCoverModelWithCorners base.1 base.1),
      sourceCoordinate ∈
        (extChartAt throatCoverModelWithCorners base.1).target :=
    extChartAt_target_mem_nhds base.1
  have hCurrentPoint : ∀ᶠ point in nhds base.1, point ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) base.1).baseSet :=
    (trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) base.1).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) base.1)
  have hRepresentative :=
    normalGraphHolonomicSpatialRepresentative_eventually_contMDiffAt period
      hPeriod displacement base patch coordinate hGraph
  filter_upwards [hOrthogonal, hTarget,
    hInverseTendsto.eventually hCurrentPoint,
    hInverseTendsto.eventually hRepresentative] with sourceCoordinate
      hOrthogonalAt hSourceTarget hCurrent hRepresentativeAt
  have hDerivative :=
    normalGraphHolonomicSourceChartGerm_fderiv_eq_family_of_mem period hPeriod
      displacement base patch coordinate sourceCoordinate hSourceTarget hCurrent
        hRepresentativeAt tangent
  rw [hDerivative]
  simpa [normalGraphCanonicalHolonomicLocalSectionNormalSourceGerm,
    normalGraphHolonomicSourceChartGerm, sourceMap, inverse, base] using
      hOrthogonalAt

/-- Weingarten pairing built from the physical local-section normal. -/
def normalGraphCanonicalHolonomicLocalSectionRawExtrinsicCurvatureCoordinates
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (boundary : OrientationBoundary period hPeriod)
    (parameter : Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (first second : ThroatCoverCoordinates)
    (current : EffectiveThroat period hPeriod × Real) : Real :=
  let base : EffectiveThroat period hPeriod × Real :=
    (orientationDoubleToThroat period hPeriod boundary, parameter)
  let graphDerivative :=
    normalGraphHolonomicFamilyDerivativeCoordinates period hPeriod displacement
      base patch coordinate current
  let normal :=
    normalGraphCanonicalHolonomicLocalSectionNormalCoordinates period hPeriod
      metric displacement boundary parameter patch coordinate current
  let normalDerivative :=
    normalGraphCanonicalHolonomicLocalSectionNormalDerivativeCoordinates period
      hPeriod metric displacement boundary parameter patch coordinate current
  localMetricCoordinateForm period hPeriod metric patch
    (normalGraphHolonomicCoordinateGerm period hPeriod displacement base patch
      coordinate current)
    (normalDerivative first +
      localLeviCivitaChristoffelApply period hPeriod metric patch
        (normalGraphHolonomicCoordinateGerm period hPeriod displacement base
          patch coordinate current) (graphDerivative first) normal)
    (graphDerivative second)

theorem normalGraphCanonicalHolonomicLocalSectionRawExtrinsicCurvatureCoordinates_contMDiffAt
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : OrientationBoundary period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter))
    (first second : ThroatCoverCoordinates) :
    ContMDiffAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real Real) ∞
      (normalGraphCanonicalHolonomicLocalSectionRawExtrinsicCurvatureCoordinates
        period hPeriod metric displacement boundary parameter patch coordinate
          first second)
      (orientationDoubleToThroat period hPeriod boundary, parameter) := by
  let base : EffectiveThroat period hPeriod × Real :=
    (orientationDoubleToThroat period hPeriod boundary, parameter)
  have hGraph : patch.coordinateMap coordinate =
      normalGraph period hPeriod displacement base.2 base.1 := by
    simpa [base, normalGraphOrientationDouble] using hAt
  have hGraphDerivative :=
    normalGraphHolonomicFamilyDerivativeCoordinates_contMDiffAt period hPeriod
      displacement base patch coordinate hGraph
  have hNormal :=
    normalGraphCanonicalHolonomicLocalSectionNormalCoordinates_contMDiffAt
      period hPeriod metric displacement parameter hNonNull boundary patch
        coordinate hAt
  have hNormalDerivative :=
    normalGraphCanonicalHolonomicLocalSectionNormalDerivativeCoordinates_contMDiffAt
      period hPeriod metric displacement parameter hNonNull boundary patch
        coordinate hAt
  have hGraphFirst := hGraphDerivative.clm_apply
    (contMDiffAt_const (c := first))
  have hGraphSecond := hGraphDerivative.clm_apply
    (contMDiffAt_const (c := second))
  have hNormalDerivativeFirst := hNormalDerivative.clm_apply
    (contMDiffAt_const (c := first))
  have hConnection :=
    normalGraphHolonomicLeviCivitaApply_contMDiffAt period hPeriod metric
      displacement base patch coordinate hGraph _ _ hGraphFirst hNormal
  exact normalGraphHolonomicMetricEvaluation_contMDiffAt period hPeriod metric
    displacement base patch coordinate hGraph _ _
      (hNormalDerivativeFirst.add hConnection) hGraphSecond

/-- The physical Weingarten pairing is covariant under a reanchoring of the
source trivialization whenever the graph and normal representatives are the
same germs. -/
theorem normalGraphCanonicalHolonomicLocalSectionRawExtrinsicCurvatureCoordinates_natural_of_eventuallyEq
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (firstBoundary secondBoundary : OrientationBoundary period hPeriod)
    (firstParameter secondParameter : Real)
    (current : EffectiveThroat period hPeriod × Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : HolonomicVector4)
    (hFirst : current.1 ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod)
          (orientationDoubleToThroat period hPeriod firstBoundary)).baseSet)
    (hSecond : current.1 ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod)
          (orientationDoubleToThroat period hPeriod secondBoundary)).baseSet)
    (hGraphGerm :
      normalGraphHolonomicCoordinateGerm period hPeriod displacement
          (orientationDoubleToThroat period hPeriod firstBoundary,
            firstParameter) patch firstCoordinate =ᶠ[nhds current]
        normalGraphHolonomicCoordinateGerm period hPeriod displacement
          (orientationDoubleToThroat period hPeriod secondBoundary,
            secondParameter) patch secondCoordinate)
    (hNormalGerm :
      normalGraphCanonicalHolonomicLocalSectionNormalCoordinates period hPeriod
          metric displacement firstBoundary firstParameter patch firstCoordinate
          =ᶠ[nhds current]
        normalGraphCanonicalHolonomicLocalSectionNormalCoordinates period hPeriod
          metric displacement secondBoundary secondParameter patch
            secondCoordinate)
    (first second : ThroatCoverCoordinates) :
    let transition :=
      normalGraphThroatTangentCoordinateTransition period hPeriod
        (orientationDoubleToThroat period hPeriod firstBoundary)
        (orientationDoubleToThroat period hPeriod secondBoundary) current.1
          hFirst hSecond
    normalGraphCanonicalHolonomicLocalSectionRawExtrinsicCurvatureCoordinates
        period hPeriod metric displacement secondBoundary secondParameter patch
          secondCoordinate (transition first) (transition second) current =
      normalGraphCanonicalHolonomicLocalSectionRawExtrinsicCurvatureCoordinates
        period hPeriod metric displacement firstBoundary firstParameter patch
          firstCoordinate first second current := by
  dsimp only
  let firstBase : EffectiveThroat period hPeriod × Real :=
    (orientationDoubleToThroat period hPeriod firstBoundary, firstParameter)
  let secondBase : EffectiveThroat period hPeriod × Real :=
    (orientationDoubleToThroat period hPeriod secondBoundary, secondParameter)
  have hGraphDerivative :=
    normalGraphHolonomicFamilyDerivativeCoordinates_natural_of_eventuallyEq
      period hPeriod displacement firstBase secondBase current patch
        firstCoordinate secondCoordinate hFirst hSecond hGraphGerm
  have hNormalDerivative :=
    normalGraphCanonicalHolonomicLocalSectionNormalDerivativeCoordinates_natural_of_eventuallyEq
      period hPeriod metric displacement firstBoundary secondBoundary
        firstParameter secondParameter current patch firstCoordinate
          secondCoordinate hFirst hSecond hNormalGerm
  have hGraphFirst := congrArg (fun derivative => derivative first)
    hGraphDerivative
  have hGraphSecond := congrArg (fun derivative => derivative second)
    hGraphDerivative
  have hNormalFirst := congrArg (fun derivative => derivative first)
    hNormalDerivative
  simp only [ContinuousLinearMap.comp_apply] at hGraphFirst hGraphSecond hNormalFirst
  dsimp only [firstBase, secondBase] at hGraphFirst hGraphSecond
  have hCoordinate := hGraphGerm.eq_of_nhds
  have hNormal := hNormalGerm.eq_of_nhds
  unfold normalGraphCanonicalHolonomicLocalSectionRawExtrinsicCurvatureCoordinates
  dsimp only
  erw [hGraphFirst, hGraphSecond, hNormalFirst, ← hCoordinate, ← hNormal]

/-- The raw Weingarten pairing bundled as the bilinear map already expressed
by its scalar formula above. -/
def normalGraphCanonicalHolonomicLocalSectionRawExtrinsicCurvatureLinearMap
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (boundary : OrientationBoundary period hPeriod)
    (parameter : Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (current : EffectiveThroat period hPeriod × Real) :
    ThroatCoverCoordinates →ₗ[Real]
      ThroatCoverCoordinates →ₗ[Real] Real :=
  LinearMap.mk₂ Real
    (fun first second =>
      normalGraphCanonicalHolonomicLocalSectionRawExtrinsicCurvatureCoordinates
        period hPeriod metric displacement boundary parameter patch coordinate
          first second current)
    (by
      intro first second third
      unfold normalGraphCanonicalHolonomicLocalSectionRawExtrinsicCurvatureCoordinates
      dsimp only
      simp_rw [← localLeviCivitaChristoffelBilinearMap_apply]
      simp only [map_add, LinearMap.add_apply]
      ring)
    (by
      intro scalar first second
      unfold normalGraphCanonicalHolonomicLocalSectionRawExtrinsicCurvatureCoordinates
      dsimp only
      simp_rw [← localLeviCivitaChristoffelBilinearMap_apply]
      simp only [map_smul, LinearMap.smul_apply]
      rw [← smul_add, map_smul]
      rfl)
    (by
      intro first second third
      unfold normalGraphCanonicalHolonomicLocalSectionRawExtrinsicCurvatureCoordinates
      dsimp only
      simp only [map_add])
    (by
      intro scalar first second
      unfold normalGraphCanonicalHolonomicLocalSectionRawExtrinsicCurvatureCoordinates
      dsimp only
      simp only [map_smul])

private def normalGraphContinuousBilinearOfLinear
    (form : ThroatCoverCoordinates →ₗ[Real]
      ThroatCoverCoordinates →ₗ[Real] Real) :
    ThroatCoverCoordinates →L[Real]
      ThroatCoverCoordinates →L[Real] Real :=
  LinearMap.toContinuousLinearMap
    { toFun := fun first =>
        LinearMap.toContinuousLinearMap (form first)
      map_add' := by
        intro first second
        apply ContinuousLinearMap.ext
        intro third
        simp
      map_smul' := by
        intro scalar first
        apply ContinuousLinearMap.ext
        intro second
        simp }

/-- Symmetric matrix and mean-curvature contraction of the same local-section
Weingarten pairing. -/
def normalGraphCanonicalHolonomicLocalSectionExtrinsicCurvatureMatrix
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (boundary : OrientationBoundary period hPeriod)
    (parameter : Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (current : EffectiveThroat period hPeriod × Real) : Matrix3 :=
  fun first second => (1 / 2 : Real) *
    (normalGraphCanonicalHolonomicLocalSectionRawExtrinsicCurvatureCoordinates
      period hPeriod metric displacement boundary parameter patch coordinate
        (throatCoordinateBasis first) (throatCoordinateBasis second) current +
    normalGraphCanonicalHolonomicLocalSectionRawExtrinsicCurvatureCoordinates
      period hPeriod metric displacement boundary parameter patch coordinate
        (throatCoordinateBasis second) (throatCoordinateBasis first) current)

def normalGraphCanonicalHolonomicLocalSectionMeanCurvatureFamily
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (boundary : OrientationBoundary period hPeriod)
    (parameter : Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (current : EffectiveThroat period hPeriod × Real) : Real :=
  let base : EffectiveThroat period hPeriod × Real :=
    (orientationDoubleToThroat period hPeriod boundary, parameter)
  Matrix.trace
    (normalGraphInducedInverseMatrixFamily period hPeriod metric displacement
        base current *
      normalGraphCanonicalHolonomicLocalSectionExtrinsicCurvatureMatrix period
        hPeriod metric displacement boundary parameter patch coordinate current)

/-- Linear-map adapter of the same local-section second fundamental form.
This uses the existing ledger basis only to expose the basis-free trace. -/
def normalGraphCanonicalHolonomicLocalSectionExtrinsicCurvatureLinearMap
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (boundary : OrientationBoundary period hPeriod)
    (parameter : Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (current : EffectiveThroat period hPeriod × Real) :
    ThroatCoverCoordinates →L[Real]
      (ThroatCoverCoordinates →L[Real] Real) :=
  let raw :=
    normalGraphCanonicalHolonomicLocalSectionRawExtrinsicCurvatureLinearMap
      period hPeriod metric displacement boundary parameter patch coordinate
        current
  normalGraphContinuousBilinearOfLinear
    ((1 / 2 : Real) • (raw + LinearMap.flip raw))

@[simp]
theorem normalGraphCanonicalHolonomicLocalSectionExtrinsicCurvatureLinearMap_apply
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (boundary : OrientationBoundary period hPeriod)
    (parameter : Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (current : EffectiveThroat period hPeriod × Real)
    (first second : ThroatCoverCoordinates) :
    normalGraphCanonicalHolonomicLocalSectionExtrinsicCurvatureLinearMap period
        hPeriod metric displacement boundary parameter patch coordinate current
          first second =
      (1 / 2 : Real) *
        (normalGraphCanonicalHolonomicLocalSectionRawExtrinsicCurvatureCoordinates
          period hPeriod metric displacement boundary parameter patch coordinate
            first second current +
        normalGraphCanonicalHolonomicLocalSectionRawExtrinsicCurvatureCoordinates
          period hPeriod metric displacement boundary parameter patch coordinate
            second first current) := by
  rfl

theorem normalGraphCanonicalHolonomicLocalSectionExtrinsicCurvatureLinearMap_toMatrix
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (boundary : OrientationBoundary period hPeriod)
    (parameter : Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (current : EffectiveThroat period hPeriod × Real) :
    LinearMap.toMatrix throatCoordinateBasis throatContinuousDualBasis
        (normalGraphCanonicalHolonomicLocalSectionExtrinsicCurvatureLinearMap
          period hPeriod metric displacement boundary parameter patch coordinate
            current).toLinearMap =
      normalGraphCanonicalHolonomicLocalSectionExtrinsicCurvatureMatrix
        period hPeriod metric displacement boundary parameter patch coordinate
          current := by
  ext row column
  simp only [LinearMap.toMatrix_apply, throatContinuousDualBasis,
    Basis.map_repr, LinearEquiv.trans_apply, Basis.dualBasis_repr]
  simp [normalGraphCanonicalHolonomicLocalSectionExtrinsicCurvatureMatrix]
  ring

/-- The symmetrized second fundamental form carries the covariant source
transition law dual to that of the inverse metric. -/
theorem normalGraphCanonicalHolonomicLocalSectionExtrinsicCurvatureLinearMap_natural_of_eventuallyEq
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (firstBoundary secondBoundary : OrientationBoundary period hPeriod)
    (firstParameter secondParameter : Real)
    (current : EffectiveThroat period hPeriod × Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : HolonomicVector4)
    (hFirstTangent : current.1 ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod)
          (orientationDoubleToThroat period hPeriod firstBoundary)).baseSet)
    (hSecondTangent : current.1 ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod)
          (orientationDoubleToThroat period hPeriod secondBoundary)).baseSet)
    (hFirstCotangent : current.1 ∈
      (trivializationAt (ThroatCoverCoordinates →L[Real] Real)
        (ThroatCotangentFiber period hPeriod)
          (orientationDoubleToThroat period hPeriod firstBoundary)).baseSet)
    (hSecondCotangent : current.1 ∈
      (trivializationAt (ThroatCoverCoordinates →L[Real] Real)
        (ThroatCotangentFiber period hPeriod)
          (orientationDoubleToThroat period hPeriod secondBoundary)).baseSet)
    (hGraphGerm :
      normalGraphHolonomicCoordinateGerm period hPeriod displacement
          (orientationDoubleToThroat period hPeriod firstBoundary,
            firstParameter) patch firstCoordinate =ᶠ[nhds current]
        normalGraphHolonomicCoordinateGerm period hPeriod displacement
          (orientationDoubleToThroat period hPeriod secondBoundary,
            secondParameter) patch secondCoordinate)
    (hNormalGerm :
      normalGraphCanonicalHolonomicLocalSectionNormalCoordinates period hPeriod
          metric displacement firstBoundary firstParameter patch firstCoordinate
          =ᶠ[nhds current]
        normalGraphCanonicalHolonomicLocalSectionNormalCoordinates period hPeriod
          metric displacement secondBoundary secondParameter patch
            secondCoordinate) :
    (normalGraphCanonicalHolonomicLocalSectionExtrinsicCurvatureLinearMap period
        hPeriod metric displacement secondBoundary secondParameter patch
          secondCoordinate current).comp
      (normalGraphThroatTangentCoordinateTransition period hPeriod
        (orientationDoubleToThroat period hPeriod firstBoundary)
        (orientationDoubleToThroat period hPeriod secondBoundary) current.1
          hFirstTangent hSecondTangent :
          ThroatCoverCoordinates →L[Real] ThroatCoverCoordinates) =
      (normalGraphThroatCotangentCoordinateTransition period hPeriod
        (orientationDoubleToThroat period hPeriod firstBoundary)
        (orientationDoubleToThroat period hPeriod secondBoundary) current.1
          hFirstCotangent hSecondCotangent :
          (ThroatCoverCoordinates →L[Real] Real) →L[Real]
            (ThroatCoverCoordinates →L[Real] Real)).comp
        (normalGraphCanonicalHolonomicLocalSectionExtrinsicCurvatureLinearMap
          period hPeriod metric displacement firstBoundary firstParameter patch
            firstCoordinate current) := by
  apply ContinuousLinearMap.ext
  intro first
  apply ContinuousLinearMap.ext
  intro secondCoordinateVector
  let transition :=
    normalGraphThroatTangentCoordinateTransition period hPeriod
      (orientationDoubleToThroat period hPeriod firstBoundary)
      (orientationDoubleToThroat period hPeriod secondBoundary) current.1
        hFirstTangent hSecondTangent
  let second := transition.symm secondCoordinateVector
  have hSecond : transition second = secondCoordinateVector :=
    transition.apply_symm_apply secondCoordinateVector
  rw [← hSecond]
  simp only [ContinuousLinearMap.comp_apply]
  dsimp only [transition]
  erw [normalGraphThroatCoordinateTransition_pairing period hPeriod
    (orientationDoubleToThroat period hPeriod firstBoundary)
    (orientationDoubleToThroat period hPeriod secondBoundary) current.1
      hFirstTangent hSecondTangent hFirstCotangent hSecondCotangent]
  rw [normalGraphCanonicalHolonomicLocalSectionExtrinsicCurvatureLinearMap_apply,
    normalGraphCanonicalHolonomicLocalSectionExtrinsicCurvatureLinearMap_apply]
  have hFirstSecond :=
    normalGraphCanonicalHolonomicLocalSectionRawExtrinsicCurvatureCoordinates_natural_of_eventuallyEq
      period hPeriod metric displacement firstBoundary secondBoundary
        firstParameter secondParameter current patch firstCoordinate
          secondCoordinate hFirstTangent hSecondTangent hGraphGerm hNormalGerm
            first second
  have hSecondFirst :=
    normalGraphCanonicalHolonomicLocalSectionRawExtrinsicCurvatureCoordinates_natural_of_eventuallyEq
      period hPeriod metric displacement firstBoundary secondBoundary
        firstParameter secondParameter current patch firstCoordinate
          secondCoordinate hFirstTangent hSecondTangent hGraphGerm hNormalGerm
            second first
  dsimp only at hFirstSecond hSecondFirst
  erw [hFirstSecond, hSecondFirst]

/-- The matrix GHY contraction is exactly the basis-free trace of
`g⁻¹ ∘ K`. -/
theorem normalGraphCanonicalHolonomicLocalSectionMeanCurvatureFamily_eq_trace
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (boundary : OrientationBoundary period hPeriod)
    (parameter : Real)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (current : EffectiveThroat period hPeriod × Real) :
    normalGraphCanonicalHolonomicLocalSectionMeanCurvatureFamily period hPeriod
        metric displacement boundary parameter patch coordinate current =
      LinearMap.trace Real ThroatCoverCoordinates
        ((normalGraphInducedMetricInverseCoordinates period hPeriod metric
          displacement
            (orientationDoubleToThroat period hPeriod boundary, parameter)
            current).toLinearMap.comp
          (normalGraphCanonicalHolonomicLocalSectionExtrinsicCurvatureLinearMap
            period hPeriod metric displacement boundary parameter patch
              coordinate current).toLinearMap) := by
  rw [LinearMap.trace_eq_matrix_trace Real throatCoordinateBasis]
  rw [LinearMap.toMatrix_comp throatCoordinateBasis
    throatContinuousDualBasis throatCoordinateBasis]
  rw [normalGraphCanonicalHolonomicLocalSectionExtrinsicCurvatureLinearMap_toMatrix]
  rfl

/-- The local-section mean-curvature representative is independent of the
source trivialization on any germ where the physical graph and normal agree. -/
theorem normalGraphCanonicalHolonomicLocalSectionMeanCurvatureFamily_natural_of_eventuallyEq
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (firstBoundary secondBoundary : OrientationBoundary period hPeriod)
    (firstParameter secondParameter : Real)
    (current : EffectiveThroat period hPeriod × Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement current.2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : HolonomicVector4)
    (hFirstTangent : current.1 ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod)
          (orientationDoubleToThroat period hPeriod firstBoundary)).baseSet)
    (hSecondTangent : current.1 ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod)
          (orientationDoubleToThroat period hPeriod secondBoundary)).baseSet)
    (hFirstCotangent : current.1 ∈
      (trivializationAt (ThroatCoverCoordinates →L[Real] Real)
        (ThroatCotangentFiber period hPeriod)
          (orientationDoubleToThroat period hPeriod firstBoundary)).baseSet)
    (hSecondCotangent : current.1 ∈
      (trivializationAt (ThroatCoverCoordinates →L[Real] Real)
        (ThroatCotangentFiber period hPeriod)
          (orientationDoubleToThroat period hPeriod secondBoundary)).baseSet)
    (hGraphGerm :
      normalGraphHolonomicCoordinateGerm period hPeriod displacement
          (orientationDoubleToThroat period hPeriod firstBoundary,
            firstParameter) patch firstCoordinate =ᶠ[nhds current]
        normalGraphHolonomicCoordinateGerm period hPeriod displacement
          (orientationDoubleToThroat period hPeriod secondBoundary,
            secondParameter) patch secondCoordinate)
    (hNormalGerm :
      normalGraphCanonicalHolonomicLocalSectionNormalCoordinates period hPeriod
          metric displacement firstBoundary firstParameter patch firstCoordinate
          =ᶠ[nhds current]
        normalGraphCanonicalHolonomicLocalSectionNormalCoordinates period hPeriod
          metric displacement secondBoundary secondParameter patch
            secondCoordinate) :
    normalGraphCanonicalHolonomicLocalSectionMeanCurvatureFamily period hPeriod
        metric displacement secondBoundary secondParameter patch secondCoordinate
          current =
      normalGraphCanonicalHolonomicLocalSectionMeanCurvatureFamily period hPeriod
        metric displacement firstBoundary firstParameter patch firstCoordinate
          current := by
  rw [normalGraphCanonicalHolonomicLocalSectionMeanCurvatureFamily_eq_trace,
    normalGraphCanonicalHolonomicLocalSectionMeanCurvatureFamily_eq_trace]
  let firstBase : EffectiveThroat period hPeriod × Real :=
    (orientationDoubleToThroat period hPeriod firstBoundary, firstParameter)
  let secondBase : EffectiveThroat period hPeriod × Real :=
    (orientationDoubleToThroat period hPeriod secondBoundary, secondParameter)
  let tangentTransition :=
    normalGraphThroatTangentCoordinateTransition period hPeriod firstBase.1
      secondBase.1 current.1 hFirstTangent hSecondTangent
  let cotangentTransition :=
    normalGraphThroatCotangentCoordinateTransition period hPeriod firstBase.1
      secondBase.1 current.1 hFirstCotangent hSecondCotangent
  apply normalGraphThroatContractedTrace_natural
    (tangentTransition := tangentTransition)
    (cotangentTransition := cotangentTransition)
  · exact normalGraphInducedMetricInverseCoordinates_natural period hPeriod
      metric displacement firstBase secondBase current hNonNull hFirstTangent
        hSecondTangent hFirstCotangent hSecondCotangent
  · exact
      normalGraphCanonicalHolonomicLocalSectionExtrinsicCurvatureLinearMap_natural_of_eventuallyEq
        period hPeriod metric displacement firstBoundary secondBoundary
          firstParameter secondParameter current patch firstCoordinate
            secondCoordinate hFirstTangent hSecondTangent hFirstCotangent
              hSecondCotangent hGraphGerm hNormalGerm

theorem normalGraphCanonicalHolonomicLocalSectionMeanCurvatureFamily_contMDiffAt
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : OrientationBoundary period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter)) :
    ContMDiffAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real Real) ∞
      (normalGraphCanonicalHolonomicLocalSectionMeanCurvatureFamily period
        hPeriod metric displacement boundary parameter patch coordinate)
      (orientationDoubleToThroat period hPeriod boundary, parameter) := by
  let base : EffectiveThroat period hPeriod × Real :=
    (orientationDoubleToThroat period hPeriod boundary, parameter)
  unfold normalGraphCanonicalHolonomicLocalSectionMeanCurvatureFamily Matrix.trace
  apply ContMDiffAt.sum
  intro row _
  simp only [Matrix.diag_apply, Matrix.mul_apply]
  apply ContMDiffAt.sum
  intro column _
  have hInverse :=
    normalGraphInducedInverseMatrixFamily_apply_contMDiffAt period hPeriod metric
      displacement base hNonNull row column
  unfold normalGraphCanonicalHolonomicLocalSectionExtrinsicCurvatureMatrix
  exact hInverse.mul (contMDiffAt_const.mul
    ((normalGraphCanonicalHolonomicLocalSectionRawExtrinsicCurvatureCoordinates_contMDiffAt
      period hPeriod metric displacement parameter hNonNull boundary patch
        coordinate hAt (throatCoordinateBasis column)
          (throatCoordinateBasis row)).add
    (normalGraphCanonicalHolonomicLocalSectionRawExtrinsicCurvatureCoordinates_contMDiffAt
      period hPeriod metric displacement parameter hNonNull boundary patch
        coordinate hAt (throatCoordinateBasis row)
          (throatCoordinateBasis column))))

/-- Differentiating the physical local-section orthogonality identifies its
Weingarten pairing with the already installed chart-free Gauss pairing. -/
theorem normalGraphCanonicalHolonomicLocalSectionRawExtrinsicCurvatureCoordinates_base_eq_gauss
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : OrientationBoundary period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter))
    (first second : ThroatCoverCoordinates) :
    let base : EffectiveThroat period hPeriod × Real :=
      (orientationDoubleToThroat period hPeriod boundary, parameter)
    normalGraphCanonicalHolonomicLocalSectionRawExtrinsicCurvatureCoordinates
        period hPeriod metric displacement boundary parameter patch coordinate
          first second base =
      normalGraphCanonicalHolonomicGaussRawExtrinsicCurvatureCoordinatesAt
        period hPeriod metric displacement parameter hNonNull boundary patch
          coordinate hAt first second := by
  dsimp only
  let base : EffectiveThroat period hPeriod × Real :=
    (orientationDoubleToThroat period hPeriod boundary, parameter)
  let sourceBase := extChartAt throatCoverModelWithCorners base.1 base.1
  let sourceGerm :=
    normalGraphHolonomicSourceChartGerm period hPeriod displacement base patch
      coordinate
  let normalGerm :=
    normalGraphCanonicalHolonomicLocalSectionNormalSourceGerm period hPeriod
      metric displacement boundary parameter patch coordinate
  let tangentGerm := fun sourceCoordinate =>
    fderiv Real sourceGerm sourceCoordinate second
  have hGraph : patch.coordinateMap coordinate =
      normalGraph period hPeriod displacement base.2 base.1 := by
    simpa [base, normalGraphOrientationDouble] using hAt
  have hSource : ContDiffAt Real ∞ sourceGerm sourceBase := by
    exact normalGraphHolonomicSourceChartGerm_contDiffAt period hPeriod
      displacement base patch coordinate hGraph
  have hNormal : ContDiffAt Real ∞ normalGerm sourceBase := by
    exact
      normalGraphCanonicalHolonomicLocalSectionNormalSourceGerm_contDiffAt period
        hPeriod metric displacement parameter hNonNull boundary patch coordinate
          hAt
  have hSourceC2 : ContDiffAt Real 2 sourceGerm sourceBase :=
    hSource.of_le (by
      change ((2 : ℕ∞) : WithTop ℕ∞) ≤
        ((⊤ : ℕ∞) : WithTop ℕ∞)
      exact WithTop.coe_le_coe.mpr le_top)
  have hFDeriv : DifferentiableAt Real (fderiv Real sourceGerm) sourceBase :=
    (hSourceC2.fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)
  have hTangent : DifferentiableAt Real tangentGerm sourceBase :=
    hFDeriv.clm_apply (differentiableAt_const second)
  have hOrthogonal :=
    normalGraphCanonicalHolonomicLocalSectionNormalSourceGerm_eventually_orthogonal
      period hPeriod metric displacement parameter hNonNull boundary patch
        coordinate hAt second
  have hGaussWeingarten :=
    localMetric_gauss_weingarten_of_eventually_orthogonal period hPeriod metric
      patch sourceGerm normalGerm tangentGerm sourceBase first
        (hSource.differentiableAt (by simp))
        (hNormal.differentiableAt (by simp)) hTangent hOrthogonal
  have hTangentDerivative :
      fderiv Real tangentGerm sourceBase first =
        normalGraphHolonomicSourceSecondDerivativeCoordinatesAt period hPeriod
          displacement base patch coordinate first second := by
    unfold normalGraphHolonomicSourceSecondDerivativeCoordinatesAt
    exact normalBoundary_fderiv_continuousLinearMap_apply_const
      (fderiv Real sourceGerm) sourceBase first second hFDeriv
  dsimp only [sourceGerm, sourceBase, normalGerm, tangentGerm]
    at hGaussWeingarten
  rw [normalGraphHolonomicSourceChartGerm_base period hPeriod displacement base
    patch coordinate hGraph] at hGaussWeingarten
  rw [normalGraphCanonicalHolonomicLocalSectionNormalSourceGerm_base period
    hPeriod metric displacement parameter hNonNull boundary patch coordinate hAt]
    at hGaussWeingarten
  rw [normalGraphCanonicalHolonomicLocalSectionNormalSourceGerm_fderiv period
    hPeriod metric displacement parameter hNonNull boundary patch coordinate hAt
      first] at hGaussWeingarten
  rw [hTangentDerivative] at hGaussWeingarten
  change
    localMetricCoordinateForm period hPeriod metric patch coordinate
        (normalGraphCanonicalHolonomicLocalSectionNormalDerivativeCoordinates
          period hPeriod metric displacement boundary parameter patch coordinate
            base first +
          localLeviCivitaChristoffelApply period hPeriod metric patch coordinate
            (normalGraphHolonomicSourceFirstDerivativeCoordinatesAt period
              hPeriod displacement base patch coordinate first)
            (normalGraphCanonicalHolonomicMetricUnitNormalCoordinatesAt period
              hPeriod metric displacement parameter hNonNull boundary patch
                coordinate hAt))
        (normalGraphHolonomicSourceFirstDerivativeCoordinatesAt period hPeriod
          displacement base patch coordinate second) =
      -localMetricCoordinateForm period hPeriod metric patch coordinate
        (normalGraphCanonicalHolonomicMetricUnitNormalCoordinatesAt period
          hPeriod metric displacement parameter hNonNull boundary patch
            coordinate hAt)
        (normalGraphHolonomicSourceSecondDerivativeCoordinatesAt period hPeriod
            displacement base patch coordinate first second +
          localLeviCivitaChristoffelApply period hPeriod metric patch coordinate
            (normalGraphHolonomicSourceFirstDerivativeCoordinatesAt period
              hPeriod displacement base patch coordinate first)
            (normalGraphHolonomicSourceFirstDerivativeCoordinatesAt period
              hPeriod displacement base patch coordinate second))
    at hGaussWeingarten
  unfold
    normalGraphCanonicalHolonomicLocalSectionRawExtrinsicCurvatureCoordinates
    normalGraphCanonicalHolonomicGaussRawExtrinsicCurvatureCoordinatesAt
    normalGraphCanonicalHolonomicCovariantAccelerationCoordinatesAt
  dsimp only
  rw [normalGraphHolonomicCoordinateGerm_base period hPeriod displacement base
    patch coordinate hGraph]
  rw [normalGraphCanonicalHolonomicLocalSectionNormalCoordinates_base_eq period
    hPeriod metric displacement parameter hNonNull boundary patch coordinate hAt]
  rw [← normalGraphHolonomicSourceFirstDerivativeCoordinatesAt_eq_family period
    hPeriod displacement base patch coordinate hGraph]
  exact hGaussWeingarten

/-- The symmetric local-section matrix is the canonical Gauss matrix at its
anchor. -/
theorem normalGraphCanonicalHolonomicLocalSectionExtrinsicCurvatureMatrix_base_eq_gauss
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : OrientationBoundary period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter)) :
    let base : EffectiveThroat period hPeriod × Real :=
      (orientationDoubleToThroat period hPeriod boundary, parameter)
    normalGraphCanonicalHolonomicLocalSectionExtrinsicCurvatureMatrix period
        hPeriod metric displacement boundary parameter patch coordinate base =
      normalGraphCanonicalHolonomicGaussExtrinsicCurvatureMatrixAt period hPeriod
        metric displacement parameter hNonNull boundary patch coordinate hAt := by
  dsimp only
  ext row column
  unfold normalGraphCanonicalHolonomicLocalSectionExtrinsicCurvatureMatrix
    normalGraphCanonicalHolonomicGaussExtrinsicCurvatureMatrixAt
    normalGraphCanonicalHolonomicGaussExtrinsicCurvatureCoordinatesAt
  rw [normalGraphCanonicalHolonomicLocalSectionRawExtrinsicCurvatureCoordinates_base_eq_gauss
      period hPeriod metric displacement parameter hNonNull boundary patch
        coordinate hAt,
    normalGraphCanonicalHolonomicLocalSectionRawExtrinsicCurvatureCoordinates_base_eq_gauss
      period hPeriod metric displacement parameter hNonNull boundary patch
        coordinate hAt]

/-- The jointly smooth local-section contraction has the exact chart-free
Gauss mean-curvature value at its anchor. -/
theorem normalGraphCanonicalHolonomicLocalSectionMeanCurvatureFamily_base_eq_gauss
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : OrientationBoundary period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter)) :
    let base : EffectiveThroat period hPeriod × Real :=
      (orientationDoubleToThroat period hPeriod boundary, parameter)
    normalGraphCanonicalHolonomicLocalSectionMeanCurvatureFamily period hPeriod
        metric displacement boundary parameter patch coordinate base =
      normalGraphCanonicalGaussMeanCurvature period hPeriod metric displacement
        parameter hNonNull boundary := by
  dsimp only
  rw [normalGraphCanonicalHolonomicLocalSectionMeanCurvatureFamily,
    normalGraphInducedInverseMatrixFamily_base,
    normalGraphCanonicalHolonomicLocalSectionExtrinsicCurvatureMatrix_base_eq_gauss]
  unfold normalGraphCanonicalGaussMeanCurvature
  exact normalGraphCanonicalHolonomicGaussMeanCurvatureAt_chart_independent
    period hPeriod metric displacement parameter hNonNull boundary patch
      (normalGraphCanonicalSelectedHolonomicPatchAt period hPeriod
        (normalGraphOrientationDouble period hPeriod displacement
          (boundary, parameter)))
      coordinate
      (normalGraphCanonicalSelectedHolonomicCoordinateAt period hPeriod
        (normalGraphOrientationDouble period hPeriod displacement
          (boundary, parameter)))
      hAt
      (normalGraphCanonicalSelectedHolonomicPatchAt_map period hPeriod
        (normalGraphOrientationDouble period hPeriod displacement
          (boundary, parameter)))

/-- On one admissible neighborhood, the fixed smooth local representative is
the same physical representative reanchored at every moving graph point. -/
theorem normalGraphCanonicalHolonomicLocalSectionMeanCurvatureFamily_eventually_eq_reanchored
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : OrientationBoundary period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : HolonomicVector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter)) :
    let base : EffectiveThroat period hPeriod × Real :=
      (orientationDoubleToThroat period hPeriod boundary, parameter)
    ∀ᶠ current in nhds base,
      NormalGraphNonNullAt period hPeriod metric displacement current.2 ∧
        (let currentBoundary :=
          normalGraphOrientationLocalSection period hPeriod boundary current.1
        let currentCoordinate :=
          normalGraphHolonomicCoordinateGerm period hPeriod displacement base
            patch coordinate current
        normalGraphCanonicalHolonomicLocalSectionMeanCurvatureFamily period
            hPeriod metric displacement boundary parameter patch coordinate
              current =
          normalGraphCanonicalHolonomicLocalSectionMeanCurvatureFamily period
            hPeriod metric displacement currentBoundary current.2 patch
              currentCoordinate current) := by
  dsimp only
  let base : EffectiveThroat period hPeriod × Real :=
    (orientationDoubleToThroat period hPeriod boundary, parameter)
  let tangentTrivialization :=
    trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) base.1
  let cotangentTrivialization :=
    trivializationAt (ThroatCoverCoordinates →L[Real] Real)
      (ThroatCotangentFiber period hPeriod) base.1
  have hGraph : patch.coordinateMap coordinate =
      normalGraph period hPeriod displacement base.2 base.1 := by
    simpa [base, normalGraphOrientationDouble] using hAt
  have hNonNullCurrent : ∀ᶠ current in nhds base,
      NormalGraphNonNullAt period hPeriod metric displacement current.2 :=
    continuous_snd.continuousAt.eventually
      ((normalGraphNonNullDomain_isOpen period hPeriod metric displacement)
        |>.mem_nhds hNonNull)
  have hFstTendsto : Tendsto Prod.fst (nhds base) (nhds base.1) :=
    continuous_fst.continuousAt
  have hSectionReconstruct :
      (fun current : EffectiveThroat period hPeriod × Real =>
        orientationDoubleToThroat period hPeriod
          (normalGraphOrientationLocalSection period hPeriod boundary current.1))
        =ᶠ[nhds base] Prod.fst := by
    change ((fun point => orientationDoubleToThroat period hPeriod
      (normalGraphOrientationLocalSection period hPeriod boundary point)) ∘
        Prod.fst) =ᶠ[nhds base] Prod.fst
    exact (normalGraphOrientationLocalSection_eventually_reconstructs period
      hPeriod boundary).comp_tendsto hFstTendsto
  have hGraphReanchor :=
    normalGraphHolonomicCoordinateGerm_eventuallyEq_reanchored period hPeriod
      displacement base patch coordinate hGraph
  have hNormalReanchor :=
    normalGraphCanonicalHolonomicLocalSectionNormalCoordinates_eventuallyEq_reanchored
      period hPeriod metric displacement parameter hNonNull boundary patch
        coordinate hAt
  have hFirstTangent : ∀ᶠ current in nhds base,
      current.1 ∈ tangentTrivialization.baseSet :=
    continuous_fst.continuousAt.eventually
      (tangentTrivialization.open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) base.1))
  have hFirstCotangent : ∀ᶠ current in nhds base,
      current.1 ∈ cotangentTrivialization.baseSet :=
    continuous_fst.continuousAt.eventually
      (cotangentTrivialization.open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt
          (ThroatCoverCoordinates →L[Real] Real)
          (ThroatCotangentFiber period hPeriod) base.1))
  filter_upwards [hNonNullCurrent, hSectionReconstruct,
    hGraphReanchor, hNormalReanchor, hFirstTangent,
      hFirstCotangent] with current hCurrentNonNull hProjection hGraphGerm
        hNormalGerm hFirstTangentAt hFirstCotangentAt
  constructor
  · exact hCurrentNonNull
  · let currentBoundary :=
      normalGraphOrientationLocalSection period hPeriod boundary current.1
    let currentCoordinate :=
      normalGraphHolonomicCoordinateGerm period hPeriod displacement base patch
        coordinate current
    let currentBase : EffectiveThroat period hPeriod × Real :=
      (orientationDoubleToThroat period hPeriod currentBoundary, current.2)
    have hCurrentProjection :
        orientationDoubleToThroat period hPeriod currentBoundary = current.1 := by
      simpa [currentBoundary] using hProjection
    have hCurrentBase : currentBase = current := by
      exact Prod.ext hCurrentProjection rfl
    have hSecondTangent : current.1 ∈
        (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod)
            (orientationDoubleToThroat period hPeriod currentBoundary)).baseSet := by
      rw [hCurrentProjection]
      exact mem_baseSet_trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) current.1
    have hSecondCotangent : current.1 ∈
        (trivializationAt (ThroatCoverCoordinates →L[Real] Real)
          (ThroatCotangentFiber period hPeriod)
            (orientationDoubleToThroat period hPeriod currentBoundary)).baseSet := by
      rw [hCurrentProjection]
      exact mem_baseSet_trivializationAt
        (ThroatCoverCoordinates →L[Real] Real)
        (ThroatCotangentFiber period hPeriod) current.1
    have hGraphGermDynamic :
        normalGraphHolonomicCoordinateGerm period hPeriod displacement base patch
            coordinate =ᶠ[nhds current]
          normalGraphHolonomicCoordinateGerm period hPeriod displacement
            currentBase patch currentCoordinate := by
      rw [hCurrentBase]
      simpa [currentCoordinate] using hGraphGerm
    have hNaturality :=
      normalGraphCanonicalHolonomicLocalSectionMeanCurvatureFamily_natural_of_eventuallyEq
        period hPeriod metric displacement boundary currentBoundary parameter
          current.2 current hCurrentNonNull patch coordinate
            currentCoordinate hFirstTangentAt hSecondTangent hFirstCotangentAt
              hSecondCotangent hGraphGermDynamic hNormalGerm
    exact hNaturality.symm

/-- P2 foundation certificate: the graph is jointly smooth, has the already
proved physical normal velocity, induces the actual ambient metric, and its
non-null domain contains the base point. -/
theorem normal_boundary_induced_metric_foundation_gate
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (hTransverse : HasNoTangentialRadical period hPeriod metric) :
    ContMDiff
        (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
        coverModelWithCorners ∞
        (fun point : EffectiveThroat period hPeriod × Real =>
          normalGraph period hPeriod displacement point.2 point.1) ∧
      0 ∈ normalGraphNonNullDomain period hPeriod metric displacement :=
  ⟨normalGraph_joint_contMDiff period hPeriod displacement,
    zero_mem_normalGraphNonNullDomain period hPeriod metric displacement
      hTransverse⟩

/-- Current P2 local-family certificate: the induced metric varies jointly
smoothly on a genuine open admissible parameter domain containing zero. -/
theorem normal_boundary_induced_metric_local_family_gate
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (hTransverse : HasNoTangentialRadical period hPeriod metric) :
    ContMDiff
        (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
        (throatCoverModelWithCorners.prod
          𝓘(Real, ThroatCovariantTwoTensorModel)) ∞
        (fun current : EffectiveThroat period hPeriod × Real =>
          TotalSpace.mk' ThroatCovariantTwoTensorModel
            (E := ThroatCovariantTwoTensorFiber period hPeriod) current.1
            (normalGraphInducedMetricValue period hPeriod metric displacement
              current.2 current.1)) ∧
      IsOpen (normalGraphNonNullDomain period hPeriod metric displacement) ∧
      0 ∈ normalGraphNonNullDomain period hPeriod metric displacement :=
  ⟨normalGraphInducedMetricValue_joint_contMDiff period hPeriod metric
      displacement,
    normalGraphNonNullDomain_isOpen period hPeriod metric displacement,
    zero_mem_normalGraphNonNullDomain period hPeriod metric displacement
      hTransverse⟩

/-! ## Joint completed functional domain for the mobile boundary -/

/-- The mobile boundary uses the boundary-enhanced metric core together with
the already constructed completed normal `C²` core. -/
abbrev CandidateANormalBoundaryFunctionalCore
    (metric : RegularGeneralLorentzMetric period hPeriod) :=
  RegularGeneralMetricBoundaryC3Core period hPeriod metric ×
    NormalBoundaryC2JetCore period hPeriod

@[implicit_reducible]
def candidateANormalBoundaryFunctionalCoreNormedAddCommGroup
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedAddCommGroup
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) := by
  letI : NormedAddCommGroup
      (RegularGeneralMetricBoundaryC3Core period hPeriod metric) :=
    regularGeneralMetricBoundaryC3CoreNormedAddCommGroup
      period hPeriod metric
  letI : NormedAddCommGroup (NormalBoundaryC2JetCore period hPeriod) :=
    (normalBoundaryC2JetCoreSubmodule period hPeriod).normedAddCommGroup
  infer_instance

local instance candidateANormalBoundaryFunctionalCoreNormedAddCommGroupInstance
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedAddCommGroup
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreNormedAddCommGroup
    period hPeriod metric

@[implicit_reducible]
def candidateANormalBoundaryFunctionalCoreNormedSpace
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) := by
  letI : NormedAddCommGroup
      (RegularGeneralMetricBoundaryC3Core period hPeriod metric) :=
    regularGeneralMetricBoundaryC3CoreNormedAddCommGroup
      period hPeriod metric
  letI : NormedSpace Real
      (RegularGeneralMetricBoundaryC3Core period hPeriod metric) :=
    regularGeneralMetricBoundaryC3CoreNormedSpace period hPeriod metric
  letI : NormedAddCommGroup (NormalBoundaryC2JetCore period hPeriod) :=
    (normalBoundaryC2JetCoreSubmodule period hPeriod).normedAddCommGroup
  letI : NormedSpace Real (NormalBoundaryC2JetCore period hPeriod) :=
    Submodule.normedSpace (normalBoundaryC2JetCoreSubmodule period hPeriod)
  infer_instance

local instance candidateANormalBoundaryFunctionalCoreNormedSpaceInstance
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreNormedSpace period hPeriod metric

@[implicit_reducible]
def candidateANormalBoundaryFunctionalCoreCompleteSpace
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    CompleteSpace
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) := by
  letI : NormedAddCommGroup
      (RegularGeneralMetricBoundaryC3Core period hPeriod metric) :=
    regularGeneralMetricBoundaryC3CoreNormedAddCommGroup
      period hPeriod metric
  letI : NormedSpace Real
      (RegularGeneralMetricBoundaryC3Core period hPeriod metric) :=
    regularGeneralMetricBoundaryC3CoreNormedSpace period hPeriod metric
  letI : CompleteSpace
      (RegularGeneralMetricBoundaryC3Core period hPeriod metric) :=
    regularGeneralMetricBoundaryC3CoreCompleteSpace period hPeriod metric
  letI : NormedAddCommGroup (NormalBoundaryC2JetCore period hPeriod) :=
    (normalBoundaryC2JetCoreSubmodule period hPeriod).normedAddCommGroup
  letI : NormedSpace Real (NormalBoundaryC2JetCore period hPeriod) :=
    Submodule.normedSpace (normalBoundaryC2JetCoreSubmodule period hPeriod)
  letI : CompleteSpace (NormalBoundaryC2JetCore period hPeriod) :=
    normalBoundaryC2JetCoreCompleteSpace period hPeriod
  infer_instance

/-- Faithful joint lift of the genuine smooth metric and normal variations. -/
def smoothToCandidateANormalBoundaryFunctionalCore
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    (SmoothSymmetricCovariantTwoTensor period hPeriod ×
      SmoothNormalDisplacement period hPeriod) →ₗ[Real]
      CandidateANormalBoundaryFunctionalCore period hPeriod metric where
  toFun variation :=
    (smoothToRegularGeneralMetricBoundaryC3Core period hPeriod metric
        variation.1,
      smoothNormalDisplacementToBoundaryC2JetCore period hPeriod variation.2)
  map_add' first second := by
    apply Prod.ext
    · exact (smoothToRegularGeneralMetricBoundaryC3Core
        period hPeriod metric).map_add first.1 second.1
    · exact (smoothNormalDisplacementToBoundaryC2JetCore
        period hPeriod).map_add first.2 second.2
  map_smul' scalar variation := by
    apply Prod.ext
    · exact (smoothToRegularGeneralMetricBoundaryC3Core
        period hPeriod metric).map_smul scalar variation.1
    · exact (smoothNormalDisplacementToBoundaryC2JetCore
        period hPeriod).map_smul scalar variation.2

theorem smoothToCandidateANormalBoundaryFunctionalCore_injective
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    Function.Injective
      (smoothToCandidateANormalBoundaryFunctionalCore
        period hPeriod metric) := by
  intro first second hEqual
  apply Prod.ext
  · apply smoothToRegularGeneralMetricBoundaryC3Core_injective
      period hPeriod metric
    exact congrArg Prod.fst hEqual
  · apply smoothNormalDisplacementToBoundaryC2JetCore_injective
      period hPeriod
    exact congrArg Prod.snd hEqual

theorem smoothToCandidateANormalBoundaryFunctionalCore_denseRange
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    DenseRange
      (smoothToCandidateANormalBoundaryFunctionalCore
        period hPeriod metric) := by
  change DenseRange (Prod.map
    (smoothToRegularGeneralMetricBoundaryC3Core period hPeriod metric)
    (smoothNormalDisplacementToBoundaryC2JetCore period hPeriod))
  exact (smoothToRegularGeneralMetricBoundaryC3Core_denseRange
    period hPeriod metric).prodMap
    (smoothNormalDisplacementToBoundaryC2JetCore_denseRange
      period hPeriod)

/-! ### The existing metric jets evaluated on the completed moving graph -/

/-- The joint chart retains exactly the existing admissible metric domain;
the completed normal direction adds no independent metric condition. -/
def candidateANormalBoundaryMetricDomain
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    Set (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  Prod.fst ⁻¹'
    regularGeneralMetricBoundaryC3Domain period hPeriod metric

theorem candidateANormalBoundaryMetricDomain_isOpen
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    IsOpen (candidateANormalBoundaryMetricDomain period hPeriod metric) :=
  (regularGeneralMetricBoundaryC3Domain_isOpen period hPeriod metric).preimage
    continuous_fst

theorem zero_mem_candidateANormalBoundaryMetricDomain
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    (0 : CandidateANormalBoundaryFunctionalCore period hPeriod metric) ∈
      candidateANormalBoundaryMetricDomain period hPeriod metric :=
  zero_mem_regularGeneralMetricBoundaryC3Domain period hPeriod metric

private def candidateANormalBoundaryMetricGraphInput
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (current :
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric × Real) ×
        OrientationBoundary period hPeriod) :
    RegularGeneralMetricBoundaryC3Core period hPeriod metric ×
      EffectiveQuotient period hPeriod :=
  (current.1.1.1,
    normalBoundaryC2Graph period hPeriod current.1.1.2 current.1.2 current.2)

private theorem candidateANormalBoundaryMetricGraphInput_continuous
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    Continuous (candidateANormalBoundaryMetricGraphInput
      period hPeriod metric) := by
  have hMetric : Continuous (fun current :
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric × Real) ×
        OrientationBoundary period hPeriod => current.1.1.1) :=
    continuous_fst.comp (continuous_fst.comp continuous_fst)
  have hNormal : Continuous (fun current :
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric × Real) ×
        OrientationBoundary period hPeriod => current.1.1.2) :=
    continuous_snd.comp (continuous_fst.comp continuous_fst)
  have hParameter : Continuous (fun current :
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric × Real) ×
        OrientationBoundary period hPeriod => current.1.2) :=
    continuous_snd.comp continuous_fst
  have hBoundary : Continuous (fun current :
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric × Real) ×
        OrientationBoundary period hPeriod => current.2) :=
    continuous_snd
  have hGraph :=
    (normalBoundaryC2Graph_joint_continuous period hPeriod).comp
      ((hNormal.prodMk hParameter).prodMk hBoundary)
  exact hMetric.prodMk hGraph

/-- One completed relative-metric coefficient evaluated at the same completed
normal graph used by the physical boundary. -/
def candidateANormalBoundaryRelativeMetricEntryAtGraph
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (row column : Fin 4)
    (variation : CandidateANormalBoundaryFunctionalCore period hPeriod metric)
    (parameter : Real) (boundary : OrientationBoundary period hPeriod) : Real :=
  regularGeneralMetricBoundaryC3RelativeEntryToContinuous period hPeriod
    metric row column variation.1
      (normalBoundaryC2Graph period hPeriod variation.2 parameter boundary)

theorem candidateANormalBoundaryRelativeMetricEntryAtGraph_joint_continuous
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (row column : Fin 4) :
    Continuous (fun current :
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric × Real) ×
        OrientationBoundary period hPeriod =>
      candidateANormalBoundaryRelativeMetricEntryAtGraph period hPeriod metric
        row column current.1.1 current.1.2 current.2) := by
  have hOuter : Continuous (fun current :
      RegularGeneralMetricBoundaryC3Core period hPeriod metric ×
        EffectiveQuotient period hPeriod =>
      regularGeneralMetricBoundaryC3RelativeEntryToContinuous period hPeriod
        metric row column current.1 current.2) :=
    regularGeneralMetricBoundaryC3RelativeEntry_joint_continuous period
      hPeriod metric row column
  have hComposed := hOuter.comp
    (candidateANormalBoundaryMetricGraphInput_continuous
      period hPeriod metric)
  apply hComposed.congr
  intro current
  rfl

@[simp]
theorem candidateANormalBoundaryRelativeMetricEntryAtGraph_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (row column : Fin 4) (parameter : Real)
    (boundary : OrientationBoundary period hPeriod) :
    candidateANormalBoundaryRelativeMetricEntryAtGraph period hPeriod metric
        row column
        (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement)) parameter boundary =
      regularGeneralMetricBoundaryC3RelativeEntryToContinuous period hPeriod
        metric row column
        (smoothToRegularGeneralMetricBoundaryC3Core
          period hPeriod metric tensor)
        (normalGraphOrientationDouble period hPeriod displacement
          (boundary, parameter)) := by
  unfold candidateANormalBoundaryRelativeMetricEntryAtGraph
    smoothToCandidateANormalBoundaryFunctionalCore
  change regularGeneralMetricBoundaryC3RelativeEntryToContinuous period hPeriod
      metric row column
      (smoothToRegularGeneralMetricBoundaryC3Core
        period hPeriod metric tensor)
      (normalBoundaryC2Graph period hPeriod
        (smoothNormalDisplacementToBoundaryC2JetCore
          period hPeriod displacement) parameter boundary) = _
  rw [normalBoundaryC2Graph_smooth]

/-- First physical-frame derivative of the same coefficient, evaluated on
the same completed graph. -/
def candidateANormalBoundaryRelativeMetricFirstEntryAtGraph
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (row column : Fin 4)
    (index : BoundaryMetricJetIndex period hPeriod)
    (variation : CandidateANormalBoundaryFunctionalCore period hPeriod metric)
    (parameter : Real) (boundary : OrientationBoundary period hPeriod) : Real :=
  regularGeneralMetricBoundaryC3RelativeFirstEntryToContinuous period hPeriod
    metric row column index variation.1
      (normalBoundaryC2Graph period hPeriod variation.2 parameter boundary)

theorem candidateANormalBoundaryRelativeMetricFirstEntryAtGraph_joint_continuous
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (row column : Fin 4)
    (index : BoundaryMetricJetIndex period hPeriod) :
    Continuous (fun current :
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric × Real) ×
        OrientationBoundary period hPeriod =>
      candidateANormalBoundaryRelativeMetricFirstEntryAtGraph period hPeriod
        metric row column index current.1.1 current.1.2 current.2) := by
  have hOuter : Continuous (fun current :
      RegularGeneralMetricBoundaryC3Core period hPeriod metric ×
        EffectiveQuotient period hPeriod =>
      regularGeneralMetricBoundaryC3RelativeFirstEntryToContinuous period
        hPeriod metric row column index current.1 current.2) :=
    regularGeneralMetricBoundaryC3RelativeFirstEntry_joint_continuous period
      hPeriod metric row column index
  have hComposed := hOuter.comp
    (candidateANormalBoundaryMetricGraphInput_continuous
      period hPeriod metric)
  apply hComposed.congr
  intro current
  rfl

@[simp]
theorem candidateANormalBoundaryRelativeMetricFirstEntryAtGraph_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (row column : Fin 4)
    (index : BoundaryMetricJetIndex period hPeriod)
    (parameter : Real) (boundary : OrientationBoundary period hPeriod) :
    candidateANormalBoundaryRelativeMetricFirstEntryAtGraph period hPeriod
        metric row column index
        (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement)) parameter boundary =
      regularGeneralMetricBoundaryC3RelativeFirstEntryToContinuous period
        hPeriod metric row column index
        (smoothToRegularGeneralMetricBoundaryC3Core
          period hPeriod metric tensor)
        (normalGraphOrientationDouble period hPeriod displacement
          (boundary, parameter)) := by
  unfold candidateANormalBoundaryRelativeMetricFirstEntryAtGraph
    smoothToCandidateANormalBoundaryFunctionalCore
  change regularGeneralMetricBoundaryC3RelativeFirstEntryToContinuous period
      hPeriod metric row column index
      (smoothToRegularGeneralMetricBoundaryC3Core
        period hPeriod metric tensor)
      (normalBoundaryC2Graph period hPeriod
        (smoothNormalDisplacementToBoundaryC2JetCore
          period hPeriod displacement) parameter boundary) = _
  rw [normalBoundaryC2Graph_smooth]

/-- Ordered second physical-frame derivative on the completed graph. -/
def candidateANormalBoundaryRelativeMetricSecondEntryAtGraph
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (row column : Fin 4)
    (outer inner : BoundaryMetricJetIndex period hPeriod)
    (variation : CandidateANormalBoundaryFunctionalCore period hPeriod metric)
    (parameter : Real) (boundary : OrientationBoundary period hPeriod) : Real :=
  regularGeneralMetricBoundaryC3RelativeSecondEntryToContinuous period hPeriod
    metric row column outer inner variation.1
      (normalBoundaryC2Graph period hPeriod variation.2 parameter boundary)

theorem candidateANormalBoundaryRelativeMetricSecondEntryAtGraph_joint_continuous
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (row column : Fin 4)
    (outer inner : BoundaryMetricJetIndex period hPeriod) :
    Continuous (fun current :
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric × Real) ×
        OrientationBoundary period hPeriod =>
      candidateANormalBoundaryRelativeMetricSecondEntryAtGraph period hPeriod
        metric row column outer inner current.1.1 current.1.2 current.2) := by
  have hOuter : Continuous (fun current :
      RegularGeneralMetricBoundaryC3Core period hPeriod metric ×
        EffectiveQuotient period hPeriod =>
      regularGeneralMetricBoundaryC3RelativeSecondEntryToContinuous period
        hPeriod metric row column outer inner current.1 current.2) :=
    regularGeneralMetricBoundaryC3RelativeSecondEntry_joint_continuous period
      hPeriod metric row column outer inner
  have hComposed := hOuter.comp
    (candidateANormalBoundaryMetricGraphInput_continuous
      period hPeriod metric)
  apply hComposed.congr
  intro current
  rfl

@[simp]
theorem candidateANormalBoundaryRelativeMetricSecondEntryAtGraph_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (row column : Fin 4)
    (outer inner : BoundaryMetricJetIndex period hPeriod)
    (parameter : Real) (boundary : OrientationBoundary period hPeriod) :
    candidateANormalBoundaryRelativeMetricSecondEntryAtGraph period hPeriod
        metric row column outer inner
        (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement)) parameter boundary =
      regularGeneralMetricBoundaryC3RelativeSecondEntryToContinuous period
        hPeriod metric row column outer inner
        (smoothToRegularGeneralMetricBoundaryC3Core
          period hPeriod metric tensor)
        (normalGraphOrientationDouble period hPeriod displacement
          (boundary, parameter)) := by
  unfold candidateANormalBoundaryRelativeMetricSecondEntryAtGraph
    smoothToCandidateANormalBoundaryFunctionalCore
  change regularGeneralMetricBoundaryC3RelativeSecondEntryToContinuous period
      hPeriod metric row column outer inner
      (smoothToRegularGeneralMetricBoundaryC3Core
        period hPeriod metric tensor)
      (normalBoundaryC2Graph period hPeriod
        (smoothNormalDisplacementToBoundaryC2JetCore
          period hPeriod displacement) parameter boundary) = _
  rw [normalBoundaryC2Graph_smooth]

/-- The additional third relative-metric jet evaluated on the completed graph. -/
def candidateANormalBoundaryRelativeMetricThirdJetAtGraph
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variation : CandidateANormalBoundaryFunctionalCore period hPeriod metric)
    (parameter : Real) (boundary : OrientationBoundary period hPeriod) :
    RegularMetricThirdJetFiber period hPeriod metric :=
  regularGeneralMetricBoundaryC3CoreToThirdJet period hPeriod metric variation.1
    (normalBoundaryC2Graph period hPeriod variation.2 parameter boundary)

theorem candidateANormalBoundaryRelativeMetricThirdJetAtGraph_joint_continuous
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    Continuous (fun current :
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric × Real) ×
        OrientationBoundary period hPeriod =>
      candidateANormalBoundaryRelativeMetricThirdJetAtGraph period hPeriod
        metric current.1.1 current.1.2 current.2) := by
  have hOuter : Continuous (fun current :
      RegularGeneralMetricBoundaryC3Core period hPeriod metric ×
        EffectiveQuotient period hPeriod =>
      regularGeneralMetricBoundaryC3CoreToThirdJet period hPeriod metric
        current.1 current.2) :=
    regularGeneralMetricBoundaryC3ThirdJet_joint_continuous period hPeriod
      metric
  have hComposed := hOuter.comp
    (candidateANormalBoundaryMetricGraphInput_continuous
      period hPeriod metric)
  apply hComposed.congr
  intro current
  rfl

@[simp]
theorem candidateANormalBoundaryRelativeMetricThirdJetAtGraph_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : OrientationBoundary period hPeriod) :
    candidateANormalBoundaryRelativeMetricThirdJetAtGraph period hPeriod metric
        (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement)) parameter boundary =
      smoothRegularGeneralMetricRelativeThirdJet period hPeriod metric tensor
        (normalGraphOrientationDouble period hPeriod displacement
          (boundary, parameter)) := by
  unfold candidateANormalBoundaryRelativeMetricThirdJetAtGraph
    smoothToCandidateANormalBoundaryFunctionalCore
  change regularGeneralMetricBoundaryC3CoreToThirdJet period hPeriod metric
      (smoothToRegularGeneralMetricBoundaryC3Core
        period hPeriod metric tensor)
      (normalBoundaryC2Graph period hPeriod
        (smoothNormalDisplacementToBoundaryC2JetCore
          period hPeriod displacement) parameter boundary) = _
  rw [normalBoundaryC2Graph_smooth]
  rfl

/-- P2 analytic-domain certificate: the joint core is faithful and dense,
and its strengthened metric component continuously reuses the bulk `C²`
chart while retaining the required third jet. -/
theorem normal_boundary_functional_core_gate
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    Function.Injective
        (smoothToCandidateANormalBoundaryFunctionalCore
          period hPeriod metric) ∧
      DenseRange
        (smoothToCandidateANormalBoundaryFunctionalCore
          period hPeriod metric) ∧
      Continuous
        (regularGeneralMetricBoundaryC3CoreToC2 period hPeriod metric) ∧
      Continuous
        (regularGeneralMetricBoundaryC3CoreToThirdJet
          period hPeriod metric) :=
  ⟨smoothToCandidateANormalBoundaryFunctionalCore_injective
      period hPeriod metric,
    smoothToCandidateANormalBoundaryFunctionalCore_denseRange
      period hPeriod metric,
    (regular_general_metric_boundary_c3_core_gate
      period hPeriod metric).2.2.1,
    (regular_general_metric_boundary_c3_core_gate
      period hPeriod metric).2.2.2⟩

end
end P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
end JanusFormal
