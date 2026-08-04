import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusBoundedFiberJetSubstitutionC2
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusBoundedFiberJet2SubstitutionC2
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
import Mathlib.Geometry.Manifold.Metrizable
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Fiber substitution bridge for the mobile Candidate-A boundary

This file instantiates only the analytic graph side of the bounded fiber-jet
substitution gate.  It reuses the completed normal `C²` core and the existing
orientation double; it introduces no boundary field or physical axiom.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 600000
set_option maxHeartbeats 1200000
noncomputable section

open scoped BoundedContinuousFunction ContDiff Manifold Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixInverse4D
open P0EFTJanusMappingTorusCanonicalNormalLiftContinuityReduction4D
open P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionWinding4D
open P0EFTJanusMappingTorusOrientationDoubleCover
open P0EFTJanusMappingTorusCutThroatBoundaryDoubleCover4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusNormalBundleOrientationCover
open P0EFTJanusD8NormalBundleD9DisplacementBridge4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusProgramPGeneralMetricPositiveDualizer4D
open P0EFTJanusProgramPGeneralMetricC2RelativeEndomorphism4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPGeneralMetricC2VolumeDensity4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryC3MetricCore4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusBoundedFiberJetSubstitutionC2
open P0EFTJanusBoundedFiberJet2SubstitutionC2

private abbrev RealHasDerivAt
    (function : Real → Real) (derivative point : Real) : Prop :=
  @HasDerivAt Real _ Real Real.normedAddCommGroup.toAddCommGroup
    RCLike.toInnerProductSpaceReal.toModule _ _ function derivative point

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev OrientationBoundary :=
  CutThroatBoundary period hPeriod

private abbrev OrientationBoundaryCover :=
  MappingTorusCover (orientationDoubleData period hPeriod)

private abbrev EffectiveThroatCover :=
  MappingTorusCover (fixedEquatorData period hPeriod)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance orientationBoundaryCompactSpace :
    CompactSpace (OrientationBoundary period hPeriod) :=
  P0EFTJanusMappingTorusCompactQuotient.fixedThroatQuotientCompactSpace
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)

local instance (priority := 30000) orientationBoundaryChartedSpace :
    ChartedSpace ThroatCoverModel (OrientationBoundary period hPeriod) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryChartedSpace
    period hPeriod

local instance (priority := 30000) orientationBoundaryIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (OrientationBoundary period hPeriod) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryIsManifold
    period hPeriod

/-- A compatible metric presentation of the already compact Hausdorff
finite-dimensional boundary manifold, used only for uniform-continuity
estimates in the derivative-optimal fiber substitution helper. -/
local instance orientationBoundaryMetrizableSpace :
    TopologicalSpace.MetrizableSpace (OrientationBoundary period hPeriod) :=
  Manifold.metrizableSpace throatCoverModelWithCorners _

local instance orientationBoundaryMetricSpace :
    MetricSpace (OrientationBoundary period hPeriod) :=
  TopologicalSpace.metrizableSpaceMetric _

local instance orientationBoundaryJet2ExplicitAddCommGroup :
    AddCommGroup
      (P0EFTJanusBoundedFiberJet2SubstitutionC2.Jet2
        (OrientationBoundary period hPeriod)) :=
  inferInstanceAs
    (AddCommGroup
      (P0EFTJanusBoundedFiberJet2SubstitutionC2.jet2Submodule
        (OrientationBoundary period hPeriod)))

local instance orientationBoundaryJet2ExplicitNormedAddCommGroup :
    NormedAddCommGroup
      (P0EFTJanusBoundedFiberJet2SubstitutionC2.Jet2
        (OrientationBoundary period hPeriod)) :=
  inferInstanceAs
    (NormedAddCommGroup
      (P0EFTJanusBoundedFiberJet2SubstitutionC2.jet2Submodule
        (OrientationBoundary period hPeriod)))

local instance orientationBoundaryJet2ExplicitNormedSpace :
    NormedSpace Real
      (P0EFTJanusBoundedFiberJet2SubstitutionC2.Jet2
        (OrientationBoundary period hPeriod)) :=
  inferInstanceAs
    (NormedSpace Real
      (P0EFTJanusBoundedFiberJet2SubstitutionC2.jet2Submodule
        (OrientationBoundary period hPeriod)))

local instance (priority := 30000) orientationBoundaryCoverChartedSpace :
    ChartedSpace ThroatCoverModel
      (OrientationBoundaryCover period hPeriod) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryCoverChartedSpace
    period hPeriod

local instance (priority := 30000) orientationBoundaryCoverIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (OrientationBoundaryCover period hPeriod) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryCoverIsManifold
    period hPeriod

local instance (priority := 30000) effectiveThroatCoverChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroatCover period hPeriod) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.effectiveThroatCoverChartedSpace
    period hPeriod

local instance (priority := 30000) effectiveThroatCoverIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroatCover period hPeriod) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.effectiveThroatCoverIsManifold
    period hPeriod

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/- The normal core is a closed subspace of a sup-normed continuous-map
space.  These local aliases select that normed structure uniformly for
Frechet calculus and remove the harmless subtype-instance diamond. -/
private abbrev normalCoreNormedAddCommGroup :
    NormedAddCommGroup (NormalBoundaryC2JetCore period hPeriod) :=
  inferInstance

private abbrev normalCoreNormedSpace :
    NormedSpace Real (NormalBoundaryC2JetCore period hPeriod) :=
  inferInstance

local instance normalCoreTopologicalSpace :
    TopologicalSpace (NormalBoundaryC2JetCore period hPeriod) :=
  (normalCoreNormedAddCommGroup period hPeriod).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

local instance normalCoreAddCommGroup :
    AddCommGroup (NormalBoundaryC2JetCore period hPeriod) :=
  (normalCoreNormedAddCommGroup period hPeriod).toAddCommGroup

local instance normalCoreAddCommMonoid :
    AddCommMonoid (NormalBoundaryC2JetCore period hPeriod) :=
  (normalCoreNormedAddCommGroup period hPeriod).toAddCommGroup.toAddCommMonoid

local instance normalCoreModule :
    Module Real (NormalBoundaryC2JetCore period hPeriod) :=
  (normalCoreNormedSpace period hPeriod).toModule

local instance regularMetricBoundaryC3CoreNormedAddCommGroup
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedAddCommGroup
      (RegularGeneralMetricBoundaryC3Core period hPeriod metric) :=
  regularGeneralMetricBoundaryC3CoreNormedAddCommGroup
    period hPeriod metric

local instance regularMetricBoundaryC3CoreNormedSpace
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (RegularGeneralMetricBoundaryC3Core period hPeriod metric) :=
  regularGeneralMetricBoundaryC3CoreNormedSpace period hPeriod metric

local instance regularMetricBoundaryC3CoreCompleteSpace
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    CompleteSpace
      (RegularGeneralMetricBoundaryC3Core period hPeriod metric) :=
  regularGeneralMetricBoundaryC3CoreCompleteSpace period hPeriod metric

local instance regularMetricBoundaryC3CoreTopologicalSpace
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    TopologicalSpace
      (RegularGeneralMetricBoundaryC3Core period hPeriod metric) :=
  (regularMetricBoundaryC3CoreNormedAddCommGroup
    period hPeriod metric).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

local instance regularMetricBoundaryC3CoreAddCommMonoid
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    AddCommMonoid
      (RegularGeneralMetricBoundaryC3Core period hPeriod metric) :=
  (regularMetricBoundaryC3CoreNormedAddCommGroup
    period hPeriod metric).toAddCommGroup.toAddCommMonoid

local instance regularMetricBoundaryC3CoreModule
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    Module Real
      (RegularGeneralMetricBoundaryC3Core period hPeriod metric) :=
  (regularMetricBoundaryC3CoreNormedSpace period hPeriod metric).toModule

local instance boundedFiberJet3NormedAddCommGroup :
    NormedAddCommGroup
      (BoundedFiberJet3 (OrientationBoundary period hPeriod)) :=
  (boundedFiberJet3Submodule
    (OrientationBoundary period hPeriod)).normedAddCommGroup

local instance boundedFiberJet3NormedSpace :
    NormedSpace Real
      (BoundedFiberJet3 (OrientationBoundary period hPeriod)) :=
  Submodule.normedSpace
    (boundedFiberJet3Submodule (OrientationBoundary period hPeriod))

local instance boundedFiberJet3TopologicalSpace :
    TopologicalSpace
      (BoundedFiberJet3 (OrientationBoundary period hPeriod)) :=
  (boundedFiberJet3NormedAddCommGroup
    period hPeriod).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

local instance boundedFiberJet3AddCommMonoid :
    AddCommMonoid
      (BoundedFiberJet3 (OrientationBoundary period hPeriod)) :=
  (boundedFiberJet3NormedAddCommGroup
    period hPeriod).toAddCommGroup.toAddCommMonoid

local instance boundedFiberJet3Module :
    Module Real
      (BoundedFiberJet3 (OrientationBoundary period hPeriod)) :=
  (boundedFiberJet3NormedSpace period hPeriod).toModule

/-- The existing canonical latitude collar, with an unrestricted raw fiber
coordinate compressed by `arctan`, on the orientation-double cover. -/
def normalBoundaryRawFiberPointCover
    (current : OrientationBoundaryCover period hPeriod × Real) :
    EffectiveQuotient period hPeriod :=
  canonicalLatitudeCollarMap period hPeriod
    (normalGraphCanonicalLatitudeBaseCover period hPeriod current.1,
      Real.arctan current.2)

theorem normalBoundaryRawFiberPointCover_eq
    (point : OrientationBoundaryCover period hPeriod) (fiber : Real) :
    normalBoundaryRawFiberPointCover period hPeriod (point, fiber) =
      quotientNormalLatitude period hPeriod
        (orientationDoubleCoverHomeomorph period hPeriod point)
        (Real.arctan fiber) := by
  unfold normalBoundaryRawFiberPointCover canonicalLatitudeCollarMap
  rw [canonicalLatitudeAnchor_baseCover period hPeriod point]

theorem normalGraphCanonicalLatitudeBaseCover_continuous :
    Continuous (normalGraphCanonicalLatitudeBaseCover period hPeriod) := by
  have hAnchor :=
    (orientationDoubleCoverHomeomorph period hPeriod).continuous
  exact
    (equatorialTwoSphereHomeomorph.continuous.comp
      ((continuous_fiber _).comp hAnchor)).prodMk
        ((continuous_time _).comp hAnchor)

theorem normalGraphCanonicalLatitudeBaseCover_contMDiff :
    ContMDiff throatCoverModelWithCorners
      canonicalLatitudeBaseModelWithCorners ∞
      (normalGraphCanonicalLatitudeBaseCover period hPeriod) := by
  have hAnchor : ContMDiff throatCoverModelWithCorners
      throatCoverModelWithCorners ∞
      (orientationDoubleCoverHomeomorph period hPeriod) :=
    orientationDoubleCoverHomeomorph_contMDiff period hPeriod
  have hCoordinates : ContMDiff throatCoverModelWithCorners
      throatCoverModelWithCorners ∞
      (fun point : OrientationBoundaryCover period hPeriod =>
        coverHomeomorphProd (fixedEquatorData period hPeriod)
          (orientationDoubleCoverHomeomorph period hPeriod point)) :=
    (chartedSpacePullback_toFun_contMDiff throatCoverModelWithCorners ∞
      (coverHomeomorphProd (fixedEquatorData period hPeriod))).comp hAnchor
  have hSphere : ContMDiff throatCoverModelWithCorners
      (modelWithCornersSelf Real (EuclideanSpace Real (Fin 2))) ∞
      (fun point : OrientationBoundaryCover period hPeriod =>
        (orientationDoubleCoverHomeomorph period hPeriod point).fiber) :=
    contMDiff_fst.comp hCoordinates
  have hTime : ContMDiff throatCoverModelWithCorners
      (modelWithCornersSelf Real Real) ∞
      (fun point : OrientationBoundaryCover period hPeriod =>
        (orientationDoubleCoverHomeomorph period hPeriod point).time) :=
    contMDiff_snd.comp hCoordinates
  have hStandardSphere : ContMDiff throatCoverModelWithCorners
      (modelWithCornersSelf Real (EuclideanSpace Real (Fin 2))) ∞
      (fun point : OrientationBoundaryCover period hPeriod =>
        equatorialTwoSphereHomeomorph
          (orientationDoubleCoverHomeomorph period hPeriod point).fiber) :=
    (chartedSpacePullback_toFun_contMDiff
      (modelWithCornersSelf Real (EuclideanSpace Real (Fin 2))) ∞
      equatorialTwoSphereHomeomorph).comp hSphere
  exact hStandardSphere.prodMk hTime

theorem normalBoundaryRawFiberPointCover_continuous :
    Continuous (normalBoundaryRawFiberPointCover period hPeriod) := by
  exact (canonicalLatitudeCollarMap_continuous period hPeriod).comp
    (((normalGraphCanonicalLatitudeBaseCover_continuous period hPeriod).comp
        continuous_fst).prodMk
      (Real.continuous_arctan.comp continuous_snd))

theorem normalBoundaryRawFiberPointCover_invariant
    (winding : Int) (point : OrientationBoundaryCover period hPeriod)
    (fiber : Real) :
    normalBoundaryRawFiberPointCover period hPeriod (winding +ᵥ point, fiber) =
      normalBoundaryRawFiberPointCover period hPeriod (point, fiber) := by
  rw [normalBoundaryRawFiberPointCover_eq,
    normalBoundaryRawFiberPointCover_eq,
    orientationDoubleCover_even_equivariant,
    quotientNormalLatitude_deck_winding]
  have hSign :
      (normalSignRepresentation (2 * winding) : Real) = 1 := by
    simpa using congrArg (fun unit : Realˣ => (unit : Real))
      (pulledBack_normal_sign_trivial winding)
  rw [hSign, one_mul]

/-- The raw collar descends to the completed orientation boundary without a
choice of representative. -/
def normalBoundaryRawFiberPoint
    (boundary : OrientationBoundary period hPeriod) (fiber : Real) :
    EffectiveQuotient period hPeriod :=
  Quotient.lift
    (fun point => normalBoundaryRawFiberPointCover period hPeriod (point, fiber))
    (fun first second hOrbit => by
      change AddAction.orbitRel Int (OrientationBoundaryCover period hPeriod)
        first second at hOrbit
      rw [AddAction.orbitRel_apply, AddAction.mem_orbit_iff] at hOrbit
      rcases hOrbit with ⟨winding, hWinding⟩
      rw [← hWinding]
      exact normalBoundaryRawFiberPointCover_invariant
        period hPeriod winding second fiber)
    boundary

@[simp]
theorem normalBoundaryRawFiberPoint_mk
    (point : OrientationBoundaryCover period hPeriod) (fiber : Real) :
    normalBoundaryRawFiberPoint period hPeriod
        (mappingTorusMk (orientationDoubleData period hPeriod) point) fiber =
      normalBoundaryRawFiberPointCover period hPeriod (point, fiber) :=
  rfl

theorem normalBoundaryRawFiberPoint_joint_continuous :
    Continuous (fun current : OrientationBoundary period hPeriod × Real =>
      normalBoundaryRawFiberPoint period hPeriod current.1 current.2) := by
  have hBoundary :=
    (mappingTorusMk_isAddQuotientCoveringMap
      (orientationDoubleData period hPeriod)).isOpenQuotientMap
  have hFiber : IsOpenQuotientMap (id : Real → Real) :=
    IsOpenQuotientMap.id
  have hProduct := hBoundary.prodMap hFiber
  apply hProduct.continuous_comp_iff.mp
  apply (normalBoundaryRawFiberPointCover_continuous
    period hPeriod).congr
  intro current
  simp only [Function.comp_apply, Prod.map_apply, id_eq]
  exact (normalBoundaryRawFiberPoint_mk period hPeriod
    current.1 current.2).symm

/-- The same canonical collar parametrized by its actual latitude coordinate,
before inserting the completed normal graph. -/
def normalBoundaryLatitudeFiberPointCover
    (current : OrientationBoundaryCover period hPeriod × Real) :
    EffectiveQuotient period hPeriod :=
  canonicalLatitudeCollarMap period hPeriod
    (normalGraphCanonicalLatitudeBaseCover period hPeriod current.1,
      current.2)

theorem normalBoundaryLatitudeFiberPointCover_eq
    (point : OrientationBoundaryCover period hPeriod) (latitude : Real) :
    normalBoundaryLatitudeFiberPointCover period hPeriod (point, latitude) =
      quotientNormalLatitude period hPeriod
        (orientationDoubleCoverHomeomorph period hPeriod point) latitude := by
  unfold normalBoundaryLatitudeFiberPointCover canonicalLatitudeCollarMap
  rw [canonicalLatitudeAnchor_baseCover period hPeriod point]

theorem normalBoundaryLatitudeFiberPointCover_continuous :
    Continuous (normalBoundaryLatitudeFiberPointCover period hPeriod) := by
  exact (canonicalLatitudeCollarMap_continuous period hPeriod).comp
    (((normalGraphCanonicalLatitudeBaseCover_continuous period hPeriod).comp
        continuous_fst).prodMk continuous_snd)

theorem normalBoundaryLatitudeFiberPointCover_contMDiff :
    ContMDiff
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      coverModelWithCorners ∞
      (normalBoundaryLatitudeFiberPointCover period hPeriod) := by
  exact (canonicalLatitudeCollar_contMDiff period hPeriod).comp
    (((normalGraphCanonicalLatitudeBaseCover_contMDiff
      period hPeriod).comp contMDiff_fst).prodMk contMDiff_snd)

theorem normalBoundaryLatitudeFiberPointCover_invariant
    (winding : Int) (point : OrientationBoundaryCover period hPeriod)
    (latitude : Real) :
    normalBoundaryLatitudeFiberPointCover period hPeriod
        (winding +ᵥ point, latitude) =
      normalBoundaryLatitudeFiberPointCover period hPeriod
        (point, latitude) := by
  rw [normalBoundaryLatitudeFiberPointCover_eq,
    normalBoundaryLatitudeFiberPointCover_eq,
    orientationDoubleCover_even_equivariant,
    quotientNormalLatitude_deck_winding]
  have hSign :
      (normalSignRepresentation (2 * winding) : Real) = 1 := by
    simpa using congrArg (fun unit : Realˣ => (unit : Real))
      (pulledBack_normal_sign_trivial winding)
  rw [hSign, one_mul]

def normalBoundaryLatitudeFiberPoint
    (boundary : OrientationBoundary period hPeriod) (latitude : Real) :
    EffectiveQuotient period hPeriod :=
  Quotient.lift
    (fun point =>
      normalBoundaryLatitudeFiberPointCover period hPeriod (point, latitude))
    (fun first second hOrbit => by
      change AddAction.orbitRel Int (OrientationBoundaryCover period hPeriod)
        first second at hOrbit
      rw [AddAction.orbitRel_apply, AddAction.mem_orbit_iff] at hOrbit
      rcases hOrbit with ⟨winding, hWinding⟩
      rw [← hWinding]
      exact normalBoundaryLatitudeFiberPointCover_invariant
        period hPeriod winding second latitude)
    boundary

@[simp]
theorem normalBoundaryLatitudeFiberPoint_mk
    (point : OrientationBoundaryCover period hPeriod) (latitude : Real) :
    normalBoundaryLatitudeFiberPoint period hPeriod
        (mappingTorusMk (orientationDoubleData period hPeriod) point) latitude =
      normalBoundaryLatitudeFiberPointCover period hPeriod
        (point, latitude) :=
  rfl

theorem normalBoundaryLatitudeFiberPoint_joint_continuous :
    Continuous (fun current : OrientationBoundary period hPeriod × Real =>
      normalBoundaryLatitudeFiberPoint period hPeriod current.1 current.2) := by
  have hBoundary :=
    (mappingTorusMk_isAddQuotientCoveringMap
      (orientationDoubleData period hPeriod)).isOpenQuotientMap
  have hFiber : IsOpenQuotientMap (id : Real → Real) :=
    IsOpenQuotientMap.id
  have hProduct := hBoundary.prodMap hFiber
  apply hProduct.continuous_comp_iff.mp
  apply (normalBoundaryLatitudeFiberPointCover_continuous
    period hPeriod).congr
  intro current
  simp only [Function.comp_apply, Prod.map_apply, id_eq]
  exact (normalBoundaryLatitudeFiberPoint_mk period hPeriod
    current.1 current.2).symm

/-- Canonical latitude tangent lift before descent through the orientation
double. -/
def normalBoundaryLatitudeFiberLiftCover
    (current : OrientationBoundaryCover period hPeriod × Real) :
    TangentBundle coverModelWithCorners (EffectiveQuotient period hPeriod) :=
  canonicalLatitudeNormalLift period hPeriod
    (normalGraphCanonicalLatitudeBaseCover period hPeriod current.1,
      current.2)

theorem normalBoundaryLatitudeFiberLiftCover_contMDiff :
    ContMDiff
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      coverModelWithCorners.tangent ∞
      (normalBoundaryLatitudeFiberLiftCover period hPeriod) := by
  exact (canonicalLatitudeNormalLift_contMDiff period hPeriod).comp
    (((normalGraphCanonicalLatitudeBaseCover_contMDiff
      period hPeriod).comp contMDiff_fst).prodMk contMDiff_snd)

/-- Latitude derivative of a genuine smooth bulk scalar on the orientation
cover. -/
def normalBoundaryLatitudeSmoothFieldDerivativeCover
    (field : SmoothQuotientField period hPeriod Real)
    (current : OrientationBoundaryCover period hPeriod × Real) : Real :=
  (tangentMap coverModelWithCorners 𝓘(Real, Real) field.toFun
    (normalBoundaryLatitudeFiberLiftCover period hPeriod current)).2

theorem normalBoundaryLatitudeSmoothFieldCover_hasDerivAt
    (field : SmoothQuotientField period hPeriod Real)
    (point : OrientationBoundaryCover period hPeriod) (latitude : Real) :
    RealHasDerivAt (fun varied => field
      (normalBoundaryLatitudeFiberPointCover
        period hPeriod (point, varied)))
      (normalBoundaryLatitudeSmoothFieldDerivativeCover
        period hPeriod field (point, latitude)) latitude := by
  let slice : Real → EffectiveQuotient period hPeriod :=
    fun varied => normalBoundaryLatitudeFiberPointCover
      period hPeriod (point, varied)
  have hFieldAt : MDifferentiableAt coverModelWithCorners 𝓘(Real, Real)
      field.toFun (slice latitude) :=
    field.contMDiff_toFun.mdifferentiableAt (by simp)
  have hSliceAt : MDifferentiableAt 𝓘(Real, Real)
      coverModelWithCorners slice latitude := by
    exact (normalBoundaryLatitudeFiberPointCover_contMDiff
      period hPeriod).mdifferentiableAt (by simp) |>.comp latitude
        (mdifferentiableAt_const.prodMk mdifferentiableAt_id)
  have hComp := tangentMap_comp_at
    (I := 𝓘(Real, Real))
    (I' := coverModelWithCorners)
    (I'' := 𝓘(Real, Real))
    (f := slice) (g := field.toFun)
    (⟨latitude, 1⟩ : TangentBundle 𝓘(Real, Real) Real)
    hFieldAt hSliceAt
  have hSecond := congrArg (fun tangent => tangent.2) hComp
  change mfderiv 𝓘(Real, Real) 𝓘(Real, Real)
      (fun varied => field
        (normalBoundaryLatitudeFiberPointCover
          period hPeriod (point, varied))) latitude 1 =
    normalBoundaryLatitudeSmoothFieldDerivativeCover
      period hPeriod field (point, latitude) at hSecond
  rw [mfderiv_eq_fderiv] at hSecond
  change deriv (fun varied => field
      (normalBoundaryLatitudeFiberPointCover
        period hPeriod (point, varied))) latitude =
    normalBoundaryLatitudeSmoothFieldDerivativeCover
      period hPeriod field (point, latitude) at hSecond
  have hComposite : ContMDiff 𝓘(Real, Real) 𝓘(Real, Real) ∞
      (fun varied => field (normalBoundaryLatitudeFiberPointCover
        period hPeriod (point, varied))) :=
    field.contMDiff_toFun.comp
      ((normalBoundaryLatitudeFiberPointCover_contMDiff
        period hPeriod).comp (contMDiff_const.prodMk contMDiff_id))
  rw [← hSecond]
  exact ((hComposite.contDiff.differentiable (by simp)).differentiableAt).hasDerivAt

/-- Coefficient of the canonical latitude tangent in the already fixed smooth
finite spanning frame, using the existing metric dualizer. -/
def normalBoundaryLatitudeFrameCoefficientCover
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (index : Fin (finiteSmoothTangentFrame period hPeriod).count)
    (current : OrientationBoundaryCover period hPeriod × Real) : Real :=
  let lift := normalBoundaryLatitudeFiberLiftCover period hPeriod current
  metric.tensor.tensor lift.1
    ((finiteSmoothTangentFrame period hPeriod).vectorAt lift.1 index)
    (generalMetricFiniteFrameInverseOperator period hPeriod
      (finiteSmoothTangentFrame period hPeriod) metric lift.1 lift.2)

theorem normalBoundaryLatitudeFrameCoefficientCover_eq
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (index : Fin (finiteSmoothTangentFrame period hPeriod).count)
    (current : OrientationBoundaryCover period hPeriod × Real) :
    normalBoundaryLatitudeFrameCoefficientCover
        period hPeriod metric index current =
      generalMetricFiniteFrameCoefficientAt period hPeriod
        (finiteSmoothTangentFrame period hPeriod) metric
        (normalBoundaryLatitudeFiberLiftCover period hPeriod current).1 index
        (normalBoundaryLatitudeFiberLiftCover period hPeriod current).2 :=
  rfl

theorem normalBoundaryLatitudeSmoothFieldDerivativeCover_eq_frame_sum
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothQuotientField period hPeriod Real)
    (current : OrientationBoundaryCover period hPeriod × Real) :
    normalBoundaryLatitudeSmoothFieldDerivativeCover
        period hPeriod field current =
      ∑ index : Fin (finiteSmoothTangentFrame period hPeriod).count,
        normalBoundaryLatitudeFrameCoefficientCover
            period hPeriod metric index current *
          frameDerivative period hPeriod Real
            (finiteSmoothTangentFrame period hPeriod) field
            (normalBoundaryLatitudeFiberLiftCover
              period hPeriod current).1 index := by
  let lift := normalBoundaryLatitudeFiberLiftCover period hPeriod current
  have hReconstruct :=
    generalMetricFiniteFrameCoefficientAt_reconstructs period hPeriod
      (finiteSmoothTangentFrame period hPeriod) metric lift.1 lift.2
  have hApplied := congrArg
    (fun tangent => mvfderiv coverModelWithCorners field.toFun lift.1 tangent)
    hReconstruct
  change mvfderiv coverModelWithCorners field.toFun lift.1 lift.2 =
    ∑ index : Fin (finiteSmoothTangentFrame period hPeriod).count,
      generalMetricFiniteFrameCoefficientAt period hPeriod
          (finiteSmoothTangentFrame period hPeriod) metric lift.1 index lift.2 *
        mvfderiv coverModelWithCorners field.toFun lift.1
          ((finiteSmoothTangentFrame period hPeriod).vectorAt lift.1 index)
  simpa only [map_sum, map_smul, smul_eq_mul] using hApplied

theorem normalBoundaryLatitudeFrameCoefficientCover_contMDiff
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (index : Fin (finiteSmoothTangentFrame period hPeriod).count) :
    ContMDiff
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      𝓘(Real, Real) ∞
      (normalBoundaryLatitudeFrameCoefficientCover
        period hPeriod metric index) := by
  unfold normalBoundaryLatitudeFrameCoefficientCover
  have hParameter :
      ContMDiff
        (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
        canonicalLatitudeParameterModelWithCorners ∞
        (fun current : OrientationBoundaryCover period hPeriod × Real =>
          (normalGraphCanonicalLatitudeBaseCover
            period hPeriod current.1, current.2)) :=
    ((normalGraphCanonicalLatitudeBaseCover_contMDiff
      period hPeriod).comp contMDiff_fst).prodMk contMDiff_snd
  have hPoint :=
    (canonicalLatitudeCollar_contMDiff period hPeriod).comp hParameter
  have hInverse :=
    (generalMetricFiniteFrameInverseOperator period hPeriod
      (finiteSmoothTangentFrame period hPeriod) metric).contMDiff.comp hPoint
  have hSolved := hInverse.clm_bundle_apply
    (normalBoundaryLatitudeFiberLiftCover_contMDiff period hPeriod)
  have hFrame :=
    ((finiteSmoothTangentFrame period hPeriod).contMDiff_vector index).comp hPoint
  have hTensor := metric.tensor.tensor.contMDiff.comp hPoint
  have hApplied := ContMDiff.clm_bundle_apply₂
    (F₃ := Real)
    (E₃ := fun _ : EffectiveQuotient period hPeriod => Real)
    hTensor hFrame hSolved
  intro current
  have hAppliedAt := hApplied current
  rw [Bundle.contMDiffAt_totalSpace] at hAppliedAt
  convert hAppliedAt.2 using 1
  funext point
  simp [normalBoundaryLatitudeFiberLiftCover,
    canonicalLatitudeNormalLift,
    canonicalLatitudeCollarMap] <;> rfl

/-- Smooth vertical unit tangent of the cover–latitude product. -/
def normalBoundaryLatitudeVerticalTangentLift
    (current : OrientationBoundaryCover period hPeriod × Real) :
    TangentBundle
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (OrientationBoundaryCover period hPeriod × Real) :=
  (equivTangentBundleProd throatCoverModelWithCorners
      (OrientationBoundaryCover period hPeriod)
      (modelWithCornersSelf Real Real) Real).symm
    (⟨current.1, 0⟩,
      canonicalLatitudeRealUnitTangentLift current.2)

theorem normalBoundaryLatitudeVerticalTangentLift_contMDiff :
    ContMDiff
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (throatCoverModelWithCorners.prod
        (modelWithCornersSelf Real Real)).tangent ∞
      (normalBoundaryLatitudeVerticalTangentLift period hPeriod) := by
  apply (contMDiff_equivTangentBundleProd_symm
    (I := throatCoverModelWithCorners)
    (I' := modelWithCornersSelf Real Real)
    (M := OrientationBoundaryCover period hPeriod)
    (M' := Real)).comp
  exact ((Bundle.contMDiff_zeroSection Real
      (TangentSpace throatCoverModelWithCorners :
        OrientationBoundaryCover period hPeriod → Type _)).of_le le_top
        |>.comp contMDiff_fst).prodMk
    (canonicalLatitudeRealUnitTangentLift_contMDiff.comp contMDiff_snd)

/-- First latitude derivative of one finite-frame normal coefficient. -/
def normalBoundaryLatitudeFrameCoefficientDerivativeCover
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (index : Fin (finiteSmoothTangentFrame period hPeriod).count)
    (current : OrientationBoundaryCover period hPeriod × Real) : Real :=
  (tangentMap
    (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
    (modelWithCornersSelf Real Real)
    (normalBoundaryLatitudeFrameCoefficientCover period hPeriod metric index)
    (normalBoundaryLatitudeVerticalTangentLift
      period hPeriod current)).2

theorem normalBoundaryLatitudeFrameCoefficientDerivativeCover_contMDiff
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (index : Fin (finiteSmoothTangentFrame period hPeriod).count) :
    ContMDiff
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      𝓘(Real, Real) ∞
      (normalBoundaryLatitudeFrameCoefficientDerivativeCover
        period hPeriod metric index) := by
  exact (contMDiff_snd_tangentBundle_modelSpace Real 𝓘(Real, Real)).comp
    (((normalBoundaryLatitudeFrameCoefficientCover_contMDiff
      period hPeriod metric index).contMDiff_tangentMap (by simp)).comp
        (normalBoundaryLatitudeVerticalTangentLift_contMDiff
          period hPeriod))

theorem normalBoundaryLatitudeFrameCoefficientCover_deriv
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (index : Fin (finiteSmoothTangentFrame period hPeriod).count)
    (point : OrientationBoundaryCover period hPeriod) (latitude : Real) :
    deriv (fun varied =>
      normalBoundaryLatitudeFrameCoefficientCover period hPeriod metric index
        (point, varied)) latitude =
      normalBoundaryLatitudeFrameCoefficientDerivativeCover
        period hPeriod metric index (point, latitude) := by
  let slice : Real → OrientationBoundaryCover period hPeriod × Real :=
    fun varied => (point, varied)
  have hCoefficientAt : MDifferentiableAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      𝓘(Real, Real)
      (normalBoundaryLatitudeFrameCoefficientCover
        period hPeriod metric index) (point, latitude) :=
    (normalBoundaryLatitudeFrameCoefficientCover_contMDiff
      period hPeriod metric index).mdifferentiableAt (by simp)
  have hSliceAt : MDifferentiableAt 𝓘(Real, Real)
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      slice latitude :=
    mdifferentiableAt_const.prodMk mdifferentiableAt_id
  have hComp := tangentMap_comp_at
    (I := 𝓘(Real, Real))
    (I' := throatCoverModelWithCorners.prod
      (modelWithCornersSelf Real Real))
    (I'' := 𝓘(Real, Real))
    (f := slice)
    (g := normalBoundaryLatitudeFrameCoefficientCover
      period hPeriod metric index)
    (⟨latitude, 1⟩ : TangentBundle 𝓘(Real, Real) Real)
    hCoefficientAt hSliceAt
  rw [tangentMap_prod_right] at hComp
  have hSecond := congrArg (fun tangent => tangent.2) hComp
  change mfderiv 𝓘(Real, Real) 𝓘(Real, Real)
      (fun varied => normalBoundaryLatitudeFrameCoefficientCover
        period hPeriod metric index (point, varied)) latitude 1 =
    normalBoundaryLatitudeFrameCoefficientDerivativeCover
      period hPeriod metric index (point, latitude) at hSecond
  rw [mfderiv_eq_fderiv] at hSecond
  change deriv (fun varied =>
      normalBoundaryLatitudeFrameCoefficientCover
        period hPeriod metric index (point, varied)) latitude =
    normalBoundaryLatitudeFrameCoefficientDerivativeCover
      period hPeriod metric index (point, latitude) at hSecond
  exact hSecond

/-- Second latitude derivative of the same coefficient. -/
def normalBoundaryLatitudeFrameCoefficientSecondDerivativeCover
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (index : Fin (finiteSmoothTangentFrame period hPeriod).count)
    (current : OrientationBoundaryCover period hPeriod × Real) : Real :=
  (tangentMap
    (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
    (modelWithCornersSelf Real Real)
    (normalBoundaryLatitudeFrameCoefficientDerivativeCover
      period hPeriod metric index)
    (normalBoundaryLatitudeVerticalTangentLift
      period hPeriod current)).2

theorem normalBoundaryLatitudeFrameCoefficientSecondDerivativeCover_contMDiff
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (index : Fin (finiteSmoothTangentFrame period hPeriod).count) :
    ContMDiff
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      𝓘(Real, Real) ∞
      (normalBoundaryLatitudeFrameCoefficientSecondDerivativeCover
        period hPeriod metric index) := by
  exact (contMDiff_snd_tangentBundle_modelSpace Real 𝓘(Real, Real)).comp
    (((normalBoundaryLatitudeFrameCoefficientDerivativeCover_contMDiff
      period hPeriod metric index).contMDiff_tangentMap (by simp)).comp
        (normalBoundaryLatitudeVerticalTangentLift_contMDiff
          period hPeriod))

theorem normalBoundaryLatitudeFrameCoefficientDerivativeCover_deriv
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (index : Fin (finiteSmoothTangentFrame period hPeriod).count)
    (point : OrientationBoundaryCover period hPeriod) (latitude : Real) :
    deriv (fun varied =>
      normalBoundaryLatitudeFrameCoefficientDerivativeCover
        period hPeriod metric index (point, varied)) latitude =
      normalBoundaryLatitudeFrameCoefficientSecondDerivativeCover
        period hPeriod metric index (point, latitude) := by
  let slice : Real → OrientationBoundaryCover period hPeriod × Real :=
    fun varied => (point, varied)
  have hDerivativeAt : MDifferentiableAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      𝓘(Real, Real)
      (normalBoundaryLatitudeFrameCoefficientDerivativeCover
        period hPeriod metric index) (point, latitude) :=
    (normalBoundaryLatitudeFrameCoefficientDerivativeCover_contMDiff
      period hPeriod metric index).mdifferentiableAt (by simp)
  have hSliceAt : MDifferentiableAt 𝓘(Real, Real)
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      slice latitude :=
    mdifferentiableAt_const.prodMk mdifferentiableAt_id
  have hComp := tangentMap_comp_at
    (I := 𝓘(Real, Real))
    (I' := throatCoverModelWithCorners.prod
      (modelWithCornersSelf Real Real))
    (I'' := 𝓘(Real, Real))
    (f := slice)
    (g := normalBoundaryLatitudeFrameCoefficientDerivativeCover
      period hPeriod metric index)
    (⟨latitude, 1⟩ : TangentBundle 𝓘(Real, Real) Real)
    hDerivativeAt hSliceAt
  rw [tangentMap_prod_right] at hComp
  have hSecond := congrArg (fun tangent => tangent.2) hComp
  change mfderiv 𝓘(Real, Real) 𝓘(Real, Real)
      (fun varied => normalBoundaryLatitudeFrameCoefficientDerivativeCover
        period hPeriod metric index (point, varied)) latitude 1 =
    normalBoundaryLatitudeFrameCoefficientSecondDerivativeCover
      period hPeriod metric index (point, latitude) at hSecond
  rw [mfderiv_eq_fderiv] at hSecond
  change deriv (fun varied =>
      normalBoundaryLatitudeFrameCoefficientDerivativeCover
        period hPeriod metric index (point, varied)) latitude =
    normalBoundaryLatitudeFrameCoefficientSecondDerivativeCover
      period hPeriod metric index (point, latitude) at hSecond
  exact hSecond

theorem normalBoundaryLatitudeFiberLiftCover_continuous :
    Continuous (normalBoundaryLatitudeFiberLiftCover period hPeriod) := by
  exact (canonicalLatitudeNormalLift_continuous period hPeriod).comp
    (((normalGraphCanonicalLatitudeBaseCover_continuous period hPeriod).comp
      continuous_fst).prodMk continuous_snd)

theorem normalBoundaryLatitudeFiberLiftCover_base
    (point : OrientationBoundaryCover period hPeriod) (latitude : Real) :
    (normalBoundaryLatitudeFiberLiftCover period hPeriod
      (point, latitude)).1 =
      normalBoundaryLatitudeFiberPointCover period hPeriod
        (point, latitude) := by
  rw [normalBoundaryLatitudeFiberPointCover_eq]
  unfold normalBoundaryLatitudeFiberLiftCover canonicalLatitudeNormalLift
  rw [canonicalLatitudeAnchor_baseCover period hPeriod point]

theorem normalBoundaryLatitudeFiberLiftCover_invariant
    (winding : Int) (point : OrientationBoundaryCover period hPeriod)
    (latitude : Real) :
    normalBoundaryLatitudeFiberLiftCover period hPeriod
        (winding +ᵥ point, latitude) =
      normalBoundaryLatitudeFiberLiftCover period hPeriod
        (point, latitude) := by
  let anchor := orientationDoubleCoverHomeomorph period hPeriod point
  have hAnchor :
      orientationDoubleCoverHomeomorph period hPeriod (winding +ᵥ point) =
        (2 * winding) +ᵥ anchor :=
    orientationDoubleCover_even_equivariant period hPeriod winding point
  have hSign :
      (normalSignRepresentation (2 * winding) : Real) = 1 := by
    simpa using congrArg (fun unit : Realˣ => (unit : Real))
      (pulledBack_normal_sign_trivial winding)
  have hCurve :
      quotientNormalLatitude period hPeriod ((2 * winding) +ᵥ anchor) =
        quotientNormalLatitude period hPeriod anchor := by
    funext current
    simpa [hSign] using
      quotientNormalLatitude_deck_winding period hPeriod
        (2 * winding) anchor current
  unfold normalBoundaryLatitudeFiberLiftCover canonicalLatitudeNormalLift
    canonicalLatitudeNormalVector
  rw [canonicalLatitudeAnchor_baseCover,
    canonicalLatitudeAnchor_baseCover, hAnchor, hCurve]

theorem normalBoundaryLatitudeFrameCoefficientCover_invariant
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (index : Fin (finiteSmoothTangentFrame period hPeriod).count)
    (winding : Int) (point : OrientationBoundaryCover period hPeriod)
    (latitude : Real) :
    normalBoundaryLatitudeFrameCoefficientCover period hPeriod metric index
        (winding +ᵥ point, latitude) =
      normalBoundaryLatitudeFrameCoefficientCover period hPeriod metric index
        (point, latitude) := by
  unfold normalBoundaryLatitudeFrameCoefficientCover
  rw [normalBoundaryLatitudeFiberLiftCover_invariant]

theorem normalBoundaryLatitudeFrameCoefficientDerivativeCover_invariant
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (index : Fin (finiteSmoothTangentFrame period hPeriod).count)
    (winding : Int) (point : OrientationBoundaryCover period hPeriod)
    (latitude : Real) :
    normalBoundaryLatitudeFrameCoefficientDerivativeCover
        period hPeriod metric index (winding +ᵥ point, latitude) =
      normalBoundaryLatitudeFrameCoefficientDerivativeCover
        period hPeriod metric index (point, latitude) := by
  rw [← normalBoundaryLatitudeFrameCoefficientCover_deriv
      period hPeriod metric index (winding +ᵥ point) latitude,
    ← normalBoundaryLatitudeFrameCoefficientCover_deriv
      period hPeriod metric index point latitude]
  apply congrArg (fun function : Real → Real => deriv function latitude)
  funext varied
  exact normalBoundaryLatitudeFrameCoefficientCover_invariant
    period hPeriod metric index winding point varied

theorem normalBoundaryLatitudeFrameCoefficientSecondDerivativeCover_invariant
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (index : Fin (finiteSmoothTangentFrame period hPeriod).count)
    (winding : Int) (point : OrientationBoundaryCover period hPeriod)
    (latitude : Real) :
    normalBoundaryLatitudeFrameCoefficientSecondDerivativeCover
        period hPeriod metric index (winding +ᵥ point, latitude) =
      normalBoundaryLatitudeFrameCoefficientSecondDerivativeCover
        period hPeriod metric index (point, latitude) := by
  rw [← normalBoundaryLatitudeFrameCoefficientDerivativeCover_deriv
      period hPeriod metric index (winding +ᵥ point) latitude,
    ← normalBoundaryLatitudeFrameCoefficientDerivativeCover_deriv
      period hPeriod metric index point latitude]
  apply congrArg (fun function : Real → Real => deriv function latitude)
  funext varied
  exact normalBoundaryLatitudeFrameCoefficientDerivativeCover_invariant
    period hPeriod metric index winding point varied

/-- The finite-frame normal coefficient descended through the already fixed
orientation double. -/
def normalBoundaryLatitudeFrameCoefficient
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (index : Fin (finiteSmoothTangentFrame period hPeriod).count)
    (boundary : OrientationBoundary period hPeriod) (latitude : Real) : Real :=
  Quotient.lift
    (fun point => normalBoundaryLatitudeFrameCoefficientCover
      period hPeriod metric index (point, latitude))
    (fun first second hOrbit => by
      change AddAction.orbitRel Int (OrientationBoundaryCover period hPeriod)
        first second at hOrbit
      rw [AddAction.orbitRel_apply, AddAction.mem_orbit_iff] at hOrbit
      rcases hOrbit with ⟨winding, hWinding⟩
      rw [← hWinding]
      exact normalBoundaryLatitudeFrameCoefficientCover_invariant
        period hPeriod metric index winding second latitude)
    boundary

@[simp]
theorem normalBoundaryLatitudeFrameCoefficient_mk
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (index : Fin (finiteSmoothTangentFrame period hPeriod).count)
    (point : OrientationBoundaryCover period hPeriod) (latitude : Real) :
    normalBoundaryLatitudeFrameCoefficient period hPeriod metric index
        (mappingTorusMk (orientationDoubleData period hPeriod) point) latitude =
      normalBoundaryLatitudeFrameCoefficientCover period hPeriod metric index
        (point, latitude) :=
  rfl

theorem normalBoundaryLatitudeFrameCoefficient_joint_continuous
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (index : Fin (finiteSmoothTangentFrame period hPeriod).count) :
    Continuous (fun current : OrientationBoundary period hPeriod × Real =>
      normalBoundaryLatitudeFrameCoefficient period hPeriod metric index
        current.1 current.2) := by
  have hBoundary :=
    (mappingTorusMk_isAddQuotientCoveringMap
      (orientationDoubleData period hPeriod)).isOpenQuotientMap
  have hFiber : IsOpenQuotientMap (id : Real → Real) :=
    IsOpenQuotientMap.id
  have hProduct := hBoundary.prodMap hFiber
  apply hProduct.continuous_comp_iff.mp
  apply (normalBoundaryLatitudeFrameCoefficientCover_contMDiff
    period hPeriod metric index).continuous.congr
  intro current
  simp only [Function.comp_apply]
  exact (normalBoundaryLatitudeFrameCoefficient_mk
    period hPeriod metric index current.1 current.2).symm

/-- First latitude derivative of the finite-frame coefficient, descended
through the orientation double. -/
def normalBoundaryLatitudeFrameCoefficientDerivative
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (index : Fin (finiteSmoothTangentFrame period hPeriod).count)
    (boundary : OrientationBoundary period hPeriod) (latitude : Real) : Real :=
  Quotient.lift
    (fun point => normalBoundaryLatitudeFrameCoefficientDerivativeCover
      period hPeriod metric index (point, latitude))
    (fun first second hOrbit => by
      change AddAction.orbitRel Int (OrientationBoundaryCover period hPeriod)
        first second at hOrbit
      rw [AddAction.orbitRel_apply, AddAction.mem_orbit_iff] at hOrbit
      rcases hOrbit with ⟨winding, hWinding⟩
      rw [← hWinding]
      exact normalBoundaryLatitudeFrameCoefficientDerivativeCover_invariant
        period hPeriod metric index winding second latitude)
    boundary

@[simp]
theorem normalBoundaryLatitudeFrameCoefficientDerivative_mk
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (index : Fin (finiteSmoothTangentFrame period hPeriod).count)
    (point : OrientationBoundaryCover period hPeriod) (latitude : Real) :
    normalBoundaryLatitudeFrameCoefficientDerivative period hPeriod metric index
        (mappingTorusMk (orientationDoubleData period hPeriod) point) latitude =
      normalBoundaryLatitudeFrameCoefficientDerivativeCover
        period hPeriod metric index (point, latitude) :=
  rfl

theorem normalBoundaryLatitudeFrameCoefficientDerivative_joint_continuous
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (index : Fin (finiteSmoothTangentFrame period hPeriod).count) :
    Continuous (fun current : OrientationBoundary period hPeriod × Real =>
      normalBoundaryLatitudeFrameCoefficientDerivative
        period hPeriod metric index current.1 current.2) := by
  have hBoundary :=
    (mappingTorusMk_isAddQuotientCoveringMap
      (orientationDoubleData period hPeriod)).isOpenQuotientMap
  have hFiber : IsOpenQuotientMap (id : Real → Real) :=
    IsOpenQuotientMap.id
  have hProduct := hBoundary.prodMap hFiber
  apply hProduct.continuous_comp_iff.mp
  apply (normalBoundaryLatitudeFrameCoefficientDerivativeCover_contMDiff
    period hPeriod metric index).continuous.congr
  intro current
  simp only [Function.comp_apply]
  exact (normalBoundaryLatitudeFrameCoefficientDerivative_mk
    period hPeriod metric index current.1 current.2).symm

/-- Second latitude derivative of the finite-frame coefficient, descended
through the orientation double. -/
def normalBoundaryLatitudeFrameCoefficientSecondDerivative
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (index : Fin (finiteSmoothTangentFrame period hPeriod).count)
    (boundary : OrientationBoundary period hPeriod) (latitude : Real) : Real :=
  Quotient.lift
    (fun point => normalBoundaryLatitudeFrameCoefficientSecondDerivativeCover
      period hPeriod metric index (point, latitude))
    (fun first second hOrbit => by
      change AddAction.orbitRel Int (OrientationBoundaryCover period hPeriod)
        first second at hOrbit
      rw [AddAction.orbitRel_apply, AddAction.mem_orbit_iff] at hOrbit
      rcases hOrbit with ⟨winding, hWinding⟩
      rw [← hWinding]
      exact
        normalBoundaryLatitudeFrameCoefficientSecondDerivativeCover_invariant
          period hPeriod metric index winding second latitude)
    boundary

@[simp]
theorem normalBoundaryLatitudeFrameCoefficientSecondDerivative_mk
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (index : Fin (finiteSmoothTangentFrame period hPeriod).count)
    (point : OrientationBoundaryCover period hPeriod) (latitude : Real) :
    normalBoundaryLatitudeFrameCoefficientSecondDerivative
        period hPeriod metric index
        (mappingTorusMk (orientationDoubleData period hPeriod) point) latitude =
      normalBoundaryLatitudeFrameCoefficientSecondDerivativeCover
        period hPeriod metric index (point, latitude) :=
  rfl

theorem normalBoundaryLatitudeFrameCoefficientSecondDerivative_joint_continuous
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (index : Fin (finiteSmoothTangentFrame period hPeriod).count) :
    Continuous (fun current : OrientationBoundary period hPeriod × Real =>
      normalBoundaryLatitudeFrameCoefficientSecondDerivative
        period hPeriod metric index current.1 current.2) := by
  have hBoundary :=
    (mappingTorusMk_isAddQuotientCoveringMap
      (orientationDoubleData period hPeriod)).isOpenQuotientMap
  have hFiber : IsOpenQuotientMap (id : Real → Real) :=
    IsOpenQuotientMap.id
  have hProduct := hBoundary.prodMap hFiber
  apply hProduct.continuous_comp_iff.mp
  apply (normalBoundaryLatitudeFrameCoefficientSecondDerivativeCover_contMDiff
    period hPeriod metric index).continuous.congr
  intro current
  simp only [Function.comp_apply]
  exact (normalBoundaryLatitudeFrameCoefficientSecondDerivative_mk
    period hPeriod metric index current.1 current.2).symm

theorem normalBoundaryLatitudeFrameCoefficient_hasDerivAt
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (index : Fin (finiteSmoothTangentFrame period hPeriod).count)
    (boundary : OrientationBoundary period hPeriod) (latitude : Real) :
    RealHasDerivAt (fun varied =>
      normalBoundaryLatitudeFrameCoefficient
        period hPeriod metric index boundary varied)
      (normalBoundaryLatitudeFrameCoefficientDerivative
        period hPeriod metric index boundary latitude) latitude := by
  refine Quotient.inductionOn boundary ?_
  intro point
  have hSmooth : ContDiff Real ∞ (fun varied =>
      normalBoundaryLatitudeFrameCoefficientCover
        period hPeriod metric index (point, varied)) := by
    exact ((normalBoundaryLatitudeFrameCoefficientCover_contMDiff
      period hPeriod metric index).comp
        (contMDiff_const.prodMk contMDiff_id)).contDiff
  have hDerivative : RealHasDerivAt (fun varied =>
      normalBoundaryLatitudeFrameCoefficientCover
        period hPeriod metric index (point, varied))
      (deriv (fun varied => normalBoundaryLatitudeFrameCoefficientCover
        period hPeriod metric index (point, varied)) latitude) latitude :=
    (hSmooth.differentiable (by simp) latitude).hasDerivAt
  rw [normalBoundaryLatitudeFrameCoefficientCover_deriv] at hDerivative
  simpa only [normalBoundaryLatitudeFrameCoefficient_mk,
    normalBoundaryLatitudeFrameCoefficientDerivative_mk] using hDerivative

theorem normalBoundaryLatitudeFrameCoefficientDerivative_hasDerivAt
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (index : Fin (finiteSmoothTangentFrame period hPeriod).count)
    (boundary : OrientationBoundary period hPeriod) (latitude : Real) :
    RealHasDerivAt (fun varied =>
      normalBoundaryLatitudeFrameCoefficientDerivative
        period hPeriod metric index boundary varied)
      (normalBoundaryLatitudeFrameCoefficientSecondDerivative
        period hPeriod metric index boundary latitude) latitude := by
  refine Quotient.inductionOn boundary ?_
  intro point
  have hSmooth : ContDiff Real ∞ (fun varied =>
      normalBoundaryLatitudeFrameCoefficientDerivativeCover
        period hPeriod metric index (point, varied)) := by
    exact ((normalBoundaryLatitudeFrameCoefficientDerivativeCover_contMDiff
      period hPeriod metric index).comp
        (contMDiff_const.prodMk contMDiff_id)).contDiff
  have hDerivative : RealHasDerivAt (fun varied =>
      normalBoundaryLatitudeFrameCoefficientDerivativeCover
        period hPeriod metric index (point, varied))
      (deriv (fun varied =>
        normalBoundaryLatitudeFrameCoefficientDerivativeCover
          period hPeriod metric index (point, varied)) latitude) latitude :=
    (hSmooth.differentiable (by simp) latitude).hasDerivAt
  rw [normalBoundaryLatitudeFrameCoefficientDerivativeCover_deriv]
    at hDerivative
  simpa only [normalBoundaryLatitudeFrameCoefficientDerivative_mk,
    normalBoundaryLatitudeFrameCoefficientSecondDerivative_mk]
    using hDerivative

/-- Restriction of the descended coefficient to the compact latitude strip
selected canonically by `arctan`. -/
def normalBoundaryLatitudeFrameCoefficientCompact
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (index : Fin (finiteSmoothTangentFrame period hPeriod).count) :
    C(OrientationBoundary period hPeriod × ArctanCompactFiber, Real) where
  toFun := fun current =>
    normalBoundaryLatitudeFrameCoefficient period hPeriod metric index
      current.1 current.2.1
  continuous_toFun := by
    have hBoundary : Continuous
        (fun current : OrientationBoundary period hPeriod ×
            ArctanCompactFiber => current.1) :=
      continuous_fst
    have hLatitude : Continuous
        (fun current : OrientationBoundary period hPeriod ×
            ArctanCompactFiber => (current.2 : Real)) :=
      continuous_subtype_val.comp continuous_snd
    have hComposed :=
      (normalBoundaryLatitudeFrameCoefficient_joint_continuous
        period hPeriod metric index).comp (hBoundary.prodMk hLatitude)
    apply hComposed.congr
    intro current
    rfl

/-- Bounded raw-fiber coefficient obtained by the fixed `arctan` collar;
there is no extension choice outside the physical latitude strip. -/
def normalBoundaryRawFrameCoefficient
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (index : Fin (finiteSmoothTangentFrame period hPeriod).count) :
    BoundedFiberField (OrientationBoundary period hPeriod) :=
  boundedArctanCompactPullbackCLM (OrientationBoundary period hPeriod)
    (normalBoundaryLatitudeFrameCoefficientCompact
      period hPeriod metric index)

@[simp]
theorem normalBoundaryRawFrameCoefficient_apply
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (index : Fin (finiteSmoothTangentFrame period hPeriod).count)
    (boundary : OrientationBoundary period hPeriod) (fiber : Real) :
    normalBoundaryRawFrameCoefficient period hPeriod metric index
        (boundary, fiber) =
      normalBoundaryLatitudeFrameCoefficient period hPeriod metric index
        boundary (Real.arctan fiber) :=
  rfl

/-- First latitude derivative restricted to the canonical compact strip. -/
def normalBoundaryLatitudeFrameCoefficientDerivativeCompact
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (index : Fin (finiteSmoothTangentFrame period hPeriod).count) :
    C(OrientationBoundary period hPeriod × ArctanCompactFiber, Real) where
  toFun := fun current =>
    normalBoundaryLatitudeFrameCoefficientDerivative
      period hPeriod metric index current.1 current.2.1
  continuous_toFun := by
    have hBoundary : Continuous
        (fun current : OrientationBoundary period hPeriod ×
            ArctanCompactFiber => current.1) :=
      continuous_fst
    have hLatitude : Continuous
        (fun current : OrientationBoundary period hPeriod ×
            ArctanCompactFiber => (current.2 : Real)) :=
      continuous_subtype_val.comp continuous_snd
    have hComposed :=
      (normalBoundaryLatitudeFrameCoefficientDerivative_joint_continuous
        period hPeriod metric index).comp (hBoundary.prodMk hLatitude)
    apply hComposed.congr
    intro current
    rfl

/-- Bounded raw-fiber pullback of the first latitude derivative. -/
def normalBoundaryRawFrameCoefficientDerivative
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (index : Fin (finiteSmoothTangentFrame period hPeriod).count) :
    BoundedFiberField (OrientationBoundary period hPeriod) :=
  boundedArctanCompactPullbackCLM (OrientationBoundary period hPeriod)
    (normalBoundaryLatitudeFrameCoefficientDerivativeCompact
      period hPeriod metric index)

@[simp]
theorem normalBoundaryRawFrameCoefficientDerivative_apply
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (index : Fin (finiteSmoothTangentFrame period hPeriod).count)
    (boundary : OrientationBoundary period hPeriod) (fiber : Real) :
    normalBoundaryRawFrameCoefficientDerivative period hPeriod metric index
        (boundary, fiber) =
      normalBoundaryLatitudeFrameCoefficientDerivative
        period hPeriod metric index boundary (Real.arctan fiber) :=
  rfl

/-- Second latitude derivative restricted to the canonical compact strip. -/
def normalBoundaryLatitudeFrameCoefficientSecondDerivativeCompact
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (index : Fin (finiteSmoothTangentFrame period hPeriod).count) :
    C(OrientationBoundary period hPeriod × ArctanCompactFiber, Real) where
  toFun := fun current =>
    normalBoundaryLatitudeFrameCoefficientSecondDerivative
      period hPeriod metric index current.1 current.2.1
  continuous_toFun := by
    have hBoundary : Continuous
        (fun current : OrientationBoundary period hPeriod ×
            ArctanCompactFiber => current.1) :=
      continuous_fst
    have hLatitude : Continuous
        (fun current : OrientationBoundary period hPeriod ×
            ArctanCompactFiber => (current.2 : Real)) :=
      continuous_subtype_val.comp continuous_snd
    have hComposed :=
      (normalBoundaryLatitudeFrameCoefficientSecondDerivative_joint_continuous
        period hPeriod metric index).comp (hBoundary.prodMk hLatitude)
    apply hComposed.congr
    intro current
    rfl

/-- Bounded raw-fiber pullback of the second latitude derivative. -/
def normalBoundaryRawFrameCoefficientSecondDerivative
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (index : Fin (finiteSmoothTangentFrame period hPeriod).count) :
    BoundedFiberField (OrientationBoundary period hPeriod) :=
  boundedArctanCompactPullbackCLM (OrientationBoundary period hPeriod)
    (normalBoundaryLatitudeFrameCoefficientSecondDerivativeCompact
      period hPeriod metric index)

@[simp]
theorem normalBoundaryRawFrameCoefficientSecondDerivative_apply
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (index : Fin (finiteSmoothTangentFrame period hPeriod).count)
    (boundary : OrientationBoundary period hPeriod) (fiber : Real) :
    normalBoundaryRawFrameCoefficientSecondDerivative
        period hPeriod metric index (boundary, fiber) =
      normalBoundaryLatitudeFrameCoefficientSecondDerivative
        period hPeriod metric index boundary (Real.arctan fiber) :=
  rfl

/-- Intrinsic canonical tangent lift along the descended latitude collar. -/
def normalBoundaryLatitudeFiberLift
    (boundary : OrientationBoundary period hPeriod) (latitude : Real) :
    TangentBundle coverModelWithCorners (EffectiveQuotient period hPeriod) :=
  Quotient.lift
    (fun point =>
      normalBoundaryLatitudeFiberLiftCover period hPeriod (point, latitude))
    (fun first second hOrbit => by
      change AddAction.orbitRel Int (OrientationBoundaryCover period hPeriod)
        first second at hOrbit
      rw [AddAction.orbitRel_apply, AddAction.mem_orbit_iff] at hOrbit
      rcases hOrbit with ⟨winding, hWinding⟩
      rw [← hWinding]
      exact normalBoundaryLatitudeFiberLiftCover_invariant
        period hPeriod winding second latitude)
    boundary

@[simp]
theorem normalBoundaryLatitudeFiberLift_mk
    (point : OrientationBoundaryCover period hPeriod) (latitude : Real) :
    normalBoundaryLatitudeFiberLift period hPeriod
        (mappingTorusMk (orientationDoubleData period hPeriod) point) latitude =
      normalBoundaryLatitudeFiberLiftCover period hPeriod
        (point, latitude) :=
  rfl

theorem normalBoundaryLatitudeFiberLift_joint_continuous :
    Continuous (fun current : OrientationBoundary period hPeriod × Real =>
      normalBoundaryLatitudeFiberLift period hPeriod current.1 current.2) := by
  have hBoundary :=
    (mappingTorusMk_isAddQuotientCoveringMap
      (orientationDoubleData period hPeriod)).isOpenQuotientMap
  have hFiber : IsOpenQuotientMap (id : Real → Real) :=
    IsOpenQuotientMap.id
  have hProduct := hBoundary.prodMap hFiber
  apply hProduct.continuous_comp_iff.mp
  apply (normalBoundaryLatitudeFiberLiftCover_continuous
    period hPeriod).congr
  intro current
  simp only [Function.comp_apply, Prod.map_apply, id_eq]
  exact (normalBoundaryLatitudeFiberLift_mk period hPeriod
    current.1 current.2).symm

theorem normalBoundaryLatitudeFiberLift_base
    (boundary : OrientationBoundary period hPeriod) (latitude : Real) :
    (normalBoundaryLatitudeFiberLift period hPeriod boundary latitude).1 =
      normalBoundaryLatitudeFiberPoint period hPeriod boundary latitude := by
  refine Quotient.inductionOn boundary ?_
  intro point
  rw [normalBoundaryLatitudeFiberLift_mk,
    normalBoundaryLatitudeFiberPoint_mk]
  exact normalBoundaryLatitudeFiberLiftCover_base
    period hPeriod point latitude

/-- Exact first derivative of any genuine smooth scalar along the descended
latitude fiber, expressed in the fixed finite frame. -/
theorem normalBoundaryLatitudeSmoothField_hasDerivAt
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothQuotientField period hPeriod Real)
    (boundary : OrientationBoundary period hPeriod) (latitude : Real) :
    RealHasDerivAt (fun varied => field
      (normalBoundaryLatitudeFiberPoint
        period hPeriod boundary varied))
      (∑ index : Fin (finiteSmoothTangentFrame period hPeriod).count,
        normalBoundaryLatitudeFrameCoefficient
            period hPeriod metric index boundary latitude *
          frameDerivative period hPeriod Real
            (finiteSmoothTangentFrame period hPeriod) field
            (normalBoundaryLatitudeFiberPoint
              period hPeriod boundary latitude) index) latitude := by
  refine Quotient.inductionOn boundary ?_
  intro point
  have hDerivative :=
    normalBoundaryLatitudeSmoothFieldCover_hasDerivAt
      period hPeriod field point latitude
  rw [normalBoundaryLatitudeSmoothFieldDerivativeCover_eq_frame_sum
    period hPeriod metric field] at hDerivative
  simpa only [normalBoundaryLatitudeFiberPoint_mk,
    normalBoundaryLatitudeFrameCoefficient_mk,
    normalBoundaryLatitudeFiberLiftCover_base] using hDerivative

theorem normalBoundaryRawFiberPoint_eq_latitude
    (boundary : OrientationBoundary period hPeriod) (fiber : Real) :
    normalBoundaryRawFiberPoint period hPeriod boundary fiber =
      normalBoundaryLatitudeFiberPoint period hPeriod boundary
        (Real.arctan fiber) := by
  refine Quotient.inductionOn boundary ?_
  intro point
  rw [normalBoundaryRawFiberPoint_mk,
    normalBoundaryLatitudeFiberPoint_mk,
    normalBoundaryRawFiberPointCover_eq,
    normalBoundaryLatitudeFiberPointCover_eq]

/-- The existing latitude collar restricted to the compact strip selected by
`arctan`. -/
def normalBoundaryLatitudeCompactInput :
    C(OrientationBoundary period hPeriod × ArctanCompactFiber,
      EffectiveQuotient period hPeriod) where
  toFun := fun current =>
    normalBoundaryLatitudeFiberPoint period hPeriod current.1 current.2.1
  continuous_toFun := by
    have hBoundary : Continuous
        (fun current : OrientationBoundary period hPeriod ×
            ArctanCompactFiber => current.1) :=
      continuous_fst
    have hLatitude : Continuous
        (fun current : OrientationBoundary period hPeriod ×
            ArctanCompactFiber => (current.2 : Real)) :=
      continuous_subtype_val.comp continuous_snd
    have hComposed :=
      (normalBoundaryLatitudeFiberPoint_joint_continuous period hPeriod).comp
        (hBoundary.prodMk hLatitude)
    apply hComposed.congr
    intro current
    rfl

/-- Pullback of an existing continuous bulk scalar to the compact latitude
strip. -/
def normalBoundaryLatitudeCompactFieldPullbackCLM :
    C(EffectiveQuotient period hPeriod, Real) →L[Real]
      C(OrientationBoundary period hPeriod × ArctanCompactFiber, Real) :=
  ContinuousMap.compCLM Real Real
    (normalBoundaryLatitudeCompactInput period hPeriod)

/-- Canonical bounded raw-fiber pullback of an existing continuous bulk
scalar. -/
def normalBoundaryRawFieldPullbackCLM :
    C(EffectiveQuotient period hPeriod, Real) →L[Real]
      BoundedFiberField (OrientationBoundary period hPeriod) :=
  (boundedArctanCompactPullbackCLM
    (OrientationBoundary period hPeriod)).comp
      (normalBoundaryLatitudeCompactFieldPullbackCLM period hPeriod)

@[simp]
theorem normalBoundaryRawFieldPullbackCLM_apply
    (field : C(EffectiveQuotient period hPeriod, Real))
    (boundary : OrientationBoundary period hPeriod) (fiber : Real) :
    normalBoundaryRawFieldPullbackCLM period hPeriod field
        (boundary, fiber) =
      field (normalBoundaryLatitudeFiberPoint period hPeriod boundary
        (Real.arctan fiber)) :=
  rfl

/-- Substitution of the completed normal value in the raw collar is exactly
the already constructed physical moving graph. -/
theorem normalBoundaryRawFiberPoint_graph
    (normal : NormalBoundaryC2JetCore period hPeriod)
    (parameter : Real) (boundary : OrientationBoundary period hPeriod) :
    normalBoundaryRawFiberPoint period hPeriod boundary
        (parameter * normalBoundaryC2JetCoreValueAt
          period hPeriod boundary normal) =
      normalBoundaryC2Graph period hPeriod normal parameter boundary := by
  refine Quotient.inductionOn boundary ?_
  intro point
  rw [normalBoundaryRawFiberPoint_mk, normalBoundaryC2Graph_mk,
    normalBoundaryRawFiberPointCover_eq]
  rfl

/-- The raw normal graph coordinate, before the already existing `arctan`
collar compression, as a bounded continuous function on the compact
orientation boundary. -/
def normalBoundaryC2RawGraphCLM :
    NormalBoundaryC2JetCore period hPeriod →L[Real]
      (OrientationBoundary period hPeriod →ᵇ Real) :=
  (compactContinuousToBoundedCLM
    (OrientationBoundary period hPeriod)).comp
      (normalBoundaryC2JetCoreToContinuous period hPeriod)

@[simp]
theorem normalBoundaryC2RawGraphCLM_apply
    (normal : NormalBoundaryC2JetCore period hPeriod)
    (boundary : OrientationBoundary period hPeriod) :
    normalBoundaryC2RawGraphCLM period hPeriod normal boundary =
      normalBoundaryC2JetCoreValueAt period hPeriod boundary normal :=
  rfl

@[simp]
theorem normalBoundaryC2RawGraphCLM_smooth
    (displacement : SmoothNormalDisplacement period hPeriod)
    (boundary : OrientationBoundary period hPeriod) :
    normalBoundaryC2RawGraphCLM period hPeriod
        (smoothNormalDisplacementToBoundaryC2JetCore
          period hPeriod displacement) boundary =
      normalDisplacementOrientationScalar period hPeriod displacement boundary :=
  rfl

/-- Raw moving-boundary graph, including its real deformation parameter. -/
def normalBoundaryC2ScaledRawGraph
    (current : NormalBoundaryC2JetCore period hPeriod × Real) :
    OrientationBoundary period hPeriod →ᵇ Real :=
  current.2 • normalBoundaryC2RawGraphCLM period hPeriod current.1

@[simp]
theorem normalBoundaryC2ScaledRawGraph_apply
    (normal : NormalBoundaryC2JetCore period hPeriod)
    (parameter : Real) (boundary : OrientationBoundary period hPeriod) :
    normalBoundaryC2ScaledRawGraph period hPeriod (normal, parameter) boundary =
      parameter * normalBoundaryC2JetCoreValueAt
        period hPeriod boundary normal :=
  rfl

theorem normalBoundaryC2ScaledRawGraph_contDiff_two :
    ContDiff Real 2 (normalBoundaryC2ScaledRawGraph period hPeriod) := by
  have hFst : ContDiff Real 2
      (Prod.fst : NormalBoundaryC2JetCore period hPeriod × Real →
        NormalBoundaryC2JetCore period hPeriod) :=
    contDiff_fst
  have hNormal : ContDiff Real 2
      (fun current : NormalBoundaryC2JetCore period hPeriod × Real =>
        normalBoundaryC2RawGraphCLM period hPeriod current.1) :=
    (normalBoundaryC2RawGraphCLM period hPeriod).contDiff.comp hFst
  exact contDiff_snd.smul hNormal

/-- The actual canonical-latitude graph.  It is the existing raw normal graph
followed by the already fixed `arctan` collar compression. -/
def normalBoundaryC2LatitudeGraph
    (current : NormalBoundaryC2JetCore period hPeriod × Real) :
    OrientationBoundary period hPeriod →ᵇ Real :=
  boundedArctanNemytskii (OrientationBoundary period hPeriod)
    (normalBoundaryC2ScaledRawGraph period hPeriod current)

@[simp]
theorem normalBoundaryC2LatitudeGraph_apply
    (normal : NormalBoundaryC2JetCore period hPeriod)
    (parameter : Real) (boundary : OrientationBoundary period hPeriod) :
    normalBoundaryC2LatitudeGraph period hPeriod (normal, parameter) boundary =
      Real.arctan (parameter * normalBoundaryC2JetCoreValueAt
        period hPeriod boundary normal) := by
  rfl

theorem normalBoundaryC2LatitudeGraph_contDiff_two :
    ContDiff Real 2 (normalBoundaryC2LatitudeGraph period hPeriod) := by
  exact
    (boundedArctanNemytskii_contDiff_two
      (OrientationBoundary period hPeriod)).comp
        (normalBoundaryC2ScaledRawGraph_contDiff_two period hPeriod)

theorem normalBoundaryLatitudeFiberPoint_graph
    (normal : NormalBoundaryC2JetCore period hPeriod)
    (parameter : Real) (boundary : OrientationBoundary period hPeriod) :
    normalBoundaryLatitudeFiberPoint period hPeriod boundary
        (normalBoundaryC2LatitudeGraph period hPeriod
          (normal, parameter) boundary) =
      normalBoundaryC2Graph period hPeriod normal parameter boundary := by
  rw [normalBoundaryC2LatitudeGraph_apply,
    ← normalBoundaryRawFiberPoint_eq_latitude]
  exact normalBoundaryRawFiberPoint_graph
    period hPeriod normal parameter boundary

/-- Public graph gate used by the metric fiber-jet substitution: the genuine
latitude graph is C² and evaluates to the pre-existing physical graph. -/
theorem normal_boundary_c2_latitude_graph_gate :
    ContDiff Real 2 (normalBoundaryC2LatitudeGraph period hPeriod) ∧
      (∀ normal parameter boundary,
        normalBoundaryLatitudeFiberPoint period hPeriod boundary
            (normalBoundaryC2LatitudeGraph period hPeriod
              (normal, parameter) boundary) =
          normalBoundaryC2Graph period hPeriod normal parameter boundary) :=
  ⟨normalBoundaryC2LatitudeGraph_contDiff_two period hPeriod,
    normalBoundaryLatitudeFiberPoint_graph period hPeriod⟩

/-- The graph input required by the generic C² substitution theorem is
exactly the existing completed normal value field. -/
theorem normal_boundary_c2_raw_graph_gate :
    Continuous (normalBoundaryC2RawGraphCLM period hPeriod) ∧
      (∀ displacement boundary,
        normalBoundaryC2RawGraphCLM period hPeriod
            (smoothNormalDisplacementToBoundaryC2JetCore
              period hPeriod displacement) boundary =
          normalDisplacementOrientationScalar period hPeriod displacement
            boundary) :=
  ⟨(normalBoundaryC2RawGraphCLM period hPeriod).continuous,
    normalBoundaryC2RawGraphCLM_smooth period hPeriod⟩

/-! ### Smooth latitude formulas used to identify the completed jets -/

private def normalBoundarySmoothFieldLatitudeValue
    (field : SmoothQuotientField period hPeriod Real)
    (boundary : OrientationBoundary period hPeriod) (latitude : Real) : Real :=
  field (normalBoundaryLatitudeFiberPoint
    period hPeriod boundary latitude)

private def normalBoundarySmoothFieldLatitudeFirst
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothQuotientField period hPeriod Real)
    (boundary : OrientationBoundary period hPeriod) (latitude : Real) : Real :=
  ∑ index : Fin (finiteSmoothTangentFrame period hPeriod).count,
    normalBoundaryLatitudeFrameCoefficient
        period hPeriod metric index boundary latitude *
      frameDerivative period hPeriod Real
        (finiteSmoothTangentFrame period hPeriod) field
        (normalBoundaryLatitudeFiberPoint
          period hPeriod boundary latitude) index

private def normalBoundarySmoothFieldLatitudeSecond
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothQuotientField period hPeriod Real)
    (boundary : OrientationBoundary period hPeriod) (latitude : Real) : Real :=
  (∑ index : Fin (finiteSmoothTangentFrame period hPeriod).count,
    normalBoundaryLatitudeFrameCoefficientDerivative
        period hPeriod metric index boundary latitude *
      frameDerivative period hPeriod Real
        (finiteSmoothTangentFrame period hPeriod) field
        (normalBoundaryLatitudeFiberPoint
          period hPeriod boundary latitude) index) +
  ∑ inner : Fin (finiteSmoothTangentFrame period hPeriod).count,
    ∑ outer : Fin (finiteSmoothTangentFrame period hPeriod).count,
      normalBoundaryLatitudeFrameCoefficient
          period hPeriod metric inner boundary latitude *
        normalBoundaryLatitudeFrameCoefficient
          period hPeriod metric outer boundary latitude *
        frameSecondDerivative period hPeriod
          (finiteSmoothTangentFrame period hPeriod) field
          (normalBoundaryLatitudeFiberPoint
            period hPeriod boundary latitude) outer inner

private def normalBoundarySmoothFieldLatitudeThird
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothQuotientField period hPeriod Real)
    (boundary : OrientationBoundary period hPeriod) (latitude : Real) : Real :=
  ((∑ index : Fin (finiteSmoothTangentFrame period hPeriod).count,
      normalBoundaryLatitudeFrameCoefficientSecondDerivative
          period hPeriod metric index boundary latitude *
        frameDerivative period hPeriod Real
          (finiteSmoothTangentFrame period hPeriod) field
          (normalBoundaryLatitudeFiberPoint
            period hPeriod boundary latitude) index) +
    ∑ inner : Fin (finiteSmoothTangentFrame period hPeriod).count,
      ∑ outer : Fin (finiteSmoothTangentFrame period hPeriod).count,
        normalBoundaryLatitudeFrameCoefficientDerivative
            period hPeriod metric inner boundary latitude *
          normalBoundaryLatitudeFrameCoefficient
            period hPeriod metric outer boundary latitude *
          frameSecondDerivative period hPeriod
            (finiteSmoothTangentFrame period hPeriod) field
            (normalBoundaryLatitudeFiberPoint
              period hPeriod boundary latitude) outer inner) +
  ((∑ inner : Fin (finiteSmoothTangentFrame period hPeriod).count,
      ∑ outer : Fin (finiteSmoothTangentFrame period hPeriod).count,
        (normalBoundaryLatitudeFrameCoefficientDerivative
              period hPeriod metric inner boundary latitude *
            normalBoundaryLatitudeFrameCoefficient
              period hPeriod metric outer boundary latitude +
          normalBoundaryLatitudeFrameCoefficient
              period hPeriod metric inner boundary latitude *
            normalBoundaryLatitudeFrameCoefficientDerivative
              period hPeriod metric outer boundary latitude) *
          frameSecondDerivative period hPeriod
            (finiteSmoothTangentFrame period hPeriod) field
            (normalBoundaryLatitudeFiberPoint
              period hPeriod boundary latitude) outer inner) +
    ∑ inner : Fin (finiteSmoothTangentFrame period hPeriod).count,
      ∑ middle : Fin (finiteSmoothTangentFrame period hPeriod).count,
        ∑ outer : Fin (finiteSmoothTangentFrame period hPeriod).count,
          normalBoundaryLatitudeFrameCoefficient
              period hPeriod metric inner boundary latitude *
            normalBoundaryLatitudeFrameCoefficient
              period hPeriod metric middle boundary latitude *
            normalBoundaryLatitudeFrameCoefficient
              period hPeriod metric outer boundary latitude *
            generalMetricFrameThirdDerivative period hPeriod
              (finiteSmoothTangentFrame period hPeriod) field
              (normalBoundaryLatitudeFiberPoint
                period hPeriod boundary latitude) outer middle inner)

private theorem normalBoundarySmoothFieldLatitudeValue_hasDerivAt
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothQuotientField period hPeriod Real)
    (boundary : OrientationBoundary period hPeriod) (latitude : Real) :
    RealHasDerivAt (normalBoundarySmoothFieldLatitudeValue
      period hPeriod field boundary)
      (normalBoundarySmoothFieldLatitudeFirst
        period hPeriod metric field boundary latitude) latitude :=
  normalBoundaryLatitudeSmoothField_hasDerivAt
    period hPeriod metric field boundary latitude

private theorem normalBoundarySmoothFieldLatitudeFirst_hasDerivAt
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothQuotientField period hPeriod Real)
    (boundary : OrientationBoundary period hPeriod) (latitude : Real) :
    RealHasDerivAt (normalBoundarySmoothFieldLatitudeFirst
      period hPeriod metric field boundary)
      (normalBoundarySmoothFieldLatitudeSecond
        period hPeriod metric field boundary latitude) latitude := by
  have hTerm (index : Fin (finiteSmoothTangentFrame period hPeriod).count) :=
    (normalBoundaryLatitudeFrameCoefficient_hasDerivAt
      period hPeriod metric index boundary latitude).mul
        (normalBoundaryLatitudeSmoothField_hasDerivAt
          period hPeriod metric
          (frameDerivativeComponentField period hPeriod
            (finiteSmoothTangentFrame period hPeriod) field index)
          boundary latitude)
  have hSum := HasDerivAt.fun_sum (u := Finset.univ)
    (fun index _ => hTerm index)
  unfold normalBoundarySmoothFieldLatitudeFirst
    normalBoundarySmoothFieldLatitudeSecond
  simpa only [frameDerivativeComponentField, frameSecondDerivative,
    Pi.mul_apply, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc] using hSum

private theorem normalBoundarySmoothFieldLatitudeSecond_hasDerivAt
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothQuotientField period hPeriod Real)
    (boundary : OrientationBoundary period hPeriod) (latitude : Real) :
    RealHasDerivAt (normalBoundarySmoothFieldLatitudeSecond
      period hPeriod metric field boundary)
      (normalBoundarySmoothFieldLatitudeThird
        period hPeriod metric field boundary latitude) latitude := by
  have hFirstTerm
      (index : Fin (finiteSmoothTangentFrame period hPeriod).count) :=
    (normalBoundaryLatitudeFrameCoefficientDerivative_hasDerivAt
      period hPeriod metric index boundary latitude).mul
        (normalBoundaryLatitudeSmoothField_hasDerivAt
          period hPeriod metric
          (frameDerivativeComponentField period hPeriod
            (finiteSmoothTangentFrame period hPeriod) field index)
          boundary latitude)
  have hFirstSum := HasDerivAt.fun_sum (u := Finset.univ)
    (fun index _ => hFirstTerm index)
  have hSecondTerm
      (inner middle : Fin (finiteSmoothTangentFrame period hPeriod).count) :=
    (((normalBoundaryLatitudeFrameCoefficient_hasDerivAt
        period hPeriod metric inner boundary latitude).mul
      (normalBoundaryLatitudeFrameCoefficient_hasDerivAt
        period hPeriod metric middle boundary latitude)).mul
      (normalBoundaryLatitudeSmoothField_hasDerivAt
        period hPeriod metric
        (frameDerivativeComponentField period hPeriod
          (finiteSmoothTangentFrame period hPeriod)
          (frameDerivativeComponentField period hPeriod
            (finiteSmoothTangentFrame period hPeriod) field inner) middle)
        boundary latitude))
  have hSecondInner
      (inner : Fin (finiteSmoothTangentFrame period hPeriod).count) :=
    HasDerivAt.fun_sum (u := Finset.univ)
      (fun middle _ => hSecondTerm inner middle)
  have hSecondSum := HasDerivAt.fun_sum (u := Finset.univ)
    (fun inner _ => hSecondInner inner)
  have hTotal := hFirstSum.add hSecondSum
  apply (hTotal.congr_of_eventuallyEq ?_).congr_deriv
  · unfold normalBoundarySmoothFieldLatitudeThird
    simp only [frameDerivativeComponentField, frameSecondDerivative,
      generalMetricFrameThirdDerivative, Pi.mul_apply,
      Finset.sum_add_distrib, Finset.mul_sum, mul_assoc, add_mul]
  · filter_upwards [] with varied
    unfold normalBoundarySmoothFieldLatitudeSecond
    rfl

/-! ## Existing metric jets on the canonical latitude fiber -/

private abbrev LatitudeCompactScalar :=
  C(OrientationBoundary period hPeriod × ArctanCompactFiber, Real)

private def regularMetricThirdJetComponentCLM
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (row column : Fin 4)
    (outer middle inner : BoundaryMetricJetIndex period hPeriod) :
    RegularMetricThirdJetFiber period hPeriod metric →L[Real] Real :=
  let rowProjection :
      RegularMetricThirdJetFiber period hPeriod metric →L[Real]
        (Fin 4 → BoundaryMetricJetIndex period hPeriod →
          BoundaryMetricJetIndex period hPeriod →
            BoundaryMetricJetIndex period hPeriod → Real) :=
    ContinuousLinearMap.proj row
  let columnProjection :
      (Fin 4 → BoundaryMetricJetIndex period hPeriod →
        BoundaryMetricJetIndex period hPeriod →
          BoundaryMetricJetIndex period hPeriod → Real) →L[Real]
        (BoundaryMetricJetIndex period hPeriod →
          BoundaryMetricJetIndex period hPeriod →
            BoundaryMetricJetIndex period hPeriod → Real) :=
    ContinuousLinearMap.proj column
  let outerProjection :
      (BoundaryMetricJetIndex period hPeriod →
        BoundaryMetricJetIndex period hPeriod →
          BoundaryMetricJetIndex period hPeriod → Real) →L[Real]
        (BoundaryMetricJetIndex period hPeriod →
          BoundaryMetricJetIndex period hPeriod → Real) :=
    ContinuousLinearMap.proj outer
  let middleProjection :
      (BoundaryMetricJetIndex period hPeriod →
        BoundaryMetricJetIndex period hPeriod → Real) →L[Real]
        (BoundaryMetricJetIndex period hPeriod → Real) :=
    ContinuousLinearMap.proj middle
  let innerProjection :
      (BoundaryMetricJetIndex period hPeriod → Real) →L[Real] Real :=
    ContinuousLinearMap.proj inner
  innerProjection.comp (middleProjection.comp (outerProjection.comp
    (columnProjection.comp rowProjection)))

private def regularMetricBoundaryC3ThirdEntryToContinuous
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (row column : Fin 4)
    (outer middle inner : BoundaryMetricJetIndex period hPeriod) :
    RegularGeneralMetricBoundaryC3Core period hPeriod metric →L[Real]
      C(EffectiveQuotient period hPeriod, Real) :=
  ((regularMetricThirdJetComponentCLM period hPeriod metric row column
      outer middle inner).compLeftContinuous Real
        (EffectiveQuotient period hPeriod)).comp
    (regularGeneralMetricBoundaryC3CoreToThirdJet period hPeriod metric)

private def normalBoundaryRelativeMetricValueCompactCLM
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (row column : Fin 4) :
    RegularGeneralMetricBoundaryC3Core period hPeriod metric →L[Real]
      LatitudeCompactScalar period hPeriod :=
  (normalBoundaryLatitudeCompactFieldPullbackCLM period hPeriod).comp
    (regularGeneralMetricBoundaryC3RelativeEntryToContinuous
      period hPeriod metric row column)

private def normalBoundaryRelativeMetricFirstCompactCLM
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (row column : Fin 4)
    (index : BoundaryMetricJetIndex period hPeriod) :
    RegularGeneralMetricBoundaryC3Core period hPeriod metric →L[Real]
      LatitudeCompactScalar period hPeriod :=
  (normalBoundaryLatitudeCompactFieldPullbackCLM period hPeriod).comp
    (regularGeneralMetricBoundaryC3RelativeFirstEntryToContinuous
      period hPeriod metric row column index)

private def normalBoundaryRelativeMetricSecondCompactCLM
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (row column : Fin 4)
    (outer inner : BoundaryMetricJetIndex period hPeriod) :
    RegularGeneralMetricBoundaryC3Core period hPeriod metric →L[Real]
      LatitudeCompactScalar period hPeriod :=
  (normalBoundaryLatitudeCompactFieldPullbackCLM period hPeriod).comp
    (regularGeneralMetricBoundaryC3RelativeSecondEntryToContinuous
      period hPeriod metric row column outer inner)

private def normalBoundaryRelativeMetricThirdCompactCLM
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (row column : Fin 4)
    (outer middle inner : BoundaryMetricJetIndex period hPeriod) :
    RegularGeneralMetricBoundaryC3Core period hPeriod metric →L[Real]
      LatitudeCompactScalar period hPeriod :=
  (normalBoundaryLatitudeCompactFieldPullbackCLM period hPeriod).comp
    (regularMetricBoundaryC3ThirdEntryToContinuous period hPeriod metric
      row column outer middle inner)

/-- Value component of one completed relative-metric entry along the compact
latitude strip. -/
def normalBoundaryRelativeMetricLatitudeValueCompactCLM
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (row column : Fin 4) :
    RegularGeneralMetricBoundaryC3Core period hPeriod metric →L[Real]
      LatitudeCompactScalar period hPeriod :=
  normalBoundaryRelativeMetricValueCompactCLM period hPeriod metric row column

/-- First latitude derivative obtained by contracting the existing first
frame jet with the intrinsic normal coefficients. -/
def normalBoundaryRelativeMetricLatitudeFirstCompactCLM
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (row column : Fin 4) :
    RegularGeneralMetricBoundaryC3Core period hPeriod metric →L[Real]
      LatitudeCompactScalar period hPeriod :=
  ∑ index : BoundaryMetricJetIndex period hPeriod,
    (ContinuousLinearMap.mul Real (LatitudeCompactScalar period hPeriod)
      (normalBoundaryLatitudeFrameCoefficientCompact
        period hPeriod metric.metric index)).comp
      (normalBoundaryRelativeMetricFirstCompactCLM
        period hPeriod metric row column index)

/-- Second latitude derivative, including the derivative of the moving
finite-frame coefficients. -/
def normalBoundaryRelativeMetricLatitudeSecondCompactCLM
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (row column : Fin 4) :
    RegularGeneralMetricBoundaryC3Core period hPeriod metric →L[Real]
      LatitudeCompactScalar period hPeriod :=
  (∑ index : BoundaryMetricJetIndex period hPeriod,
    (ContinuousLinearMap.mul Real (LatitudeCompactScalar period hPeriod)
      (normalBoundaryLatitudeFrameCoefficientDerivativeCompact
        period hPeriod metric.metric index)).comp
      (normalBoundaryRelativeMetricFirstCompactCLM
        period hPeriod metric row column index)) +
  ∑ inner : BoundaryMetricJetIndex period hPeriod,
    ∑ outer : BoundaryMetricJetIndex period hPeriod,
      (ContinuousLinearMap.mul Real (LatitudeCompactScalar period hPeriod)
        (normalBoundaryLatitudeFrameCoefficientCompact
            period hPeriod metric.metric inner *
          normalBoundaryLatitudeFrameCoefficientCompact
            period hPeriod metric.metric outer)).comp
        (normalBoundaryRelativeMetricSecondCompactCLM
          period hPeriod metric row column outer inner)

/-- Third latitude derivative obtained from the existing ordered third frame
jet and the first two derivatives of the intrinsic coefficients. -/
def normalBoundaryRelativeMetricLatitudeThirdCompactCLM
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (row column : Fin 4) :
    RegularGeneralMetricBoundaryC3Core period hPeriod metric →L[Real]
      LatitudeCompactScalar period hPeriod :=
  ((∑ index : BoundaryMetricJetIndex period hPeriod,
      (ContinuousLinearMap.mul Real (LatitudeCompactScalar period hPeriod)
        (normalBoundaryLatitudeFrameCoefficientSecondDerivativeCompact
          period hPeriod metric.metric index)).comp
        (normalBoundaryRelativeMetricFirstCompactCLM
          period hPeriod metric row column index)) +
    ∑ inner : BoundaryMetricJetIndex period hPeriod,
      ∑ outer : BoundaryMetricJetIndex period hPeriod,
        (ContinuousLinearMap.mul Real (LatitudeCompactScalar period hPeriod)
          (normalBoundaryLatitudeFrameCoefficientDerivativeCompact
                period hPeriod metric.metric inner *
            normalBoundaryLatitudeFrameCoefficientCompact
              period hPeriod metric.metric outer)).comp
          (normalBoundaryRelativeMetricSecondCompactCLM
            period hPeriod metric row column outer inner)) +
  ((∑ inner : BoundaryMetricJetIndex period hPeriod,
      ∑ outer : BoundaryMetricJetIndex period hPeriod,
        (ContinuousLinearMap.mul Real (LatitudeCompactScalar period hPeriod)
          (normalBoundaryLatitudeFrameCoefficientDerivativeCompact
                period hPeriod metric.metric inner *
              normalBoundaryLatitudeFrameCoefficientCompact
                period hPeriod metric.metric outer +
            normalBoundaryLatitudeFrameCoefficientCompact
                period hPeriod metric.metric inner *
              normalBoundaryLatitudeFrameCoefficientDerivativeCompact
                period hPeriod metric.metric outer)).comp
          (normalBoundaryRelativeMetricSecondCompactCLM
            period hPeriod metric row column outer inner)) +
    ∑ inner : BoundaryMetricJetIndex period hPeriod,
      ∑ middle : BoundaryMetricJetIndex period hPeriod,
        ∑ outer : BoundaryMetricJetIndex period hPeriod,
          (ContinuousLinearMap.mul Real (LatitudeCompactScalar period hPeriod)
            (normalBoundaryLatitudeFrameCoefficientCompact
                  period hPeriod metric.metric inner *
              normalBoundaryLatitudeFrameCoefficientCompact
                  period hPeriod metric.metric middle *
              normalBoundaryLatitudeFrameCoefficientCompact
                period hPeriod metric.metric outer)).comp
            (normalBoundaryRelativeMetricThirdCompactCLM
              period hPeriod metric row column outer middle inner))

/-! ### Latitude jets of one existing spatial first derivative -/

/-- Value of a fixed physical-frame first derivative along the compact
latitude collar. -/
def normalBoundaryRelativeMetricSpatialFirstLatitudeValueCompactCLM
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (row column : Fin 4)
    (spatial : BoundaryMetricJetIndex period hPeriod) :
    RegularGeneralMetricBoundaryC3Core period hPeriod metric →L[Real]
      LatitudeCompactScalar period hPeriod :=
  normalBoundaryRelativeMetricFirstCompactCLM
    period hPeriod metric row column spatial

/-- First latitude derivative of the fixed spatial first derivative. -/
def normalBoundaryRelativeMetricSpatialFirstLatitudeFirstCompactCLM
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (row column : Fin 4)
    (spatial : BoundaryMetricJetIndex period hPeriod) :
    RegularGeneralMetricBoundaryC3Core period hPeriod metric →L[Real]
      LatitudeCompactScalar period hPeriod :=
  ∑ outer : BoundaryMetricJetIndex period hPeriod,
    (ContinuousLinearMap.mul Real (LatitudeCompactScalar period hPeriod)
      (normalBoundaryLatitudeFrameCoefficientCompact
        period hPeriod metric.metric outer)).comp
      (normalBoundaryRelativeMetricSecondCompactCLM
        period hPeriod metric row column outer spatial)

/-- Second latitude derivative of the fixed spatial first derivative.  Its
highest term is exactly the already completed ordered third metric jet. -/
def normalBoundaryRelativeMetricSpatialFirstLatitudeSecondCompactCLM
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (row column : Fin 4)
    (spatial : BoundaryMetricJetIndex period hPeriod) :
    RegularGeneralMetricBoundaryC3Core period hPeriod metric →L[Real]
      LatitudeCompactScalar period hPeriod :=
  (∑ outer : BoundaryMetricJetIndex period hPeriod,
    (ContinuousLinearMap.mul Real (LatitudeCompactScalar period hPeriod)
      (normalBoundaryLatitudeFrameCoefficientDerivativeCompact
        period hPeriod metric.metric outer)).comp
      (normalBoundaryRelativeMetricSecondCompactCLM
        period hPeriod metric row column outer spatial)) +
  ∑ middle : BoundaryMetricJetIndex period hPeriod,
    ∑ outer : BoundaryMetricJetIndex period hPeriod,
      (ContinuousLinearMap.mul Real (LatitudeCompactScalar period hPeriod)
        (normalBoundaryLatitudeFrameCoefficientCompact
              period hPeriod metric.metric middle *
          normalBoundaryLatitudeFrameCoefficientCompact
            period hPeriod metric.metric outer)).comp
        (normalBoundaryRelativeMetricThirdCompactCLM
          period hPeriod metric row column outer middle spatial)

private abbrev normalBoundarySmoothRelativeMetricField
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (row column : Fin 4) : SmoothQuotientField period hPeriod Real :=
  smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod
    (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
    metric.metric tensor row column

private abbrev normalBoundarySmoothRelativeMetricSpatialFirstField
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (row column : Fin 4)
    (spatial : BoundaryMetricJetIndex period hPeriod) :
    SmoothQuotientField period hPeriod Real :=
  frameDerivativeComponentField period hPeriod
    (finiteSmoothTangentFrame period hPeriod)
    (normalBoundarySmoothRelativeMetricField
      period hPeriod metric tensor row column) spatial

private theorem
    normalBoundaryRelativeMetricSpatialFirstLatitudeValueCompactCLM_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (row column : Fin 4)
    (spatial : BoundaryMetricJetIndex period hPeriod)
    (boundary : OrientationBoundary period hPeriod)
    (latitude : ArctanCompactFiber) :
    normalBoundaryRelativeMetricSpatialFirstLatitudeValueCompactCLM
        period hPeriod metric row column spatial
        (smoothToRegularGeneralMetricBoundaryC3Core
          period hPeriod metric tensor) (boundary, latitude) =
      normalBoundarySmoothFieldLatitudeValue period hPeriod
        (normalBoundarySmoothRelativeMetricSpatialFirstField
          period hPeriod metric tensor row column spatial)
        boundary latitude := by
  rfl

private theorem
    normalBoundaryRelativeMetricSpatialFirstLatitudeFirstCompactCLM_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (row column : Fin 4)
    (spatial : BoundaryMetricJetIndex period hPeriod)
    (boundary : OrientationBoundary period hPeriod)
    (latitude : ArctanCompactFiber) :
    normalBoundaryRelativeMetricSpatialFirstLatitudeFirstCompactCLM
        period hPeriod metric row column spatial
        (smoothToRegularGeneralMetricBoundaryC3Core
          period hPeriod metric tensor) (boundary, latitude) =
      normalBoundarySmoothFieldLatitudeFirst period hPeriod metric.metric
        (normalBoundarySmoothRelativeMetricSpatialFirstField
          period hPeriod metric tensor row column spatial)
        boundary latitude := by
  simp [normalBoundaryRelativeMetricSpatialFirstLatitudeFirstCompactCLM,
    normalBoundaryRelativeMetricSecondCompactCLM,
    normalBoundarySmoothFieldLatitudeFirst,
    normalBoundarySmoothRelativeMetricSpatialFirstField,
    normalBoundaryLatitudeFrameCoefficientCompact,
    normalBoundaryLatitudeCompactFieldPullbackCLM,
    normalBoundaryLatitudeCompactInput, frameSecondDerivative]

private theorem
    normalBoundaryRelativeMetricSpatialFirstLatitudeSecondCompactCLM_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (row column : Fin 4)
    (spatial : BoundaryMetricJetIndex period hPeriod)
    (boundary : OrientationBoundary period hPeriod)
    (latitude : ArctanCompactFiber) :
    normalBoundaryRelativeMetricSpatialFirstLatitudeSecondCompactCLM
        period hPeriod metric row column spatial
        (smoothToRegularGeneralMetricBoundaryC3Core
          period hPeriod metric tensor) (boundary, latitude) =
      normalBoundarySmoothFieldLatitudeSecond period hPeriod metric.metric
        (normalBoundarySmoothRelativeMetricSpatialFirstField
          period hPeriod metric tensor row column spatial)
        boundary latitude := by
  simp [normalBoundaryRelativeMetricSpatialFirstLatitudeSecondCompactCLM,
    normalBoundaryRelativeMetricSecondCompactCLM,
    normalBoundaryRelativeMetricThirdCompactCLM,
    regularMetricBoundaryC3ThirdEntryToContinuous,
    regularMetricThirdJetComponentCLM,
    smoothRegularGeneralMetricRelativeThirdJetLinearMap,
    smoothRegularGeneralMetricRelativeThirdJet,
    generalMetricFrameThirdDerivative,
    normalBoundarySmoothFieldLatitudeSecond,
    normalBoundarySmoothRelativeMetricSpatialFirstField,
    normalBoundaryLatitudeFrameCoefficientCompact,
    normalBoundaryLatitudeFrameCoefficientDerivativeCompact,
    normalBoundaryLatitudeCompactFieldPullbackCLM,
    normalBoundaryLatitudeCompactInput, frameSecondDerivative]

private theorem normalBoundaryRelativeMetricLatitudeValueCompactCLM_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (row column : Fin 4) (boundary : OrientationBoundary period hPeriod)
    (latitude : ArctanCompactFiber) :
    normalBoundaryRelativeMetricLatitudeValueCompactCLM
        period hPeriod metric row column
        (smoothToRegularGeneralMetricBoundaryC3Core
          period hPeriod metric tensor) (boundary, latitude) =
      normalBoundarySmoothFieldLatitudeValue period hPeriod
        (normalBoundarySmoothRelativeMetricField
          period hPeriod metric tensor row column) boundary latitude := by
  rfl

private theorem normalBoundaryRelativeMetricLatitudeFirstCompactCLM_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (row column : Fin 4) (boundary : OrientationBoundary period hPeriod)
    (latitude : ArctanCompactFiber) :
    normalBoundaryRelativeMetricLatitudeFirstCompactCLM
        period hPeriod metric row column
        (smoothToRegularGeneralMetricBoundaryC3Core
          period hPeriod metric tensor) (boundary, latitude) =
      normalBoundarySmoothFieldLatitudeFirst period hPeriod metric.metric
        (normalBoundarySmoothRelativeMetricField
          period hPeriod metric tensor row column) boundary latitude := by
  simp [normalBoundaryRelativeMetricLatitudeFirstCompactCLM,
    normalBoundaryRelativeMetricFirstCompactCLM,
    normalBoundarySmoothFieldLatitudeFirst,
    normalBoundarySmoothRelativeMetricField,
    normalBoundaryLatitudeFrameCoefficientCompact,
    normalBoundaryLatitudeCompactFieldPullbackCLM,
    normalBoundaryLatitudeCompactInput]

private theorem normalBoundaryRelativeMetricLatitudeSecondCompactCLM_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (row column : Fin 4) (boundary : OrientationBoundary period hPeriod)
    (latitude : ArctanCompactFiber) :
    normalBoundaryRelativeMetricLatitudeSecondCompactCLM
        period hPeriod metric row column
        (smoothToRegularGeneralMetricBoundaryC3Core
          period hPeriod metric tensor) (boundary, latitude) =
      normalBoundarySmoothFieldLatitudeSecond period hPeriod metric.metric
        (normalBoundarySmoothRelativeMetricField
          period hPeriod metric tensor row column) boundary latitude := by
  simp [normalBoundaryRelativeMetricLatitudeSecondCompactCLM,
    normalBoundaryRelativeMetricFirstCompactCLM,
    normalBoundaryRelativeMetricSecondCompactCLM,
    normalBoundarySmoothFieldLatitudeSecond,
    normalBoundarySmoothRelativeMetricField,
    normalBoundaryLatitudeFrameCoefficientCompact,
    normalBoundaryLatitudeFrameCoefficientDerivativeCompact,
    normalBoundaryLatitudeCompactFieldPullbackCLM,
    normalBoundaryLatitudeCompactInput]

private theorem normalBoundaryRelativeMetricLatitudeThirdCompactCLM_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (row column : Fin 4) (boundary : OrientationBoundary period hPeriod)
    (latitude : ArctanCompactFiber) :
    normalBoundaryRelativeMetricLatitudeThirdCompactCLM
        period hPeriod metric row column
        (smoothToRegularGeneralMetricBoundaryC3Core
          period hPeriod metric tensor) (boundary, latitude) =
      normalBoundarySmoothFieldLatitudeThird period hPeriod metric.metric
        (normalBoundarySmoothRelativeMetricField
          period hPeriod metric tensor row column) boundary latitude := by
  simp [normalBoundaryRelativeMetricLatitudeThirdCompactCLM,
    normalBoundaryRelativeMetricFirstCompactCLM,
    normalBoundaryRelativeMetricSecondCompactCLM,
    normalBoundaryRelativeMetricThirdCompactCLM,
    regularMetricBoundaryC3ThirdEntryToContinuous,
    regularMetricThirdJetComponentCLM,
    smoothRegularGeneralMetricRelativeThirdJetLinearMap,
    smoothRegularGeneralMetricRelativeThirdJet,
    normalBoundarySmoothFieldLatitudeThird,
    normalBoundarySmoothRelativeMetricField,
    normalBoundaryLatitudeFrameCoefficientCompact,
    normalBoundaryLatitudeFrameCoefficientDerivativeCompact,
    normalBoundaryLatitudeFrameCoefficientSecondDerivativeCompact,
    normalBoundaryLatitudeCompactFieldPullbackCLM,
    normalBoundaryLatitudeCompactInput, add_mul]

private abbrev RawFiberScalar :=
  BoundedFiberField (OrientationBoundary period hPeriod)

private def normalBoundaryRelativeMetricLatitudeValueRawCLM
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (row column : Fin 4) :
    RegularGeneralMetricBoundaryC3Core period hPeriod metric →L[Real]
      RawFiberScalar period hPeriod :=
  (boundedArctanCompactPullbackCLM
    (OrientationBoundary period hPeriod)).comp
      (normalBoundaryRelativeMetricLatitudeValueCompactCLM
        period hPeriod metric row column)

private def normalBoundaryRelativeMetricLatitudeFirstRawCLM
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (row column : Fin 4) :
    RegularGeneralMetricBoundaryC3Core period hPeriod metric →L[Real]
      RawFiberScalar period hPeriod :=
  (boundedArctanCompactPullbackCLM
    (OrientationBoundary period hPeriod)).comp
      (normalBoundaryRelativeMetricLatitudeFirstCompactCLM
        period hPeriod metric row column)

private def normalBoundaryRelativeMetricLatitudeSecondRawCLM
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (row column : Fin 4) :
    RegularGeneralMetricBoundaryC3Core period hPeriod metric →L[Real]
      RawFiberScalar period hPeriod :=
  (boundedArctanCompactPullbackCLM
    (OrientationBoundary period hPeriod)).comp
      (normalBoundaryRelativeMetricLatitudeSecondCompactCLM
        period hPeriod metric row column)

private def normalBoundaryRelativeMetricLatitudeThirdRawCLM
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (row column : Fin 4) :
    RegularGeneralMetricBoundaryC3Core period hPeriod metric →L[Real]
      RawFiberScalar period hPeriod :=
  (boundedArctanCompactPullbackCLM
    (OrientationBoundary period hPeriod)).comp
      (normalBoundaryRelativeMetricLatitudeThirdCompactCLM
        period hPeriod metric row column)

/-- Raw value field; only the coordinate is changed from latitude to the
unrestricted `arctan` parameter. -/
def normalBoundaryRelativeMetricRawValueCLM
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (row column : Fin 4) :
    RegularGeneralMetricBoundaryC3Core period hPeriod metric →L[Real]
      RawFiberScalar period hPeriod :=
  normalBoundaryRelativeMetricLatitudeValueRawCLM
    period hPeriod metric row column

@[simp]
theorem normalBoundaryRelativeMetricRawValueCLM_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (row column : Fin 4)
    (variation : RegularGeneralMetricBoundaryC3Core period hPeriod metric)
    (boundary : OrientationBoundary period hPeriod) (fiber : Real) :
    normalBoundaryRelativeMetricRawValueCLM period hPeriod metric row column
        variation (boundary, fiber) =
      regularGeneralMetricBoundaryC3RelativeEntryToContinuous period hPeriod
        metric row column variation
        (normalBoundaryRawFiberPoint period hPeriod boundary fiber) := by
  rw [normalBoundaryRawFiberPoint_eq_latitude]
  rfl

/-- First raw-fiber derivative by the exact `arctan` chain rule. -/
def normalBoundaryRelativeMetricRawFirstCLM
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (row column : Fin 4) :
    RegularGeneralMetricBoundaryC3Core period hPeriod metric →L[Real]
      RawFiberScalar period hPeriod :=
  (ContinuousLinearMap.mul Real (RawFiberScalar period hPeriod)
    ((boundedFiberArctanJet3
      (OrientationBoundary period hPeriod)).1 1)).comp
        (normalBoundaryRelativeMetricLatitudeFirstRawCLM
          period hPeriod metric row column)

/-- Second raw-fiber derivative by the exact `arctan` chain rule. -/
def normalBoundaryRelativeMetricRawSecondCLM
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (row column : Fin 4) :
    RegularGeneralMetricBoundaryC3Core period hPeriod metric →L[Real]
      RawFiberScalar period hPeriod :=
  ((ContinuousLinearMap.mul Real (RawFiberScalar period hPeriod)
    (((boundedFiberArctanJet3
      (OrientationBoundary period hPeriod)).1 1) ^ 2)).comp
        (normalBoundaryRelativeMetricLatitudeSecondRawCLM
          period hPeriod metric row column)) +
  (ContinuousLinearMap.mul Real (RawFiberScalar period hPeriod)
    ((boundedFiberArctanJet3
      (OrientationBoundary period hPeriod)).1 2)).comp
        (normalBoundaryRelativeMetricLatitudeFirstRawCLM
          period hPeriod metric row column)

/-- Third raw-fiber derivative by the exact `arctan` chain rule. -/
def normalBoundaryRelativeMetricRawThirdCLM
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (row column : Fin 4) :
    RegularGeneralMetricBoundaryC3Core period hPeriod metric →L[Real]
      RawFiberScalar period hPeriod :=
  ((ContinuousLinearMap.mul Real (RawFiberScalar period hPeriod)
    (((boundedFiberArctanJet3
      (OrientationBoundary period hPeriod)).1 1) ^ 3)).comp
        (normalBoundaryRelativeMetricLatitudeThirdRawCLM
          period hPeriod metric row column)) +
  ((ContinuousLinearMap.mul Real (RawFiberScalar period hPeriod)
    ((3 : Real) •
      ((boundedFiberArctanJet3
          (OrientationBoundary period hPeriod)).1 1 *
        (boundedFiberArctanJet3
          (OrientationBoundary period hPeriod)).1 2))).comp
        (normalBoundaryRelativeMetricLatitudeSecondRawCLM
          period hPeriod metric row column)) +
  (ContinuousLinearMap.mul Real (RawFiberScalar period hPeriod)
    ((boundedFiberArctanJet3
      (OrientationBoundary period hPeriod)).1 3)).comp
        (normalBoundaryRelativeMetricLatitudeFirstRawCLM
          period hPeriod metric row column)

private def normalBoundaryRelativeMetricSpatialFirstLatitudeValueRawCLM
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (row column : Fin 4)
    (spatial : BoundaryMetricJetIndex period hPeriod) :
    RegularGeneralMetricBoundaryC3Core period hPeriod metric →L[Real]
      RawFiberScalar period hPeriod :=
  (boundedArctanCompactPullbackCLM
    (OrientationBoundary period hPeriod)).comp
      (normalBoundaryRelativeMetricSpatialFirstLatitudeValueCompactCLM
        period hPeriod metric row column spatial)

private def normalBoundaryRelativeMetricSpatialFirstLatitudeFirstRawCLM
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (row column : Fin 4)
    (spatial : BoundaryMetricJetIndex period hPeriod) :
    RegularGeneralMetricBoundaryC3Core period hPeriod metric →L[Real]
      RawFiberScalar period hPeriod :=
  (boundedArctanCompactPullbackCLM
    (OrientationBoundary period hPeriod)).comp
      (normalBoundaryRelativeMetricSpatialFirstLatitudeFirstCompactCLM
        period hPeriod metric row column spatial)

private def normalBoundaryRelativeMetricSpatialFirstLatitudeSecondRawCLM
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (row column : Fin 4)
    (spatial : BoundaryMetricJetIndex period hPeriod) :
    RegularGeneralMetricBoundaryC3Core period hPeriod metric →L[Real]
      RawFiberScalar period hPeriod :=
  (boundedArctanCompactPullbackCLM
    (OrientationBoundary period hPeriod)).comp
      (normalBoundaryRelativeMetricSpatialFirstLatitudeSecondCompactCLM
        period hPeriod metric row column spatial)

/-- Raw value of one existing spatial first derivative. -/
def normalBoundaryRelativeMetricSpatialFirstRawValueCLM
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (row column : Fin 4)
    (spatial : BoundaryMetricJetIndex period hPeriod) :
    RegularGeneralMetricBoundaryC3Core period hPeriod metric →L[Real]
      RawFiberScalar period hPeriod :=
  normalBoundaryRelativeMetricSpatialFirstLatitudeValueRawCLM
    period hPeriod metric row column spatial

@[simp]
theorem normalBoundaryRelativeMetricSpatialFirstRawValueCLM_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (row column : Fin 4)
    (spatial : BoundaryMetricJetIndex period hPeriod)
    (variation : RegularGeneralMetricBoundaryC3Core period hPeriod metric)
    (boundary : OrientationBoundary period hPeriod) (fiber : Real) :
    normalBoundaryRelativeMetricSpatialFirstRawValueCLM period hPeriod
        metric row column spatial variation (boundary, fiber) =
      regularGeneralMetricBoundaryC3RelativeFirstEntryToContinuous
        period hPeriod metric row column spatial variation
        (normalBoundaryRawFiberPoint period hPeriod boundary fiber) := by
  rw [normalBoundaryRawFiberPoint_eq_latitude]
  rfl

/-- First raw-fiber derivative of the fixed spatial first derivative. -/
def normalBoundaryRelativeMetricSpatialFirstRawFirstCLM
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (row column : Fin 4)
    (spatial : BoundaryMetricJetIndex period hPeriod) :
    RegularGeneralMetricBoundaryC3Core period hPeriod metric →L[Real]
      RawFiberScalar period hPeriod :=
  (ContinuousLinearMap.mul Real (RawFiberScalar period hPeriod)
    ((boundedFiberArctanJet3
      (OrientationBoundary period hPeriod)).1 1)).comp
        (normalBoundaryRelativeMetricSpatialFirstLatitudeFirstRawCLM
          period hPeriod metric row column spatial)

/-- Second raw-fiber derivative of the fixed spatial first derivative. -/
def normalBoundaryRelativeMetricSpatialFirstRawSecondCLM
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (row column : Fin 4)
    (spatial : BoundaryMetricJetIndex period hPeriod) :
    RegularGeneralMetricBoundaryC3Core period hPeriod metric →L[Real]
      RawFiberScalar period hPeriod :=
  ((ContinuousLinearMap.mul Real (RawFiberScalar period hPeriod)
    (((boundedFiberArctanJet3
      (OrientationBoundary period hPeriod)).1 1) ^ 2)).comp
        (normalBoundaryRelativeMetricSpatialFirstLatitudeSecondRawCLM
          period hPeriod metric row column spatial)) +
  (ContinuousLinearMap.mul Real (RawFiberScalar period hPeriod)
    ((boundedFiberArctanJet3
      (OrientationBoundary period hPeriod)).1 2)).comp
        (normalBoundaryRelativeMetricSpatialFirstLatitudeFirstRawCLM
          period hPeriod metric row column spatial)

private theorem normalBoundaryRelativeMetricSpatialFirstRawValueCLM_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (row column : Fin 4)
    (spatial : BoundaryMetricJetIndex period hPeriod)
    (boundary : OrientationBoundary period hPeriod) (fiber : Real) :
    normalBoundaryRelativeMetricSpatialFirstRawValueCLM period hPeriod
        metric row column spatial
        (smoothToRegularGeneralMetricBoundaryC3Core
          period hPeriod metric tensor) (boundary, fiber) =
      normalBoundarySmoothFieldLatitudeValue period hPeriod
        (normalBoundarySmoothRelativeMetricSpatialFirstField
          period hPeriod metric tensor row column spatial)
        boundary (Real.arctan fiber) := by
  rfl

private theorem normalBoundaryRelativeMetricSpatialFirstRawFirstCLM_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (row column : Fin 4)
    (spatial : BoundaryMetricJetIndex period hPeriod)
    (boundary : OrientationBoundary period hPeriod) (fiber : Real) :
    normalBoundaryRelativeMetricSpatialFirstRawFirstCLM period hPeriod
        metric row column spatial
        (smoothToRegularGeneralMetricBoundaryC3Core
          period hPeriod metric tensor) (boundary, fiber) =
      (boundedFiberArctanJet3
          (OrientationBoundary period hPeriod)).1 1 (boundary, fiber) *
        normalBoundarySmoothFieldLatitudeFirst period hPeriod metric.metric
          (normalBoundarySmoothRelativeMetricSpatialFirstField
            period hPeriod metric tensor row column spatial)
          boundary (Real.arctan fiber) := by
  simp [normalBoundaryRelativeMetricSpatialFirstRawFirstCLM,
    normalBoundaryRelativeMetricSpatialFirstLatitudeFirstRawCLM,
    normalBoundaryRelativeMetricSpatialFirstLatitudeFirstCompactCLM_smooth,
    arctanCompactFiberMap]

private theorem normalBoundaryRelativeMetricSpatialFirstRawSecondCLM_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (row column : Fin 4)
    (spatial : BoundaryMetricJetIndex period hPeriod)
    (boundary : OrientationBoundary period hPeriod) (fiber : Real) :
    normalBoundaryRelativeMetricSpatialFirstRawSecondCLM period hPeriod
        metric row column spatial
        (smoothToRegularGeneralMetricBoundaryC3Core
          period hPeriod metric tensor) (boundary, fiber) =
      ((boundedFiberArctanJet3
          (OrientationBoundary period hPeriod)).1 1 (boundary, fiber)) ^ 2 *
        normalBoundarySmoothFieldLatitudeSecond period hPeriod metric.metric
          (normalBoundarySmoothRelativeMetricSpatialFirstField
            period hPeriod metric tensor row column spatial)
          boundary (Real.arctan fiber) +
      (boundedFiberArctanJet3
          (OrientationBoundary period hPeriod)).1 2 (boundary, fiber) *
        normalBoundarySmoothFieldLatitudeFirst period hPeriod metric.metric
          (normalBoundarySmoothRelativeMetricSpatialFirstField
            period hPeriod metric tensor row column spatial)
          boundary (Real.arctan fiber) := by
  simp [normalBoundaryRelativeMetricSpatialFirstRawSecondCLM,
    normalBoundaryRelativeMetricSpatialFirstLatitudeFirstRawCLM,
    normalBoundaryRelativeMetricSpatialFirstLatitudeSecondRawCLM,
    normalBoundaryRelativeMetricSpatialFirstLatitudeFirstCompactCLM_smooth,
    normalBoundaryRelativeMetricSpatialFirstLatitudeSecondCompactCLM_smooth,
    arctanCompactFiberMap]

private theorem normalBoundaryRelativeMetricRawValueCLM_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (row column : Fin 4) (boundary : OrientationBoundary period hPeriod)
    (fiber : Real) :
    normalBoundaryRelativeMetricRawValueCLM period hPeriod metric row column
        (smoothToRegularGeneralMetricBoundaryC3Core
          period hPeriod metric tensor) (boundary, fiber) =
      normalBoundarySmoothFieldLatitudeValue period hPeriod
        (normalBoundarySmoothRelativeMetricField
          period hPeriod metric tensor row column) boundary
        (Real.arctan fiber) := by
  rfl

private theorem normalBoundaryRelativeMetricRawFirstCLM_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (row column : Fin 4) (boundary : OrientationBoundary period hPeriod)
    (fiber : Real) :
    normalBoundaryRelativeMetricRawFirstCLM period hPeriod metric row column
        (smoothToRegularGeneralMetricBoundaryC3Core
          period hPeriod metric tensor) (boundary, fiber) =
      (boundedFiberArctanJet3
          (OrientationBoundary period hPeriod)).1 1 (boundary, fiber) *
        normalBoundarySmoothFieldLatitudeFirst period hPeriod metric.metric
          (normalBoundarySmoothRelativeMetricField
            period hPeriod metric tensor row column) boundary
          (Real.arctan fiber) := by
  simp [normalBoundaryRelativeMetricRawFirstCLM,
    normalBoundaryRelativeMetricLatitudeFirstRawCLM,
    normalBoundaryRelativeMetricLatitudeFirstCompactCLM_smooth,
    arctanCompactFiberMap]

private theorem normalBoundaryRelativeMetricRawSecondCLM_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (row column : Fin 4) (boundary : OrientationBoundary period hPeriod)
    (fiber : Real) :
    normalBoundaryRelativeMetricRawSecondCLM period hPeriod metric row column
        (smoothToRegularGeneralMetricBoundaryC3Core
          period hPeriod metric tensor) (boundary, fiber) =
      ((boundedFiberArctanJet3
          (OrientationBoundary period hPeriod)).1 1 (boundary, fiber)) ^ 2 *
        normalBoundarySmoothFieldLatitudeSecond period hPeriod metric.metric
          (normalBoundarySmoothRelativeMetricField
            period hPeriod metric tensor row column) boundary
          (Real.arctan fiber) +
      (boundedFiberArctanJet3
          (OrientationBoundary period hPeriod)).1 2 (boundary, fiber) *
        normalBoundarySmoothFieldLatitudeFirst period hPeriod metric.metric
          (normalBoundarySmoothRelativeMetricField
            period hPeriod metric tensor row column) boundary
          (Real.arctan fiber) := by
  simp [normalBoundaryRelativeMetricRawSecondCLM,
    normalBoundaryRelativeMetricLatitudeFirstRawCLM,
    normalBoundaryRelativeMetricLatitudeSecondRawCLM,
    normalBoundaryRelativeMetricLatitudeFirstCompactCLM_smooth,
    normalBoundaryRelativeMetricLatitudeSecondCompactCLM_smooth,
    arctanCompactFiberMap]

private theorem normalBoundaryRelativeMetricRawThirdCLM_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (row column : Fin 4) (boundary : OrientationBoundary period hPeriod)
    (fiber : Real) :
    normalBoundaryRelativeMetricRawThirdCLM period hPeriod metric row column
        (smoothToRegularGeneralMetricBoundaryC3Core
          period hPeriod metric tensor) (boundary, fiber) =
      ((boundedFiberArctanJet3
          (OrientationBoundary period hPeriod)).1 1 (boundary, fiber)) ^ 3 *
        normalBoundarySmoothFieldLatitudeThird period hPeriod metric.metric
          (normalBoundarySmoothRelativeMetricField
            period hPeriod metric tensor row column) boundary
          (Real.arctan fiber) +
      (3 : Real) *
          ((boundedFiberArctanJet3
              (OrientationBoundary period hPeriod)).1 1 (boundary, fiber) *
            (boundedFiberArctanJet3
              (OrientationBoundary period hPeriod)).1 2 (boundary, fiber)) *
        normalBoundarySmoothFieldLatitudeSecond period hPeriod metric.metric
          (normalBoundarySmoothRelativeMetricField
            period hPeriod metric tensor row column) boundary
          (Real.arctan fiber) +
      (boundedFiberArctanJet3
          (OrientationBoundary period hPeriod)).1 3 (boundary, fiber) *
        normalBoundarySmoothFieldLatitudeFirst period hPeriod metric.metric
          (normalBoundarySmoothRelativeMetricField
            period hPeriod metric tensor row column) boundary
          (Real.arctan fiber) := by
  simp [normalBoundaryRelativeMetricRawThirdCLM,
    normalBoundaryRelativeMetricLatitudeFirstRawCLM,
    normalBoundaryRelativeMetricLatitudeSecondRawCLM,
    normalBoundaryRelativeMetricLatitudeThirdRawCLM,
    normalBoundaryRelativeMetricLatitudeFirstCompactCLM_smooth,
    normalBoundaryRelativeMetricLatitudeSecondCompactCLM_smooth,
    normalBoundaryRelativeMetricLatitudeThirdCompactCLM_smooth,
    arctanCompactFiberMap]
  ring

/-- Continuous linear ambient raw third jet assembled from the single
existing `C³` metric core. -/
def normalBoundaryRelativeMetricRawJetAmbientCLM
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (row column : Fin 4) :
    RegularGeneralMetricBoundaryC3Core period hPeriod metric →L[Real]
      BoundedFiberJet3Ambient (OrientationBoundary period hPeriod) :=
  ContinuousLinearMap.pi ![
    normalBoundaryRelativeMetricRawValueCLM
      period hPeriod metric row column,
    normalBoundaryRelativeMetricRawFirstCLM
      period hPeriod metric row column,
    normalBoundaryRelativeMetricRawSecondCLM
      period hPeriod metric row column,
    normalBoundaryRelativeMetricRawThirdCLM
      period hPeriod metric row column]

private theorem normalBoundaryRelativeMetricRawJetAmbientCLM_smooth_mem
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (row column : Fin 4) :
    (boundedFiberJet3Submodule
      (OrientationBoundary period hPeriod)).carrier
        (normalBoundaryRelativeMetricRawJetAmbientCLM period hPeriod metric
          row column (smoothToRegularGeneralMetricBoundaryC3Core
            period hPeriod metric tensor)) := by
  refine And.intro ?_ (And.intro ?_ ?_)
  next =>
    intro boundary fiber
    change RealHasDerivAt
      (fun varied => normalBoundaryRelativeMetricRawValueCLM
        period hPeriod metric row column
        (smoothToRegularGeneralMetricBoundaryC3Core
          period hPeriod metric tensor) (boundary, varied))
      (normalBoundaryRelativeMetricRawFirstCLM
        period hPeriod metric row column
        (smoothToRegularGeneralMetricBoundaryC3Core
          period hPeriod metric tensor) (boundary, fiber)) fiber
    have hComposed :=
      (normalBoundarySmoothFieldLatitudeValue_hasDerivAt period hPeriod
        metric.metric
        (normalBoundarySmoothRelativeMetricField
          period hPeriod metric tensor row column) boundary
        (Real.arctan fiber)).comp fiber
          ((boundedFiberArctanJet3
            (OrientationBoundary period hPeriod)).2.1 boundary fiber)
    apply (hComposed.congr_of_eventuallyEq ?_).congr_deriv
    next =>
      rw [normalBoundaryRelativeMetricRawFirstCLM_smooth]
      ring
    next =>
      filter_upwards [] with varied
      rw [normalBoundaryRelativeMetricRawValueCLM_smooth]
      rfl
  next =>
    intro boundary fiber
    change RealHasDerivAt
      (fun varied => normalBoundaryRelativeMetricRawFirstCLM
        period hPeriod metric row column
        (smoothToRegularGeneralMetricBoundaryC3Core
          period hPeriod metric tensor) (boundary, varied))
      (normalBoundaryRelativeMetricRawSecondCLM
        period hPeriod metric row column
        (smoothToRegularGeneralMetricBoundaryC3Core
          period hPeriod metric tensor) (boundary, fiber)) fiber
    have hComposed :=
      (normalBoundarySmoothFieldLatitudeFirst_hasDerivAt period hPeriod
        metric.metric
        (normalBoundarySmoothRelativeMetricField
          period hPeriod metric tensor row column) boundary
        (Real.arctan fiber)).comp fiber
          ((boundedFiberArctanJet3
            (OrientationBoundary period hPeriod)).2.1 boundary fiber)
    have hProduct :=
      ((boundedFiberArctanJet3
        (OrientationBoundary period hPeriod)).2.2.1 boundary fiber).mul
          hComposed
    convert hProduct using 1
    next =>
      funext varied
      rw [normalBoundaryRelativeMetricRawFirstCLM_smooth]
      rfl
    next =>
      rw [normalBoundaryRelativeMetricRawSecondCLM_smooth]
      simp only [Function.comp_apply]
      ring
  next =>
    intro boundary fiber
    change RealHasDerivAt
      (fun varied => normalBoundaryRelativeMetricRawSecondCLM
        period hPeriod metric row column
        (smoothToRegularGeneralMetricBoundaryC3Core
          period hPeriod metric tensor) (boundary, varied))
      (normalBoundaryRelativeMetricRawThirdCLM
        period hPeriod metric row column
        (smoothToRegularGeneralMetricBoundaryC3Core
          period hPeriod metric tensor) (boundary, fiber)) fiber
    have hSecondComposed :=
      (normalBoundarySmoothFieldLatitudeSecond_hasDerivAt period hPeriod
        metric.metric
        (normalBoundarySmoothRelativeMetricField
          period hPeriod metric tensor row column) boundary
        (Real.arctan fiber)).comp fiber
          ((boundedFiberArctanJet3
            (OrientationBoundary period hPeriod)).2.1 boundary fiber)
    have hFirstComposed :=
      (normalBoundarySmoothFieldLatitudeFirst_hasDerivAt period hPeriod
        metric.metric
        (normalBoundarySmoothRelativeMetricField
          period hPeriod metric tensor row column) boundary
        (Real.arctan fiber)).comp fiber
          ((boundedFiberArctanJet3
            (OrientationBoundary period hPeriod)).2.1 boundary fiber)
    have hFirstTerm :=
      (((boundedFiberArctanJet3
        (OrientationBoundary period hPeriod)).2.2.1 boundary fiber).pow 2).mul
          hSecondComposed
    have hSecondTerm :=
      ((boundedFiberArctanJet3
        (OrientationBoundary period hPeriod)).2.2.2 boundary fiber).mul
          hFirstComposed
    have hSum := hFirstTerm.add hSecondTerm
    convert hSum using 1
    next =>
      funext varied
      rw [normalBoundaryRelativeMetricRawSecondCLM_smooth]
      rfl
    next =>
      rw [normalBoundaryRelativeMetricRawThirdCLM_smooth]
      simp only [Function.comp_apply, Pi.pow_apply]
      ring

/-- The ambient raw jet of every completed metric variation is compatible.
This is the closed extension of the genuine smooth jet, not an additional
boundary regularity assumption. -/
theorem normalBoundaryRelativeMetricRawJetAmbientCLM_mem
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (row column : Fin 4)
    (variation : RegularGeneralMetricBoundaryC3Core period hPeriod metric) :
    (boundedFiberJet3Submodule
      (OrientationBoundary period hPeriod)).carrier
        (normalBoundaryRelativeMetricRawJetAmbientCLM period hPeriod metric
          row column variation) := by
  let ambientJet := normalBoundaryRelativeMetricRawJetAmbientCLM
    period hPeriod metric row column
  let smoothInclusion := smoothToRegularGeneralMetricBoundaryC3Core
    period hPeriod metric
  let compatible : Set
      (RegularGeneralMetricBoundaryC3Core period hPeriod metric) :=
    ambientJet ⁻¹' (boundedFiberJet3Submodule
      (OrientationBoundary period hPeriod) : Set
        (BoundedFiberJet3Ambient (OrientationBoundary period hPeriod)))
  have hClosed : IsClosed compatible :=
    (boundedFiberJet3Submodule_isClosed
      (OrientationBoundary period hPeriod)).preimage ambientJet.continuous
  have hRange : Set.range smoothInclusion ⊆ compatible := by
    rintro current ⟨tensor, rfl⟩
    exact normalBoundaryRelativeMetricRawJetAmbientCLM_smooth_mem
      period hPeriod metric tensor row column
  have hClosure : closure (Set.range smoothInclusion) ⊆ compatible :=
    closure_minimal hRange hClosed
  apply hClosure
  rw [(smoothToRegularGeneralMetricBoundaryC3Core_denseRange
    period hPeriod metric).closure_range]
  exact Set.mem_univ variation

/-- Canonical compatible bounded raw jet of one completed relative-metric
entry along the mobile normal collar. -/
def normalBoundaryRelativeMetricRawJet3CLM
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (row column : Fin 4) :
    RegularGeneralMetricBoundaryC3Core period hPeriod metric →L[Real]
      BoundedFiberJet3 (OrientationBoundary period hPeriod) :=
  (normalBoundaryRelativeMetricRawJetAmbientCLM period hPeriod metric
    row column).codRestrict
      (boundedFiberJet3Submodule (OrientationBoundary period hPeriod))
      (normalBoundaryRelativeMetricRawJetAmbientCLM_mem
        period hPeriod metric row column)

/-! ## CÂ² evaluation on the completed physical moving graph -/

/-- Input of the generic bounded fiber-jet evaluator. Its first component
is the completed metric jet above; its second component is the existing
completed normal graph. -/
def candidateANormalBoundaryRelativeMetricFiberEvaluationInput
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (row column : Fin 4)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) :
    Prod (BoundedFiberJet3 (OrientationBoundary period hPeriod))
      (BoundedContinuousFunction
        (OrientationBoundary period hPeriod) Real) :=
  (normalBoundaryRelativeMetricRawJet3CLM period hPeriod metric row column
      current.1.1,
    normalBoundaryC2ScaledRawGraph period hPeriod (current.1.2, current.2))

theorem candidateANormalBoundaryRelativeMetricFiberEvaluationInput_contDiff_two
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (row column : Fin 4) :
    ContDiff Real 2
      (candidateANormalBoundaryRelativeMetricFiberEvaluationInput
        period hPeriod metric row column) := by
  have hMetricProjection : ContDiff Real 2 (fun current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real =>
      current.1.1) :=
    contDiff_fst.comp contDiff_fst
  have hNormalProjection : ContDiff Real 2 (fun current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real =>
      current.1.2) :=
    contDiff_snd.comp contDiff_fst
  have hJet := (normalBoundaryRelativeMetricRawJet3CLM
    period hPeriod metric row column).contDiff.comp hMetricProjection
  have hGraph := (normalBoundaryC2ScaledRawGraph_contDiff_two
    period hPeriod).comp (hNormalProjection.prodMk contDiff_snd)
  exact hJet.prodMk hGraph

/-- One completed relative-metric coefficient evaluated by the generic C2
fiber-jet substitution theorem. -/
def candidateANormalBoundaryRelativeMetricFiberEvaluation
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (row column : Fin 4)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) :
    BoundedContinuousFunction (OrientationBoundary period hPeriod) Real :=
  boundedFiberJet3Evaluation (OrientationBoundary period hPeriod)
    (candidateANormalBoundaryRelativeMetricFiberEvaluationInput
      period hPeriod metric row column current)

theorem candidateANormalBoundaryRelativeMetricFiberEvaluation_contDiff_two
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (row column : Fin 4) :
    ContDiff Real 2
      (candidateANormalBoundaryRelativeMetricFiberEvaluation
        period hPeriod metric row column) :=
  (boundedFiberJet3Evaluation_contDiff_two
    (OrientationBoundary period hPeriod)).comp
      (candidateANormalBoundaryRelativeMetricFiberEvaluationInput_contDiff_two
        period hPeriod metric row column)

@[simp]
theorem candidateANormalBoundaryRelativeMetricFiberEvaluation_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (row column : Fin 4)
    (variation : CandidateANormalBoundaryFunctionalCore period hPeriod metric)
    (parameter : Real) (boundary : OrientationBoundary period hPeriod) :
    candidateANormalBoundaryRelativeMetricFiberEvaluation period hPeriod
        metric row column (variation, parameter) boundary =
      candidateANormalBoundaryRelativeMetricEntryAtGraph period hPeriod metric
        row column variation parameter boundary := by
  change normalBoundaryRelativeMetricRawValueCLM period hPeriod metric
      row column variation.1
        (boundary, normalBoundaryC2ScaledRawGraph period hPeriod
          (variation.2, parameter) boundary) =
    regularGeneralMetricBoundaryC3RelativeEntryToContinuous period hPeriod
      metric row column variation.1
        (normalBoundaryC2Graph period hPeriod variation.2 parameter boundary)
  rw [normalBoundaryRelativeMetricRawValueCLM_apply,
    normalBoundaryC2ScaledRawGraph_apply,
    normalBoundaryRawFiberPoint_graph]

/-- Public H10 metric-entry gate: the existing physical moving evaluation
is the value of a genuine C2 map on the completed metric-normal core. -/
theorem candidate_a_normal_boundary_relative_metric_fiber_c2_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (row column : Fin 4) :
    And
      (ContDiff Real 2
        (candidateANormalBoundaryRelativeMetricFiberEvaluation
          period hPeriod metric row column))
      (∀ variation parameter boundary,
        candidateANormalBoundaryRelativeMetricFiberEvaluation period hPeriod
            metric row column (variation, parameter) boundary =
          candidateANormalBoundaryRelativeMetricEntryAtGraph
            period hPeriod metric row column variation parameter boundary) :=
  And.intro
    (candidateANormalBoundaryRelativeMetricFiberEvaluation_contDiff_two
      period hPeriod metric row column)
    (candidateANormalBoundaryRelativeMetricFiberEvaluation_apply
      period hPeriod metric row column)

/-! ## C² evaluation of the existing spatial first metric jet -/

/-- The raw value/first/second fiber jet of one fixed spatial derivative.
This uses exactly the completed metric `C³` core: the top component contains
the existing third metric jet and no fourth derivative. -/
def normalBoundaryRelativeMetricSpatialFirstRawJetAmbientCLM
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (row column : Fin 4)
    (spatial : BoundaryMetricJetIndex period hPeriod) :
    RegularGeneralMetricBoundaryC3Core period hPeriod metric →L[Real]
      P0EFTJanusBoundedFiberJet2SubstitutionC2.Ambient
        (OrientationBoundary period hPeriod) :=
  ContinuousLinearMap.pi ![
    normalBoundaryRelativeMetricSpatialFirstRawValueCLM
      period hPeriod metric row column spatial,
    normalBoundaryRelativeMetricSpatialFirstRawFirstCLM
      period hPeriod metric row column spatial,
    normalBoundaryRelativeMetricSpatialFirstRawSecondCLM
      period hPeriod metric row column spatial]

private theorem
    normalBoundaryRelativeMetricSpatialFirstRawJetAmbientCLM_smooth_derivative_mem
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (row column : Fin 4)
    (spatial : BoundaryMetricJetIndex period hPeriod) :
    (P0EFTJanusBoundedFiberJet2SubstitutionC2.jet2DerivativeSubmodule
      (OrientationBoundary period hPeriod)).carrier
        (normalBoundaryRelativeMetricSpatialFirstRawJetAmbientCLM
          period hPeriod metric row column spatial
          (smoothToRegularGeneralMetricBoundaryC3Core
            period hPeriod metric tensor)) := by
  refine And.intro ?_ ?_
  · intro boundary fiber
    change RealHasDerivAt
      (fun varied => normalBoundaryRelativeMetricSpatialFirstRawValueCLM
        period hPeriod metric row column spatial
        (smoothToRegularGeneralMetricBoundaryC3Core
          period hPeriod metric tensor) (boundary, varied))
      (normalBoundaryRelativeMetricSpatialFirstRawFirstCLM
        period hPeriod metric row column spatial
        (smoothToRegularGeneralMetricBoundaryC3Core
          period hPeriod metric tensor) (boundary, fiber)) fiber
    have hComposed :=
      (normalBoundarySmoothFieldLatitudeValue_hasDerivAt period hPeriod
        metric.metric
        (normalBoundarySmoothRelativeMetricSpatialFirstField
          period hPeriod metric tensor row column spatial) boundary
        (Real.arctan fiber)).comp fiber
          ((boundedFiberArctanJet3
            (OrientationBoundary period hPeriod)).2.1 boundary fiber)
    apply (hComposed.congr_of_eventuallyEq ?_).congr_deriv
    · rw [normalBoundaryRelativeMetricSpatialFirstRawFirstCLM_smooth]
      ring
    · filter_upwards [] with varied
      rw [normalBoundaryRelativeMetricSpatialFirstRawValueCLM_smooth]
      rfl
  · intro boundary fiber
    change RealHasDerivAt
      (fun varied => normalBoundaryRelativeMetricSpatialFirstRawFirstCLM
        period hPeriod metric row column spatial
        (smoothToRegularGeneralMetricBoundaryC3Core
          period hPeriod metric tensor) (boundary, varied))
      (normalBoundaryRelativeMetricSpatialFirstRawSecondCLM
        period hPeriod metric row column spatial
        (smoothToRegularGeneralMetricBoundaryC3Core
          period hPeriod metric tensor) (boundary, fiber)) fiber
    have hComposed :=
      (normalBoundarySmoothFieldLatitudeFirst_hasDerivAt period hPeriod
        metric.metric
        (normalBoundarySmoothRelativeMetricSpatialFirstField
          period hPeriod metric tensor row column spatial) boundary
        (Real.arctan fiber)).comp fiber
          ((boundedFiberArctanJet3
            (OrientationBoundary period hPeriod)).2.1 boundary fiber)
    have hProduct :=
      ((boundedFiberArctanJet3
        (OrientationBoundary period hPeriod)).2.2.1 boundary fiber).mul
          hComposed
    convert hProduct using 1
    · funext varied
      rw [normalBoundaryRelativeMetricSpatialFirstRawFirstCLM_smooth]
      rfl
    · rw [normalBoundaryRelativeMetricSpatialFirstRawSecondCLM_smooth]
      simp only [Function.comp_apply]
      ring

/-- The two derivative identities extend from smooth tensors to the whole
completed metric core by density and closedness. -/
theorem normalBoundaryRelativeMetricSpatialFirstRawJetAmbientCLM_derivative_mem
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (row column : Fin 4)
    (spatial : BoundaryMetricJetIndex period hPeriod)
    (variation : RegularGeneralMetricBoundaryC3Core period hPeriod metric) :
    (P0EFTJanusBoundedFiberJet2SubstitutionC2.jet2DerivativeSubmodule
      (OrientationBoundary period hPeriod)).carrier
        (normalBoundaryRelativeMetricSpatialFirstRawJetAmbientCLM
          period hPeriod metric row column spatial variation) := by
  let ambientJet :=
    normalBoundaryRelativeMetricSpatialFirstRawJetAmbientCLM
      period hPeriod metric row column spatial
  let smoothInclusion := smoothToRegularGeneralMetricBoundaryC3Core
    period hPeriod metric
  let compatible : Set
      (RegularGeneralMetricBoundaryC3Core period hPeriod metric) :=
    ambientJet ⁻¹'
      (P0EFTJanusBoundedFiberJet2SubstitutionC2.jet2DerivativeSubmodule
        (OrientationBoundary period hPeriod) : Set
          (P0EFTJanusBoundedFiberJet2SubstitutionC2.Ambient
            (OrientationBoundary period hPeriod)))
  have hClosed : IsClosed compatible :=
    (P0EFTJanusBoundedFiberJet2SubstitutionC2.jet2DerivativeSubmodule_isClosed
      (OrientationBoundary period hPeriod)).preimage ambientJet.continuous
  have hRange : Set.range smoothInclusion ⊆ compatible := by
    rintro current ⟨tensor, rfl⟩
    exact
      normalBoundaryRelativeMetricSpatialFirstRawJetAmbientCLM_smooth_derivative_mem
        period hPeriod metric tensor row column spatial
  have hClosure : closure (Set.range smoothInclusion) ⊆ compatible :=
    closure_minimal hRange hClosed
  apply hClosure
  rw [(smoothToRegularGeneralMetricBoundaryC3Core_denseRange
    period hPeriod metric).closure_range]
  exact Set.mem_univ variation

private theorem
    normalBoundaryRelativeMetricSpatialFirstRawSecondCLM_uniformContinuous
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (row column : Fin 4)
    (spatial : BoundaryMetricJetIndex period hPeriod)
    (variation : RegularGeneralMetricBoundaryC3Core period hPeriod metric) :
    UniformContinuous
      (normalBoundaryRelativeMetricSpatialFirstRawSecondCLM
        period hPeriod metric row column spatial variation) := by
  have hArctanFirst : UniformContinuous
      ((boundedFiberArctanJet3
        (OrientationBoundary period hPeriod)).1 1) := by
    simpa using
      (boundedFiberArctanJet3_component_uniformContinuous
        (OrientationBoundary period hPeriod) (1 : Fin 3))
  have hArctanSecond : UniformContinuous
      ((boundedFiberArctanJet3
        (OrientationBoundary period hPeriod)).1 2) := by
    simpa using
      (boundedFiberArctanJet3_component_uniformContinuous
        (OrientationBoundary period hPeriod) (2 : Fin 3))
  have hLatitudeFirst : UniformContinuous
      (normalBoundaryRelativeMetricSpatialFirstLatitudeFirstRawCLM
        period hPeriod metric row column spatial variation) := by
    simpa [normalBoundaryRelativeMetricSpatialFirstLatitudeFirstRawCLM] using
      (boundedArctanCompactPullback_uniformContinuous
        (OrientationBoundary period hPeriod)
        (normalBoundaryRelativeMetricSpatialFirstLatitudeFirstCompactCLM
          period hPeriod metric row column spatial variation))
  have hLatitudeSecond : UniformContinuous
      (normalBoundaryRelativeMetricSpatialFirstLatitudeSecondRawCLM
        period hPeriod metric row column spatial variation) := by
    simpa [normalBoundaryRelativeMetricSpatialFirstLatitudeSecondRawCLM] using
      (boundedArctanCompactPullback_uniformContinuous
        (OrientationBoundary period hPeriod)
        (normalBoundaryRelativeMetricSpatialFirstLatitudeSecondCompactCLM
          period hPeriod metric row column spatial variation))
  have hArctanProduct :=
    field_mul_uniformContinuous (OrientationBoundary period hPeriod)
      ((boundedFiberArctanJet3
        (OrientationBoundary period hPeriod)).1 1)
      ((boundedFiberArctanJet3
        (OrientationBoundary period hPeriod)).1 1)
      hArctanFirst hArctanFirst
  have hFirstTerm := field_mul_uniformContinuous
    (OrientationBoundary period hPeriod)
    (((boundedFiberArctanJet3
        (OrientationBoundary period hPeriod)).1 1) *
      (boundedFiberArctanJet3
        (OrientationBoundary period hPeriod)).1 1)
    (normalBoundaryRelativeMetricSpatialFirstLatitudeSecondRawCLM
      period hPeriod metric row column spatial variation)
    hArctanProduct hLatitudeSecond
  have hSecondTerm := field_mul_uniformContinuous
    (OrientationBoundary period hPeriod)
    ((boundedFiberArctanJet3
      (OrientationBoundary period hPeriod)).1 2)
    (normalBoundaryRelativeMetricSpatialFirstLatitudeFirstRawCLM
      period hPeriod metric row column spatial variation)
    hArctanSecond hLatitudeFirst
  change UniformContinuous (fun point =>
    ((boundedFiberArctanJet3
        (OrientationBoundary period hPeriod)).1 1 point) ^ 2 *
      normalBoundaryRelativeMetricSpatialFirstLatitudeSecondRawCLM
        period hPeriod metric row column spatial variation point +
    (boundedFiberArctanJet3
        (OrientationBoundary period hPeriod)).1 2 point *
      normalBoundaryRelativeMetricSpatialFirstLatitudeFirstRawCLM
        period hPeriod metric row column spatial variation point)
  simpa [pow_two] using hFirstTerm.add hSecondTerm

/-- Every completed variation supplies a genuine derivative-optimal raw
second jet.  Uniform continuity follows from compact latitude pullback and
the bounded `arctan` jet, rather than from a fourth metric derivative. -/
theorem normalBoundaryRelativeMetricSpatialFirstRawJetAmbientCLM_mem
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (row column : Fin 4)
    (spatial : BoundaryMetricJetIndex period hPeriod)
    (variation : RegularGeneralMetricBoundaryC3Core period hPeriod metric) :
    (P0EFTJanusBoundedFiberJet2SubstitutionC2.jet2Submodule
      (OrientationBoundary period hPeriod)).carrier
        (normalBoundaryRelativeMetricSpatialFirstRawJetAmbientCLM
          period hPeriod metric row column spatial variation) := by
  have hDerivative :=
    normalBoundaryRelativeMetricSpatialFirstRawJetAmbientCLM_derivative_mem
      period hPeriod metric row column spatial variation
  exact ⟨hDerivative.1, hDerivative.2,
    normalBoundaryRelativeMetricSpatialFirstRawSecondCLM_uniformContinuous
      period hPeriod metric row column spatial variation⟩

/-- Canonical completed value/first/second raw jet of an existing spatial
first metric derivative. -/
def normalBoundaryRelativeMetricSpatialFirstRawJet2CLM
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (row column : Fin 4)
    (spatial : BoundaryMetricJetIndex period hPeriod) :
    RegularGeneralMetricBoundaryC3Core period hPeriod metric →L[Real]
      P0EFTJanusBoundedFiberJet2SubstitutionC2.Jet2
        (OrientationBoundary period hPeriod) :=
  (normalBoundaryRelativeMetricSpatialFirstRawJetAmbientCLM
    period hPeriod metric row column spatial).codRestrict
      (P0EFTJanusBoundedFiberJet2SubstitutionC2.jet2Submodule
        (OrientationBoundary period hPeriod))
      (normalBoundaryRelativeMetricSpatialFirstRawJetAmbientCLM_mem
        period hPeriod metric row column spatial)

/-- Input of the derivative-optimal evaluator for one fixed spatial metric
derivative on the completed moving graph. -/
def candidateANormalBoundaryRelativeMetricSpatialFirstFiberEvaluationInput
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (row column : Fin 4)
    (spatial : BoundaryMetricJetIndex period hPeriod)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) :
    Prod
      (P0EFTJanusBoundedFiberJet2SubstitutionC2.Jet2
        (OrientationBoundary period hPeriod))
      (BoundedContinuousFunction
        (OrientationBoundary period hPeriod) Real) :=
  (normalBoundaryRelativeMetricSpatialFirstRawJet2CLM
      period hPeriod metric row column spatial current.1.1,
    normalBoundaryC2ScaledRawGraph period hPeriod (current.1.2, current.2))

theorem
    candidateANormalBoundaryRelativeMetricSpatialFirstFiberEvaluationInput_contDiff_two
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (row column : Fin 4)
    (spatial : BoundaryMetricJetIndex period hPeriod) :
    ContDiff Real 2
      (candidateANormalBoundaryRelativeMetricSpatialFirstFiberEvaluationInput
        period hPeriod metric row column spatial) := by
  have hMetricProjection : ContDiff Real 2 (fun current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real =>
      current.1.1) :=
    contDiff_fst.comp contDiff_fst
  have hNormalProjection : ContDiff Real 2 (fun current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real =>
      current.1.2) :=
    contDiff_snd.comp contDiff_fst
  have hJet :=
    (normalBoundaryRelativeMetricSpatialFirstRawJet2CLM
      period hPeriod metric row column spatial).contDiff.comp
        hMetricProjection
  have hGraph := (normalBoundaryC2ScaledRawGraph_contDiff_two
    period hPeriod).comp (hNormalProjection.prodMk contDiff_snd)
  exact hJet.prodMk hGraph

/-- One completed physical-frame first derivative evaluated on the same
moving boundary as the metric value. -/
def candidateANormalBoundaryRelativeMetricSpatialFirstFiberEvaluation
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (row column : Fin 4)
    (spatial : BoundaryMetricJetIndex period hPeriod)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) :
    BoundedContinuousFunction (OrientationBoundary period hPeriod) Real :=
  P0EFTJanusBoundedFiberJet2SubstitutionC2.evaluation
    (OrientationBoundary period hPeriod)
    (candidateANormalBoundaryRelativeMetricSpatialFirstFiberEvaluationInput
      period hPeriod metric row column spatial current)

theorem candidateANormalBoundaryRelativeMetricSpatialFirstFiberEvaluation_contDiff_two
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (row column : Fin 4)
    (spatial : BoundaryMetricJetIndex period hPeriod) :
    ContDiff Real 2
      (candidateANormalBoundaryRelativeMetricSpatialFirstFiberEvaluation
        period hPeriod metric row column spatial) :=
  (P0EFTJanusBoundedFiberJet2SubstitutionC2.evaluation_contDiff_two
    (OrientationBoundary period hPeriod)).comp
      (candidateANormalBoundaryRelativeMetricSpatialFirstFiberEvaluationInput_contDiff_two
        period hPeriod metric row column spatial)

@[simp]
theorem candidateANormalBoundaryRelativeMetricSpatialFirstFiberEvaluation_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (row column : Fin 4)
    (spatial : BoundaryMetricJetIndex period hPeriod)
    (variation : CandidateANormalBoundaryFunctionalCore period hPeriod metric)
    (parameter : Real) (boundary : OrientationBoundary period hPeriod) :
    candidateANormalBoundaryRelativeMetricSpatialFirstFiberEvaluation
        period hPeriod metric row column spatial (variation, parameter)
        boundary =
      candidateANormalBoundaryRelativeMetricFirstEntryAtGraph
        period hPeriod metric row column spatial variation parameter
        boundary := by
  change normalBoundaryRelativeMetricSpatialFirstRawValueCLM
      period hPeriod metric row column spatial variation.1
        (boundary, normalBoundaryC2ScaledRawGraph period hPeriod
          (variation.2, parameter) boundary) =
    regularGeneralMetricBoundaryC3RelativeFirstEntryToContinuous
      period hPeriod metric row column spatial variation.1
        (normalBoundaryC2Graph period hPeriod variation.2 parameter boundary)
  rw [normalBoundaryRelativeMetricSpatialFirstRawValueCLM_apply,
    normalBoundaryC2ScaledRawGraph_apply,
    normalBoundaryRawFiberPoint_graph]

/-- Public H10 spatial-metric gate: every already existing physical-frame
first metric derivative is a genuine `C²` map on the completed mobile core.
No fourth derivative or additional boundary axiom is used. -/
theorem candidate_a_normal_boundary_relative_metric_spatial_first_fiber_c2_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (row column : Fin 4)
    (spatial : BoundaryMetricJetIndex period hPeriod) :
    And
      (ContDiff Real 2
        (candidateANormalBoundaryRelativeMetricSpatialFirstFiberEvaluation
          period hPeriod metric row column spatial))
      (∀ variation parameter boundary,
        candidateANormalBoundaryRelativeMetricSpatialFirstFiberEvaluation
            period hPeriod metric row column spatial (variation, parameter)
            boundary =
          candidateANormalBoundaryRelativeMetricFirstEntryAtGraph
            period hPeriod metric row column spatial variation parameter
            boundary) :=
  And.intro
    (candidateANormalBoundaryRelativeMetricSpatialFirstFiberEvaluation_contDiff_two
      period hPeriod metric row column spatial)
    (candidateANormalBoundaryRelativeMetricSpatialFirstFiberEvaluation_apply
      period hPeriod metric row column spatial)

/-! ## Matrix assembly for the completed GHY algebra -/

/-- Global bounded matrix fields on the compact orientation double. -/
abbrev CandidateANormalBoundaryMatrixField :=
  Matrix (Fin 4) (Fin 4)
    (BoundedContinuousFunction (OrientationBoundary period hPeriod) Real)

@[reducible] local instance candidateANormalBoundaryMatrixFieldNormedAddCommGroup :
    NormedAddCommGroup (CandidateANormalBoundaryMatrixField period hPeriod) :=
  Pi.normedAddCommGroup

@[reducible] local instance candidateANormalBoundaryMatrixFieldNormedSpace :
    NormedSpace Real (CandidateANormalBoundaryMatrixField period hPeriod) :=
  Pi.normedSpace

/-- The evaluated relative ambient metric, assembled once from the scalar
fiber gates. -/
def candidateANormalBoundaryRelativeMetricMatrixFiberEvaluation
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) :
    CandidateANormalBoundaryMatrixField period hPeriod :=
  fun row column =>
    candidateANormalBoundaryRelativeMetricFiberEvaluation
      period hPeriod metric row column current

theorem candidateANormalBoundaryRelativeMetricMatrixFiberEvaluation_contDiff_two
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    ContDiff Real 2
      (candidateANormalBoundaryRelativeMetricMatrixFiberEvaluation
        period hPeriod metric) := by
  change @ContDiff Real _
    (Prod (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real)
    _ _
    (Fin 4 → Fin 4 →
      BoundedContinuousFunction (OrientationBoundary period hPeriod) Real)
    Pi.normedAddCommGroup Pi.normedSpace 2
    (fun current row column =>
      candidateANormalBoundaryRelativeMetricFiberEvaluation
        period hPeriod metric row column current)
  rw [contDiff_pi]
  intro row
  rw [contDiff_pi]
  intro column
  exact candidateANormalBoundaryRelativeMetricFiberEvaluation_contDiff_two
    period hPeriod metric row column

@[simp]
theorem candidateANormalBoundaryRelativeMetricMatrixFiberEvaluation_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variation : CandidateANormalBoundaryFunctionalCore period hPeriod metric)
    (parameter : Real) (boundary : OrientationBoundary period hPeriod)
    (row column : Fin 4) :
    candidateANormalBoundaryRelativeMetricMatrixFiberEvaluation
        period hPeriod metric (variation, parameter) row column boundary =
      candidateANormalBoundaryRelativeMetricEntryAtGraph period hPeriod metric
        row column variation parameter boundary :=
  candidateANormalBoundaryRelativeMetricFiberEvaluation_apply
    period hPeriod metric row column variation parameter boundary

/-- The actual relative metric endomorphism is identity plus the completed
variation matrix already used by the regular metric chart. -/
def candidateANormalBoundaryTotalRelativeMetricMatrixFiberEvaluation
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) :
    CandidateANormalBoundaryMatrixField period hPeriod :=
  1 + candidateANormalBoundaryRelativeMetricMatrixFiberEvaluation
    period hPeriod metric current

theorem candidateANormalBoundaryTotalRelativeMetricMatrixFiberEvaluation_contDiff_two
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    ContDiff Real 2
      (candidateANormalBoundaryTotalRelativeMetricMatrixFiberEvaluation
        period hPeriod metric) :=
  contDiff_const.add
    (candidateANormalBoundaryRelativeMetricMatrixFiberEvaluation_contDiff_two
      period hPeriod metric)

@[simp]
theorem candidateANormalBoundaryTotalRelativeMetricMatrixFiberEvaluation_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variation : CandidateANormalBoundaryFunctionalCore period hPeriod metric)
    (parameter : Real) (boundary : OrientationBoundary period hPeriod)
    (row column : Fin 4) :
    candidateANormalBoundaryTotalRelativeMetricMatrixFiberEvaluation
        period hPeriod metric (variation, parameter) row column boundary =
      (1 : Matrix (Fin 4) (Fin 4) Real) row column +
        candidateANormalBoundaryRelativeMetricEntryAtGraph period hPeriod metric
          row column variation parameter boundary := by
  rw [candidateANormalBoundaryTotalRelativeMetricMatrixFiberEvaluation]
  by_cases hEntry : row = column <;> simp [Matrix.one_apply, hEntry]

/-- Matrix of every first spatial metric derivative needed by the completed
Levi--Civita contraction. -/
def candidateANormalBoundaryRelativeMetricSpatialFirstMatrixFiberEvaluation
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (spatial : BoundaryMetricJetIndex period hPeriod)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) :
    CandidateANormalBoundaryMatrixField period hPeriod :=
  fun row column =>
    candidateANormalBoundaryRelativeMetricSpatialFirstFiberEvaluation
      period hPeriod metric row column spatial current

theorem candidateANormalBoundaryRelativeMetricSpatialFirstMatrixFiberEvaluation_contDiff_two
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (spatial : BoundaryMetricJetIndex period hPeriod) :
    ContDiff Real 2
      (candidateANormalBoundaryRelativeMetricSpatialFirstMatrixFiberEvaluation
        period hPeriod metric spatial) := by
  change @ContDiff Real _
    (Prod (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real)
    _ _
    (Fin 4 → Fin 4 →
      BoundedContinuousFunction (OrientationBoundary period hPeriod) Real)
    Pi.normedAddCommGroup Pi.normedSpace 2
    (fun current row column =>
      candidateANormalBoundaryRelativeMetricSpatialFirstFiberEvaluation
        period hPeriod metric row column spatial current)
  rw [contDiff_pi]
  intro row
  rw [contDiff_pi]
  intro column
  exact
    candidateANormalBoundaryRelativeMetricSpatialFirstFiberEvaluation_contDiff_two
      period hPeriod metric row column spatial

@[simp]
theorem
    candidateANormalBoundaryRelativeMetricSpatialFirstMatrixFiberEvaluation_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (spatial : BoundaryMetricJetIndex period hPeriod)
    (variation : CandidateANormalBoundaryFunctionalCore period hPeriod metric)
    (parameter : Real) (boundary : OrientationBoundary period hPeriod)
    (row column : Fin 4) :
    candidateANormalBoundaryRelativeMetricSpatialFirstMatrixFiberEvaluation
        period hPeriod metric spatial (variation, parameter)
          row column boundary =
      candidateANormalBoundaryRelativeMetricFirstEntryAtGraph
        period hPeriod metric row column spatial variation parameter
          boundary :=
  candidateANormalBoundaryRelativeMetricSpatialFirstFiberEvaluation_apply
    period hPeriod metric row column spatial variation parameter boundary

/-- Determinant polynomial on the global bounded matrix algebra. -/
def candidateANormalBoundaryMatrixFieldDeterminant
    (matrix : CandidateANormalBoundaryMatrixField period hPeriod) :
    BoundedContinuousFunction (OrientationBoundary period hPeriod) Real :=
  Matrix.det matrix

theorem candidateANormalBoundaryMatrixFieldDeterminant_contDiff :
    ContDiff Real ∞
      (candidateANormalBoundaryMatrixFieldDeterminant period hPeriod) := by
  classical
  change ContDiff Real ∞
    (fun matrix : CandidateANormalBoundaryMatrixField period hPeriod =>
      Matrix.det matrix)
  simp_rw [Matrix.det_apply']
  apply ContDiff.sum
  intro permutation _
  apply contDiff_const.mul
  apply contDiff_prod
  intro index _
  exact contDiff_apply_apply Real
    (BoundedContinuousFunction (OrientationBoundary period hPeriod) Real)
    (permutation index) index

/-- Determinant of the actual evaluated ambient relative metric. -/
def candidateANormalBoundaryTotalRelativeMetricDeterminantFiberEvaluation
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) :
    BoundedContinuousFunction (OrientationBoundary period hPeriod) Real :=
  candidateANormalBoundaryMatrixFieldDeterminant period hPeriod
    (candidateANormalBoundaryTotalRelativeMetricMatrixFiberEvaluation
      period hPeriod metric current)

theorem candidateANormalBoundaryTotalRelativeMetricDeterminantFiberEvaluation_contDiff_two
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    ContDiff Real 2
      (candidateANormalBoundaryTotalRelativeMetricDeterminantFiberEvaluation
        period hPeriod metric) := by
  have hDet : ContDiff Real 2
      (candidateANormalBoundaryMatrixFieldDeterminant period hPeriod) :=
    (candidateANormalBoundaryMatrixFieldDeterminant_contDiff
      period hPeriod).of_le
        (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  exact hDet.comp
    (candidateANormalBoundaryTotalRelativeMetricMatrixFiberEvaluation_contDiff_two
      period hPeriod metric)

private def candidateANormalBoundaryMatrixFieldEvaluationRingHom
    (boundary : OrientationBoundary period hPeriod) :
    BoundedContinuousFunction (OrientationBoundary period hPeriod) Real →+*
      Real where
  toFun field := field boundary
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp]
theorem
    candidateANormalBoundaryTotalRelativeMetricDeterminantFiberEvaluation_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variation : CandidateANormalBoundaryFunctionalCore period hPeriod metric)
    (parameter : Real) (boundary : OrientationBoundary period hPeriod) :
    candidateANormalBoundaryTotalRelativeMetricDeterminantFiberEvaluation
        period hPeriod metric (variation, parameter) boundary =
      Matrix.det (fun row column : Fin 4 =>
        (1 : Matrix (Fin 4) (Fin 4) Real) row column +
          candidateANormalBoundaryRelativeMetricEntryAtGraph
            period hPeriod metric row column variation parameter boundary) := by
  have hMap :=
    (candidateANormalBoundaryMatrixFieldEvaluationRingHom
      period hPeriod boundary).map_det
        (candidateANormalBoundaryTotalRelativeMetricMatrixFiberEvaluation
          period hPeriod metric (variation, parameter))
  change
    (Matrix.det
      (candidateANormalBoundaryTotalRelativeMetricMatrixFiberEvaluation
        period hPeriod metric (variation, parameter))) boundary =
      Matrix.det (fun row column =>
        candidateANormalBoundaryTotalRelativeMetricMatrixFiberEvaluation
          period hPeriod metric (variation, parameter) row column boundary)
    at hMap
  change
    (Matrix.det
      (candidateANormalBoundaryTotalRelativeMetricMatrixFiberEvaluation
        period hPeriod metric (variation, parameter))) boundary = _
  calc
    (Matrix.det
        (candidateANormalBoundaryTotalRelativeMetricMatrixFiberEvaluation
          period hPeriod metric (variation, parameter))) boundary =
      Matrix.det (fun row column =>
        candidateANormalBoundaryTotalRelativeMetricMatrixFiberEvaluation
          period hPeriod metric (variation, parameter) row column boundary) :=
        hMap
    _ = Matrix.det (fun row column : Fin 4 =>
        (1 : Matrix (Fin 4) (Fin 4) Real) row column +
          candidateANormalBoundaryRelativeMetricEntryAtGraph
            period hPeriod metric row column variation parameter boundary) := by
      congr 1
      funext row column
      exact
        candidateANormalBoundaryTotalRelativeMetricMatrixFiberEvaluation_apply
          period hPeriod metric variation parameter boundary row column

/-! ## Reuse of the completed C2 inverse on the moving graph -/

/-- The completed normal graph as a continuous map on the compact
orientation boundary. -/
private def candidateANormalBoundaryGraphContinuousMap
    (normal : NormalBoundaryC2JetCore period hPeriod)
    (parameter : Real) :
    C(OrientationBoundary period hPeriod, EffectiveQuotient period hPeriod) :=
  { toFun := normalBoundaryC2Graph period hPeriod normal parameter
    continuous_toFun :=
      normalBoundaryC2Graph_continuous period hPeriod normal parameter }

/-- Evaluate an already completed finite C2 matrix on the same moving graph
used by the boundary action. -/
def candidateANormalBoundaryC2MatrixGraphEvaluation
    (normal : NormalBoundaryC2JetCore period hPeriod)
    (parameter : Real)
    (matrix : C2FiniteMatrix period hPeriod 4) :
    CandidateANormalBoundaryMatrixField period hPeriod :=
  fun row column =>
    compactContinuousToBoundedCLM (OrientationBoundary period hPeriod)
      ((canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
          (matrix row column)).comp
        (candidateANormalBoundaryGraphContinuousMap
          period hPeriod normal parameter))

@[simp]
theorem candidateANormalBoundaryC2MatrixGraphEvaluation_apply
    (normal : NormalBoundaryC2JetCore period hPeriod)
    (parameter : Real) (matrix : C2FiniteMatrix period hPeriod 4)
    (row column : Fin 4) (boundary : OrientationBoundary period hPeriod) :
    candidateANormalBoundaryC2MatrixGraphEvaluation
        period hPeriod normal parameter matrix row column boundary =
      canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
        (matrix row column)
        (normalBoundaryC2Graph period hPeriod normal parameter boundary) :=
  rfl

@[simp]
theorem candidateANormalBoundaryC2MatrixGraphEvaluation_add
    (normal : NormalBoundaryC2JetCore period hPeriod)
    (parameter : Real) (first second : C2FiniteMatrix period hPeriod 4) :
    candidateANormalBoundaryC2MatrixGraphEvaluation
        period hPeriod normal parameter (first + second) =
      candidateANormalBoundaryC2MatrixGraphEvaluation
          period hPeriod normal parameter first +
        candidateANormalBoundaryC2MatrixGraphEvaluation
          period hPeriod normal parameter second := by
  ext row column boundary
  rfl

@[simp]
theorem candidateANormalBoundaryC2MatrixGraphEvaluation_product
    (normal : NormalBoundaryC2JetCore period hPeriod)
    (parameter : Real) (first second : C2FiniteMatrix period hPeriod 4) :
    candidateANormalBoundaryC2MatrixGraphEvaluation period hPeriod normal
        parameter
        (c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) 4
          first second) =
      candidateANormalBoundaryC2MatrixGraphEvaluation
          period hPeriod normal parameter first *
      candidateANormalBoundaryC2MatrixGraphEvaluation
          period hPeriod normal parameter second := by
  ext row column boundary
  change
    canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
        (c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) 4
          first second row column)
        (normalBoundaryC2Graph period hPeriod normal parameter boundary) =
      ∑ middle : Fin 4,
        canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
            (first row middle)
            (normalBoundaryC2Graph period hPeriod normal parameter boundary) *
          canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
            (second middle column)
            (normalBoundaryC2Graph period hPeriod normal parameter boundary)
  rw [c2FiniteMatrixProduct_apply, map_sum]
  simp only [ContinuousMap.sum_apply]
  apply Finset.sum_congr rfl
  intro middle _
  rfl

@[simp]
theorem candidateANormalBoundaryC2MatrixGraphEvaluation_identity
    (normal : NormalBoundaryC2JetCore period hPeriod)
    (parameter : Real) :
    candidateANormalBoundaryC2MatrixGraphEvaluation period hPeriod normal
        parameter (c2FiniteMatrixIdentity period hPeriod 4) = 1 := by
  ext row column boundary
  rw [candidateANormalBoundaryC2MatrixGraphEvaluation_apply,
    Matrix.one_apply, c2FiniteMatrixIdentity]
  have hLift :
      smoothFiniteMatrixToC2 period hPeriod 4
          (smoothFiniteMatrixIdentity period hPeriod 4) row column =
        smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
          (smoothFiniteMatrixIdentity period hPeriod 4 row column) :=
    rfl
  rw [hLift, canonicalPhysicalScalarC2JetCoreToContinuous_smooth]
  by_cases hEntry : row = column <;>
    simp [smoothFiniteMatrixIdentity, hEntry,
      P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0Space4D.smoothToCanonicalPhysicalContinuousScalar,
      P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D.constantSmoothField]

@[simp]
theorem candidateANormalBoundaryC2MatrixGraphEvaluation_relativeMatrix
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variation : CandidateANormalBoundaryFunctionalCore
      period hPeriod metric)
    (parameter : Real) :
    candidateANormalBoundaryC2MatrixGraphEvaluation period hPeriod
        variation.2 parameter
        (regularGeneralMetricBoundaryC3CoreToRelativeMatrix
          period hPeriod metric variation.1) =
      candidateANormalBoundaryRelativeMetricMatrixFiberEvaluation
        period hPeriod metric (variation, parameter) := by
  ext row column boundary
  rw [candidateANormalBoundaryC2MatrixGraphEvaluation_apply,
    candidateANormalBoundaryRelativeMetricMatrixFiberEvaluation_apply]
  rfl

@[simp]
theorem candidateANormalBoundaryC2MatrixGraphEvaluation_extendedMatrix
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variation : CandidateANormalBoundaryFunctionalCore
      period hPeriod metric)
    (parameter : Real) :
    candidateANormalBoundaryC2MatrixGraphEvaluation period hPeriod
        variation.2 parameter
        (generalMetricRelativeC2ExtendedMatrix period hPeriod
          (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
          metric.metric
          (regularGeneralMetricBoundaryC3CoreToC2
            period hPeriod metric variation.1)) =
      candidateANormalBoundaryTotalRelativeMetricMatrixFiberEvaluation
        period hPeriod metric (variation, parameter) := by
  rw [generalMetricRelativeC2ExtendedMatrix]
  change
    candidateANormalBoundaryC2MatrixGraphEvaluation period hPeriod
        variation.2 parameter
        (c2FiniteMatrixIdentity period hPeriod 4 +
          regularGeneralMetricBoundaryC3CoreToRelativeMatrix
            period hPeriod metric variation.1) = _
  rw [candidateANormalBoundaryC2MatrixGraphEvaluation_add,
    candidateANormalBoundaryC2MatrixGraphEvaluation_identity,
    candidateANormalBoundaryC2MatrixGraphEvaluation_relativeMatrix]
  rfl

/-- Joint parameter domain: the existing admissible metric open set, with
the normal displacement and action parameter left unrestricted. -/
def candidateANormalBoundaryMetricParameterDomain
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    Set (Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) :=
  Prod.fst ⁻¹'
    candidateANormalBoundaryMetricDomain period hPeriod metric

theorem candidateANormalBoundaryMetricParameterDomain_isOpen
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    IsOpen
      (candidateANormalBoundaryMetricParameterDomain
        period hPeriod metric) :=
  (candidateANormalBoundaryMetricDomain_isOpen
    period hPeriod metric).preimage continuous_fst

theorem zero_mem_candidateANormalBoundaryMetricParameterDomain
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    (0 : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) ∈
      candidateANormalBoundaryMetricParameterDomain
        period hPeriod metric :=
  zero_mem_candidateANormalBoundaryMetricDomain period hPeriod metric

private theorem candidateANormalBoundaryMetricParameterDomain_c2Open
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real)
    (hCurrent : current ∈
      candidateANormalBoundaryMetricParameterDomain
        period hPeriod metric) :
    regularGeneralMetricBoundaryC3CoreToC2 period hPeriod metric
        current.1.1 ∈
      generalMetricRelativeC2OpenDomain period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
        metric.metric := by
  change current.1.1 ∈
    regularGeneralMetricBoundaryC3Domain period hPeriod metric at hCurrent
  change regularGeneralMetricBoundaryC3CoreToC2 period hPeriod metric
      current.1.1 ∈
    regularGeneralMetricC2Domain period hPeriod metric at hCurrent
  change regularGeneralMetricBoundaryC3CoreToC2 period hPeriod metric
      current.1.1 ∈
    generalMetricRelativeC2VolumeDomain period hPeriod
      (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
      metric.metric at hCurrent
  exact hCurrent.1

/-- The already existing completed C2 inverse, evaluated on the mobile
boundary graph.  It is a witness, not a second inverse construction. -/
def candidateANormalBoundaryC2InverseMatrixFiberEvaluation
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) :
    CandidateANormalBoundaryMatrixField period hPeriod :=
  candidateANormalBoundaryC2MatrixGraphEvaluation period hPeriod
    current.1.2 current.2
    (generalMetricRelativeC2InverseMatrix period hPeriod
      (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
      metric.metric
      (regularGeneralMetricBoundaryC3CoreToC2 period hPeriod metric
        current.1.1))

theorem candidateANormalBoundaryTotalRelativeMetric_mul_c2Inverse
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real)
    (hCurrent : current ∈
      candidateANormalBoundaryMetricParameterDomain
        period hPeriod metric) :
    candidateANormalBoundaryTotalRelativeMetricMatrixFiberEvaluation
        period hPeriod metric current *
      candidateANormalBoundaryC2InverseMatrixFiberEvaluation
        period hPeriod metric current = 1 := by
  have hProduct := generalMetricRelativeC2Extended_mul_inverse
    period hPeriod
    (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
    metric.metric
    (regularGeneralMetricBoundaryC3CoreToC2 period hPeriod metric
      current.1.1)
    (candidateANormalBoundaryMetricParameterDomain_c2Open
      period hPeriod metric current hCurrent)
  change
    c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) 4
        (generalMetricRelativeC2ExtendedMatrix period hPeriod
          (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
          metric.metric
          (regularGeneralMetricBoundaryC3CoreToC2 period hPeriod metric
            current.1.1))
        (generalMetricRelativeC2InverseMatrix period hPeriod
          (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
          metric.metric
          (regularGeneralMetricBoundaryC3CoreToC2 period hPeriod metric
            current.1.1)) =
      c2FiniteMatrixIdentity period hPeriod 4 at hProduct
  have hEvaluated := congrArg
    (candidateANormalBoundaryC2MatrixGraphEvaluation period hPeriod
      current.1.2 current.2) hProduct
  rw [candidateANormalBoundaryC2MatrixGraphEvaluation_product,
    candidateANormalBoundaryC2MatrixGraphEvaluation_extendedMatrix,
    candidateANormalBoundaryC2MatrixGraphEvaluation_identity] at hEvaluated
  simpa only [candidateANormalBoundaryC2InverseMatrixFiberEvaluation] using
    hEvaluated

theorem candidateANormalBoundaryC2Inverse_mul_totalRelativeMetric
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real)
    (hCurrent : current ∈
      candidateANormalBoundaryMetricParameterDomain
        period hPeriod metric) :
    candidateANormalBoundaryC2InverseMatrixFiberEvaluation
        period hPeriod metric current *
      candidateANormalBoundaryTotalRelativeMetricMatrixFiberEvaluation
        period hPeriod metric current = 1 := by
  have hProduct := generalMetricRelativeC2Inverse_mul_extended
    period hPeriod
    (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
    metric.metric
    (regularGeneralMetricBoundaryC3CoreToC2 period hPeriod metric
      current.1.1)
    (candidateANormalBoundaryMetricParameterDomain_c2Open
      period hPeriod metric current hCurrent)
  change
    c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) 4
        (generalMetricRelativeC2InverseMatrix period hPeriod
          (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
          metric.metric
          (regularGeneralMetricBoundaryC3CoreToC2 period hPeriod metric
            current.1.1))
        (generalMetricRelativeC2ExtendedMatrix period hPeriod
          (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
          metric.metric
          (regularGeneralMetricBoundaryC3CoreToC2 period hPeriod metric
            current.1.1)) =
      c2FiniteMatrixIdentity period hPeriod 4 at hProduct
  have hEvaluated := congrArg
    (candidateANormalBoundaryC2MatrixGraphEvaluation period hPeriod
      current.1.2 current.2) hProduct
  rw [candidateANormalBoundaryC2MatrixGraphEvaluation_product,
    candidateANormalBoundaryC2MatrixGraphEvaluation_extendedMatrix,
    candidateANormalBoundaryC2MatrixGraphEvaluation_identity] at hEvaluated
  simpa only [candidateANormalBoundaryC2InverseMatrixFiberEvaluation] using
    hEvaluated

theorem candidateANormalBoundaryTotalRelativeMetric_isUnit
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real)
    (hCurrent : current ∈
      candidateANormalBoundaryMetricParameterDomain
        period hPeriod metric) :
    IsUnit
      (candidateANormalBoundaryTotalRelativeMetricMatrixFiberEvaluation
        period hPeriod metric current) := by
  rw [isUnit_iff_exists]
  exact ⟨candidateANormalBoundaryC2InverseMatrixFiberEvaluation
      period hPeriod metric current,
    candidateANormalBoundaryTotalRelativeMetric_mul_c2Inverse
      period hPeriod metric current hCurrent,
    candidateANormalBoundaryC2Inverse_mul_totalRelativeMetric
      period hPeriod metric current hCurrent⟩

theorem candidateANormalBoundaryTotalRelativeMetricDeterminant_isUnit
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real)
    (hCurrent : current ∈
      candidateANormalBoundaryMetricParameterDomain
        period hPeriod metric) :
    IsUnit
      (candidateANormalBoundaryTotalRelativeMetricDeterminantFiberEvaluation
        period hPeriod metric current) := by
  exact (Matrix.isUnit_iff_isUnit_det _).mp
    (candidateANormalBoundaryTotalRelativeMetric_isUnit
      period hPeriod metric current hCurrent)

/-- Inverse of the evaluated determinant in the existing Banach algebra of
bounded boundary fields. -/
def candidateANormalBoundaryTotalRelativeMetricDeterminantInverseFiberEvaluation
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) :
    BoundedContinuousFunction (OrientationBoundary period hPeriod) Real :=
  Ring.inverse
    (candidateANormalBoundaryTotalRelativeMetricDeterminantFiberEvaluation
      period hPeriod metric current)

theorem
    candidateANormalBoundaryTotalRelativeMetricDeterminantInverseFiberEvaluation_contDiffOn_two
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    ContDiffOn Real 2
      (candidateANormalBoundaryTotalRelativeMetricDeterminantInverseFiberEvaluation
        period hPeriod metric)
      (candidateANormalBoundaryMetricParameterDomain
        period hPeriod metric) := by
  intro current hCurrent
  have hUnit :=
    candidateANormalBoundaryTotalRelativeMetricDeterminant_isUnit
      period hPeriod metric current hCurrent
  have hInverse : ContDiffAt Real 2 Ring.inverse
      (candidateANormalBoundaryTotalRelativeMetricDeterminantFiberEvaluation
        period hPeriod metric current) := by
    simpa using (contDiffAt_ringInverse Real hUnit.unit :
      ContDiffAt Real 2 Ring.inverse
        (hUnit.unit : BoundedContinuousFunction
          (OrientationBoundary period hPeriod) Real))
  exact hInverse.comp_contDiffWithinAt current
    ((candidateANormalBoundaryTotalRelativeMetricDeterminantFiberEvaluation_contDiff_two
      period hPeriod metric).contDiffWithinAt)

/-- Adjugate polynomial on the same global bounded matrix space. -/
def candidateANormalBoundaryMatrixFieldAdjugate
    (matrix : CandidateANormalBoundaryMatrixField period hPeriod) :
    CandidateANormalBoundaryMatrixField period hPeriod :=
  Matrix.adjugate matrix

theorem candidateANormalBoundaryMatrixFieldAdjugate_contDiff :
    ContDiff Real ∞
      (candidateANormalBoundaryMatrixFieldAdjugate period hPeriod) := by
  change @ContDiff Real _
    (Fin 4 → Fin 4 →
      BoundedContinuousFunction (OrientationBoundary period hPeriod) Real)
    Pi.normedAddCommGroup Pi.normedSpace
    (Fin 4 → Fin 4 →
      BoundedContinuousFunction (OrientationBoundary period hPeriod) Real)
    Pi.normedAddCommGroup Pi.normedSpace ∞
    (fun matrix row column => Matrix.adjugate matrix row column)
  rw [contDiff_pi]
  intro row
  rw [contDiff_pi]
  intro column
  have hUpdate : ContDiff Real ∞
      (fun matrix : CandidateANormalBoundaryMatrixField period hPeriod =>
        Matrix.updateRow matrix column (Pi.single row 1)) := by
    change @ContDiff Real _
      (Fin 4 → Fin 4 →
        BoundedContinuousFunction (OrientationBoundary period hPeriod) Real)
      Pi.normedAddCommGroup Pi.normedSpace
      (Fin 4 → Fin 4 →
        BoundedContinuousFunction (OrientationBoundary period hPeriod) Real)
      Pi.normedAddCommGroup Pi.normedSpace ∞
      (fun matrix currentRow currentColumn =>
        Matrix.updateRow matrix column (Pi.single row 1)
          currentRow currentColumn)
    rw [contDiff_pi]
    intro currentRow
    rw [contDiff_pi]
    intro currentColumn
    by_cases hRow : currentRow = column
    · subst currentRow
      simp only [Matrix.updateRow_self]
      exact contDiff_const
    · simpa only [Matrix.updateRow_ne hRow] using
        (contDiff_apply_apply Real
          (BoundedContinuousFunction
            (OrientationBoundary period hPeriod) Real)
          currentRow currentColumn)
  change ContDiff Real ∞
    (fun matrix : CandidateANormalBoundaryMatrixField period hPeriod =>
      Matrix.adjugate matrix row column)
  rw [show (fun matrix : CandidateANormalBoundaryMatrixField period hPeriod =>
      Matrix.adjugate matrix row column) =
    fun matrix => candidateANormalBoundaryMatrixFieldDeterminant
      period hPeriod
      (Matrix.updateRow matrix column (Pi.single row 1)) by
        funext matrix
        exact Matrix.adjugate_apply matrix row column]
  exact (candidateANormalBoundaryMatrixFieldDeterminant_contDiff
    period hPeriod).comp hUpdate

/-- The actual evaluated inverse matrix.  Mathlib's nonsingular inverse is
the determinant inverse times the adjugate. -/
def candidateANormalBoundaryTotalRelativeMetricInverseMatrixFiberEvaluation
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) :
    CandidateANormalBoundaryMatrixField period hPeriod :=
  (candidateANormalBoundaryTotalRelativeMetricMatrixFiberEvaluation
    period hPeriod metric current)⁻¹

theorem candidateANormalBoundaryTotalRelativeMetricInverseMatrixFiberEvaluation_contDiffOn_two
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    ContDiffOn Real 2
      (candidateANormalBoundaryTotalRelativeMetricInverseMatrixFiberEvaluation
        period hPeriod metric)
      (candidateANormalBoundaryMetricParameterDomain
        period hPeriod metric) := by
  have hDetInverse :=
    candidateANormalBoundaryTotalRelativeMetricDeterminantInverseFiberEvaluation_contDiffOn_two
      period hPeriod metric
  have hAdjugate : ContDiff Real 2 (fun current =>
      candidateANormalBoundaryMatrixFieldAdjugate period hPeriod
        (candidateANormalBoundaryTotalRelativeMetricMatrixFiberEvaluation
          period hPeriod metric current)) :=
    (candidateANormalBoundaryMatrixFieldAdjugate_contDiff
      period hPeriod).of_le
        (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top) |>.comp
      (candidateANormalBoundaryTotalRelativeMetricMatrixFiberEvaluation_contDiff_two
        period hPeriod metric)
  rw [show
      candidateANormalBoundaryTotalRelativeMetricInverseMatrixFiberEvaluation
          period hPeriod metric =
        fun current =>
          candidateANormalBoundaryTotalRelativeMetricDeterminantInverseFiberEvaluation
              period hPeriod metric current •
            candidateANormalBoundaryMatrixFieldAdjugate period hPeriod
              (candidateANormalBoundaryTotalRelativeMetricMatrixFiberEvaluation
                period hPeriod metric current) by
    funext current
    exact Matrix.inv_def _]
  change @ContDiffOn Real _
    (Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real)
    _ _
    (Fin 4 → Fin 4 →
      BoundedContinuousFunction (OrientationBoundary period hPeriod) Real)
    Pi.normedAddCommGroup Pi.normedSpace 2
    (fun current row column =>
      candidateANormalBoundaryTotalRelativeMetricDeterminantInverseFiberEvaluation
          period hPeriod metric current *
        candidateANormalBoundaryMatrixFieldAdjugate period hPeriod
          (candidateANormalBoundaryTotalRelativeMetricMatrixFiberEvaluation
            period hPeriod metric current) row column)
    (candidateANormalBoundaryMetricParameterDomain
      period hPeriod metric)
  rw [contDiffOn_pi]
  intro row
  rw [contDiffOn_pi]
  intro column
  exact hDetInverse.mul
    ((contDiffOn_pi.mp (contDiffOn_pi.mp hAdjugate.contDiffOn row) column))

/-- On the admissible domain, the adjugate presentation is exactly the
previously completed C2 inverse evaluated on the same graph. -/
theorem candidateANormalBoundaryTotalRelativeMetricInverseMatrixFiberEvaluation_eq_c2Inverse
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real)
    (hCurrent : current ∈
      candidateANormalBoundaryMetricParameterDomain
        period hPeriod metric) :
    candidateANormalBoundaryTotalRelativeMetricInverseMatrixFiberEvaluation
        period hPeriod metric current =
      candidateANormalBoundaryC2InverseMatrixFiberEvaluation
        period hPeriod metric current := by
  change
    (candidateANormalBoundaryTotalRelativeMetricMatrixFiberEvaluation
      period hPeriod metric current)⁻¹ = _
  exact Matrix.inv_eq_left_inv
    (candidateANormalBoundaryC2Inverse_mul_totalRelativeMetric
      period hPeriod metric current hCurrent)

/-- Public inverse-metric part of H10: the old admissible metric domain is
open around zero, and the evaluated inverse is C2 there and agrees with the
already completed bulk C2 inverse. -/
theorem candidate_a_normal_boundary_inverse_metric_matrix_fiber_c2_gate
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    IsOpen
        (candidateANormalBoundaryMetricParameterDomain
          period hPeriod metric) ∧
      (0 : Prod
        (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) ∈
        candidateANormalBoundaryMetricParameterDomain
          period hPeriod metric ∧
      ContDiffOn Real 2
        (candidateANormalBoundaryTotalRelativeMetricInverseMatrixFiberEvaluation
          period hPeriod metric)
        (candidateANormalBoundaryMetricParameterDomain
          period hPeriod metric) ∧
      ∀ current,
        current ∈ candidateANormalBoundaryMetricParameterDomain
            period hPeriod metric →
          candidateANormalBoundaryTotalRelativeMetricInverseMatrixFiberEvaluation
              period hPeriod metric current =
            candidateANormalBoundaryC2InverseMatrixFiberEvaluation
              period hPeriod metric current :=
  ⟨candidateANormalBoundaryMetricParameterDomain_isOpen
      period hPeriod metric,
    zero_mem_candidateANormalBoundaryMetricParameterDomain
      period hPeriod metric,
    candidateANormalBoundaryTotalRelativeMetricInverseMatrixFiberEvaluation_contDiffOn_two
      period hPeriod metric,
    candidateANormalBoundaryTotalRelativeMetricInverseMatrixFiberEvaluation_eq_c2Inverse
      period hPeriod metric⟩

/-- Public matrix-level H10 gate.  It is only finite assembly of the scalar
gates, so it introduces no additional metric representation. -/
theorem candidate_a_normal_boundary_metric_matrix_fiber_c2_gate
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    ContDiff Real 2
        (candidateANormalBoundaryTotalRelativeMetricMatrixFiberEvaluation
          period hPeriod metric) ∧
      ContDiff Real 2
        (candidateANormalBoundaryTotalRelativeMetricDeterminantFiberEvaluation
          period hPeriod metric) ∧
      ∀ spatial : BoundaryMetricJetIndex period hPeriod,
        ContDiff Real 2
          (candidateANormalBoundaryRelativeMetricSpatialFirstMatrixFiberEvaluation
            period hPeriod metric spatial) :=
  ⟨candidateANormalBoundaryTotalRelativeMetricMatrixFiberEvaluation_contDiff_two
      period hPeriod metric,
    candidateANormalBoundaryTotalRelativeMetricDeterminantFiberEvaluation_contDiff_two
      period hPeriod metric,
    candidateANormalBoundaryRelativeMetricSpatialFirstMatrixFiberEvaluation_contDiff_two
      period hPeriod metric⟩

end
end P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
end JanusFormal
