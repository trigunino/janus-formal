import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusBoundedFiberJetSubstitutionC2
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusBoundedFiberJet2SubstitutionC2
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularFrameMetricInverse4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D
import Mathlib.Geometry.Manifold.Metrizable
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Determinant

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
open Bundle
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusEquivariantSmoothDescent4D
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
open P0EFTJanusMappingTorusCutBoundaryFirstSheetCurrentBridge4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusNormalBundleOrientationCover
open P0EFTJanusD8NormalBundleD9DisplacementBridge4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusMappingTorusIntrinsicCoverLorentzTensor4D
open P0EFTJanusMappingTorusIntrinsicLorentzMetricDescent4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusMappingTorusIntrinsicMetricBVThroatBracket4D
open P0EFTJanusMappingTorusIntrinsicMetricThroatNondegenerate4D
open P0EFTJanusProgramPGeneralMetricPositiveDualizer4D
open P0EFTJanusProgramPGeneralMetricC2RelativeEndomorphism4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPGeneralMetricC2VolumeDensity4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2Maxwell4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusProgramPRegularFrameMetricInverse4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusProgramPRegularFrameMaxwellCurvatureBridge4D
open P0EFTJanusProgramPGlobalNormalDisplacementCollarGraph4D
open P0EFTJanusProgramPThroatFiniteFrameReconstruction4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryC3MetricCore4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalNormalDisplacementCollarJointSmooth4D
open P0EFTJanusBoundedFiberJetSubstitutionC2
open P0EFTJanusBoundedFiberJet2SubstitutionC2

private abbrev RealHasDerivAt
    (function : Real → Real) (derivative point : Real) : Prop :=
  @HasDerivAt Real _ Real Real.normedAddCommGroup.toAddCommGroup
    RCLike.toInnerProductSpaceReal.toModule _ _ function derivative point

variable (period : Real) (hPeriod : period ≠ 0)

/-- Public shorthand for the oriented cut-throat boundary used by the
Candidate-A fiber API. -/
abbrev OrientationBoundary :=
  CutThroatBoundary period hPeriod

private abbrev OrientationBoundaryCover :=
  MappingTorusCover (orientationDoubleData period hPeriod)

private abbrev EffectiveThroatCover :=
  MappingTorusCover (fixedEquatorData period hPeriod)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

/-- Index of the already existing finite smooth spanning frame on the
orientation boundary. -/
abbrev NormalBoundaryTangentIndex :=
  Fin (finiteSmoothThroatGeneratingFrame
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)).count

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

/-- The descended collar point is jointly smooth in the orientation-boundary
point and latitude. -/
theorem normalBoundaryLatitudeFiberPoint_joint_contMDiff :
    ContMDiff
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      coverModelWithCorners ∞
      (fun current : OrientationBoundary period hPeriod × Real =>
        normalBoundaryLatitudeFiberPoint period hPeriod current.1 current.2) := by
  let coverField := fun current :
      OrientationBoundaryCover period hPeriod × Real =>
    normalBoundaryLatitudeFiberPointCover period hPeriod current
  have hInvariant : ∀ (winding : Int)
      (current : OrientationBoundaryCover period hPeriod × Real),
      coverField (winding +ᵥ current.1, current.2) = coverField current := by
    intro winding current
    exact normalBoundaryLatitudeFiberPointCover_invariant
      period hPeriod winding current.1 current.2
  have hDescended := mappingTorusInvariantMapProd_contMDiff
    (orientationDoubleData period hPeriod) throatCoverModelWithCorners ∞
    (modelWithCornersSelf Real Real) coverModelWithCorners coverField hInvariant
    (fixedThroat_projection_isLocalDiffeomorph_smooth
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
    (normalBoundaryLatitudeFiberPointCover_contMDiff period hPeriod)
  exact hDescended.congr fun current => by
    obtain ⟨coverPoint, hPoint⟩ :=
      mappingTorusMk_surjective (orientationDoubleData period hPeriod) current.1
    rcases current with ⟨boundary, latitude⟩
    dsimp only at hPoint ⊢
    subst boundary
    rfl

/-- The zero-latitude slice is exactly the fixed throat pulled back to its
orientation double. -/
@[simp]
theorem normalBoundaryLatitudeFiberPoint_zero
    (boundary : OrientationBoundary period hPeriod) :
    normalBoundaryLatitudeFiberPoint period hPeriod boundary 0 =
      fixedThroatQuotientInclusion period hPeriod
        (orientationDoubleToThroat period hPeriod boundary) := by
  refine Quotient.inductionOn boundary ?_
  intro point
  rw [normalBoundaryLatitudeFiberPoint_mk,
    normalBoundaryLatitudeFiberPointCover_eq, quotientNormalLatitude_zero,
    orientationDoubleToThroat_mk]

/-- Horizontal source tangent supplied by the existing spanning frame on the
orientation boundary. -/
def normalBoundaryLatitudeHorizontalTangentLift
    (index : NormalBoundaryTangentIndex period hPeriod)
    (current : OrientationBoundary period hPeriod × Real) :
    TangentBundle
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (OrientationBoundary period hPeriod × Real) :=
  (equivTangentBundleProd throatCoverModelWithCorners
      (OrientationBoundary period hPeriod)
      (modelWithCornersSelf Real Real) Real).symm
    (⟨current.1,
        (finiteSmoothThroatGeneratingFrame
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
            |>.vectorAt current.1 index⟩,
      ⟨current.2, 0⟩)

theorem normalBoundaryLatitudeHorizontalTangentLift_contMDiff
    (index : NormalBoundaryTangentIndex period hPeriod) :
    ContMDiff
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (throatCoverModelWithCorners.prod
        (modelWithCornersSelf Real Real)).tangent ∞
      (normalBoundaryLatitudeHorizontalTangentLift
        period hPeriod index) := by
  apply (contMDiff_equivTangentBundleProd_symm
    (I := throatCoverModelWithCorners)
    (I' := modelWithCornersSelf Real Real)
    (M := OrientationBoundary period hPeriod)
    (M' := Real)).comp
  have hBoundary : ContMDiff
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      throatCoverModelWithCorners.tangent ∞
      (fun current : OrientationBoundary period hPeriod × Real =>
        (⟨current.1,
          (finiteSmoothThroatGeneratingFrame
            (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
              |>.vectorAt current.1 index⟩ :
          TangentBundle throatCoverModelWithCorners
            (OrientationBoundary period hPeriod))) :=
    by
      have hFrame :=
        (finiteSmoothThroatGeneratingFrame
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
            |>.contMDiff_vector index
      change ContMDiff throatCoverModelWithCorners
        throatCoverModelWithCorners.tangent ∞
        (fun point : OrientationBoundary period hPeriod =>
          (⟨point,
            (finiteSmoothThroatGeneratingFrame
              (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
                |>.vectorAt point index⟩ :
            TangentBundle throatCoverModelWithCorners
              (OrientationBoundary period hPeriod))) at hFrame
      exact hFrame.comp contMDiff_fst
  have hFiber : ContMDiff
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real Real).tangent ∞
      (fun current : OrientationBoundary period hPeriod × Real =>
        (⟨current.2, 0⟩ :
          TangentBundle (modelWithCornersSelf Real Real) Real)) :=
    (Bundle.contMDiff_zeroSection Real
      (TangentSpace (modelWithCornersSelf Real Real) : Real → Type _)).of_le
        le_top |>.comp contMDiff_snd
  exact hBoundary.prodMk hFiber

/-- Horizontal derivative of the same installed collar map. -/
def normalBoundaryLatitudeHorizontalFiberLift
    (index : NormalBoundaryTangentIndex period hPeriod)
    (current : OrientationBoundary period hPeriod × Real) :
    TangentBundle coverModelWithCorners (EffectiveQuotient period hPeriod) :=
  tangentMap
    (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
    coverModelWithCorners
    (fun point : OrientationBoundary period hPeriod × Real =>
      normalBoundaryLatitudeFiberPoint period hPeriod point.1 point.2)
    (normalBoundaryLatitudeHorizontalTangentLift
      period hPeriod index current)

theorem normalBoundaryLatitudeHorizontalFiberLift_contMDiff
    (index : NormalBoundaryTangentIndex period hPeriod) :
    ContMDiff
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      coverModelWithCorners.tangent ∞
      (normalBoundaryLatitudeHorizontalFiberLift
        period hPeriod index) := by
  exact ((normalBoundaryLatitudeFiberPoint_joint_contMDiff period hPeriod)
    |>.contMDiff_tangentMap (by simp)).comp
      (normalBoundaryLatitudeHorizontalTangentLift_contMDiff
        period hPeriod index)

@[simp]
theorem normalBoundaryLatitudeHorizontalFiberLift_base
    (index : NormalBoundaryTangentIndex period hPeriod)
    (current : OrientationBoundary period hPeriod × Real) :
    (normalBoundaryLatitudeHorizontalFiberLift
      period hPeriod index current).1 =
      normalBoundaryLatitudeFiberPoint period hPeriod current.1 current.2 :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The installed horizontal lift is the genuine boundary partial derivative
of the same joint collar map at every latitude. -/
theorem normalBoundaryLatitudeHorizontalFiberLift_eq_mfderiv_horizontal
    (index : NormalBoundaryTangentIndex period hPeriod)
    (boundary : OrientationBoundary period hPeriod) (latitude : Real) :
    (normalBoundaryLatitudeHorizontalFiberLift period hPeriod index
        (boundary, latitude)).2 =
      mfderiv throatCoverModelWithCorners coverModelWithCorners
        (fun point : OrientationBoundary period hPeriod =>
          normalBoundaryLatitudeFiberPoint period hPeriod point latitude)
        boundary
        ((finiteSmoothThroatGeneratingFrame
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)).vectorAt
            boundary index) := by
  let vector :=
    (finiteSmoothThroatGeneratingFrame
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)).vectorAt
        boundary index
  let collar := fun current : OrientationBoundary period hPeriod × Real =>
    normalBoundaryLatitudeFiberPoint period hPeriod current.1 current.2
  have hCollar : MDifferentiableAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      coverModelWithCorners collar (boundary, latitude) :=
    (normalBoundaryLatitudeFiberPoint_joint_contMDiff period hPeriod)
      |>.mdifferentiableAt (by simp)
  have hProduct := mfderiv_prod_eq_add_apply
    (E := ThroatCoverCoordinates) (E' := Real)
    (I := throatCoverModelWithCorners)
    (I' := modelWithCornersSelf Real Real)
    (v := (vector, 0)) hCollar
  rw [map_zero, add_zero] at hProduct
  unfold normalBoundaryLatitudeHorizontalFiberLift
    normalBoundaryLatitudeHorizontalTangentLift
  change mfderiv
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      coverModelWithCorners collar (boundary, latitude) (vector, 0) = _
  exact hProduct

attribute [-instance] orientationBoundaryMetricSpace
    orientationBoundaryChartedSpace in
/-- At zero latitude the installed horizontal lift is the derivative of the
zero slice of the same collar map. -/
def normalBoundaryLatitudeZeroHorizontalTangentMap
    (index : NormalBoundaryTangentIndex period hPeriod)
    (boundary : OrientationBoundary period hPeriod) :
    TangentBundle coverModelWithCorners (EffectiveQuotient period hPeriod) := by
  letI : TopologicalSpace (OrientationBoundary period hPeriod) :=
    instTopologicalSpaceQuotient
  letI : ChartedSpace ThroatCoverModel
      (OrientationBoundary period hPeriod) :=
    AddAction.instChartedSpaceQuotient
  exact @tangentMap
    Real inferInstance
    ThroatCoverCoordinates inferInstance inferInstance
    ThroatCoverModel inferInstance
    throatCoverModelWithCorners
    (OrientationBoundary period hPeriod) instTopologicalSpaceQuotient
      AddAction.instChartedSpaceQuotient
    CoverCoordinates inferInstance inferInstance
    CoverModel inferInstance
    coverModelWithCorners
    (EffectiveQuotient period hPeriod) inferInstance inferInstance
    (fun point : OrientationBoundary period hPeriod =>
      normalBoundaryLatitudeFiberPoint period hPeriod point 0)
    ⟨boundary,
      (finiteSmoothThroatGeneratingFrame
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
          |>.vectorAt boundary index⟩

attribute [-instance] orientationBoundaryMetricSpace
    orientationBoundaryChartedSpace in
theorem normalBoundaryLatitudeHorizontalFiberLift_zero_tangentMap
    (index : NormalBoundaryTangentIndex period hPeriod)
    (boundary : OrientationBoundary period hPeriod) :
    normalBoundaryLatitudeHorizontalFiberLift period hPeriod index
        (boundary, 0) =
      normalBoundaryLatitudeZeroHorizontalTangentMap period hPeriod
        index boundary := by
  letI : TopologicalSpace (OrientationBoundary period hPeriod) :=
    instTopologicalSpaceQuotient
  letI : ChartedSpace ThroatCoverModel
      (OrientationBoundary period hPeriod) :=
    AddAction.instChartedSpaceQuotient
  let slice : OrientationBoundary period hPeriod →
      OrientationBoundary period hPeriod × Real := fun point => (point, 0)
  have hCollarAt : MDifferentiableAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      coverModelWithCorners
      (fun current : OrientationBoundary period hPeriod × Real =>
        normalBoundaryLatitudeFiberPoint period hPeriod current.1 current.2)
      (boundary, 0) :=
    (normalBoundaryLatitudeFiberPoint_joint_contMDiff period hPeriod)
      |>.mdifferentiableAt (by simp)
  have hSliceAt : MDifferentiableAt throatCoverModelWithCorners
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      slice boundary :=
    mdifferentiableAt_id.prodMk mdifferentiableAt_const
  have hComp := tangentMap_comp_at
    (I := throatCoverModelWithCorners)
    (I' := throatCoverModelWithCorners.prod
      (modelWithCornersSelf Real Real))
    (I'' := coverModelWithCorners)
    (f := slice)
    (g := fun current : OrientationBoundary period hPeriod × Real =>
      normalBoundaryLatitudeFiberPoint period hPeriod current.1 current.2)
    (⟨boundary,
      (finiteSmoothThroatGeneratingFrame
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
          |>.vectorAt boundary index⟩ :
      TangentBundle throatCoverModelWithCorners
        (OrientationBoundary period hPeriod))
    hCollarAt hSliceAt
  rw [tangentMap_prod_left] at hComp
  simp only [Function.comp_def] at hComp
  unfold normalBoundaryLatitudeHorizontalFiberLift
    normalBoundaryLatitudeHorizontalTangentLift
    normalBoundaryLatitudeZeroHorizontalTangentMap
  change tangentMap
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      coverModelWithCorners
      (fun current : OrientationBoundary period hPeriod × Real =>
        normalBoundaryLatitudeFiberPoint period hPeriod current.1 current.2)
      ⟨(boundary, 0),
        ((finiteSmoothThroatGeneratingFrame
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
            |>.vectorAt boundary index, 0)⟩ =
    @tangentMap
      Real inferInstance
      ThroatCoverCoordinates inferInstance inferInstance
      ThroatCoverModel inferInstance
      throatCoverModelWithCorners
      (OrientationBoundary period hPeriod) instTopologicalSpaceQuotient
        AddAction.instChartedSpaceQuotient
      CoverCoordinates inferInstance inferInstance
      CoverModel inferInstance
      coverModelWithCorners
      (EffectiveQuotient period hPeriod) inferInstance inferInstance
      (fun point : OrientationBoundary period hPeriod =>
        normalBoundaryLatitudeFiberPoint period hPeriod point 0)
      ⟨boundary,
        (finiteSmoothThroatGeneratingFrame
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
            |>.vectorAt boundary index⟩
  simpa only [slice] using hComp.symm

attribute [-instance] orientationBoundaryMetricSpace
    orientationBoundaryChartedSpace in
/-- Tangent equivalence of the already proved orientation-double local
diffeomorphism. -/
def normalBoundaryOrientationTangentEquiv
    (boundary : OrientationBoundary period hPeriod) :
    TangentSpace throatCoverModelWithCorners boundary ≃L[Real]
      TangentSpace throatCoverModelWithCorners
        (orientationDoubleToThroat period hPeriod boundary) := by
  letI : TopologicalSpace (OrientationBoundary period hPeriod) :=
    instTopologicalSpaceQuotient
  letI : ChartedSpace ThroatCoverModel
      (OrientationBoundary period hPeriod) :=
    AddAction.instChartedSpaceQuotient
  exact (orientationDoubleToThroat_isLocalDiffeomorph
    period hPeriod boundary).mfderivToContinuousLinearEquiv (by simp)

attribute [-instance] orientationBoundaryMetricSpace
    orientationBoundaryChartedSpace in
theorem normalBoundaryOrientationTangentEquiv_apply
    (boundary : OrientationBoundary period hPeriod)
    (vector : TangentSpace throatCoverModelWithCorners boundary) :
    normalBoundaryOrientationTangentEquiv period hPeriod boundary vector =
      mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
        (orientationDoubleToThroat period hPeriod) boundary vector := by
  letI : TopologicalSpace (OrientationBoundary period hPeriod) :=
    instTopologicalSpaceQuotient
  letI : ChartedSpace ThroatCoverModel
      (OrientationBoundary period hPeriod) :=
    AddAction.instChartedSpaceQuotient
  change ((orientationDoubleToThroat_isLocalDiffeomorph
      period hPeriod boundary).mfderivToContinuousLinearEquiv
        (by simp)) vector = _
  exact congrArg (fun derivative => derivative vector)
    (orientationDoubleToThroat_isLocalDiffeomorph period hPeriod boundary
      |>.mfderivToContinuousLinearEquiv_coe (by simp))

attribute [-instance] orientationBoundaryMetricSpace
    orientationBoundaryChartedSpace in
/-- The derivative of the installed local orientation section is the inverse
of the installed orientation tangent equivalence. -/
theorem normalGraphOrientationLocalSection_mfderiv_tangentEquiv
    (boundary : OrientationBoundary period hPeriod)
    (vector : TangentSpace throatCoverModelWithCorners boundary) :
    mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
        (normalGraphOrientationLocalSection period hPeriod boundary)
        (orientationDoubleToThroat period hPeriod boundary)
        (normalBoundaryOrientationTangentEquiv period hPeriod boundary vector) =
      vector := by
  letI : TopologicalSpace (OrientationBoundary period hPeriod) :=
    instTopologicalSpaceQuotient
  letI : ChartedSpace ThroatCoverModel
      (OrientationBoundary period hPeriod) :=
    AddAction.instChartedSpaceQuotient
  rw [normalBoundaryOrientationTangentEquiv_apply]
  exact
    (orientationDoubleToThroat_isLocalDiffeomorph period hPeriod boundary
      |>.mfderivToContinuousLinearEquiv (by simp)).left_inv vector

attribute [-instance] orientationBoundaryMetricSpace
    orientationBoundaryChartedSpace in
/-- The zero-slice derivative factors through the orientation projection and
the already installed fixed-throat inclusion. -/
theorem normalBoundaryLatitudeZeroHorizontalTangentMap_eq_fixedThroat
    (index : NormalBoundaryTangentIndex period hPeriod)
    (boundary : OrientationBoundary period hPeriod) :
    normalBoundaryLatitudeZeroHorizontalTangentMap period hPeriod
        index boundary =
      tangentMap throatCoverModelWithCorners coverModelWithCorners
        (fixedThroatQuotientInclusion period hPeriod)
        ⟨orientationDoubleToThroat period hPeriod boundary,
          normalBoundaryOrientationTangentEquiv period hPeriod boundary
            ((finiteSmoothThroatGeneratingFrame
              (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
                |>.vectorAt boundary index)⟩ := by
  letI : TopologicalSpace (OrientationBoundary period hPeriod) :=
    instTopologicalSpaceQuotient
  letI : ChartedSpace ThroatCoverModel
      (OrientationBoundary period hPeriod) :=
    AddAction.instChartedSpaceQuotient
  let sourceTangent : TangentBundle throatCoverModelWithCorners
      (OrientationBoundary period hPeriod) :=
    ⟨boundary,
      (finiteSmoothThroatGeneratingFrame
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
          |>.vectorAt boundary index⟩
  have hOuter : MDifferentiableAt throatCoverModelWithCorners
      coverModelWithCorners (fixedThroatQuotientInclusion period hPeriod)
      (orientationDoubleToThroat period hPeriod boundary) :=
    (fixedThroatQuotientInclusion_contMDiff period hPeriod)
      |>.mdifferentiableAt (by simp)
  have hInner : MDifferentiableAt throatCoverModelWithCorners
      throatCoverModelWithCorners (orientationDoubleToThroat period hPeriod)
      boundary :=
    (orientationDoubleToThroat_contMDiff period hPeriod)
      |>.mdifferentiableAt (by simp)
  have hComp := tangentMap_comp_at
    (I := throatCoverModelWithCorners)
    (I' := throatCoverModelWithCorners)
    (I'' := coverModelWithCorners)
    (f := orientationDoubleToThroat period hPeriod)
    (g := fixedThroatQuotientInclusion period hPeriod)
    sourceTangent hOuter hInner
  have hMap :
      fixedThroatQuotientInclusion period hPeriod ∘
          orientationDoubleToThroat period hPeriod =
        fun point : OrientationBoundary period hPeriod =>
          normalBoundaryLatitudeFiberPoint period hPeriod point 0 := by
    funext point
    exact (normalBoundaryLatitudeFiberPoint_zero
      period hPeriod point).symm
  rw [hMap] at hComp
  have hTangent :
      tangentMap throatCoverModelWithCorners throatCoverModelWithCorners
          (orientationDoubleToThroat period hPeriod) sourceTangent =
        ⟨orientationDoubleToThroat period hPeriod boundary,
          normalBoundaryOrientationTangentEquiv period hPeriod boundary
            ((finiteSmoothThroatGeneratingFrame
              (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
                |>.vectorAt boundary index)⟩ := by
    apply Bundle.TotalSpace.ext
    · rfl
    · exact (normalBoundaryOrientationTangentEquiv_apply period hPeriod
        boundary
        ((finiteSmoothThroatGeneratingFrame
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
            |>.vectorAt boundary index)).symm.heq
  rw [hTangent] at hComp
  simpa only [sourceTangent,
    normalBoundaryLatitudeZeroHorizontalTangentMap] using hComp

/-- Combined zero-slice bridge from the installed horizontal lift to the
fixed-throat differential. -/
theorem normalBoundaryLatitudeHorizontalFiberLift_zero_eq_fixedThroat
    (index : NormalBoundaryTangentIndex period hPeriod)
    (boundary : OrientationBoundary period hPeriod) :
    normalBoundaryLatitudeHorizontalFiberLift period hPeriod index
        (boundary, 0) =
      tangentMap throatCoverModelWithCorners coverModelWithCorners
        (fixedThroatQuotientInclusion period hPeriod)
        ⟨orientationDoubleToThroat period hPeriod boundary,
          normalBoundaryOrientationTangentEquiv period hPeriod boundary
            ((finiteSmoothThroatGeneratingFrame
              (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
                |>.vectorAt boundary index)⟩ :=
  (normalBoundaryLatitudeHorizontalFiberLift_zero_tangentMap
    period hPeriod index boundary).trans
      (normalBoundaryLatitudeZeroHorizontalTangentMap_eq_fixedThroat
        period hPeriod index boundary)

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

theorem normalBoundaryLatitudeFiberLift_joint_contMDiff :
    ContMDiff
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      coverModelWithCorners.tangent ∞
      (fun current : OrientationBoundary period hPeriod × Real =>
        normalBoundaryLatitudeFiberLift period hPeriod current.1 current.2) := by
  let coverField := fun current :
      OrientationBoundaryCover period hPeriod × Real =>
    normalBoundaryLatitudeFiberLiftCover period hPeriod current
  have hInvariant : ∀ (winding : Int)
      (current : OrientationBoundaryCover period hPeriod × Real),
      coverField (winding +ᵥ current.1, current.2) = coverField current := by
    intro winding current
    exact normalBoundaryLatitudeFiberLiftCover_invariant
      period hPeriod winding current.1 current.2
  have hDescended := mappingTorusInvariantMapProd_contMDiff
    (orientationDoubleData period hPeriod) throatCoverModelWithCorners ∞
    (modelWithCornersSelf Real Real) coverModelWithCorners.tangent coverField
    hInvariant
    (fixedThroat_projection_isLocalDiffeomorph_smooth
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
    (normalBoundaryLatitudeFiberLiftCover_contMDiff period hPeriod)
  exact hDescended.congr fun current => by
    obtain ⟨coverPoint, hPoint⟩ :=
      mappingTorusMk_surjective (orientationDoubleData period hPeriod) current.1
    rcases current with ⟨boundary, latitude⟩
    dsimp only at hPoint ⊢
    subst boundary
    rfl

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

set_option backward.isDefEq.respectTransparency false in
/-- The descended canonical latitude lift is the genuine vertical partial
derivative of the same joint collar map. -/
theorem normalBoundaryLatitudeFiberLift_eq_mfderiv_vertical
    (boundary : OrientationBoundary period hPeriod) (latitude : Real) :
    (normalBoundaryLatitudeFiberLift period hPeriod boundary latitude).2 =
      mfderiv (modelWithCornersSelf Real Real) coverModelWithCorners
        (fun varied : Real =>
          normalBoundaryLatitudeFiberPoint period hPeriod boundary varied)
        latitude 1 := by
  refine Quotient.inductionOn boundary ?_
  intro point
  rw [normalBoundaryLatitudeFiberLift_mk,
    normalBoundaryLatitudeFiberPoint_mk]
  unfold normalBoundaryLatitudeFiberLiftCover
    normalBoundaryLatitudeFiberPointCover
  let base := normalGraphCanonicalLatitudeBaseCover period hPeriod point
  let collar := canonicalLatitudeCollarMap period hPeriod
  have hCollar : MDifferentiableAt canonicalLatitudeParameterModelWithCorners
      coverModelWithCorners collar (base, latitude) :=
    (canonicalLatitudeCollar_contMDiff period hPeriod)
      |>.mdifferentiableAt (by simp)
  have hProduct := mfderiv_prod_eq_add_apply
    (v := (0, 1)) hCollar
  rw [map_zero, zero_add] at hProduct
  have hLift := congrArg (fun tangent => tangent.2)
    (canonicalLatitudeNormalLift_eq_tangentMap_vertical period hPeriod
      (canonicalLatitudeCollar_contMDiffOne period hPeriod) (base, latitude))
  change (canonicalLatitudeNormalLift period hPeriod (base, latitude)).2 = _
  rw [hLift]
  exact hProduct

/-! ### Existing regular-frame coordinates of the collar tangents -/

/-- Canonical coefficient of a smooth tangent lift in the regular frame
already stored by the base metric. -/
def normalBoundaryRegularFrameCoefficient
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (lift : OrientationBoundary period hPeriod × Real →
      TangentBundle coverModelWithCorners (EffectiveQuotient period hPeriod))
    (row : Fin 4)
    (current : OrientationBoundary period hPeriod × Real) : Real :=
  metric.metric.tensor.tensor (lift current).1
    ((regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
      |>.vectorAt (lift current).1 row)
    (generalMetricFiniteFrameInverseOperator period hPeriod
      (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
      metric.metric (lift current).1 (lift current).2)

theorem normalBoundaryRegularFrameCoefficient_contMDiff
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (lift : OrientationBoundary period hPeriod × Real →
      TangentBundle coverModelWithCorners (EffectiveQuotient period hPeriod))
    (hLift : ContMDiff
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      coverModelWithCorners.tangent ∞ lift)
    (row : Fin 4) :
    ContMDiff
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real Real) ∞
      (normalBoundaryRegularFrameCoefficient
        period hPeriod metric lift row) := by
  unfold normalBoundaryRegularFrameCoefficient
  have hProjection : ContMDiff coverModelWithCorners.tangent
      coverModelWithCorners ∞
      (fun current : TangentBundle coverModelWithCorners
          (EffectiveQuotient period hPeriod) => current.1) :=
    Bundle.contMDiff_proj
      (fun point : EffectiveQuotient period hPeriod =>
        TangentSpace coverModelWithCorners point)
  have hPoint := hProjection.comp hLift
  have hInverse :=
    (generalMetricFiniteFrameInverseOperator period hPeriod
      (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
      metric.metric).contMDiff.comp hPoint
  have hSolved := hInverse.clm_bundle_apply hLift
  have hFrame :=
    ((regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
      |>.contMDiff_vector row).comp hPoint
  have hTensor := metric.metric.tensor.tensor.contMDiff.comp hPoint
  have hApplied := ContMDiff.clm_bundle_apply₂
    (F₃ := Real)
    (E₃ := fun _ : EffectiveQuotient period hPeriod => Real)
    hTensor hFrame hSolved
  intro current
  have hAppliedAt := hApplied current
  rw [Bundle.contMDiffAt_totalSpace] at hAppliedAt
  convert hAppliedAt.2 using 1 <;> rfl

/-- Vertical latitude coefficient in the installed regular frame. -/
def normalBoundaryLatitudeVerticalRegularFrameCoefficient
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (row : Fin 4)
    (current : OrientationBoundary period hPeriod × Real) : Real :=
  normalBoundaryRegularFrameCoefficient period hPeriod metric
    (fun point =>
      normalBoundaryLatitudeFiberLift period hPeriod point.1 point.2)
    row current

theorem normalBoundaryLatitudeVerticalRegularFrameCoefficient_contMDiff
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (row : Fin 4) :
    ContMDiff
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real Real) ∞
      (normalBoundaryLatitudeVerticalRegularFrameCoefficient
        period hPeriod metric row) :=
  normalBoundaryRegularFrameCoefficient_contMDiff period hPeriod metric _
    (normalBoundaryLatitudeFiberLift_joint_contMDiff period hPeriod) row

/-- Horizontal coefficient for one pre-existing throat generator. -/
def normalBoundaryLatitudeHorizontalRegularFrameCoefficient
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (index : NormalBoundaryTangentIndex period hPeriod)
    (row : Fin 4)
    (current : OrientationBoundary period hPeriod × Real) : Real :=
  normalBoundaryRegularFrameCoefficient period hPeriod metric
    (normalBoundaryLatitudeHorizontalFiberLift period hPeriod index)
    row current

theorem normalBoundaryLatitudeHorizontalRegularFrameCoefficient_contMDiff
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (index : NormalBoundaryTangentIndex period hPeriod)
    (row : Fin 4) :
    ContMDiff
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real Real) ∞
      (normalBoundaryLatitudeHorizontalRegularFrameCoefficient
        period hPeriod metric index row) :=
  normalBoundaryRegularFrameCoefficient_contMDiff period hPeriod metric _
    (normalBoundaryLatitudeHorizontalFiberLift_contMDiff
      period hPeriod index) row

theorem normalBoundaryLatitudeVerticalRegularFrame_reconstructs
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (current : OrientationBoundary period hPeriod × Real) :
    (normalBoundaryLatitudeFiberLift period hPeriod current.1 current.2).2 =
      ∑ row : Fin 4,
        normalBoundaryLatitudeVerticalRegularFrameCoefficient
            period hPeriod metric row current •
          ((regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
            |>.vectorAt
              (normalBoundaryLatitudeFiberLift
                period hPeriod current.1 current.2).1 row) := by
  exact generalMetricFiniteFrameCoefficientAt_reconstructs period hPeriod
    (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
    metric.metric
    (normalBoundaryLatitudeFiberLift period hPeriod current.1 current.2).1
    (normalBoundaryLatitudeFiberLift period hPeriod current.1 current.2).2

theorem normalBoundaryLatitudeHorizontalRegularFrame_reconstructs
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (index : NormalBoundaryTangentIndex period hPeriod)
    (current : OrientationBoundary period hPeriod × Real) :
    (normalBoundaryLatitudeHorizontalFiberLift
        period hPeriod index current).2 =
      ∑ row : Fin 4,
        normalBoundaryLatitudeHorizontalRegularFrameCoefficient
            period hPeriod metric index row current •
          ((regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
            |>.vectorAt
              (normalBoundaryLatitudeHorizontalFiberLift
                period hPeriod index current).1 row) := by
  exact generalMetricFiniteFrameCoefficientAt_reconstructs period hPeriod
    (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
    metric.metric
    (normalBoundaryLatitudeHorizontalFiberLift
      period hPeriod index current).1
    (normalBoundaryLatitudeHorizontalFiberLift
      period hPeriod index current).2

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

/-! ### The stored spatial two-jet of the raw graph -/

/-- First stored spatial derivative as a bounded field on the compact
orientation boundary. -/
def normalBoundaryC2RawSpatialFirstCLM
    (index : NormalBoundaryTangentIndex period hPeriod) :
    NormalBoundaryC2JetCore period hPeriod →L[Real]
      (OrientationBoundary period hPeriod →ᵇ Real) :=
  (compactContinuousToBoundedCLM
      (OrientationBoundary period hPeriod)).comp
    (((ContinuousLinearMap.proj index).compLeftContinuous Real
        (OrientationBoundary period hPeriod)).comp
      (normalBoundaryC2JetCoreFirstToContinuous period hPeriod))

@[simp]
theorem normalBoundaryC2RawSpatialFirstCLM_apply
    (index : NormalBoundaryTangentIndex period hPeriod)
    (normal : NormalBoundaryC2JetCore period hPeriod)
    (boundary : OrientationBoundary period hPeriod) :
    normalBoundaryC2RawSpatialFirstCLM period hPeriod index normal boundary =
      normalBoundaryC2JetCoreFirstAt period hPeriod boundary normal index :=
  rfl

/-- Ordered second stored spatial derivative as a bounded field. -/
def normalBoundaryC2RawSpatialSecondCLM
    (outer inner : NormalBoundaryTangentIndex period hPeriod) :
    NormalBoundaryC2JetCore period hPeriod →L[Real]
      (OrientationBoundary period hPeriod →ᵇ Real) :=
  (compactContinuousToBoundedCLM
      (OrientationBoundary period hPeriod)).comp
    (((ContinuousLinearMap.proj inner).comp
        (ContinuousLinearMap.proj outer) |>.compLeftContinuous Real
          (OrientationBoundary period hPeriod)).comp
      (normalBoundaryC2JetCoreSecondToContinuous period hPeriod))

@[simp]
theorem normalBoundaryC2RawSpatialSecondCLM_apply
    (outer inner : NormalBoundaryTangentIndex period hPeriod)
    (normal : NormalBoundaryC2JetCore period hPeriod)
    (boundary : OrientationBoundary period hPeriod) :
    normalBoundaryC2RawSpatialSecondCLM period hPeriod outer inner normal
        boundary =
      normalBoundaryC2JetCoreSecondAt period hPeriod boundary normal outer
        inner :=
  rfl

/-- First spatial derivative of the raw moving graph `parameter • normal`. -/
def normalBoundaryC2ScaledRawSpatialFirst
    (index : NormalBoundaryTangentIndex period hPeriod)
    (current : NormalBoundaryC2JetCore period hPeriod × Real) :
    OrientationBoundary period hPeriod →ᵇ Real :=
  current.2 •
    normalBoundaryC2RawSpatialFirstCLM period hPeriod index current.1

theorem normalBoundaryC2ScaledRawSpatialFirst_contDiff_two
    (index : NormalBoundaryTangentIndex period hPeriod) :
    ContDiff Real 2
      (normalBoundaryC2ScaledRawSpatialFirst period hPeriod index) := by
  exact contDiff_snd.smul
    ((normalBoundaryC2RawSpatialFirstCLM period hPeriod index).contDiff.comp
      contDiff_fst)

@[simp]
theorem normalBoundaryC2ScaledRawSpatialFirst_apply
    (index : NormalBoundaryTangentIndex period hPeriod)
    (normal : NormalBoundaryC2JetCore period hPeriod)
    (parameter : Real) (boundary : OrientationBoundary period hPeriod) :
    normalBoundaryC2ScaledRawSpatialFirst period hPeriod index
        (normal, parameter) boundary =
      parameter * normalBoundaryC2JetCoreFirstAt period hPeriod boundary
        normal index :=
  rfl

/-- Ordered second spatial derivative of the same raw moving graph. -/
def normalBoundaryC2ScaledRawSpatialSecond
    (outer inner : NormalBoundaryTangentIndex period hPeriod)
    (current : NormalBoundaryC2JetCore period hPeriod × Real) :
    OrientationBoundary period hPeriod →ᵇ Real :=
  current.2 •
    normalBoundaryC2RawSpatialSecondCLM period hPeriod outer inner current.1

theorem normalBoundaryC2ScaledRawSpatialSecond_contDiff_two
    (outer inner : NormalBoundaryTangentIndex period hPeriod) :
    ContDiff Real 2
      (normalBoundaryC2ScaledRawSpatialSecond
        period hPeriod outer inner) := by
  exact contDiff_snd.smul
    ((normalBoundaryC2RawSpatialSecondCLM
        period hPeriod outer inner).contDiff.comp contDiff_fst)

@[simp]
theorem normalBoundaryC2ScaledRawSpatialSecond_apply
    (outer inner : NormalBoundaryTangentIndex period hPeriod)
    (normal : NormalBoundaryC2JetCore period hPeriod)
    (parameter : Real) (boundary : OrientationBoundary period hPeriod) :
    normalBoundaryC2ScaledRawSpatialSecond period hPeriod outer inner
        (normal, parameter) boundary =
      parameter * normalBoundaryC2JetCoreSecondAt period hPeriod boundary
        normal outer inner :=
  rfl

/-- Public completed raw-graph two-jet gate.  It exposes only the derivatives
already stored in the normal core. -/
theorem normal_boundary_c2_raw_spatial_two_jet_gate :
    (∀ index : NormalBoundaryTangentIndex period hPeriod,
      ContDiff Real 2
        (normalBoundaryC2ScaledRawSpatialFirst period hPeriod index)) ∧
      (∀ outer inner : NormalBoundaryTangentIndex period hPeriod,
        ContDiff Real 2
          (normalBoundaryC2ScaledRawSpatialSecond
            period hPeriod outer inner)) :=
  ⟨normalBoundaryC2ScaledRawSpatialFirst_contDiff_two period hPeriod,
    normalBoundaryC2ScaledRawSpatialSecond_contDiff_two period hPeriod⟩

/-! ### Generic smooth coefficients on the fixed boundary collar -/

/-- Vertical unit tangent on the descended boundary–latitude product. -/
def normalBoundaryLatitudeQuotientVerticalTangentLift
    (current : OrientationBoundary period hPeriod × Real) :
    TangentBundle
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (OrientationBoundary period hPeriod × Real) :=
  (equivTangentBundleProd throatCoverModelWithCorners
      (OrientationBoundary period hPeriod)
      (modelWithCornersSelf Real Real) Real).symm
    (⟨current.1, 0⟩, canonicalLatitudeRealUnitTangentLift current.2)

theorem normalBoundaryLatitudeQuotientVerticalTangentLift_contMDiff :
    ContMDiff
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (throatCoverModelWithCorners.prod
        (modelWithCornersSelf Real Real)).tangent ∞
      (normalBoundaryLatitudeQuotientVerticalTangentLift
        period hPeriod) := by
  apply (contMDiff_equivTangentBundleProd_symm
    (I := throatCoverModelWithCorners)
    (I' := modelWithCornersSelf Real Real)
    (M := OrientationBoundary period hPeriod)
    (M' := Real)).comp
  exact ((Bundle.contMDiff_zeroSection Real
      (TangentSpace throatCoverModelWithCorners :
        OrientationBoundary period hPeriod → Type _)).of_le le_top
        |>.comp contMDiff_fst).prodMk
    (canonicalLatitudeRealUnitTangentLift_contMDiff.comp contMDiff_snd)

/-- Derivative in the real latitude variable of a smooth scalar on the fixed
boundary collar. -/
def normalBoundaryLatitudeFieldDerivative
    (field : OrientationBoundary period hPeriod × Real → Real)
    (current : OrientationBoundary period hPeriod × Real) : Real :=
  (tangentMap
    (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
    (modelWithCornersSelf Real Real) field
    (normalBoundaryLatitudeQuotientVerticalTangentLift
      period hPeriod current)).2

theorem normalBoundaryLatitudeFieldDerivative_contMDiff
    (field : OrientationBoundary period hPeriod × Real → Real)
    (hField : ContMDiff
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real Real) ∞ field) :
    ContMDiff
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real Real) ∞
      (normalBoundaryLatitudeFieldDerivative period hPeriod field) := by
  exact (contMDiff_snd_tangentBundle_modelSpace Real
    (modelWithCornersSelf Real Real)).comp
      ((hField.contMDiff_tangentMap (by simp)).comp
        (normalBoundaryLatitudeQuotientVerticalTangentLift_contMDiff
          period hPeriod))

/-- Derivative of a smooth collar scalar along one of the already installed
horizontal boundary generators. -/
def normalBoundaryHorizontalFieldDerivative
    (index : NormalBoundaryTangentIndex period hPeriod)
    (field : OrientationBoundary period hPeriod × Real → Real)
    (current : OrientationBoundary period hPeriod × Real) : Real :=
  (tangentMap
    (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
    (modelWithCornersSelf Real Real) field
    (normalBoundaryLatitudeHorizontalTangentLift
      period hPeriod index current)).2

theorem normalBoundaryHorizontalFieldDerivative_contMDiff
    (index : NormalBoundaryTangentIndex period hPeriod)
    (field : OrientationBoundary period hPeriod × Real → Real)
    (hField : ContMDiff
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real Real) ∞ field) :
    ContMDiff
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real Real) ∞
      (normalBoundaryHorizontalFieldDerivative
        period hPeriod index field) := by
  exact (contMDiff_snd_tangentBundle_modelSpace Real
    (modelWithCornersSelf Real Real)).comp
      ((hField.contMDiff_tangentMap (by simp)).comp
        (normalBoundaryLatitudeHorizontalTangentLift_contMDiff
          period hPeriod index))

theorem normalBoundaryLatitudeField_deriv
    (field : OrientationBoundary period hPeriod × Real → Real)
    (hField : ContMDiff
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real Real) ∞ field)
    (boundary : OrientationBoundary period hPeriod) (latitude : Real) :
    deriv (fun varied => field (boundary, varied)) latitude =
      normalBoundaryLatitudeFieldDerivative period hPeriod field
        (boundary, latitude) := by
  let slice : Real → OrientationBoundary period hPeriod × Real :=
    fun varied => (boundary, varied)
  have hFieldAt : MDifferentiableAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real Real) field (boundary, latitude) :=
    hField.mdifferentiableAt (by simp)
  have hSliceAt : MDifferentiableAt (modelWithCornersSelf Real Real)
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      slice latitude :=
    mdifferentiableAt_const.prodMk mdifferentiableAt_id
  have hComp := tangentMap_comp_at
    (I := modelWithCornersSelf Real Real)
    (I' := throatCoverModelWithCorners.prod
      (modelWithCornersSelf Real Real))
    (I'' := modelWithCornersSelf Real Real)
    (f := slice) (g := field)
    (⟨latitude, 1⟩ :
      TangentBundle (modelWithCornersSelf Real Real) Real)
    hFieldAt hSliceAt
  rw [tangentMap_prod_right] at hComp
  have hSecond := congrArg (fun tangent => tangent.2) hComp
  change mfderiv (modelWithCornersSelf Real Real)
      (modelWithCornersSelf Real Real)
      (fun varied => field (boundary, varied)) latitude 1 =
    normalBoundaryLatitudeFieldDerivative period hPeriod field
      (boundary, latitude) at hSecond
  rw [mfderiv_eq_fderiv] at hSecond
  exact hSecond

theorem normalBoundaryLatitudeField_hasDerivAt
    (field : OrientationBoundary period hPeriod × Real → Real)
    (hField : ContMDiff
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real Real) ∞ field)
    (boundary : OrientationBoundary period hPeriod) (latitude : Real) :
    RealHasDerivAt (fun varied => field (boundary, varied))
      (normalBoundaryLatitudeFieldDerivative period hPeriod field
        (boundary, latitude)) latitude := by
  have hSmooth : ContDiff Real ∞ (fun varied => field (boundary, varied)) :=
    (hField.comp (contMDiff_const.prodMk contMDiff_id)).contDiff
  have hDerivative :=
    (hSmooth.differentiable (by simp) latitude).hasDerivAt
  rw [normalBoundaryLatitudeField_deriv
    period hPeriod field hField boundary latitude] at hDerivative
  exact hDerivative

def normalBoundaryLatitudeFieldSecondDerivative
    (field : OrientationBoundary period hPeriod × Real → Real) :=
  normalBoundaryLatitudeFieldDerivative period hPeriod
    (normalBoundaryLatitudeFieldDerivative period hPeriod field)

def normalBoundaryLatitudeFieldThirdDerivative
    (field : OrientationBoundary period hPeriod × Real → Real) :=
  normalBoundaryLatitudeFieldDerivative period hPeriod
    (normalBoundaryLatitudeFieldSecondDerivative period hPeriod field)

theorem normalBoundaryLatitudeFieldSecondDerivative_contMDiff
    (field : OrientationBoundary period hPeriod × Real → Real)
    (hField : ContMDiff
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real Real) ∞ field) :
    ContMDiff
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real Real) ∞
      (normalBoundaryLatitudeFieldSecondDerivative
        period hPeriod field) :=
  normalBoundaryLatitudeFieldDerivative_contMDiff period hPeriod _
    (normalBoundaryLatitudeFieldDerivative_contMDiff
      period hPeriod field hField)

theorem normalBoundaryLatitudeFieldThirdDerivative_contMDiff
    (field : OrientationBoundary period hPeriod × Real → Real)
    (hField : ContMDiff
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real Real) ∞ field) :
    ContMDiff
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real Real) ∞
      (normalBoundaryLatitudeFieldThirdDerivative
        period hPeriod field) :=
  normalBoundaryLatitudeFieldDerivative_contMDiff period hPeriod _
    (normalBoundaryLatitudeFieldSecondDerivative_contMDiff
      period hPeriod field hField)

theorem normalBoundaryLatitudeFieldDerivative_hasDerivAt
    (field : OrientationBoundary period hPeriod × Real → Real)
    (hField : ContMDiff
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real Real) ∞ field)
    (boundary : OrientationBoundary period hPeriod) (latitude : Real) :
    RealHasDerivAt (fun varied =>
      normalBoundaryLatitudeFieldDerivative period hPeriod field
        (boundary, varied))
      (normalBoundaryLatitudeFieldSecondDerivative period hPeriod field
        (boundary, latitude)) latitude :=
  normalBoundaryLatitudeField_hasDerivAt period hPeriod _
    (normalBoundaryLatitudeFieldDerivative_contMDiff
      period hPeriod field hField) boundary latitude

theorem normalBoundaryLatitudeFieldSecondDerivative_hasDerivAt
    (field : OrientationBoundary period hPeriod × Real → Real)
    (hField : ContMDiff
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real Real) ∞ field)
    (boundary : OrientationBoundary period hPeriod) (latitude : Real) :
    RealHasDerivAt (fun varied =>
      normalBoundaryLatitudeFieldSecondDerivative period hPeriod field
        (boundary, varied))
      (normalBoundaryLatitudeFieldThirdDerivative period hPeriod field
        (boundary, latitude)) latitude :=
  normalBoundaryLatitudeField_hasDerivAt period hPeriod _
    (normalBoundaryLatitudeFieldSecondDerivative_contMDiff
      period hPeriod field hField) boundary latitude

/-- Restriction of a smooth collar coefficient to the canonical compact
latitude interval. -/
def normalBoundaryLatitudeSmoothFiberCompact
    (field : OrientationBoundary period hPeriod × Real → Real)
    (hField : Continuous field) :
    C(OrientationBoundary period hPeriod × ArctanCompactFiber, Real) where
  toFun := fun current => field (current.1, current.2.1)
  continuous_toFun := hField.comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))

/-- Bounded pullback of the preceding coefficient by the installed `arctan`
raw coordinate. -/
def normalBoundarySmoothFiberRaw
    (field : OrientationBoundary period hPeriod × Real → Real)
    (hField : Continuous field) :
    BoundedFiberField (OrientationBoundary period hPeriod) :=
  boundedArctanCompactPullbackCLM (OrientationBoundary period hPeriod)
    (normalBoundaryLatitudeSmoothFiberCompact
      period hPeriod field hField)

@[simp]
theorem normalBoundarySmoothFiberRaw_apply
    (field : OrientationBoundary period hPeriod × Real → Real)
    (hField : Continuous field)
    (boundary : OrientationBoundary period hPeriod) (fiber : Real) :
    normalBoundarySmoothFiberRaw period hPeriod field hField
        (boundary, fiber) =
      field (boundary, Real.arctan fiber) :=
  rfl

def normalBoundarySmoothFiberValueRaw
    (field : OrientationBoundary period hPeriod × Real → Real)
    (hField : ContMDiff
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real Real) ∞ field) :=
  normalBoundarySmoothFiberRaw period hPeriod field hField.continuous

def normalBoundarySmoothFiberFirstRaw
    (field : OrientationBoundary period hPeriod × Real → Real)
    (hField : ContMDiff
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real Real) ∞ field) :=
  normalBoundarySmoothFiberRaw period hPeriod
    (normalBoundaryLatitudeFieldDerivative period hPeriod field)
    (normalBoundaryLatitudeFieldDerivative_contMDiff
      period hPeriod field hField).continuous

def normalBoundarySmoothFiberSecondRaw
    (field : OrientationBoundary period hPeriod × Real → Real)
    (hField : ContMDiff
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real Real) ∞ field) :=
  normalBoundarySmoothFiberRaw period hPeriod
    (normalBoundaryLatitudeFieldSecondDerivative period hPeriod field)
    (normalBoundaryLatitudeFieldSecondDerivative_contMDiff
      period hPeriod field hField).continuous

def normalBoundarySmoothFiberThirdRaw
    (field : OrientationBoundary period hPeriod × Real → Real)
    (hField : ContMDiff
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real Real) ∞ field) :=
  normalBoundarySmoothFiberRaw period hPeriod
    (normalBoundaryLatitudeFieldThirdDerivative period hPeriod field)
    (normalBoundaryLatitudeFieldThirdDerivative_contMDiff
      period hPeriod field hField).continuous

@[simp] theorem normalBoundarySmoothFiberValueRaw_apply
    (field : OrientationBoundary period hPeriod × Real → Real)
    (hField : ContMDiff
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real Real) ∞ field)
    (boundary : OrientationBoundary period hPeriod) (fiber : Real) :
    normalBoundarySmoothFiberValueRaw period hPeriod field hField
        (boundary, fiber) = field (boundary, Real.arctan fiber) :=
  rfl

@[simp] theorem normalBoundarySmoothFiberFirstRaw_apply
    (field : OrientationBoundary period hPeriod × Real → Real)
    (hField : ContMDiff
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real Real) ∞ field)
    (boundary : OrientationBoundary period hPeriod) (fiber : Real) :
    normalBoundarySmoothFiberFirstRaw period hPeriod field hField
        (boundary, fiber) =
      normalBoundaryLatitudeFieldDerivative period hPeriod field
        (boundary, Real.arctan fiber) :=
  rfl

@[simp] theorem normalBoundarySmoothFiberSecondRaw_apply
    (field : OrientationBoundary period hPeriod × Real → Real)
    (hField : ContMDiff
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real Real) ∞ field)
    (boundary : OrientationBoundary period hPeriod) (fiber : Real) :
    normalBoundarySmoothFiberSecondRaw period hPeriod field hField
        (boundary, fiber) =
      normalBoundaryLatitudeFieldSecondDerivative period hPeriod field
        (boundary, Real.arctan fiber) :=
  rfl

@[simp] theorem normalBoundarySmoothFiberThirdRaw_apply
    (field : OrientationBoundary period hPeriod × Real → Real)
    (hField : ContMDiff
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real Real) ∞ field)
    (boundary : OrientationBoundary period hPeriod) (fiber : Real) :
    normalBoundarySmoothFiberThirdRaw period hPeriod field hField
        (boundary, fiber) =
      normalBoundaryLatitudeFieldThirdDerivative period hPeriod field
        (boundary, Real.arctan fiber) :=
  rfl

/-- Compatible bounded raw jet of any jointly smooth fixed collar
coefficient. -/
def normalBoundarySmoothFiberRawJetAmbient
    (field : OrientationBoundary period hPeriod × Real → Real)
    (hField : ContMDiff
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real Real) ∞ field) :
    BoundedFiberJet3Ambient (OrientationBoundary period hPeriod) := ![
  normalBoundarySmoothFiberValueRaw period hPeriod field hField,
  (boundedFiberArctanJet3
      (OrientationBoundary period hPeriod)).1 1 *
    normalBoundarySmoothFiberFirstRaw period hPeriod field hField,
  ((boundedFiberArctanJet3
      (OrientationBoundary period hPeriod)).1 1) ^ 2 *
      normalBoundarySmoothFiberSecondRaw period hPeriod field hField +
    (boundedFiberArctanJet3
      (OrientationBoundary period hPeriod)).1 2 *
      normalBoundarySmoothFiberFirstRaw period hPeriod field hField,
  ((boundedFiberArctanJet3
      (OrientationBoundary period hPeriod)).1 1) ^ 3 *
      normalBoundarySmoothFiberThirdRaw period hPeriod field hField +
    (3 : Real) •
      ((boundedFiberArctanJet3
          (OrientationBoundary period hPeriod)).1 1 *
        (boundedFiberArctanJet3
          (OrientationBoundary period hPeriod)).1 2) *
      normalBoundarySmoothFiberSecondRaw period hPeriod field hField +
    (boundedFiberArctanJet3
      (OrientationBoundary period hPeriod)).1 3 *
      normalBoundarySmoothFiberFirstRaw period hPeriod field hField]

private theorem normalBoundarySmoothFiberRawJetAmbient_mem
    (field : OrientationBoundary period hPeriod × Real → Real)
    (hField : ContMDiff
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real Real) ∞ field) :
    (boundedFiberJet3Submodule
      (OrientationBoundary period hPeriod)).carrier
        (normalBoundarySmoothFiberRawJetAmbient
          period hPeriod field hField) := by
  refine And.intro ?_ (And.intro ?_ ?_)
  · intro boundary fiber
    change RealHasDerivAt
      (fun varied => normalBoundarySmoothFiberValueRaw
        period hPeriod field hField (boundary, varied))
      ((boundedFiberArctanJet3
          (OrientationBoundary period hPeriod)).1 1 (boundary, fiber) *
        normalBoundarySmoothFiberFirstRaw period hPeriod field hField
          (boundary, fiber)) fiber
    have hComposed :=
      (normalBoundaryLatitudeField_hasDerivAt period hPeriod field hField
        boundary (Real.arctan fiber)).comp fiber
          ((boundedFiberArctanJet3
            (OrientationBoundary period hPeriod)).2.1 boundary fiber)
    apply (hComposed.congr_of_eventuallyEq ?_).congr_deriv
    · rw [normalBoundarySmoothFiberFirstRaw_apply]
      ring
    · filter_upwards [] with varied
      rw [normalBoundarySmoothFiberValueRaw_apply]
      rfl
  · intro boundary fiber
    change RealHasDerivAt
      (fun varied =>
        (boundedFiberArctanJet3
            (OrientationBoundary period hPeriod)).1 1 (boundary, varied) *
          normalBoundarySmoothFiberFirstRaw period hPeriod field hField
            (boundary, varied))
      (((boundedFiberArctanJet3
            (OrientationBoundary period hPeriod)).1 1 (boundary, fiber)) ^ 2 *
          normalBoundarySmoothFiberSecondRaw period hPeriod field hField
            (boundary, fiber) +
        (boundedFiberArctanJet3
            (OrientationBoundary period hPeriod)).1 2 (boundary, fiber) *
          normalBoundarySmoothFiberFirstRaw period hPeriod field hField
            (boundary, fiber)) fiber
    have hComposed :=
      (normalBoundaryLatitudeFieldDerivative_hasDerivAt period hPeriod
        field hField boundary (Real.arctan fiber)).comp fiber
          ((boundedFiberArctanJet3
            (OrientationBoundary period hPeriod)).2.1 boundary fiber)
    have hProduct :=
      ((boundedFiberArctanJet3
        (OrientationBoundary period hPeriod)).2.2.1 boundary fiber).mul
          hComposed
    convert hProduct using 1
    · funext varied
      rw [normalBoundarySmoothFiberFirstRaw_apply]
      rfl
    · rw [normalBoundarySmoothFiberFirstRaw_apply,
        normalBoundarySmoothFiberSecondRaw_apply]
      simp only [Function.comp_apply]
      ring
  · intro boundary fiber
    change RealHasDerivAt
      (fun varied =>
        ((boundedFiberArctanJet3
            (OrientationBoundary period hPeriod)).1 1 (boundary, varied)) ^ 2 *
            normalBoundarySmoothFiberSecondRaw period hPeriod field hField
              (boundary, varied) +
          (boundedFiberArctanJet3
              (OrientationBoundary period hPeriod)).1 2 (boundary, varied) *
            normalBoundarySmoothFiberFirstRaw period hPeriod field hField
              (boundary, varied))
      (((boundedFiberArctanJet3
            (OrientationBoundary period hPeriod)).1 1 (boundary, fiber)) ^ 3 *
          normalBoundarySmoothFiberThirdRaw period hPeriod field hField
            (boundary, fiber) +
        (3 : Real) *
            ((boundedFiberArctanJet3
                (OrientationBoundary period hPeriod)).1 1 (boundary, fiber) *
              (boundedFiberArctanJet3
                (OrientationBoundary period hPeriod)).1 2 (boundary, fiber)) *
          normalBoundarySmoothFiberSecondRaw period hPeriod field hField
            (boundary, fiber) +
        (boundedFiberArctanJet3
            (OrientationBoundary period hPeriod)).1 3 (boundary, fiber) *
          normalBoundarySmoothFiberFirstRaw period hPeriod field hField
            (boundary, fiber)) fiber
    have hSecondComposed :=
      (normalBoundaryLatitudeFieldSecondDerivative_hasDerivAt period hPeriod
        field hField boundary (Real.arctan fiber)).comp fiber
          ((boundedFiberArctanJet3
            (OrientationBoundary period hPeriod)).2.1 boundary fiber)
    have hFirstComposed :=
      (normalBoundaryLatitudeFieldDerivative_hasDerivAt period hPeriod
        field hField boundary (Real.arctan fiber)).comp fiber
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
    convert hFirstTerm.add hSecondTerm using 1
    · funext varied
      rw [normalBoundarySmoothFiberFirstRaw_apply,
        normalBoundarySmoothFiberSecondRaw_apply]
      rfl
    · rw [normalBoundarySmoothFiberFirstRaw_apply,
        normalBoundarySmoothFiberSecondRaw_apply,
        normalBoundarySmoothFiberThirdRaw_apply]
      simp only [Function.comp_apply, Pi.pow_apply]
      ring

def normalBoundarySmoothFiberRawJet3
    (field : OrientationBoundary period hPeriod × Real → Real)
    (hField : ContMDiff
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real Real) ∞ field) :
    BoundedFiberJet3 (OrientationBoundary period hPeriod) :=
  ⟨normalBoundarySmoothFiberRawJetAmbient period hPeriod field hField,
    normalBoundarySmoothFiberRawJetAmbient_mem
      period hPeriod field hField⟩

/-- `C²` substitution of any fixed jointly smooth collar coefficient on the
completed normal graph. -/
def normalBoundarySmoothFiberEvaluation
    (field : OrientationBoundary period hPeriod × Real → Real)
    (hField : ContMDiff
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real Real) ∞ field)
    (current : NormalBoundaryC2JetCore period hPeriod × Real) :
    BoundedContinuousFunction (OrientationBoundary period hPeriod) Real :=
  boundedFiberJet3Evaluation (OrientationBoundary period hPeriod)
    (normalBoundarySmoothFiberRawJet3 period hPeriod field hField,
      normalBoundaryC2ScaledRawGraph period hPeriod current)

theorem normalBoundarySmoothFiberEvaluation_contDiff_two
    (field : OrientationBoundary period hPeriod × Real → Real)
    (hField : ContMDiff
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real Real) ∞ field) :
    ContDiff Real 2
      (normalBoundarySmoothFiberEvaluation
        period hPeriod field hField) :=
  (boundedFiberJet3Evaluation_contDiff_two
    (OrientationBoundary period hPeriod)).comp
      (contDiff_const.prodMk
        (normalBoundaryC2ScaledRawGraph_contDiff_two period hPeriod))

@[simp]
theorem normalBoundarySmoothFiberEvaluation_apply
    (field : OrientationBoundary period hPeriod × Real → Real)
    (hField : ContMDiff
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real Real) ∞ field)
    (normal : NormalBoundaryC2JetCore period hPeriod)
    (parameter : Real) (boundary : OrientationBoundary period hPeriod) :
    normalBoundarySmoothFiberEvaluation period hPeriod field hField
        (normal, parameter) boundary =
      field (boundary, Real.arctan
        (parameter * normalBoundaryC2JetCoreValueAt
          period hPeriod boundary normal)) := by
  change normalBoundarySmoothFiberValueRaw period hPeriod field hField
      (boundary, normalBoundaryC2ScaledRawGraph period hPeriod
        (normal, parameter) boundary) = _
  rw [normalBoundarySmoothFiberValueRaw_apply,
    normalBoundaryC2ScaledRawGraph_apply]

/-! ### Completed regular-frame coefficients of the graph tangent -/

def candidateANormalBoundaryVerticalRegularFrameCoefficientFiberEvaluation
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (row : Fin 4)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) :
    BoundedContinuousFunction (OrientationBoundary period hPeriod) Real :=
  normalBoundarySmoothFiberEvaluation period hPeriod
    (normalBoundaryLatitudeVerticalRegularFrameCoefficient
      period hPeriod metric row)
    (normalBoundaryLatitudeVerticalRegularFrameCoefficient_contMDiff
      period hPeriod metric row)
    (current.1.2, current.2)

theorem
    candidateANormalBoundaryVerticalRegularFrameCoefficientFiberEvaluation_contDiff_two
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (row : Fin 4) :
    ContDiff Real 2
      (candidateANormalBoundaryVerticalRegularFrameCoefficientFiberEvaluation
        period hPeriod metric row) := by
  have hInput : ContDiff Real 2 (fun current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real =>
      (current.1.2, current.2)) :=
    (contDiff_snd.comp contDiff_fst).prodMk contDiff_snd
  exact (normalBoundarySmoothFiberEvaluation_contDiff_two period hPeriod
    (normalBoundaryLatitudeVerticalRegularFrameCoefficient
      period hPeriod metric row)
    (normalBoundaryLatitudeVerticalRegularFrameCoefficient_contMDiff
      period hPeriod metric row)).comp hInput

@[simp]
theorem
    candidateANormalBoundaryVerticalRegularFrameCoefficientFiberEvaluation_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (row : Fin 4)
    (variation : CandidateANormalBoundaryFunctionalCore period hPeriod metric)
    (parameter : Real) (boundary : OrientationBoundary period hPeriod) :
    candidateANormalBoundaryVerticalRegularFrameCoefficientFiberEvaluation
        period hPeriod metric row (variation, parameter) boundary =
      normalBoundaryLatitudeVerticalRegularFrameCoefficient period hPeriod
        metric row
        (boundary, Real.arctan
          (parameter * normalBoundaryC2JetCoreValueAt
            period hPeriod boundary variation.2)) :=
  normalBoundarySmoothFiberEvaluation_apply period hPeriod _ _ variation.2
    parameter boundary

def candidateANormalBoundaryHorizontalRegularFrameCoefficientFiberEvaluation
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (index : NormalBoundaryTangentIndex period hPeriod)
    (row : Fin 4)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) :
    BoundedContinuousFunction (OrientationBoundary period hPeriod) Real :=
  normalBoundarySmoothFiberEvaluation period hPeriod
    (normalBoundaryLatitudeHorizontalRegularFrameCoefficient
      period hPeriod metric index row)
    (normalBoundaryLatitudeHorizontalRegularFrameCoefficient_contMDiff
      period hPeriod metric index row)
    (current.1.2, current.2)

theorem
    candidateANormalBoundaryHorizontalRegularFrameCoefficientFiberEvaluation_contDiff_two
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (index : NormalBoundaryTangentIndex period hPeriod)
    (row : Fin 4) :
    ContDiff Real 2
      (candidateANormalBoundaryHorizontalRegularFrameCoefficientFiberEvaluation
        period hPeriod metric index row) := by
  have hInput : ContDiff Real 2 (fun current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real =>
      (current.1.2, current.2)) :=
    (contDiff_snd.comp contDiff_fst).prodMk contDiff_snd
  exact (normalBoundarySmoothFiberEvaluation_contDiff_two period hPeriod
    (normalBoundaryLatitudeHorizontalRegularFrameCoefficient
      period hPeriod metric index row)
    (normalBoundaryLatitudeHorizontalRegularFrameCoefficient_contMDiff
      period hPeriod metric index row)).comp hInput

@[simp]
theorem
    candidateANormalBoundaryHorizontalRegularFrameCoefficientFiberEvaluation_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (index : NormalBoundaryTangentIndex period hPeriod)
    (row : Fin 4)
    (variation : CandidateANormalBoundaryFunctionalCore period hPeriod metric)
    (parameter : Real) (boundary : OrientationBoundary period hPeriod) :
    candidateANormalBoundaryHorizontalRegularFrameCoefficientFiberEvaluation
        period hPeriod metric index row (variation, parameter) boundary =
      normalBoundaryLatitudeHorizontalRegularFrameCoefficient period hPeriod
        metric index row
        (boundary, Real.arctan
          (parameter * normalBoundaryC2JetCoreValueAt
            period hPeriod boundary variation.2)) :=
  normalBoundarySmoothFiberEvaluation_apply period hPeriod _ _ variation.2
    parameter boundary

/-- Evaluation adapter for a fixed smooth collar scalar on the full
metric-normal functional core. -/
def candidateANormalBoundarySmoothCollarFieldFiberEvaluation
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (field : OrientationBoundary period hPeriod × Real → Real)
    (hField : ContMDiff
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real Real) ∞ field)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) :
    BoundedContinuousFunction (OrientationBoundary period hPeriod) Real :=
  normalBoundarySmoothFiberEvaluation period hPeriod field hField
    (current.1.2, current.2)

theorem candidateANormalBoundarySmoothCollarFieldFiberEvaluation_contDiff_two
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (field : OrientationBoundary period hPeriod × Real → Real)
    (hField : ContMDiff
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real Real) ∞ field) :
    ContDiff Real 2
      (candidateANormalBoundarySmoothCollarFieldFiberEvaluation
        period hPeriod metric field hField) := by
  have hInput : ContDiff Real 2 (fun current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real =>
      (current.1.2, current.2)) :=
    (contDiff_snd.comp contDiff_fst).prodMk contDiff_snd
  exact (normalBoundarySmoothFiberEvaluation_contDiff_two
    period hPeriod field hField).comp hInput

@[simp]
theorem candidateANormalBoundarySmoothCollarFieldFiberEvaluation_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (field : OrientationBoundary period hPeriod × Real → Real)
    (hField : ContMDiff
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real Real) ∞ field)
    (variation : CandidateANormalBoundaryFunctionalCore period hPeriod metric)
    (parameter : Real) (boundary : OrientationBoundary period hPeriod) :
    candidateANormalBoundarySmoothCollarFieldFiberEvaluation period hPeriod
        metric field hField (variation, parameter) boundary =
      field (boundary, Real.arctan
        (parameter * normalBoundaryC2JetCoreValueAt
          period hPeriod boundary variation.2)) :=
  normalBoundarySmoothFiberEvaluation_apply period hPeriod field hField
    variation.2 parameter boundary

/-- Horizontal source derivative of a horizontal collar coefficient. -/
def candidateANormalBoundaryHorizontalCoefficientSourceDerivativeFiberEvaluation
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (derivative index : NormalBoundaryTangentIndex period hPeriod)
    (row : Fin 4)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) :
    BoundedContinuousFunction (OrientationBoundary period hPeriod) Real :=
  candidateANormalBoundarySmoothCollarFieldFiberEvaluation period hPeriod metric
    (normalBoundaryHorizontalFieldDerivative period hPeriod derivative
      (normalBoundaryLatitudeHorizontalRegularFrameCoefficient
        period hPeriod metric index row))
    (normalBoundaryHorizontalFieldDerivative_contMDiff period hPeriod derivative
      _ (normalBoundaryLatitudeHorizontalRegularFrameCoefficient_contMDiff
        period hPeriod metric index row)) current

theorem
    candidateANormalBoundaryHorizontalCoefficientSourceDerivativeFiberEvaluation_contDiff_two
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (derivative index : NormalBoundaryTangentIndex period hPeriod)
    (row : Fin 4) :
    ContDiff Real 2
      (candidateANormalBoundaryHorizontalCoefficientSourceDerivativeFiberEvaluation
        period hPeriod metric derivative index row) :=
  candidateANormalBoundarySmoothCollarFieldFiberEvaluation_contDiff_two
    period hPeriod metric _ _

/-- Horizontal source derivative of the vertical collar coefficient. -/
def candidateANormalBoundaryVerticalCoefficientSourceDerivativeFiberEvaluation
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (derivative : NormalBoundaryTangentIndex period hPeriod)
    (row : Fin 4)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) :
    BoundedContinuousFunction (OrientationBoundary period hPeriod) Real :=
  candidateANormalBoundarySmoothCollarFieldFiberEvaluation period hPeriod metric
    (normalBoundaryHorizontalFieldDerivative period hPeriod derivative
      (normalBoundaryLatitudeVerticalRegularFrameCoefficient
        period hPeriod metric row))
    (normalBoundaryHorizontalFieldDerivative_contMDiff period hPeriod derivative
      _ (normalBoundaryLatitudeVerticalRegularFrameCoefficient_contMDiff
        period hPeriod metric row)) current

theorem
    candidateANormalBoundaryVerticalCoefficientSourceDerivativeFiberEvaluation_contDiff_two
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (derivative : NormalBoundaryTangentIndex period hPeriod)
    (row : Fin 4) :
    ContDiff Real 2
      (candidateANormalBoundaryVerticalCoefficientSourceDerivativeFiberEvaluation
        period hPeriod metric derivative row) :=
  candidateANormalBoundarySmoothCollarFieldFiberEvaluation_contDiff_two
    period hPeriod metric _ _

/-- Latitude derivative of a horizontal collar coefficient. -/
def candidateANormalBoundaryHorizontalCoefficientLatitudeDerivativeFiberEvaluation
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (index : NormalBoundaryTangentIndex period hPeriod)
    (row : Fin 4)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) :
    BoundedContinuousFunction (OrientationBoundary period hPeriod) Real :=
  candidateANormalBoundarySmoothCollarFieldFiberEvaluation period hPeriod metric
    (normalBoundaryLatitudeFieldDerivative period hPeriod
      (normalBoundaryLatitudeHorizontalRegularFrameCoefficient
        period hPeriod metric index row))
    (normalBoundaryLatitudeFieldDerivative_contMDiff period hPeriod _
      (normalBoundaryLatitudeHorizontalRegularFrameCoefficient_contMDiff
        period hPeriod metric index row)) current

theorem
    candidateANormalBoundaryHorizontalCoefficientLatitudeDerivativeFiberEvaluation_contDiff_two
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (index : NormalBoundaryTangentIndex period hPeriod)
    (row : Fin 4) :
    ContDiff Real 2
      (candidateANormalBoundaryHorizontalCoefficientLatitudeDerivativeFiberEvaluation
        period hPeriod metric index row) :=
  candidateANormalBoundarySmoothCollarFieldFiberEvaluation_contDiff_two
    period hPeriod metric _ _

/-- Latitude derivative of the vertical collar coefficient. -/
def candidateANormalBoundaryVerticalCoefficientLatitudeDerivativeFiberEvaluation
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (row : Fin 4)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) :
    BoundedContinuousFunction (OrientationBoundary period hPeriod) Real :=
  candidateANormalBoundarySmoothCollarFieldFiberEvaluation period hPeriod metric
    (normalBoundaryLatitudeFieldDerivative period hPeriod
      (normalBoundaryLatitudeVerticalRegularFrameCoefficient
        period hPeriod metric row))
    (normalBoundaryLatitudeFieldDerivative_contMDiff period hPeriod _
      (normalBoundaryLatitudeVerticalRegularFrameCoefficient_contMDiff
        period hPeriod metric row)) current

theorem
    candidateANormalBoundaryVerticalCoefficientLatitudeDerivativeFiberEvaluation_contDiff_two
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (row : Fin 4) :
    ContDiff Real 2
      (candidateANormalBoundaryVerticalCoefficientLatitudeDerivativeFiberEvaluation
        period hPeriod metric row) :=
  candidateANormalBoundarySmoothCollarFieldFiberEvaluation_contDiff_two
    period hPeriod metric _ _

/-- Raw graph value on the full metric-normal functional core. -/
def candidateANormalBoundaryRawGraphFiberEvaluation
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) :
    BoundedContinuousFunction (OrientationBoundary period hPeriod) Real :=
  normalBoundaryC2ScaledRawGraph period hPeriod (current.1.2, current.2)

theorem candidateANormalBoundaryRawGraphFiberEvaluation_contDiff_two
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    ContDiff Real 2
      (candidateANormalBoundaryRawGraphFiberEvaluation
        period hPeriod metric) := by
  exact (normalBoundaryC2ScaledRawGraph_contDiff_two period hPeriod).comp
    ((contDiff_snd.comp contDiff_fst).prodMk contDiff_snd)

/-- Everywhere-invertible denominator `1 + r²` of the raw collar. -/
def candidateANormalBoundaryRawGraphQuadraticDenominator
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) :
    BoundedContinuousFunction (OrientationBoundary period hPeriod) Real :=
  1 + (candidateANormalBoundaryRawGraphFiberEvaluation
    period hPeriod metric current) ^ 2

theorem candidateANormalBoundaryRawGraphQuadraticDenominator_contDiff_two
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    ContDiff Real 2
      (candidateANormalBoundaryRawGraphQuadraticDenominator
        period hPeriod metric) :=
  contDiff_const.add
    ((candidateANormalBoundaryRawGraphFiberEvaluation_contDiff_two
      period hPeriod metric).pow 2)

theorem candidateANormalBoundaryRawGraphQuadraticDenominator_isUnit
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) :
    IsUnit (candidateANormalBoundaryRawGraphQuadraticDenominator
      period hPeriod metric current) := by
  let inverseContinuous : C(OrientationBoundary period hPeriod, Real) :=
    { toFun := fun boundary =>
        1 / (1 +
          (candidateANormalBoundaryRawGraphFiberEvaluation period hPeriod
            metric current boundary) ^ 2)
      continuous_toFun := continuous_const.div
        (continuous_const.add
          ((candidateANormalBoundaryRawGraphFiberEvaluation period hPeriod
            metric current).continuous.pow 2))
        (fun boundary => by positivity) }
  let inverse : BoundedContinuousFunction
      (OrientationBoundary period hPeriod) Real :=
    BoundedContinuousFunction.mkOfCompact inverseContinuous
  apply isUnit_iff_exists_inv.mpr
  refine ⟨inverse, ?_⟩
  ext boundary
  change (1 +
      (candidateANormalBoundaryRawGraphFiberEvaluation period hPeriod metric
        current boundary) ^ 2) *
      (1 / (1 +
        (candidateANormalBoundaryRawGraphFiberEvaluation period hPeriod metric
          current boundary) ^ 2)) = 1
  field_simp

/-- The derivative of `arctan` evaluated on the completed raw graph, proved
smooth through inversion in the existing Banach algebra. -/
def candidateANormalBoundaryRawArctanDerivativeFiberEvaluation
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) :
    BoundedContinuousFunction (OrientationBoundary period hPeriod) Real :=
  Ring.inverse
    (candidateANormalBoundaryRawGraphQuadraticDenominator
      period hPeriod metric current)

theorem
    candidateANormalBoundaryRawArctanDerivativeFiberEvaluation_contDiff_two
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    ContDiff Real 2
      (candidateANormalBoundaryRawArctanDerivativeFiberEvaluation
        period hPeriod metric) := by
  rw [contDiff_iff_contDiffAt]
  intro current
  have hUnit :=
    candidateANormalBoundaryRawGraphQuadraticDenominator_isUnit
      period hPeriod metric current
  have hInverse : ContDiffAt Real 2 Ring.inverse
      (hUnit.unit : BoundedContinuousFunction
        (OrientationBoundary period hPeriod) Real) :=
    contDiffAt_ringInverse Real hUnit.unit
  rw [hUnit.unit_spec] at hInverse
  exact hInverse.comp current
    (candidateANormalBoundaryRawGraphQuadraticDenominator_contDiff_two
      period hPeriod metric).contDiffAt

@[simp]
theorem candidateANormalBoundaryRawArctanDerivativeFiberEvaluation_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real)
    (boundary : OrientationBoundary period hPeriod) :
    candidateANormalBoundaryRawArctanDerivativeFiberEvaluation period hPeriod
        metric current boundary =
      1 / (1 +
        (candidateANormalBoundaryRawGraphFiberEvaluation period hPeriod metric
          current boundary) ^ 2) := by
  have hUnit :=
    candidateANormalBoundaryRawGraphQuadraticDenominator_isUnit
      period hPeriod metric current
  have hMul : Ring.inverse
      (candidateANormalBoundaryRawGraphQuadraticDenominator
        period hPeriod metric current) *
      candidateANormalBoundaryRawGraphQuadraticDenominator
        period hPeriod metric current = 1 :=
    by
      rw [← hUnit.unit_spec, Ring.inverse_unit]
      exact Units.inv_mul hUnit.unit
  have hEval := congrArg
    (fun field : BoundedContinuousFunction
      (OrientationBoundary period hPeriod) Real => field boundary) hMul
  rw [candidateANormalBoundaryRawArctanDerivativeFiberEvaluation]
  apply (eq_div_iff (show 1 +
    (candidateANormalBoundaryRawGraphFiberEvaluation period hPeriod metric
      current boundary) ^ 2 ≠ 0 by positivity)).2
  simpa [candidateANormalBoundaryRawGraphQuadraticDenominator] using hEval

/-- First spatial derivative of the actual compressed latitude graph. -/
def candidateANormalBoundaryLatitudeSpatialFirstFiberEvaluation
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (index : NormalBoundaryTangentIndex period hPeriod)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) :
    BoundedContinuousFunction (OrientationBoundary period hPeriod) Real :=
  normalBoundaryC2ScaledRawSpatialFirst period hPeriod index
      (current.1.2, current.2) *
    candidateANormalBoundaryRawArctanDerivativeFiberEvaluation
      period hPeriod metric current

theorem candidateANormalBoundaryLatitudeSpatialFirstFiberEvaluation_contDiff_two
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (index : NormalBoundaryTangentIndex period hPeriod) :
    ContDiff Real 2
      (candidateANormalBoundaryLatitudeSpatialFirstFiberEvaluation
        period hPeriod metric index) := by
  have hRawFirst : ContDiff Real 2 (fun current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real =>
      normalBoundaryC2ScaledRawSpatialFirst period hPeriod index
        (current.1.2, current.2)) :=
    (normalBoundaryC2ScaledRawSpatialFirst_contDiff_two
      period hPeriod index).comp
        ((contDiff_snd.comp contDiff_fst).prodMk contDiff_snd)
  exact hRawFirst.mul
    (candidateANormalBoundaryRawArctanDerivativeFiberEvaluation_contDiff_two
      period hPeriod metric)

/-- Ordered second spatial derivative of the same compressed latitude graph,
using the stored normal two-jet and the exact second derivative of `arctan`. -/
def candidateANormalBoundaryLatitudeSpatialSecondFiberEvaluation
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (outer inner : NormalBoundaryTangentIndex period hPeriod)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) :
    BoundedContinuousFunction (OrientationBoundary period hPeriod) Real :=
  normalBoundaryC2ScaledRawSpatialSecond period hPeriod outer inner
      (current.1.2, current.2) *
    candidateANormalBoundaryRawArctanDerivativeFiberEvaluation
      period hPeriod metric current -
    (2 : Real) •
      (candidateANormalBoundaryRawGraphFiberEvaluation
          period hPeriod metric current *
        normalBoundaryC2ScaledRawSpatialFirst period hPeriod outer
          (current.1.2, current.2) *
        normalBoundaryC2ScaledRawSpatialFirst period hPeriod inner
          (current.1.2, current.2) *
        (candidateANormalBoundaryRawArctanDerivativeFiberEvaluation
          period hPeriod metric current) ^ 2)

theorem candidateANormalBoundaryLatitudeSpatialSecondFiberEvaluation_contDiff_two
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (outer inner : NormalBoundaryTangentIndex period hPeriod) :
    ContDiff Real 2
      (candidateANormalBoundaryLatitudeSpatialSecondFiberEvaluation
        period hPeriod metric outer inner) := by
  have hInput : ContDiff Real 2 (fun current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real =>
      (current.1.2, current.2)) :=
    (contDiff_snd.comp contDiff_fst).prodMk contDiff_snd
  have hRawFirst (index : NormalBoundaryTangentIndex period hPeriod) :
      ContDiff Real 2 (fun current : Prod
        (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real =>
        normalBoundaryC2ScaledRawSpatialFirst period hPeriod index
          (current.1.2, current.2)) :=
    (normalBoundaryC2ScaledRawSpatialFirst_contDiff_two
      period hPeriod index).comp hInput
  have hRawSecond : ContDiff Real 2 (fun current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real =>
      normalBoundaryC2ScaledRawSpatialSecond period hPeriod outer inner
        (current.1.2, current.2)) :=
    (normalBoundaryC2ScaledRawSpatialSecond_contDiff_two
      period hPeriod outer inner).comp hInput
  have hRaw :=
    candidateANormalBoundaryRawGraphFiberEvaluation_contDiff_two
      period hPeriod metric
  have hDerivative :=
    candidateANormalBoundaryRawArctanDerivativeFiberEvaluation_contDiff_two
      period hPeriod metric
  exact (hRawSecond.mul hDerivative).sub
    (ContDiff.const_smul (2 : Real)
      ((((hRaw.mul (hRawFirst outer)).mul (hRawFirst inner)).mul
        (hDerivative.pow 2))))

/-- Spatial derivative of one completed graph-tangent coefficient.  This is
the ordinary chain rule for the existing horizontal/vertical collar lifts. -/
def candidateANormalBoundaryGraphTangentRegularFrameSpatialDerivativeFiberEvaluation
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (outer inner : NormalBoundaryTangentIndex period hPeriod)
    (row : Fin 4)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) :
    BoundedContinuousFunction (OrientationBoundary period hPeriod) Real :=
  candidateANormalBoundaryHorizontalCoefficientSourceDerivativeFiberEvaluation
      period hPeriod metric outer inner row current +
    candidateANormalBoundaryLatitudeSpatialFirstFiberEvaluation
        period hPeriod metric outer current *
      candidateANormalBoundaryHorizontalCoefficientLatitudeDerivativeFiberEvaluation
        period hPeriod metric inner row current +
    candidateANormalBoundaryLatitudeSpatialSecondFiberEvaluation
        period hPeriod metric outer inner current *
      candidateANormalBoundaryVerticalRegularFrameCoefficientFiberEvaluation
        period hPeriod metric row current +
    candidateANormalBoundaryLatitudeSpatialFirstFiberEvaluation
        period hPeriod metric inner current *
      (candidateANormalBoundaryVerticalCoefficientSourceDerivativeFiberEvaluation
          period hPeriod metric outer row current +
        candidateANormalBoundaryLatitudeSpatialFirstFiberEvaluation
            period hPeriod metric outer current *
          candidateANormalBoundaryVerticalCoefficientLatitudeDerivativeFiberEvaluation
            period hPeriod metric row current)

theorem candidateANormalBoundaryGraphTangentRegularFrameSpatialDerivativeFiberEvaluation_contDiff_two
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (outer inner : NormalBoundaryTangentIndex period hPeriod)
    (row : Fin 4) :
    ContDiff Real 2
      (candidateANormalBoundaryGraphTangentRegularFrameSpatialDerivativeFiberEvaluation
        period hPeriod metric outer inner row) := by
  have hHorizontalSource :=
    candidateANormalBoundaryHorizontalCoefficientSourceDerivativeFiberEvaluation_contDiff_two
      period hPeriod metric outer inner row
  have hOuter :=
    candidateANormalBoundaryLatitudeSpatialFirstFiberEvaluation_contDiff_two
      period hPeriod metric outer
  have hInner :=
    candidateANormalBoundaryLatitudeSpatialFirstFiberEvaluation_contDiff_two
      period hPeriod metric inner
  have hHorizontalLatitude :=
    candidateANormalBoundaryHorizontalCoefficientLatitudeDerivativeFiberEvaluation_contDiff_two
      period hPeriod metric inner row
  have hSecond :=
    candidateANormalBoundaryLatitudeSpatialSecondFiberEvaluation_contDiff_two
      period hPeriod metric outer inner
  have hVertical :=
    candidateANormalBoundaryVerticalRegularFrameCoefficientFiberEvaluation_contDiff_two
      period hPeriod metric row
  have hVerticalSource :=
    candidateANormalBoundaryVerticalCoefficientSourceDerivativeFiberEvaluation_contDiff_two
      period hPeriod metric outer row
  have hVerticalLatitude :=
    candidateANormalBoundaryVerticalCoefficientLatitudeDerivativeFiberEvaluation_contDiff_two
      period hPeriod metric row
  exact ((hHorizontalSource.add
      (hOuter.mul hHorizontalLatitude)).add
      (hSecond.mul hVertical)).add
    (hInner.mul (hVerticalSource.add
      (hOuter.mul hVerticalLatitude)))

/-- Regular-frame coefficient of the raw vertical contribution after the
single `arctan` chain-rule factor. -/
def candidateANormalBoundaryRawVerticalRegularFrameCoefficientFiberEvaluation
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (row : Fin 4)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) :
    BoundedContinuousFunction (OrientationBoundary period hPeriod) Real :=
  candidateANormalBoundaryRawArctanDerivativeFiberEvaluation period hPeriod
      metric current *
    candidateANormalBoundaryVerticalRegularFrameCoefficientFiberEvaluation
      period hPeriod metric row current

theorem
    candidateANormalBoundaryRawVerticalRegularFrameCoefficientFiberEvaluation_contDiff_two
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (row : Fin 4) :
    ContDiff Real 2
      (candidateANormalBoundaryRawVerticalRegularFrameCoefficientFiberEvaluation
        period hPeriod metric row) :=
  (candidateANormalBoundaryRawArctanDerivativeFiberEvaluation_contDiff_two
    period hPeriod metric).mul
      (candidateANormalBoundaryVerticalRegularFrameCoefficientFiberEvaluation_contDiff_two
        period hPeriod metric row)

@[simp]
theorem
    candidateANormalBoundaryRawVerticalRegularFrameCoefficientFiberEvaluation_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (row : Fin 4)
    (variation : CandidateANormalBoundaryFunctionalCore period hPeriod metric)
    (parameter : Real) (boundary : OrientationBoundary period hPeriod) :
    candidateANormalBoundaryRawVerticalRegularFrameCoefficientFiberEvaluation
        period hPeriod metric row (variation, parameter) boundary =
      (1 / (1 +
        (parameter * normalBoundaryC2JetCoreValueAt period hPeriod boundary
          variation.2) ^ 2)) *
        normalBoundaryLatitudeVerticalRegularFrameCoefficient period hPeriod
          metric row
          (boundary, Real.arctan
            (parameter * normalBoundaryC2JetCoreValueAt period hPeriod
              boundary variation.2)) := by
  simp [candidateANormalBoundaryRawVerticalRegularFrameCoefficientFiberEvaluation,
    candidateANormalBoundaryRawGraphFiberEvaluation,
    normalBoundaryC2ScaledRawGraph_apply]

/-- Regular-frame coefficient of one tangent generator of the completed
moving graph. -/
def candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (index : NormalBoundaryTangentIndex period hPeriod)
    (row : Fin 4)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) :
    BoundedContinuousFunction (OrientationBoundary period hPeriod) Real :=
  candidateANormalBoundaryHorizontalRegularFrameCoefficientFiberEvaluation
      period hPeriod metric index row current +
    normalBoundaryC2ScaledRawSpatialFirst period hPeriod index
        (current.1.2, current.2) *
      candidateANormalBoundaryRawVerticalRegularFrameCoefficientFiberEvaluation
        period hPeriod metric row current

theorem
    candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation_contDiff_two
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (index : NormalBoundaryTangentIndex period hPeriod)
    (row : Fin 4) :
    ContDiff Real 2
      (candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation
        period hPeriod metric index row) := by
  have hSpatial : ContDiff Real 2 (fun current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real =>
      normalBoundaryC2ScaledRawSpatialFirst period hPeriod index
        (current.1.2, current.2)) :=
    (normalBoundaryC2ScaledRawSpatialFirst_contDiff_two
      period hPeriod index).comp
        ((contDiff_snd.comp contDiff_fst).prodMk contDiff_snd)
  exact
    (candidateANormalBoundaryHorizontalRegularFrameCoefficientFiberEvaluation_contDiff_two
      period hPeriod metric index row).add
      (hSpatial.mul
        (candidateANormalBoundaryRawVerticalRegularFrameCoefficientFiberEvaluation_contDiff_two
          period hPeriod metric row))

@[simp]
theorem
    candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (index : NormalBoundaryTangentIndex period hPeriod)
    (row : Fin 4)
    (variation : CandidateANormalBoundaryFunctionalCore period hPeriod metric)
    (parameter : Real) (boundary : OrientationBoundary period hPeriod) :
    candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation
        period hPeriod metric index row (variation, parameter) boundary =
      normalBoundaryLatitudeHorizontalRegularFrameCoefficient period hPeriod
          metric index row
          (boundary, Real.arctan
            (parameter * normalBoundaryC2JetCoreValueAt period hPeriod
              boundary variation.2)) +
        (parameter * normalBoundaryC2JetCoreFirstAt period hPeriod boundary
          variation.2 index) *
          ((1 / (1 +
            (parameter * normalBoundaryC2JetCoreValueAt period hPeriod
              boundary variation.2) ^ 2)) *
            normalBoundaryLatitudeVerticalRegularFrameCoefficient period
              hPeriod metric row
              (boundary, Real.arctan
                (parameter * normalBoundaryC2JetCoreValueAt period hPeriod
                  boundary variation.2))) := by
  simp [candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation,
    normalBoundaryC2ScaledRawSpatialFirst_apply]

set_option backward.isDefEq.respectTransparency false in
/-- On the dense smooth core, the stored first normal jet and the arctangent
chain factor are exactly the manifold derivative of the graph latitude on
each installed throat generator. -/
theorem normalGraphLatitude_mvfderiv_frame
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : OrientationBoundary period hPeriod)
    (index : NormalBoundaryTangentIndex period hPeriod) :
    mvfderiv throatCoverModelWithCorners
        (fun point : OrientationBoundary period hPeriod =>
          Real.arctan (parameter *
            normalDisplacementOrientationScalar period hPeriod displacement
              point)) boundary
        ((finiteSmoothThroatGeneratingFrame
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)).vectorAt
            boundary index) =
      (1 / (1 + (parameter * normalBoundaryC2JetCoreValueAt period hPeriod
        boundary (smoothNormalDisplacementToBoundaryC2JetCore
          period hPeriod displacement)) ^ 2)) *
        (parameter * normalBoundaryC2JetCoreFirstAt period hPeriod boundary
          (smoothNormalDisplacementToBoundaryC2JetCore
            period hPeriod displacement) index) := by
  let scalar : OrientationBoundary period hPeriod → Real :=
    normalDisplacementOrientationScalar period hPeriod displacement
  let raw : OrientationBoundary period hPeriod → Real :=
    fun point => parameter * scalar point
  let vector :=
    (finiteSmoothThroatGeneratingFrame
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)).vectorAt
        boundary index
  have hScalarDiff : MDifferentiableAt throatCoverModelWithCorners
      (modelWithCornersSelf Real Real) scalar boundary :=
    (normalDisplacementOrientationScalar_contMDiff period hPeriod displacement)
      |>.mdifferentiableAt (by simp)
  have hRawDiff : MDifferentiableAt throatCoverModelWithCorners
      (modelWithCornersSelf Real Real) raw boundary := by
    change MDifferentiableAt throatCoverModelWithCorners
      (modelWithCornersSelf Real Real)
        ((fun _ : OrientationBoundary period hPeriod => parameter) * scalar)
          boundary
    exact mdifferentiableAt_const.mul hScalarDiff
  have hOuter :=
    (Real.hasDerivAt_arctan (raw boundary)).hasFDerivAt.hasMFDerivAt
  have hComp := hOuter.comp boundary hRawDiff.hasMFDerivAt
  have hDerivative := congrArg (fun derivative => derivative vector) hComp.mfderiv
  have hDerivative' := congrArg
    (NormedSpace.fromTangentSpace (Real.arctan (raw boundary))) hDerivative
  have hDerivativeV :
      mvfderiv throatCoverModelWithCorners (Real.arctan ∘ raw)
          boundary vector =
        (1 / (1 + raw boundary ^ 2)) *
          mvfderiv throatCoverModelWithCorners raw boundary vector := by
    refine hDerivative'.trans ?_
    change (NormedSpace.fromTangentSpace (Real.arctan (raw boundary)))
        (ContinuousLinearMap.toSpanSingleton Real
          (1 / (1 + raw boundary ^ 2))
            (mfderiv throatCoverModelWithCorners
              (modelWithCornersSelf Real Real) raw boundary vector)) = _
    rw [ContinuousLinearMap.toSpanSingleton_apply]
    change mvfderiv throatCoverModelWithCorners raw boundary vector *
        (1 / (1 + raw boundary ^ 2)) =
      (1 / (1 + raw boundary ^ 2)) *
        mvfderiv throatCoverModelWithCorners raw boundary vector
    exact mul_comm _ _
  have hRawDerivative :
      mvfderiv throatCoverModelWithCorners raw boundary vector =
        parameter * mvfderiv throatCoverModelWithCorners scalar boundary vector := by
    have hConstDiff : MDifferentiableAt throatCoverModelWithCorners
        (modelWithCornersSelf Real Real)
        (fun _ : OrientationBoundary period hPeriod => parameter) boundary :=
      mdifferentiableAt_const
    have hMul := congrArg (fun derivative => derivative vector)
      (mvfderiv_mul hConstDiff hScalarDiff)
    rw [show raw =
      (fun _ : OrientationBoundary period hPeriod => parameter) * scalar by rfl]
    simpa [mvfderiv_const] using hMul
  have hFirst := congrFun
    (normalBoundaryC2JetCoreFirstAt_smooth period hPeriod displacement boundary)
      index
  rw [throatFrameDerivative_eq_mvfderiv] at hFirst
  have hFirst' : normalBoundaryC2JetCoreFirstAt period hPeriod boundary
      (smoothNormalDisplacementToBoundaryC2JetCore period hPeriod displacement)
        index =
    mvfderiv throatCoverModelWithCorners scalar boundary vector := by
    change _ = mvfderiv throatCoverModelWithCorners scalar boundary vector at hFirst
    exact hFirst
  change mvfderiv throatCoverModelWithCorners (Real.arctan ∘ raw)
      boundary vector = _
  rw [hDerivativeV, hRawDerivative]
  rw [← hFirst']
  rw [normalBoundaryC2JetCoreValueAt_smooth]

set_option backward.isDefEq.respectTransparency false in
/-- Along every installed finite throat generator, the derivative of the
smooth normal graph is the joint collar derivative applied to its horizontal
tangent and to the already stored arctangent-chain slope. -/
theorem normalGraphCollar_mfderiv_frame
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : OrientationBoundary period hPeriod)
    (index : NormalBoundaryTangentIndex period hPeriod) :
    let scalar := normalDisplacementOrientationScalar
      period hPeriod displacement
    let latitude := fun point : OrientationBoundary period hPeriod =>
      Real.arctan (parameter * scalar point)
    let vector :=
      (finiteSmoothThroatGeneratingFrame
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)).vectorAt
          boundary index
    let slope :=
      (1 / (1 + (parameter * normalBoundaryC2JetCoreValueAt period hPeriod
        boundary (smoothNormalDisplacementToBoundaryC2JetCore
          period hPeriod displacement)) ^ 2)) *
        (parameter * normalBoundaryC2JetCoreFirstAt period hPeriod boundary
          (smoothNormalDisplacementToBoundaryC2JetCore
            period hPeriod displacement) index)
    mfderiv throatCoverModelWithCorners coverModelWithCorners
        (fun point : OrientationBoundary period hPeriod =>
          normalBoundaryLatitudeFiberPoint period hPeriod point
            (latitude point)) boundary vector =
      mfderiv
          (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
          coverModelWithCorners
          (fun current : OrientationBoundary period hPeriod × Real =>
            normalBoundaryLatitudeFiberPoint period hPeriod
              current.1 current.2)
          (boundary, latitude boundary) (vector, slope) := by
  dsimp only
  let scalar : OrientationBoundary period hPeriod → Real :=
    normalDisplacementOrientationScalar period hPeriod displacement
  let latitude : OrientationBoundary period hPeriod → Real :=
    fun point => Real.arctan (parameter * scalar point)
  let graphParameter : OrientationBoundary period hPeriod →
      OrientationBoundary period hPeriod × Real :=
    fun point => (point, latitude point)
  let collar : OrientationBoundary period hPeriod × Real →
      MappingTorus (reflectedSphereData period hPeriod) :=
    fun current => normalBoundaryLatitudeFiberPoint period hPeriod
      current.1 current.2
  let vector :=
    (finiteSmoothThroatGeneratingFrame
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)).vectorAt
        boundary index
  let slope :=
    (1 / (1 + (parameter * normalBoundaryC2JetCoreValueAt period hPeriod
      boundary (smoothNormalDisplacementToBoundaryC2JetCore
        period hPeriod displacement)) ^ 2)) *
      (parameter * normalBoundaryC2JetCoreFirstAt period hPeriod boundary
        (smoothNormalDisplacementToBoundaryC2JetCore
          period hPeriod displacement) index)
  have hScalar : ContMDiff throatCoverModelWithCorners
      (modelWithCornersSelf Real Real) ∞ scalar :=
    normalDisplacementOrientationScalar_contMDiff period hPeriod displacement
  have hRaw : ContMDiff throatCoverModelWithCorners
      (modelWithCornersSelf Real Real) ∞
      (fun point => parameter * scalar point) :=
    contMDiff_const.mul hScalar
  have hLatitude : ContMDiff throatCoverModelWithCorners
      (modelWithCornersSelf Real Real) ∞ latitude := by
    exact Real.contDiff_arctan.contMDiff.comp hRaw
  have hParameter : MDifferentiableAt throatCoverModelWithCorners
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      graphParameter boundary :=
    (contMDiff_id.prodMk hLatitude).mdifferentiableAt (by simp)
  have hCollar : MDifferentiableAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      coverModelWithCorners collar (graphParameter boundary) :=
    (normalBoundaryLatitudeFiberPoint_joint_contMDiff period hPeriod)
      |>.mdifferentiableAt (by simp)
  have hLatitudeApply := normalGraphLatitude_mvfderiv_frame
    period hPeriod displacement parameter boundary index
  change mvfderiv throatCoverModelWithCorners latitude boundary vector = slope
    at hLatitudeApply
  have hLatitudeApply' :
      mfderiv throatCoverModelWithCorners (modelWithCornersSelf Real Real)
          latitude boundary vector = slope := by
    change (NormedSpace.fromTangentSpace (latitude boundary))
      (mfderiv throatCoverModelWithCorners (modelWithCornersSelf Real Real)
        latitude boundary vector) = slope at hLatitudeApply
    exact hLatitudeApply
  have hParameterDerivative := congrArg (fun derivative => derivative vector)
    (mfderiv_prodMk
      (f := fun point : OrientationBoundary period hPeriod => point)
      (g := latitude) mdifferentiableAt_id
      (hLatitude.mdifferentiableAt (by simp)))
  have hIdentityApply :
      mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
          (fun point : OrientationBoundary period hPeriod => point)
          boundary vector = vector := by
    change mfderiv throatCoverModelWithCorners throatCoverModelWithCorners id
      boundary vector = vector
    rw [mfderiv_id]
    rfl
  have hParameterApply :
      mfderiv throatCoverModelWithCorners
          (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
          graphParameter boundary vector = (vector, slope) := by
    refine hParameterDerivative.trans ?_
    change
      (mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
          (fun point : OrientationBoundary period hPeriod => point)
          boundary vector,
        mfderiv throatCoverModelWithCorners (modelWithCornersSelf Real Real)
          latitude boundary vector) = (vector, slope)
    rw [hIdentityApply, hLatitudeApply']
  have hComp := mfderiv_comp boundary hCollar hParameter
  have hCompApply := congrArg (fun derivative => derivative vector) hComp
  have hCompApply' :
      mfderiv throatCoverModelWithCorners coverModelWithCorners
          (collar ∘ graphParameter) boundary vector =
        mfderiv
          (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
          coverModelWithCorners collar (graphParameter boundary)
            (mfderiv throatCoverModelWithCorners
              (throatCoverModelWithCorners.prod
                (modelWithCornersSelf Real Real))
              graphParameter boundary vector) := by
    simpa only [Function.comp_def, ContinuousLinearMap.comp_apply] using hCompApply
  rw [hParameterApply] at hCompApply'
  simpa only [collar, graphParameter, latitude, scalar, vector, slope,
    Function.comp_def] using hCompApply'

set_option backward.isDefEq.respectTransparency false in
/-- The collar derivative just computed is the derivative of the historical
same-action normal graph pulled back to the orientation double. -/
theorem normalGraphOrientationDouble_mfderiv_frame_eq_collar
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : OrientationBoundary period hPeriod)
    (index : NormalBoundaryTangentIndex period hPeriod) :
    let latitude := fun point : OrientationBoundary period hPeriod =>
      Real.arctan (parameter *
        normalDisplacementOrientationScalar period hPeriod displacement point)
    let vector :=
      (finiteSmoothThroatGeneratingFrame
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)).vectorAt
          boundary index
    let slope :=
      (1 / (1 + (parameter * normalBoundaryC2JetCoreValueAt period hPeriod
        boundary (smoothNormalDisplacementToBoundaryC2JetCore
          period hPeriod displacement)) ^ 2)) *
        (parameter * normalBoundaryC2JetCoreFirstAt period hPeriod boundary
          (smoothNormalDisplacementToBoundaryC2JetCore
            period hPeriod displacement) index)
    mfderiv throatCoverModelWithCorners coverModelWithCorners
        (fun point : OrientationBoundary period hPeriod =>
          normalGraphOrientationDouble period hPeriod displacement
            (point, parameter)) boundary vector =
      mfderiv
        (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
        coverModelWithCorners
        (fun current : OrientationBoundary period hPeriod × Real =>
          normalBoundaryLatitudeFiberPoint period hPeriod current.1 current.2)
        (boundary, latitude boundary) (vector, slope) := by
  dsimp only
  let scalar : OrientationBoundary period hPeriod → Real :=
    normalDisplacementOrientationScalar period hPeriod displacement
  let latitude : OrientationBoundary period hPeriod → Real :=
    fun point => Real.arctan (parameter * scalar point)
  let vector :=
    (finiteSmoothThroatGeneratingFrame
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)).vectorAt
        boundary index
  let slope :=
    (1 / (1 + (parameter * normalBoundaryC2JetCoreValueAt period hPeriod
      boundary (smoothNormalDisplacementToBoundaryC2JetCore
        period hPeriod displacement)) ^ 2)) *
      (parameter * normalBoundaryC2JetCoreFirstAt period hPeriod boundary
        (smoothNormalDisplacementToBoundaryC2JetCore
          period hPeriod displacement) index)
  let collar := fun current : OrientationBoundary period hPeriod × Real =>
    normalBoundaryLatitudeFiberPoint period hPeriod current.1 current.2
  have hGraph :
      (fun point : OrientationBoundary period hPeriod =>
        normalBoundaryLatitudeFiberPoint period hPeriod point
          (latitude point)) =
        (fun point : OrientationBoundary period hPeriod =>
          normalGraphOrientationDouble period hPeriod displacement
            (point, parameter)) := by
    funext point
    change normalBoundaryLatitudeFiberPoint period hPeriod point
        (Real.arctan (parameter * scalar point)) = _
    rw [show scalar point = normalBoundaryC2JetCoreValueAt period hPeriod point
      (smoothNormalDisplacementToBoundaryC2JetCore period hPeriod displacement) by
        exact (normalBoundaryC2JetCoreValueAt_smooth
          period hPeriod displacement point).symm]
    rw [← normalBoundaryRawFiberPoint_eq_latitude,
      normalBoundaryRawFiberPoint_graph, normalBoundaryC2Graph_smooth]
  have hGraphDerivative := normalGraphCollar_mfderiv_frame
    period hPeriod displacement parameter boundary index
  change mfderiv throatCoverModelWithCorners coverModelWithCorners
      (fun point => normalBoundaryLatitudeFiberPoint period hPeriod point
        (latitude point)) boundary vector =
    mfderiv
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      coverModelWithCorners collar (boundary, latitude boundary)
        (vector, slope) at hGraphDerivative
  rw [hGraph] at hGraphDerivative
  exact hGraphDerivative

set_option backward.isDefEq.respectTransparency false in
/-- The historical horizontal and vertical regular-frame coefficients
reconstruct the genuine collar derivative of a smooth moving graph. -/
theorem normalGraphCollarRegularFrame_reconstructs
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : OrientationBoundary period hPeriod)
    (index : NormalBoundaryTangentIndex period hPeriod) :
    let latitude := Real.arctan (parameter *
      normalDisplacementOrientationScalar period hPeriod displacement boundary)
    let vector :=
      (finiteSmoothThroatGeneratingFrame
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)).vectorAt
          boundary index
    let slope :=
      (1 / (1 + (parameter * normalBoundaryC2JetCoreValueAt period hPeriod
        boundary (smoothNormalDisplacementToBoundaryC2JetCore
          period hPeriod displacement)) ^ 2)) *
        (parameter * normalBoundaryC2JetCoreFirstAt period hPeriod boundary
          (smoothNormalDisplacementToBoundaryC2JetCore
            period hPeriod displacement) index)
    let point := normalBoundaryLatitudeFiberPoint
      period hPeriod boundary latitude
    (∑ row : Fin 4,
      (normalBoundaryLatitudeHorizontalRegularFrameCoefficient period hPeriod
          metric index row (boundary, latitude) +
        slope * normalBoundaryLatitudeVerticalRegularFrameCoefficient
          period hPeriod metric row (boundary, latitude)) •
        metric.frame row point) =
      mfderiv
        (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
        coverModelWithCorners
        (fun current : OrientationBoundary period hPeriod × Real =>
          normalBoundaryLatitudeFiberPoint period hPeriod current.1 current.2)
        (boundary, latitude) (vector, slope) := by
  dsimp only
  classical
  let latitude := Real.arctan (parameter *
    normalDisplacementOrientationScalar period hPeriod displacement boundary)
  let vector :=
    (finiteSmoothThroatGeneratingFrame
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)).vectorAt
        boundary index
  let slope :=
    (1 / (1 + (parameter * normalBoundaryC2JetCoreValueAt period hPeriod
      boundary (smoothNormalDisplacementToBoundaryC2JetCore
        period hPeriod displacement)) ^ 2)) *
      (parameter * normalBoundaryC2JetCoreFirstAt period hPeriod boundary
        (smoothNormalDisplacementToBoundaryC2JetCore
          period hPeriod displacement) index)
  let point := normalBoundaryLatitudeFiberPoint
    period hPeriod boundary latitude
  let collar := fun current : OrientationBoundary period hPeriod × Real =>
    normalBoundaryLatitudeFiberPoint period hPeriod current.1 current.2
  have hHorizontal :=
    normalBoundaryLatitudeHorizontalRegularFrame_reconstructs
      period hPeriod metric index (boundary, latitude)
  rw [normalBoundaryLatitudeHorizontalFiberLift_base] at hHorizontal
  change (normalBoundaryLatitudeHorizontalFiberLift period hPeriod index
      (boundary, latitude)).2 =
    ∑ row : Fin 4,
      normalBoundaryLatitudeHorizontalRegularFrameCoefficient period hPeriod
          metric index row (boundary, latitude) •
        metric.frame row point at hHorizontal
  have hVertical := normalBoundaryLatitudeVerticalRegularFrame_reconstructs
    period hPeriod metric (boundary, latitude)
  rw [normalBoundaryLatitudeFiberLift_base] at hVertical
  change (normalBoundaryLatitudeFiberLift period hPeriod
      boundary latitude).2 =
    ∑ row : Fin 4,
      normalBoundaryLatitudeVerticalRegularFrameCoefficient period hPeriod
          metric row (boundary, latitude) •
        metric.frame row point at hVertical
  have hHorizontalDerivative :=
    normalBoundaryLatitudeHorizontalFiberLift_eq_mfderiv_horizontal
      period hPeriod index boundary latitude
  have hVerticalDerivative :=
    normalBoundaryLatitudeFiberLift_eq_mfderiv_vertical
      period hPeriod boundary latitude
  have hVerticalSlope :
      mfderiv (modelWithCornersSelf Real Real) coverModelWithCorners
          (fun varied : Real => collar (boundary, varied)) latitude slope =
        slope • (normalBoundaryLatitudeFiberLift period hPeriod
          boundary latitude).2 := by
    calc
      mfderiv (modelWithCornersSelf Real Real) coverModelWithCorners
          (fun varied : Real => collar (boundary, varied)) latitude slope =
        mfderiv (modelWithCornersSelf Real Real) coverModelWithCorners
          (fun varied : Real => collar (boundary, varied)) latitude
            (slope • (1 : Real)) := by simp
      _ = slope • mfderiv (modelWithCornersSelf Real Real)
          coverModelWithCorners
          (fun varied : Real => collar (boundary, varied)) latitude 1 := by
        rw [map_smul]
      _ = slope • (normalBoundaryLatitudeFiberLift period hPeriod
          boundary latitude).2 := by rw [← hVerticalDerivative]
  have hCollar : MDifferentiableAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      coverModelWithCorners collar (boundary, latitude) :=
    (normalBoundaryLatitudeFiberPoint_joint_contMDiff period hPeriod)
      |>.mdifferentiableAt (by simp)
  have hSplit := mfderiv_prod_eq_add_apply
    (E := ThroatCoverCoordinates) (E' := Real)
    (I := throatCoverModelWithCorners)
    (I' := modelWithCornersSelf Real Real)
    (v := (vector, slope)) hCollar
  calc
    (∑ row : Fin 4,
      (normalBoundaryLatitudeHorizontalRegularFrameCoefficient period hPeriod
          metric index row (boundary, latitude) +
        slope * normalBoundaryLatitudeVerticalRegularFrameCoefficient
          period hPeriod metric row (boundary, latitude)) •
        metric.frame row point) =
      (∑ row : Fin 4,
        normalBoundaryLatitudeHorizontalRegularFrameCoefficient period hPeriod
            metric index row (boundary, latitude) •
          metric.frame row point) +
        slope • (∑ row : Fin 4,
          normalBoundaryLatitudeVerticalRegularFrameCoefficient period hPeriod
              metric row (boundary, latitude) •
            metric.frame row point) := by
      simp only [add_smul, Finset.sum_add_distrib, Finset.smul_sum, smul_smul]
    _ = mfderiv throatCoverModelWithCorners coverModelWithCorners
          (fun point : OrientationBoundary period hPeriod =>
            collar (point, latitude)) boundary vector +
        mfderiv (modelWithCornersSelf Real Real) coverModelWithCorners
          (fun varied : Real => collar (boundary, varied)) latitude slope := by
      rw [← hHorizontal, ← hVertical]
      rw [hHorizontalDerivative, ← hVerticalSlope]
    _ = mfderiv
        (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
        coverModelWithCorners collar (boundary, latitude) (vector, slope) :=
      hSplit.symm

set_option backward.isDefEq.respectTransparency false in
/-- On the dense smooth core, the completed graph-tangent coefficients
reconstruct the derivative of the pre-existing same-action normal graph. -/
theorem candidateANormalBoundaryGraphTangent_smooth_reconstructs
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : OrientationBoundary period hPeriod)
    (index : NormalBoundaryTangentIndex period hPeriod) :
    let variation := smoothToCandidateANormalBoundaryFunctionalCore
      period hPeriod metric (tensor, displacement)
    let point := normalGraphOrientationDouble period hPeriod displacement
      (boundary, parameter)
    let vector :=
      (finiteSmoothThroatGeneratingFrame
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)).vectorAt
          boundary index
    (∑ row : Fin 4,
      candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation
          period hPeriod metric index row (variation, parameter) boundary •
        metric.frame row point) =
      mfderiv throatCoverModelWithCorners coverModelWithCorners
        (fun current : OrientationBoundary period hPeriod =>
          normalGraphOrientationDouble period hPeriod displacement
            (current, parameter)) boundary vector := by
  dsimp only
  classical
  let variation := smoothToCandidateANormalBoundaryFunctionalCore
    period hPeriod metric (tensor, displacement)
  let normal := smoothNormalDisplacementToBoundaryC2JetCore
    period hPeriod displacement
  let latitude := Real.arctan (parameter *
    normalDisplacementOrientationScalar period hPeriod displacement boundary)
  let slope :=
    (1 / (1 + (parameter * normalBoundaryC2JetCoreValueAt period hPeriod
      boundary normal) ^ 2)) *
      (parameter * normalBoundaryC2JetCoreFirstAt period hPeriod boundary
        normal index)
  let point := normalGraphOrientationDouble period hPeriod displacement
    (boundary, parameter)
  let collarPoint := normalBoundaryLatitudeFiberPoint
    period hPeriod boundary latitude
  have hPoint : collarPoint = point := by
    change normalBoundaryLatitudeFiberPoint period hPeriod boundary
        (Real.arctan (parameter *
          normalDisplacementOrientationScalar period hPeriod displacement
            boundary)) = _
    rw [show normalDisplacementOrientationScalar period hPeriod displacement
          boundary = normalBoundaryC2JetCoreValueAt period hPeriod boundary
          normal by
        exact (normalBoundaryC2JetCoreValueAt_smooth
          period hPeriod displacement boundary).symm]
    rw [← normalBoundaryRawFiberPoint_eq_latitude,
      normalBoundaryRawFiberPoint_graph, normalBoundaryC2Graph_smooth]
  have hCoefficient (row : Fin 4) :
      candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation
          period hPeriod metric index row (variation, parameter) boundary =
        normalBoundaryLatitudeHorizontalRegularFrameCoefficient period hPeriod
            metric index row (boundary, latitude) +
          slope * normalBoundaryLatitudeVerticalRegularFrameCoefficient
            period hPeriod metric row (boundary, latitude) := by
    rw [candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation_apply]
    change normalBoundaryLatitudeHorizontalRegularFrameCoefficient period hPeriod
          metric index row
          (boundary, Real.arctan (parameter *
            normalBoundaryC2JetCoreValueAt period hPeriod boundary normal)) +
        (parameter * normalBoundaryC2JetCoreFirstAt period hPeriod boundary
          normal index) *
          ((1 / (1 + (parameter * normalBoundaryC2JetCoreValueAt period hPeriod
            boundary normal) ^ 2)) *
            normalBoundaryLatitudeVerticalRegularFrameCoefficient period hPeriod
              metric row
              (boundary, Real.arctan (parameter *
                normalBoundaryC2JetCoreValueAt period hPeriod boundary normal))) = _
    dsimp only [latitude, slope]
    rw [normalBoundaryC2JetCoreValueAt_smooth]
    ring
  have hCollar := normalGraphCollarRegularFrame_reconstructs
    period hPeriod metric displacement parameter boundary index
  have hHistorical := normalGraphOrientationDouble_mfderiv_frame_eq_collar
    period hPeriod displacement parameter boundary index
  change (∑ row : Fin 4,
      (normalBoundaryLatitudeHorizontalRegularFrameCoefficient period hPeriod
          metric index row (boundary, latitude) +
        slope * normalBoundaryLatitudeVerticalRegularFrameCoefficient
          period hPeriod metric row (boundary, latitude)) •
        metric.frame row collarPoint) = _ at hCollar
  rw [hPoint] at hCollar
  change mfderiv throatCoverModelWithCorners coverModelWithCorners
      (fun current : OrientationBoundary period hPeriod =>
        normalGraphOrientationDouble period hPeriod displacement
          (current, parameter)) boundary _ = _ at hHistorical
  calc
    (∑ row : Fin 4,
      candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation
          period hPeriod metric index row (variation, parameter) boundary •
        metric.frame row point) =
      (∑ row : Fin 4,
        (normalBoundaryLatitudeHorizontalRegularFrameCoefficient period hPeriod
            metric index row (boundary, latitude) +
          slope * normalBoundaryLatitudeVerticalRegularFrameCoefficient
            period hPeriod metric row (boundary, latitude)) •
          metric.frame row point) := by
      apply Finset.sum_congr rfl
      intro row _
      rw [hCoefficient row]
    _ = _ := hCollar.trans hHistorical.symm

@[simp]
theorem
    candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation_zero_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (index : NormalBoundaryTangentIndex period hPeriod)
    (row : Fin 4) (boundary : OrientationBoundary period hPeriod) :
    candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation
        period hPeriod metric index row 0 boundary =
      normalBoundaryLatitudeHorizontalRegularFrameCoefficient period hPeriod
        metric index row (boundary, 0) := by
  rw [candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation_apply]
  simp

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

/-- Global induced-metric matrices in the already existing finite throat
generating frame. -/
abbrev CandidateANormalBoundaryInducedMetricMatrixField :=
  Matrix (NormalBoundaryTangentIndex period hPeriod)
    (NormalBoundaryTangentIndex period hPeriod)
    (BoundedContinuousFunction (OrientationBoundary period hPeriod) Real)

@[reducible] local instance candidateANormalBoundaryMatrixFieldNormedAddCommGroup :
    NormedAddCommGroup (CandidateANormalBoundaryMatrixField period hPeriod) :=
  Pi.normedAddCommGroup

@[reducible] local instance candidateANormalBoundaryMatrixFieldNormedSpace :
    NormedSpace Real (CandidateANormalBoundaryMatrixField period hPeriod) :=
  Pi.normedSpace

@[reducible] local instance
    candidateANormalBoundaryInducedMetricMatrixFieldNormedAddCommGroup :
    NormedAddCommGroup
      (CandidateANormalBoundaryInducedMetricMatrixField period hPeriod) :=
  Pi.normedAddCommGroup

@[reducible] local instance
    candidateANormalBoundaryInducedMetricMatrixFieldNormedSpace :
    NormedSpace Real
      (CandidateANormalBoundaryInducedMetricMatrixField period hPeriod) :=
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

/-- Existing change-of-frame coefficient from the regular metric frame to the
canonical physical frame, evaluated on the completed graph. -/
def candidateANormalBoundaryRegularFromPhysicalCoefficientFiberEvaluation
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (regular : Fin 4) (physical : BoundaryMetricJetIndex period hPeriod)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) :
    BoundedContinuousFunction (OrientationBoundary period hPeriod) Real :=
  candidateANormalBoundarySmoothCollarFieldFiberEvaluation period hPeriod metric
    (fun point =>
      regularFrameFromPhysicalCoefficient period hPeriod metric regular physical
        (normalBoundaryLatitudeFiberPoint
          period hPeriod point.1 point.2))
    ((regularFrameFromPhysicalCoefficient period hPeriod metric regular physical
      |>.contMDiff_toFun).comp
        (normalBoundaryLatitudeFiberPoint_joint_contMDiff
          period hPeriod)) current

theorem
    candidateANormalBoundaryRegularFromPhysicalCoefficientFiberEvaluation_contDiff_two
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (regular : Fin 4) (physical : BoundaryMetricJetIndex period hPeriod) :
    ContDiff Real 2
      (candidateANormalBoundaryRegularFromPhysicalCoefficientFiberEvaluation
        period hPeriod metric regular physical) := by
  exact candidateANormalBoundarySmoothCollarFieldFiberEvaluation_contDiff_two
    period hPeriod metric _ _

@[simp]
theorem candidateANormalBoundaryRegularFromPhysicalCoefficientFiberEvaluation_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (regular : Fin 4) (physical : BoundaryMetricJetIndex period hPeriod)
    (variation : CandidateANormalBoundaryFunctionalCore period hPeriod metric)
    (parameter : Real) (boundary : OrientationBoundary period hPeriod) :
    candidateANormalBoundaryRegularFromPhysicalCoefficientFiberEvaluation
        period hPeriod metric regular physical (variation, parameter) boundary =
      regularFrameFromPhysicalCoefficient period hPeriod metric regular physical
        (normalBoundaryC2Graph period hPeriod variation.2 parameter
          boundary) := by
  rw [candidateANormalBoundaryRegularFromPhysicalCoefficientFiberEvaluation,
    candidateANormalBoundarySmoothCollarFieldFiberEvaluation_apply]
  rw [← normalBoundaryC2LatitudeGraph_apply,
    normalBoundaryLatitudeFiberPoint_graph]

/-- First derivative of the relative metric in one regular-frame direction,
obtained from the already stored physical-frame first jet. -/
def candidateANormalBoundaryRelativeMetricRegularFirstMatrixFiberEvaluation
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (regular : Fin 4)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) :
    CandidateANormalBoundaryMatrixField period hPeriod :=
  fun row column =>
    ∑ physical : BoundaryMetricJetIndex period hPeriod,
      candidateANormalBoundaryRegularFromPhysicalCoefficientFiberEvaluation
          period hPeriod metric regular physical current *
        candidateANormalBoundaryRelativeMetricSpatialFirstFiberEvaluation
          period hPeriod metric row column physical current

theorem
    candidateANormalBoundaryRelativeMetricRegularFirstMatrixFiberEvaluation_contDiff_two
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (regular : Fin 4) :
    ContDiff Real 2
      (candidateANormalBoundaryRelativeMetricRegularFirstMatrixFiberEvaluation
        period hPeriod metric regular) := by
  change @ContDiff Real _
    (Prod (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real)
    _ _
    (Fin 4 → Fin 4 →
      BoundedContinuousFunction (OrientationBoundary period hPeriod) Real)
    Pi.normedAddCommGroup Pi.normedSpace 2
    (candidateANormalBoundaryRelativeMetricRegularFirstMatrixFiberEvaluation
      period hPeriod metric regular)
  rw [contDiff_pi]
  intro row
  rw [contDiff_pi]
  intro column
  unfold candidateANormalBoundaryRelativeMetricRegularFirstMatrixFiberEvaluation
  apply ContDiff.sum
  intro physical _
  exact
    (candidateANormalBoundaryRegularFromPhysicalCoefficientFiberEvaluation_contDiff_two
      period hPeriod metric regular physical).mul
    (candidateANormalBoundaryRelativeMetricSpatialFirstFiberEvaluation_contDiff_two
      period hPeriod metric row column physical)

@[simp]
theorem
    candidateANormalBoundaryRelativeMetricRegularFirstMatrixFiberEvaluation_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (regular : Fin 4)
    (variation : CandidateANormalBoundaryFunctionalCore period hPeriod metric)
    (parameter : Real) (boundary : OrientationBoundary period hPeriod)
    (row column : Fin 4) :
    candidateANormalBoundaryRelativeMetricRegularFirstMatrixFiberEvaluation
        period hPeriod metric regular (variation, parameter) row column
          boundary =
      ∑ physical : BoundaryMetricJetIndex period hPeriod,
        regularFrameFromPhysicalCoefficient period hPeriod metric regular
            physical
            (normalBoundaryC2Graph period hPeriod variation.2 parameter
              boundary) *
          candidateANormalBoundaryRelativeMetricFirstEntryAtGraph
            period hPeriod metric row column physical variation parameter
              boundary := by
  simp [candidateANormalBoundaryRelativeMetricRegularFirstMatrixFiberEvaluation]

/-- The assembled regular derivative is exactly the existing completed C2
regular-frame derivative, not a second metric jet. -/
theorem
    candidateANormalBoundaryRelativeMetricRegularFirstMatrixFiberEvaluation_eq_existing
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (regular : Fin 4)
    (variation : CandidateANormalBoundaryFunctionalCore period hPeriod metric)
    (parameter : Real) (boundary : OrientationBoundary period hPeriod)
    (row column : Fin 4) :
    candidateANormalBoundaryRelativeMetricRegularFirstMatrixFiberEvaluation
        period hPeriod metric regular (variation, parameter) row column
          boundary =
      regularFrameC2FirstDerivative period hPeriod metric regular
        (regularGeneralMetricBoundaryC3RelativeEntry period hPeriod metric
          row column variation.1)
        (normalBoundaryC2Graph period hPeriod variation.2 parameter
          boundary) := by
  rw [candidateANormalBoundaryRelativeMetricRegularFirstMatrixFiberEvaluation_apply]
  unfold candidateANormalBoundaryRelativeMetricFirstEntryAtGraph
    regularFrameC2FirstDerivative
  simp only [ContinuousMap.sum_apply, ContinuousMap.mul_apply]
  apply Finset.sum_congr rfl
  intro physical _
  rfl

/-- First regular-frame derivative of the fixed background metric matrix,
evaluated by the existing smooth-field substitution. -/
def candidateANormalBoundaryBaseMetricRegularFirstMatrixFiberEvaluation
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (regular : Fin 4)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) :
    CandidateANormalBoundaryMatrixField period hPeriod :=
  fun row column =>
    candidateANormalBoundarySmoothCollarFieldFiberEvaluation
      period hPeriod metric
      (fun point =>
        frameDerivativeComponentField period hPeriod
          (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
          (regularFrameMetricMatrix period hPeriod metric row column) regular
          (normalBoundaryLatitudeFiberPoint
            period hPeriod point.1 point.2))
      ((frameDerivativeComponentField period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
        (regularFrameMetricMatrix period hPeriod metric row column) regular
        |>.contMDiff_toFun).comp
          (normalBoundaryLatitudeFiberPoint_joint_contMDiff
            period hPeriod)) current

theorem
    candidateANormalBoundaryBaseMetricRegularFirstMatrixFiberEvaluation_contDiff_two
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (regular : Fin 4) :
    ContDiff Real 2
      (candidateANormalBoundaryBaseMetricRegularFirstMatrixFiberEvaluation
        period hPeriod metric regular) := by
  change @ContDiff Real _
    (Prod (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real)
    _ _
    (Fin 4 → Fin 4 →
      BoundedContinuousFunction (OrientationBoundary period hPeriod) Real)
    Pi.normedAddCommGroup Pi.normedSpace 2
    (candidateANormalBoundaryBaseMetricRegularFirstMatrixFiberEvaluation
      period hPeriod metric regular)
  rw [contDiff_pi]
  intro row
  rw [contDiff_pi]
  intro column
  exact candidateANormalBoundarySmoothCollarFieldFiberEvaluation_contDiff_two
    period hPeriod metric _ _

@[simp]
theorem
    candidateANormalBoundaryBaseMetricRegularFirstMatrixFiberEvaluation_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (regular row column : Fin 4)
    (variation : CandidateANormalBoundaryFunctionalCore period hPeriod metric)
    (parameter : Real) (boundary : OrientationBoundary period hPeriod) :
    candidateANormalBoundaryBaseMetricRegularFirstMatrixFiberEvaluation
        period hPeriod metric regular (variation, parameter) row column
          boundary =
      frameDerivative period hPeriod Real
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
        (regularFrameMetricMatrix period hPeriod metric row column)
        (normalBoundaryC2Graph period hPeriod variation.2 parameter boundary)
        regular := by
  rw [candidateANormalBoundaryBaseMetricRegularFirstMatrixFiberEvaluation,
    candidateANormalBoundarySmoothCollarFieldFiberEvaluation_apply]
  rw [← normalBoundaryC2LatitudeGraph_apply,
    normalBoundaryLatitudeFiberPoint_graph]
  rfl

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

@[simp] theorem candidateANormalBoundaryMatrixFieldEvaluationRingHom_mapMatrix_apply
    (boundary : OrientationBoundary period hPeriod)
    (matrix : CandidateANormalBoundaryInducedMetricMatrixField period hPeriod)
    (row column : NormalBoundaryTangentIndex period hPeriod) :
    ((candidateANormalBoundaryMatrixFieldEvaluationRingHom
        period hPeriod boundary).mapMatrix matrix) row column =
      matrix row column boundary := by
  rfl

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

/-! ## Fixed smooth coefficients on the same completed graph -/

/-- Continuous-map view of an existing smooth bulk scalar. -/
private def normalBoundarySmoothFieldContinuous
    (field : SmoothQuotientField period hPeriod Real) :
    C(EffectiveQuotient period hPeriod, Real) :=
  ⟨field, field.contMDiff_toFun.continuous⟩

/-- Pullback of an existing smooth scalar to the compact latitude strip. -/
private def normalBoundarySmoothFieldLatitudeCompactPullback
    (field : SmoothQuotientField period hPeriod Real) :
    C(OrientationBoundary period hPeriod × ArctanCompactFiber, Real) :=
  normalBoundaryLatitudeCompactFieldPullbackCLM period hPeriod
    (normalBoundarySmoothFieldContinuous period hPeriod field)

private def normalBoundarySmoothFieldLatitudeValueCompact
    (field : SmoothQuotientField period hPeriod Real) :
    C(OrientationBoundary period hPeriod × ArctanCompactFiber, Real) :=
  normalBoundarySmoothFieldLatitudeCompactPullback period hPeriod field

private def normalBoundarySmoothFieldLatitudeFirstCompact
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothQuotientField period hPeriod Real) :
    C(OrientationBoundary period hPeriod × ArctanCompactFiber, Real) :=
  ∑ index : Fin (finiteSmoothTangentFrame period hPeriod).count,
    normalBoundaryLatitudeFrameCoefficientCompact
        period hPeriod metric index *
      normalBoundarySmoothFieldLatitudeCompactPullback period hPeriod
        (frameDerivativeComponentField period hPeriod
          (finiteSmoothTangentFrame period hPeriod) field index)

private def normalBoundarySmoothFieldLatitudeSecondCompact
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothQuotientField period hPeriod Real) :
    C(OrientationBoundary period hPeriod × ArctanCompactFiber, Real) :=
  (∑ index : Fin (finiteSmoothTangentFrame period hPeriod).count,
    normalBoundaryLatitudeFrameCoefficientDerivativeCompact
        period hPeriod metric index *
      normalBoundarySmoothFieldLatitudeCompactPullback period hPeriod
        (frameDerivativeComponentField period hPeriod
          (finiteSmoothTangentFrame period hPeriod) field index)) +
  ∑ inner : Fin (finiteSmoothTangentFrame period hPeriod).count,
    ∑ outer : Fin (finiteSmoothTangentFrame period hPeriod).count,
      (normalBoundaryLatitudeFrameCoefficientCompact
          period hPeriod metric inner *
        normalBoundaryLatitudeFrameCoefficientCompact
          period hPeriod metric outer) *
      normalBoundarySmoothFieldLatitudeCompactPullback period hPeriod
        (frameDerivativeComponentField period hPeriod
          (finiteSmoothTangentFrame period hPeriod)
          (frameDerivativeComponentField period hPeriod
            (finiteSmoothTangentFrame period hPeriod) field inner) outer)

private def normalBoundarySmoothFieldLatitudeThirdCompact
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothQuotientField period hPeriod Real) :
    C(OrientationBoundary period hPeriod × ArctanCompactFiber, Real) :=
  ((∑ index : Fin (finiteSmoothTangentFrame period hPeriod).count,
      normalBoundaryLatitudeFrameCoefficientSecondDerivativeCompact
          period hPeriod metric index *
        normalBoundarySmoothFieldLatitudeCompactPullback period hPeriod
          (frameDerivativeComponentField period hPeriod
            (finiteSmoothTangentFrame period hPeriod) field index)) +
    ∑ inner : Fin (finiteSmoothTangentFrame period hPeriod).count,
      ∑ outer : Fin (finiteSmoothTangentFrame period hPeriod).count,
        (normalBoundaryLatitudeFrameCoefficientDerivativeCompact
            period hPeriod metric inner *
          normalBoundaryLatitudeFrameCoefficientCompact
            period hPeriod metric outer) *
        normalBoundarySmoothFieldLatitudeCompactPullback period hPeriod
          (frameDerivativeComponentField period hPeriod
            (finiteSmoothTangentFrame period hPeriod)
            (frameDerivativeComponentField period hPeriod
              (finiteSmoothTangentFrame period hPeriod) field inner) outer)) +
  ((∑ inner : Fin (finiteSmoothTangentFrame period hPeriod).count,
      ∑ outer : Fin (finiteSmoothTangentFrame period hPeriod).count,
        (normalBoundaryLatitudeFrameCoefficientDerivativeCompact
              period hPeriod metric inner *
            normalBoundaryLatitudeFrameCoefficientCompact
              period hPeriod metric outer +
          normalBoundaryLatitudeFrameCoefficientCompact
              period hPeriod metric inner *
            normalBoundaryLatitudeFrameCoefficientDerivativeCompact
              period hPeriod metric outer) *
        normalBoundarySmoothFieldLatitudeCompactPullback period hPeriod
          (frameDerivativeComponentField period hPeriod
            (finiteSmoothTangentFrame period hPeriod)
            (frameDerivativeComponentField period hPeriod
              (finiteSmoothTangentFrame period hPeriod) field inner) outer)) +
    ∑ inner : Fin (finiteSmoothTangentFrame period hPeriod).count,
      ∑ middle : Fin (finiteSmoothTangentFrame period hPeriod).count,
        ∑ outer : Fin (finiteSmoothTangentFrame period hPeriod).count,
          ((normalBoundaryLatitudeFrameCoefficientCompact
                period hPeriod metric inner *
              normalBoundaryLatitudeFrameCoefficientCompact
                period hPeriod metric middle) *
            normalBoundaryLatitudeFrameCoefficientCompact
              period hPeriod metric outer) *
          normalBoundarySmoothFieldLatitudeCompactPullback period hPeriod
            (frameDerivativeComponentField period hPeriod
              (finiteSmoothTangentFrame period hPeriod)
              (frameDerivativeComponentField period hPeriod
                (finiteSmoothTangentFrame period hPeriod)
                (frameDerivativeComponentField period hPeriod
                  (finiteSmoothTangentFrame period hPeriod) field inner)
                middle) outer))

private def normalBoundarySmoothFieldLatitudeValueRaw
    (field : SmoothQuotientField period hPeriod Real) :
    RawFiberScalar period hPeriod :=
  boundedArctanCompactPullbackCLM (OrientationBoundary period hPeriod)
    (normalBoundarySmoothFieldLatitudeValueCompact period hPeriod field)

private def normalBoundarySmoothFieldLatitudeFirstRaw
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothQuotientField period hPeriod Real) :
    RawFiberScalar period hPeriod :=
  boundedArctanCompactPullbackCLM (OrientationBoundary period hPeriod)
    (normalBoundarySmoothFieldLatitudeFirstCompact
      period hPeriod metric field)

private def normalBoundarySmoothFieldLatitudeSecondRaw
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothQuotientField period hPeriod Real) :
    RawFiberScalar period hPeriod :=
  boundedArctanCompactPullbackCLM (OrientationBoundary period hPeriod)
    (normalBoundarySmoothFieldLatitudeSecondCompact
      period hPeriod metric field)

private def normalBoundarySmoothFieldLatitudeThirdRaw
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothQuotientField period hPeriod Real) :
    RawFiberScalar period hPeriod :=
  boundedArctanCompactPullbackCLM (OrientationBoundary period hPeriod)
    (normalBoundarySmoothFieldLatitudeThirdCompact
      period hPeriod metric field)

private theorem normalBoundarySmoothFieldLatitudeValueRaw_apply
    (field : SmoothQuotientField period hPeriod Real)
    (boundary : OrientationBoundary period hPeriod) (fiber : Real) :
    normalBoundarySmoothFieldLatitudeValueRaw period hPeriod field
        (boundary, fiber) =
      normalBoundarySmoothFieldLatitudeValue period hPeriod field boundary
        (Real.arctan fiber) := by
  rfl

private theorem normalBoundarySmoothFieldLatitudeValueRaw_eq_rawFiberPoint
    (field : SmoothQuotientField period hPeriod Real)
    (boundary : OrientationBoundary period hPeriod) (fiber : Real) :
    normalBoundarySmoothFieldLatitudeValueRaw period hPeriod field
        (boundary, fiber) =
      field (normalBoundaryRawFiberPoint period hPeriod boundary fiber) := by
  rw [normalBoundaryRawFiberPoint_eq_latitude]
  rfl

private theorem normalBoundarySmoothFieldLatitudeFirstRaw_apply
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothQuotientField period hPeriod Real)
    (boundary : OrientationBoundary period hPeriod) (fiber : Real) :
    normalBoundarySmoothFieldLatitudeFirstRaw period hPeriod metric field
        (boundary, fiber) =
      normalBoundarySmoothFieldLatitudeFirst period hPeriod metric field
        boundary (Real.arctan fiber) := by
  simp [normalBoundarySmoothFieldLatitudeFirstRaw,
    normalBoundarySmoothFieldLatitudeFirstCompact,
    normalBoundarySmoothFieldLatitudeCompactPullback,
    normalBoundarySmoothFieldContinuous,
    normalBoundarySmoothFieldLatitudeFirst,
    normalBoundaryLatitudeFrameCoefficientCompact,
    normalBoundaryLatitudeCompactFieldPullbackCLM,
    normalBoundaryLatitudeCompactInput,
    frameDerivativeComponentField,
    arctanCompactFiberMap]

private theorem normalBoundarySmoothFieldLatitudeSecondRaw_apply
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothQuotientField period hPeriod Real)
    (boundary : OrientationBoundary period hPeriod) (fiber : Real) :
    normalBoundarySmoothFieldLatitudeSecondRaw period hPeriod metric field
        (boundary, fiber) =
      normalBoundarySmoothFieldLatitudeSecond period hPeriod metric field
        boundary (Real.arctan fiber) := by
  simp [normalBoundarySmoothFieldLatitudeSecondRaw,
    normalBoundarySmoothFieldLatitudeSecondCompact,
    normalBoundarySmoothFieldLatitudeCompactPullback,
    normalBoundarySmoothFieldContinuous,
    normalBoundarySmoothFieldLatitudeSecond,
    normalBoundaryLatitudeFrameCoefficientCompact,
    normalBoundaryLatitudeFrameCoefficientDerivativeCompact,
    normalBoundaryLatitudeCompactFieldPullbackCLM,
    normalBoundaryLatitudeCompactInput,
    frameDerivativeComponentField, frameSecondDerivative,
    arctanCompactFiberMap]

private theorem normalBoundarySmoothFieldLatitudeThirdRaw_apply
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothQuotientField period hPeriod Real)
    (boundary : OrientationBoundary period hPeriod) (fiber : Real) :
    normalBoundarySmoothFieldLatitudeThirdRaw period hPeriod metric field
        (boundary, fiber) =
      normalBoundarySmoothFieldLatitudeThird period hPeriod metric field
        boundary (Real.arctan fiber) := by
  simp [normalBoundarySmoothFieldLatitudeThirdRaw,
    normalBoundarySmoothFieldLatitudeThirdCompact,
    normalBoundarySmoothFieldLatitudeCompactPullback,
    normalBoundarySmoothFieldContinuous,
    normalBoundarySmoothFieldLatitudeThird,
    normalBoundaryLatitudeFrameCoefficientCompact,
    normalBoundaryLatitudeFrameCoefficientDerivativeCompact,
    normalBoundaryLatitudeFrameCoefficientSecondDerivativeCompact,
    normalBoundaryLatitudeCompactFieldPullbackCLM,
    normalBoundaryLatitudeCompactInput,
    frameDerivativeComponentField, frameSecondDerivative,
    generalMetricFrameThirdDerivative, add_mul,
    arctanCompactFiberMap]

/-- The exact raw value and first three fiber derivatives of one fixed smooth
bulk scalar. -/
def normalBoundarySmoothFieldRawJetAmbient
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothQuotientField period hPeriod Real) :
    BoundedFiberJet3Ambient (OrientationBoundary period hPeriod) := ![
  normalBoundarySmoothFieldLatitudeValueRaw period hPeriod field,
  (boundedFiberArctanJet3
      (OrientationBoundary period hPeriod)).1 1 *
    normalBoundarySmoothFieldLatitudeFirstRaw
      period hPeriod metric field,
  ((boundedFiberArctanJet3
      (OrientationBoundary period hPeriod)).1 1) ^ 2 *
      normalBoundarySmoothFieldLatitudeSecondRaw
        period hPeriod metric field +
    (boundedFiberArctanJet3
      (OrientationBoundary period hPeriod)).1 2 *
      normalBoundarySmoothFieldLatitudeFirstRaw
        period hPeriod metric field,
  ((boundedFiberArctanJet3
      (OrientationBoundary period hPeriod)).1 1) ^ 3 *
      normalBoundarySmoothFieldLatitudeThirdRaw
        period hPeriod metric field +
    (3 : Real) •
      ((boundedFiberArctanJet3
          (OrientationBoundary period hPeriod)).1 1 *
        (boundedFiberArctanJet3
          (OrientationBoundary period hPeriod)).1 2) *
      normalBoundarySmoothFieldLatitudeSecondRaw
        period hPeriod metric field +
    (boundedFiberArctanJet3
      (OrientationBoundary period hPeriod)).1 3 *
      normalBoundarySmoothFieldLatitudeFirstRaw
        period hPeriod metric field]

private theorem normalBoundarySmoothFieldRawJetAmbient_mem
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothQuotientField period hPeriod Real) :
    (boundedFiberJet3Submodule
      (OrientationBoundary period hPeriod)).carrier
        (normalBoundarySmoothFieldRawJetAmbient
          period hPeriod metric field) := by
  refine And.intro ?_ (And.intro ?_ ?_)
  · intro boundary fiber
    change RealHasDerivAt
      (fun varied => normalBoundarySmoothFieldLatitudeValueRaw
        period hPeriod field (boundary, varied))
      ((boundedFiberArctanJet3
          (OrientationBoundary period hPeriod)).1 1 (boundary, fiber) *
        normalBoundarySmoothFieldLatitudeFirstRaw period hPeriod metric field
          (boundary, fiber)) fiber
    have hComposed :=
      (normalBoundarySmoothFieldLatitudeValue_hasDerivAt period hPeriod
        metric field boundary (Real.arctan fiber)).comp fiber
          ((boundedFiberArctanJet3
            (OrientationBoundary period hPeriod)).2.1 boundary fiber)
    apply (hComposed.congr_of_eventuallyEq ?_).congr_deriv
    · rw [normalBoundarySmoothFieldLatitudeFirstRaw_apply]
      ring
    · filter_upwards [] with varied
      rw [normalBoundarySmoothFieldLatitudeValueRaw_apply]
      rfl
  · intro boundary fiber
    change RealHasDerivAt
      (fun varied =>
        (boundedFiberArctanJet3
            (OrientationBoundary period hPeriod)).1 1 (boundary, varied) *
          normalBoundarySmoothFieldLatitudeFirstRaw period hPeriod metric field
            (boundary, varied))
      (((boundedFiberArctanJet3
            (OrientationBoundary period hPeriod)).1 1 (boundary, fiber)) ^ 2 *
          normalBoundarySmoothFieldLatitudeSecondRaw period hPeriod metric field
            (boundary, fiber) +
        (boundedFiberArctanJet3
            (OrientationBoundary period hPeriod)).1 2 (boundary, fiber) *
          normalBoundarySmoothFieldLatitudeFirstRaw period hPeriod metric field
            (boundary, fiber)) fiber
    have hComposed :=
      (normalBoundarySmoothFieldLatitudeFirst_hasDerivAt period hPeriod
        metric field boundary (Real.arctan fiber)).comp fiber
          ((boundedFiberArctanJet3
            (OrientationBoundary period hPeriod)).2.1 boundary fiber)
    have hProduct :=
      ((boundedFiberArctanJet3
        (OrientationBoundary period hPeriod)).2.2.1 boundary fiber).mul
          hComposed
    convert hProduct using 1
    · funext varied
      rw [normalBoundarySmoothFieldLatitudeFirstRaw_apply]
      rfl
    · rw [normalBoundarySmoothFieldLatitudeFirstRaw_apply,
        normalBoundarySmoothFieldLatitudeSecondRaw_apply]
      simp only [Function.comp_apply]
      ring
  · intro boundary fiber
    change RealHasDerivAt
      (fun varied =>
        ((boundedFiberArctanJet3
            (OrientationBoundary period hPeriod)).1 1 (boundary, varied)) ^ 2 *
            normalBoundarySmoothFieldLatitudeSecondRaw period hPeriod metric field
              (boundary, varied) +
          (boundedFiberArctanJet3
              (OrientationBoundary period hPeriod)).1 2 (boundary, varied) *
            normalBoundarySmoothFieldLatitudeFirstRaw period hPeriod metric field
              (boundary, varied))
      (((boundedFiberArctanJet3
            (OrientationBoundary period hPeriod)).1 1 (boundary, fiber)) ^ 3 *
          normalBoundarySmoothFieldLatitudeThirdRaw period hPeriod metric field
            (boundary, fiber) +
        (3 : Real) *
            ((boundedFiberArctanJet3
                (OrientationBoundary period hPeriod)).1 1 (boundary, fiber) *
              (boundedFiberArctanJet3
                (OrientationBoundary period hPeriod)).1 2 (boundary, fiber)) *
          normalBoundarySmoothFieldLatitudeSecondRaw period hPeriod metric field
            (boundary, fiber) +
        (boundedFiberArctanJet3
            (OrientationBoundary period hPeriod)).1 3 (boundary, fiber) *
          normalBoundarySmoothFieldLatitudeFirstRaw period hPeriod metric field
            (boundary, fiber)) fiber
    have hSecondComposed :=
      (normalBoundarySmoothFieldLatitudeSecond_hasDerivAt period hPeriod
        metric field boundary (Real.arctan fiber)).comp fiber
          ((boundedFiberArctanJet3
            (OrientationBoundary period hPeriod)).2.1 boundary fiber)
    have hFirstComposed :=
      (normalBoundarySmoothFieldLatitudeFirst_hasDerivAt period hPeriod
        metric field boundary (Real.arctan fiber)).comp fiber
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
    convert hFirstTerm.add hSecondTerm using 1
    · funext varied
      rw [normalBoundarySmoothFieldLatitudeFirstRaw_apply,
        normalBoundarySmoothFieldLatitudeSecondRaw_apply]
      rfl
    · rw [normalBoundarySmoothFieldLatitudeFirstRaw_apply,
        normalBoundarySmoothFieldLatitudeSecondRaw_apply,
        normalBoundarySmoothFieldLatitudeThirdRaw_apply]
      simp only [Function.comp_apply, Pi.pow_apply]
      ring

/-- Compatible bounded raw jet of an already existing smooth coefficient. -/
def normalBoundarySmoothFieldRawJet3
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothQuotientField period hPeriod Real) :
    BoundedFiberJet3 (OrientationBoundary period hPeriod) :=
  ⟨normalBoundarySmoothFieldRawJetAmbient period hPeriod metric field,
    normalBoundarySmoothFieldRawJetAmbient_mem
      period hPeriod metric field⟩

/-- Evaluation of a fixed smooth coefficient on the same completed graph. -/
def candidateANormalBoundarySmoothFieldFiberEvaluation
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothQuotientField period hPeriod Real)
    (current : NormalBoundaryC2JetCore period hPeriod × Real) :
    BoundedContinuousFunction (OrientationBoundary period hPeriod) Real :=
  boundedFiberJet3Evaluation (OrientationBoundary period hPeriod)
    (normalBoundarySmoothFieldRawJet3 period hPeriod metric field,
      normalBoundaryC2ScaledRawGraph period hPeriod current)

theorem candidateANormalBoundarySmoothFieldFiberEvaluation_contDiff_two
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothQuotientField period hPeriod Real) :
    ContDiff Real 2
      (candidateANormalBoundarySmoothFieldFiberEvaluation
        period hPeriod metric field) :=
  (boundedFiberJet3Evaluation_contDiff_two
    (OrientationBoundary period hPeriod)).comp
      (contDiff_const.prodMk
        (normalBoundaryC2ScaledRawGraph_contDiff_two period hPeriod))

@[simp]
theorem candidateANormalBoundarySmoothFieldFiberEvaluation_apply
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothQuotientField period hPeriod Real)
    (normal : NormalBoundaryC2JetCore period hPeriod)
    (parameter : Real) (boundary : OrientationBoundary period hPeriod) :
    candidateANormalBoundarySmoothFieldFiberEvaluation period hPeriod metric
        field (normal, parameter) boundary =
      field (normalBoundaryC2Graph period hPeriod normal parameter boundary) := by
  change normalBoundarySmoothFieldLatitudeValueRaw period hPeriod field
      (boundary, normalBoundaryC2ScaledRawGraph period hPeriod
        (normal, parameter) boundary) = _
  rw [normalBoundarySmoothFieldLatitudeValueRaw_eq_rawFiberPoint,
    normalBoundaryC2ScaledRawGraph_apply,
    normalBoundaryRawFiberPoint_graph]

/-- Public fixed-coefficient gate used by the completed frame and collar
assembly. -/
theorem candidate_a_normal_boundary_smooth_field_fiber_c2_gate
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothQuotientField period hPeriod Real) :
    ContDiff Real 2
        (candidateANormalBoundarySmoothFieldFiberEvaluation
          period hPeriod metric field) ∧
      ∀ normal parameter boundary,
        candidateANormalBoundarySmoothFieldFiberEvaluation period hPeriod
            metric field (normal, parameter) boundary =
          field (normalBoundaryC2Graph period hPeriod normal parameter
            boundary) :=
  ⟨candidateANormalBoundarySmoothFieldFiberEvaluation_contDiff_two
      period hPeriod metric field,
    candidateANormalBoundarySmoothFieldFiberEvaluation_apply
      period hPeriod metric field⟩

/-! ## The actual ambient metric on the completed graph -/

/-- Entrywise evaluation of an already existing smooth finite matrix on the
same completed graph. -/
def candidateANormalBoundarySmoothMatrixFiberEvaluation
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (matrix : SmoothFiniteMatrix period hPeriod 4)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) :
    CandidateANormalBoundaryMatrixField period hPeriod :=
  fun row column =>
    candidateANormalBoundarySmoothFieldFiberEvaluation period hPeriod
      metric.metric (matrix row column) (current.1.2, current.2)

theorem candidateANormalBoundarySmoothMatrixFiberEvaluation_contDiff_two
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (matrix : SmoothFiniteMatrix period hPeriod 4) :
    ContDiff Real 2
      (candidateANormalBoundarySmoothMatrixFiberEvaluation
        period hPeriod metric matrix) := by
  have hInput : ContDiff Real 2 (fun current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real =>
      (current.1.2, current.2)) :=
    (contDiff_snd.comp contDiff_fst).prodMk contDiff_snd
  change @ContDiff Real _
    (Prod (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real)
    _ _
    (Fin 4 → Fin 4 →
      BoundedContinuousFunction (OrientationBoundary period hPeriod) Real)
    Pi.normedAddCommGroup Pi.normedSpace 2
    (fun current row column =>
      candidateANormalBoundarySmoothFieldFiberEvaluation period hPeriod
        metric.metric (matrix row column) (current.1.2, current.2))
  rw [contDiff_pi]
  intro row
  rw [contDiff_pi]
  intro column
  exact
    (candidateANormalBoundarySmoothFieldFiberEvaluation_contDiff_two
      period hPeriod metric.metric (matrix row column)).comp hInput

@[simp]
theorem candidateANormalBoundarySmoothMatrixFiberEvaluation_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (matrix : SmoothFiniteMatrix period hPeriod 4)
    (variation : CandidateANormalBoundaryFunctionalCore period hPeriod metric)
    (parameter : Real) (boundary : OrientationBoundary period hPeriod)
    (row column : Fin 4) :
    candidateANormalBoundarySmoothMatrixFiberEvaluation period hPeriod metric
        matrix (variation, parameter) row column boundary =
      matrix row column
        (normalBoundaryC2Graph period hPeriod variation.2 parameter
          boundary) :=
  candidateANormalBoundarySmoothFieldFiberEvaluation_apply period hPeriod
    metric.metric (matrix row column) variation.2 parameter boundary

/-- The fixed background metric matrix evaluated on the moving graph. -/
def candidateANormalBoundaryBaseMetricMatrixFiberEvaluation
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    Prod (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real →
      CandidateANormalBoundaryMatrixField period hPeriod :=
  candidateANormalBoundarySmoothMatrixFiberEvaluation period hPeriod metric
    (regularFrameMetricMatrix period hPeriod metric)

theorem candidateANormalBoundaryBaseMetricMatrixFiberEvaluation_contDiff_two
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    ContDiff Real 2
      (candidateANormalBoundaryBaseMetricMatrixFiberEvaluation
        period hPeriod metric) :=
  candidateANormalBoundarySmoothMatrixFiberEvaluation_contDiff_two period
    hPeriod metric (regularFrameMetricMatrix period hPeriod metric)

/-- The fixed background inverse-metric matrix evaluated on the moving
graph. -/
def candidateANormalBoundaryBaseInverseMetricMatrixFiberEvaluation
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    Prod (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real →
      CandidateANormalBoundaryMatrixField period hPeriod :=
  candidateANormalBoundarySmoothMatrixFiberEvaluation period hPeriod metric
    (regularFrameMetricInverseMatrix period hPeriod metric)

theorem
    candidateANormalBoundaryBaseInverseMetricMatrixFiberEvaluation_contDiff_two
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    ContDiff Real 2
      (candidateANormalBoundaryBaseInverseMetricMatrixFiberEvaluation
        period hPeriod metric) :=
  candidateANormalBoundarySmoothMatrixFiberEvaluation_contDiff_two period
    hPeriod metric (regularFrameMetricInverseMatrix period hPeriod metric)

@[simp]
theorem candidateANormalBoundaryC2MatrixGraphEvaluation_baseInverseMetric
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variation : CandidateANormalBoundaryFunctionalCore period hPeriod metric)
    (parameter : Real) :
    candidateANormalBoundaryC2MatrixGraphEvaluation period hPeriod
        variation.2 parameter
        (regularFrameMetricInverseC2Matrix period hPeriod metric) =
      candidateANormalBoundaryBaseInverseMetricMatrixFiberEvaluation
        period hPeriod metric (variation, parameter) := by
  ext row column boundary
  rw [candidateANormalBoundaryC2MatrixGraphEvaluation_apply]
  unfold candidateANormalBoundaryBaseInverseMetricMatrixFiberEvaluation
  rw [candidateANormalBoundarySmoothMatrixFiberEvaluation_apply]
  have hJet :
      regularFrameMetricInverseC2Matrix period hPeriod metric row column =
        smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
          (regularFrameMetricInverseMatrix period hPeriod metric row column) :=
    rfl
  rw [hJet, canonicalPhysicalScalarC2JetCoreToContinuous_smooth]
  rfl

/-- The actual covariant ambient metric is the already installed chart
formula `g₀ (1 + g₀⁻¹h)`, now evaluated on the completed graph. -/
def candidateANormalBoundaryActualMetricMatrixFiberEvaluation
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) :
    CandidateANormalBoundaryMatrixField period hPeriod :=
  candidateANormalBoundaryBaseMetricMatrixFiberEvaluation period hPeriod
      metric current *
    candidateANormalBoundaryTotalRelativeMetricMatrixFiberEvaluation period
      hPeriod metric current

theorem candidateANormalBoundaryActualMetricMatrixFiberEvaluation_contDiff_two
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    ContDiff Real 2
      (candidateANormalBoundaryActualMetricMatrixFiberEvaluation
        period hPeriod metric) := by
  have hBase :=
    candidateANormalBoundaryBaseMetricMatrixFiberEvaluation_contDiff_two
      period hPeriod metric
  have hRelative :=
    candidateANormalBoundaryTotalRelativeMetricMatrixFiberEvaluation_contDiff_two
      period hPeriod metric
  change @ContDiff Real _
    (Prod (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real)
    _ _
    (Fin 4 → Fin 4 →
      BoundedContinuousFunction (OrientationBoundary period hPeriod) Real)
    Pi.normedAddCommGroup Pi.normedSpace 2
    (fun current =>
      candidateANormalBoundaryBaseMetricMatrixFiberEvaluation period hPeriod
          metric current *
        candidateANormalBoundaryTotalRelativeMetricMatrixFiberEvaluation
          period hPeriod metric current)
  rw [contDiff_pi]
  intro row
  rw [contDiff_pi]
  intro column
  simp_rw [Matrix.mul_apply]
  apply ContDiff.sum
  intro middle _
  exact
    ((contDiff_pi.mp (contDiff_pi.mp hBase row) middle).mul
      (contDiff_pi.mp (contDiff_pi.mp hRelative middle) column))

/-- First regular-frame derivative of the actual varied metric.  This is the
Leibniz derivative of the installed chart identity `g = g0 (1 + g0⁻¹h)`. -/
def candidateANormalBoundaryActualMetricRegularFirstMatrixFiberEvaluation
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (regular : Fin 4)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) :
    CandidateANormalBoundaryMatrixField period hPeriod :=
  candidateANormalBoundaryBaseMetricRegularFirstMatrixFiberEvaluation
        period hPeriod metric regular current *
      candidateANormalBoundaryTotalRelativeMetricMatrixFiberEvaluation
        period hPeriod metric current +
    candidateANormalBoundaryBaseMetricMatrixFiberEvaluation
        period hPeriod metric current *
      candidateANormalBoundaryRelativeMetricRegularFirstMatrixFiberEvaluation
        period hPeriod metric regular current

theorem
    candidateANormalBoundaryActualMetricRegularFirstMatrixFiberEvaluation_contDiff_two
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (regular : Fin 4) :
    ContDiff Real 2
      (candidateANormalBoundaryActualMetricRegularFirstMatrixFiberEvaluation
        period hPeriod metric regular) := by
  have hBaseFirst :=
    candidateANormalBoundaryBaseMetricRegularFirstMatrixFiberEvaluation_contDiff_two
      period hPeriod metric regular
  have hRelative :=
    candidateANormalBoundaryTotalRelativeMetricMatrixFiberEvaluation_contDiff_two
      period hPeriod metric
  have hBase :=
    candidateANormalBoundaryBaseMetricMatrixFiberEvaluation_contDiff_two
      period hPeriod metric
  have hRelativeFirst :=
    candidateANormalBoundaryRelativeMetricRegularFirstMatrixFiberEvaluation_contDiff_two
      period hPeriod metric regular
  change @ContDiff Real _
    (Prod (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real)
    _ _
    (Fin 4 → Fin 4 →
      BoundedContinuousFunction (OrientationBoundary period hPeriod) Real)
    Pi.normedAddCommGroup Pi.normedSpace 2
    (candidateANormalBoundaryActualMetricRegularFirstMatrixFiberEvaluation
      period hPeriod metric regular)
  rw [contDiff_pi]
  intro row
  rw [contDiff_pi]
  intro column
  simp_rw [candidateANormalBoundaryActualMetricRegularFirstMatrixFiberEvaluation,
    Matrix.add_apply, Matrix.mul_apply]
  exact (ContDiff.sum fun middle _ =>
      (contDiff_pi.mp (contDiff_pi.mp hBaseFirst row) middle).mul
        (contDiff_pi.mp (contDiff_pi.mp hRelative middle) column)).add
    (ContDiff.sum fun middle _ =>
      (contDiff_pi.mp (contDiff_pi.mp hBase row) middle).mul
        (contDiff_pi.mp (contDiff_pi.mp hRelativeFirst middle) column))

@[simp]
theorem
    candidateANormalBoundaryActualMetricRegularFirstMatrixFiberEvaluation_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (regular : Fin 4)
    (variation : CandidateANormalBoundaryFunctionalCore period hPeriod metric)
    (parameter : Real) (boundary : OrientationBoundary period hPeriod)
    (row column : Fin 4) :
    candidateANormalBoundaryActualMetricRegularFirstMatrixFiberEvaluation
        period hPeriod metric regular (variation, parameter) row column
          boundary =
      ∑ middle : Fin 4,
        (frameDerivative period hPeriod Real
              (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
              (regularFrameMetricMatrix period hPeriod metric row middle)
              (normalBoundaryC2Graph period hPeriod variation.2 parameter
                boundary) regular *
            ((1 : Matrix (Fin 4) (Fin 4) Real) middle column +
              candidateANormalBoundaryRelativeMetricEntryAtGraph period hPeriod
                metric middle column variation parameter boundary) +
          regularFrameMetricMatrix period hPeriod metric row middle
              (normalBoundaryC2Graph period hPeriod variation.2 parameter
                boundary) *
            candidateANormalBoundaryRelativeMetricRegularFirstMatrixFiberEvaluation
              period hPeriod metric regular (variation, parameter)
                middle column boundary) := by
  simp [candidateANormalBoundaryActualMetricRegularFirstMatrixFiberEvaluation,
    candidateANormalBoundaryBaseMetricMatrixFiberEvaluation,
    Matrix.mul_apply, Finset.sum_add_distrib]

/-- The completed first derivative is exactly the first derivative of the
already installed regular metric chart, evaluated on the same graph. -/
theorem candidateANormalBoundaryActualMetricRegularFirstMatrixFiberEvaluation_eq_existing
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (regular : Fin 4)
    (variation : CandidateANormalBoundaryFunctionalCore period hPeriod metric)
    (parameter : Real) (boundary : OrientationBoundary period hPeriod)
    (row column : Fin 4) :
    candidateANormalBoundaryActualMetricRegularFirstMatrixFiberEvaluation
        period hPeriod metric regular (variation, parameter) row column
          boundary =
      regularGeneralMetricC0MetricFirstDerivative period hPeriod metric
        (regularGeneralMetricBoundaryC3CoreToC2
          period hPeriod metric variation.1)
        regular row column
        (normalBoundaryC2Graph period hPeriod variation.2 parameter
          boundary) := by
  rw [candidateANormalBoundaryActualMetricRegularFirstMatrixFiberEvaluation_apply,
    regularGeneralMetricC0MetricFirstDerivative_apply_expansion]
  apply Finset.sum_congr rfl
  intro middle _
  rw [candidateANormalBoundaryRelativeMetricRegularFirstMatrixFiberEvaluation_eq_existing]
  unfold candidateANormalBoundaryRelativeMetricEntryAtGraph
    regularGeneralMetricBoundaryC3RelativeEntryToContinuous
  rfl

@[simp]
theorem candidateANormalBoundaryActualMetricMatrixFiberEvaluation_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variation : CandidateANormalBoundaryFunctionalCore period hPeriod metric)
    (parameter : Real) (boundary : OrientationBoundary period hPeriod)
    (row column : Fin 4) :
    candidateANormalBoundaryActualMetricMatrixFiberEvaluation period hPeriod
        metric (variation, parameter) row column boundary =
      ∑ middle : Fin 4,
        regularFrameMetricMatrix period hPeriod metric row middle
            (normalBoundaryC2Graph period hPeriod variation.2 parameter
              boundary) *
          ((1 : Matrix (Fin 4) (Fin 4) Real) middle column +
            candidateANormalBoundaryRelativeMetricEntryAtGraph period hPeriod
              metric middle column variation parameter boundary) := by
  simp [candidateANormalBoundaryActualMetricMatrixFiberEvaluation,
    candidateANormalBoundaryBaseMetricMatrixFiberEvaluation,
    Matrix.mul_apply]

/-- The completed actual metric is exactly the installed regular metric
chart evaluated on the same graph. -/
theorem candidateANormalBoundaryActualMetricMatrixFiberEvaluation_eq_existing
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variation : CandidateANormalBoundaryFunctionalCore period hPeriod metric)
    (parameter : Real) (boundary : OrientationBoundary period hPeriod)
    (row column : Fin 4) :
    candidateANormalBoundaryActualMetricMatrixFiberEvaluation period hPeriod
        metric (variation, parameter) row column boundary =
      regularGeneralMetricC0MetricCoefficient period hPeriod metric
        (regularGeneralMetricBoundaryC3CoreToC2
          period hPeriod metric variation.1)
        row column
        (normalBoundaryC2Graph period hPeriod variation.2 parameter
          boundary) := by
  rw [candidateANormalBoundaryActualMetricMatrixFiberEvaluation_apply,
    regularGeneralMetricC0MetricCoefficient_apply_expansion]
  apply Finset.sum_congr rfl
  intro middle _
  unfold candidateANormalBoundaryRelativeMetricEntryAtGraph
    regularGeneralMetricBoundaryC3RelativeEntryToContinuous
  rfl

/-- On the dense smooth core, the completed matrix is exactly the physical
varied metric `g + h` evaluated on the existing moving graph. -/
theorem candidateANormalBoundaryActualMetricMatrixFiberEvaluation_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : OrientationBoundary period hPeriod)
    (row column : Fin 4) :
    let point := normalGraphOrientationDouble period hPeriod displacement
      (boundary, parameter)
    candidateANormalBoundaryActualMetricMatrixFiberEvaluation period hPeriod
          metric
          (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
            (tensor, displacement), parameter) row column boundary =
        metric.metric.tensor.tensor point (metric.frame row point)
            (metric.frame column point) +
          tensor.tensor point (metric.frame row point)
            (metric.frame column point) := by
  dsimp only
  classical
  let point := normalGraphOrientationDouble period hPeriod displacement
    (boundary, parameter)
  let raised := inverseMetricSharp period hPeriod metric.metric point
    (tensor.tensor point (metric.frame column point))
  have hCoefficient (middle : Fin 4) :
      smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod
          (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
          metric.metric tensor middle column point =
        generalMetricFiniteFrameCoefficientAt period hPeriod
          (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
          metric.metric point middle raised := by
    rfl
  have hReconstruct := generalMetricFiniteFrameCoefficientAt_reconstructs
    period hPeriod
      (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
      metric.metric point raised
  have hRaised : raised = ∑ middle : Fin 4,
      smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod
          (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
          metric.metric tensor middle column point •
        metric.frame middle point := by
    calc
      raised = ∑ middle : Fin 4,
          generalMetricFiniteFrameCoefficientAt period hPeriod
              (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
              metric.metric point middle raised • metric.frame middle point :=
        hReconstruct
      _ = _ := by
        apply Finset.sum_congr rfl
        intro middle _
        rw [hCoefficient]
  have hPair' :
      ∑ middle : Fin 4,
        regularFrameMetricMatrix period hPeriod metric row middle point *
          smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod
            (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
            metric.metric tensor middle column point =
        metric.metric.tensor.tensor point (metric.frame row point) raised := by
    calc
      _ = ∑ middle : Fin 4,
          smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod
              (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
              metric.metric tensor middle column point *
            regularFrameMetricMatrix period hPeriod metric row middle point := by
        apply Finset.sum_congr rfl
        intro middle _
        rw [mul_comm]
      _ = metric.metric.tensor.tensor point (metric.frame row point)
          (∑ middle : Fin 4,
            smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod
                (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
                metric.metric tensor middle column point •
              metric.frame middle point) := by
        rw [map_sum]
        simp only [map_smul, smul_eq_mul, regularFrameMetricMatrix_apply]
      _ = _ := congrArg
        (fun vector => metric.metric.tensor.tensor point
          (metric.frame row point) vector) hRaised.symm
  have hFlat := congrArg
    (fun covector => covector (metric.frame row point))
    (metric_flat_inverseMetricSharp period hPeriod metric.metric point
      (tensor.tensor point (metric.frame column point)))
  have hFlat' :
      metric.metric.tensor.tensor point raised (metric.frame row point) =
        tensor.tensor point (metric.frame column point)
          (metric.frame row point) := by
    rw [← metric.metric.musical_eq_tensor point]
    exact hFlat
  have hPairRaised :
      metric.metric.tensor.tensor point (metric.frame row point) raised =
        tensor.tensor point (metric.frame row point)
          (metric.frame column point) := by
    calc
      metric.metric.tensor.tensor point (metric.frame row point) raised =
          metric.metric.tensor.tensor point raised (metric.frame row point) :=
        metric.metric.tensor.symmetric _ _ _
      _ = tensor.tensor point (metric.frame column point)
          (metric.frame row point) := hFlat'
      _ = tensor.tensor point (metric.frame row point)
          (metric.frame column point) := tensor.symmetric _ _ _
  have hRelative (middle : Fin 4) :
      candidateANormalBoundaryRelativeMetricEntryAtGraph period hPeriod metric
          middle column
          (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
            (tensor, displacement)) parameter boundary =
        smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod
          (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
          metric.metric tensor middle column point := by
    rw [candidateANormalBoundaryRelativeMetricEntryAtGraph_smooth]
    rfl
  have hBase :
      ∑ middle : Fin 4,
        regularFrameMetricMatrix period hPeriod metric row middle point *
          (1 : Matrix (Fin 4) (Fin 4) Real) middle column =
        regularFrameMetricMatrix period hPeriod metric row column point := by
    let base : Matrix (Fin 4) (Fin 4) Real := fun first second =>
      regularFrameMetricMatrix period hPeriod metric first second point
    have hIdentity := congrFun (congrFun (Matrix.mul_one base) row) column
    exact hIdentity
  rw [candidateANormalBoundaryActualMetricMatrixFiberEvaluation_apply]
  change (∑ middle : Fin 4,
      regularFrameMetricMatrix period hPeriod metric row middle
          (normalBoundaryC2Graph period hPeriod
            (smoothNormalDisplacementToBoundaryC2JetCore period hPeriod
              displacement) parameter boundary) *
        ((1 : Matrix (Fin 4) (Fin 4) Real) middle column +
          candidateANormalBoundaryRelativeMetricEntryAtGraph period hPeriod
            metric middle column
              (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod
                metric (tensor, displacement)) parameter boundary)) = _
  rw [normalBoundaryC2Graph_smooth]
  simp_rw [hRelative]
  change (∑ middle : Fin 4,
      regularFrameMetricMatrix period hPeriod metric row middle point *
        ((1 : Matrix (Fin 4) (Fin 4) Real) middle column +
          smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod
            (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
            metric.metric tensor middle column point)) =
      metric.metric.tensor.tensor point (metric.frame row point)
          (metric.frame column point) +
        tensor.tensor point (metric.frame row point)
          (metric.frame column point)
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib, hBase, hPair', hPairRaised,
    regularFrameMetricMatrix_apply]

/-- If the smooth variation is represented by an admissible Lorentz metric,
the completed matrix is exactly that varied metric on the moving graph. -/
theorem candidateANormalBoundaryActualMetricMatrixFiberEvaluation_eq_variedMetric
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : OrientationBoundary period hPeriod)
    (row column : Fin 4) :
    let point := normalGraphOrientationDouble period hPeriod displacement
      (boundary, parameter)
    candidateANormalBoundaryActualMetricMatrixFiberEvaluation period hPeriod
          metric
          (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
            (tensor, displacement), parameter) row column boundary =
        variedMetric.tensor.tensor point (metric.frame row point)
          (metric.frame column point) := by
  dsimp only
  rw [candidateANormalBoundaryActualMetricMatrixFiberEvaluation_smooth]
  rw [hVaried]
  rfl

@[simp]
theorem candidateANormalBoundaryRelativeMetricMatrixFiberEvaluation_zero
    (metric : RegularGeneralLorentzMetric period hPeriod)
    : candidateANormalBoundaryRelativeMetricMatrixFiberEvaluation
        period hPeriod metric 0 = 0 := by
  ext row column boundary
  rw [candidateANormalBoundaryRelativeMetricMatrixFiberEvaluation_apply]
  unfold candidateANormalBoundaryRelativeMetricEntryAtGraph
  change (regularGeneralMetricBoundaryC3RelativeEntryToContinuous period hPeriod
    metric row column) 0 _ = 0
  rw [map_zero]
  rfl

@[simp]
theorem candidateANormalBoundaryTotalRelativeMetricMatrixFiberEvaluation_zero
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    candidateANormalBoundaryTotalRelativeMetricMatrixFiberEvaluation
        period hPeriod metric 0 = 1 := by
  rw [candidateANormalBoundaryTotalRelativeMetricMatrixFiberEvaluation,
    candidateANormalBoundaryRelativeMetricMatrixFiberEvaluation_zero,
    add_zero]

@[simp]
theorem candidateANormalBoundaryActualMetricMatrixFiberEvaluation_zero
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    candidateANormalBoundaryActualMetricMatrixFiberEvaluation
        period hPeriod metric 0 =
      candidateANormalBoundaryBaseMetricMatrixFiberEvaluation
        period hPeriod metric 0 := by
  rw [candidateANormalBoundaryActualMetricMatrixFiberEvaluation,
    candidateANormalBoundaryTotalRelativeMetricMatrixFiberEvaluation_zero,
    Matrix.mul_one]

@[simp]
theorem candidateANormalBoundaryActualMetricMatrixFiberEvaluation_zero_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (boundary : OrientationBoundary period hPeriod) (row column : Fin 4) :
    candidateANormalBoundaryActualMetricMatrixFiberEvaluation period hPeriod
        metric 0 row column boundary =
      regularFrameMetricMatrix period hPeriod metric row column
        (normalBoundaryC2Graph period hPeriod 0 0 boundary) := by
  rw [candidateANormalBoundaryActualMetricMatrixFiberEvaluation_zero]
  exact candidateANormalBoundarySmoothMatrixFiberEvaluation_apply period hPeriod
    metric (regularFrameMetricMatrix period hPeriod metric) 0 0 boundary row column

/-- Induced metric of the completed graph in the existing finite throat
generating frame. -/
def candidateANormalBoundaryInducedMetricMatrixFiberEvaluation
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) :
    CandidateANormalBoundaryInducedMetricMatrixField period hPeriod :=
  fun first second =>
    ∑ row : Fin 4, ∑ column : Fin 4,
      candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation
          period hPeriod metric first row current *
        candidateANormalBoundaryActualMetricMatrixFiberEvaluation
          period hPeriod metric current row column *
        candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation
          period hPeriod metric second column current

theorem candidateANormalBoundaryInducedMetricMatrixFiberEvaluation_contDiff_two
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    ContDiff Real 2
      (candidateANormalBoundaryInducedMetricMatrixFiberEvaluation
        period hPeriod metric) := by
  have hTangent (index : NormalBoundaryTangentIndex period hPeriod)
      (row : Fin 4) :=
    candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation_contDiff_two
      period hPeriod metric index row
  have hMetric :=
    candidateANormalBoundaryActualMetricMatrixFiberEvaluation_contDiff_two
      period hPeriod metric
  change @ContDiff Real _
    (Prod (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real)
    _ _
    (NormalBoundaryTangentIndex period hPeriod →
      NormalBoundaryTangentIndex period hPeriod →
      BoundedContinuousFunction (OrientationBoundary period hPeriod) Real)
    Pi.normedAddCommGroup Pi.normedSpace 2
    (candidateANormalBoundaryInducedMetricMatrixFiberEvaluation
      period hPeriod metric)
  rw [contDiff_pi]
  intro first
  rw [contDiff_pi]
  intro second
  unfold candidateANormalBoundaryInducedMetricMatrixFiberEvaluation
  apply ContDiff.sum
  intro row _
  apply ContDiff.sum
  intro column _
  exact ((hTangent first row).mul
    (contDiff_pi.mp (contDiff_pi.mp hMetric row) column)).mul
      (hTangent second column)

@[simp]
theorem candidateANormalBoundaryInducedMetricMatrixFiberEvaluation_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variation : CandidateANormalBoundaryFunctionalCore period hPeriod metric)
    (parameter : Real) (boundary : OrientationBoundary period hPeriod)
    (first second : NormalBoundaryTangentIndex period hPeriod) :
    candidateANormalBoundaryInducedMetricMatrixFiberEvaluation period hPeriod
        metric (variation, parameter) first second boundary =
      ∑ row : Fin 4, ∑ column : Fin 4,
        candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation
            period hPeriod metric first row (variation, parameter) boundary *
          candidateANormalBoundaryActualMetricMatrixFiberEvaluation
            period hPeriod metric (variation, parameter) row column boundary *
          candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation
            period hPeriod metric second column (variation, parameter)
              boundary := by
  simp [candidateANormalBoundaryInducedMetricMatrixFiberEvaluation]

set_option backward.isDefEq.respectTransparency false in
/-- On every admissible smooth metric germ, the completed finite-frame
induced metric is exactly the metric induced on the pre-existing same-action
normal graph.  This is the unrestricted smooth-core identification, not the
base-point specialization below. -/
theorem candidateANormalBoundaryInducedMetricMatrixFiberEvaluation_smooth_eq_normalGraph
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : OrientationBoundary period hPeriod)
    (first second : NormalBoundaryTangentIndex period hPeriod) :
    let variation := smoothToCandidateANormalBoundaryFunctionalCore
      period hPeriod metric (tensor, displacement)
    let point := normalGraphOrientationDouble period hPeriod displacement
      (boundary, parameter)
    let vector := fun index =>
      (finiteSmoothThroatGeneratingFrame
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)).vectorAt
          boundary index
    candidateANormalBoundaryInducedMetricMatrixFiberEvaluation period hPeriod
        metric (variation, parameter) first second boundary =
      variedMetric.tensor.tensor point
        (mfderiv throatCoverModelWithCorners coverModelWithCorners
          (fun current : OrientationBoundary period hPeriod =>
            normalGraphOrientationDouble period hPeriod displacement
              (current, parameter)) boundary (vector first))
        (mfderiv throatCoverModelWithCorners coverModelWithCorners
          (fun current : OrientationBoundary period hPeriod =>
            normalGraphOrientationDouble period hPeriod displacement
              (current, parameter)) boundary (vector second)) := by
  dsimp only
  classical
  let variation := smoothToCandidateANormalBoundaryFunctionalCore
    period hPeriod metric (tensor, displacement)
  let point := normalGraphOrientationDouble period hPeriod displacement
    (boundary, parameter)
  let graph := fun current : OrientationBoundary period hPeriod =>
    normalGraphOrientationDouble period hPeriod displacement
      (current, parameter)
  let vector := fun index =>
    (finiteSmoothThroatGeneratingFrame
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)).vectorAt
        boundary index
  have hMetric (row column : Fin 4) :=
    candidateANormalBoundaryActualMetricMatrixFiberEvaluation_eq_variedMetric
      period hPeriod metric tensor variedMetric hVaried displacement parameter
        boundary row column
  have hFirst := candidateANormalBoundaryGraphTangent_smooth_reconstructs
    period hPeriod metric tensor displacement parameter boundary first
  change (∑ row : Fin 4,
      candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation
          period hPeriod metric first row (variation, parameter) boundary •
        metric.frame row point) =
      mfderiv throatCoverModelWithCorners coverModelWithCorners graph boundary
        (vector first) at hFirst
  have hSecond := candidateANormalBoundaryGraphTangent_smooth_reconstructs
    period hPeriod metric tensor displacement parameter boundary second
  change (∑ column : Fin 4,
      candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation
          period hPeriod metric second column (variation, parameter) boundary •
        metric.frame column point) =
      mfderiv throatCoverModelWithCorners coverModelWithCorners graph boundary
        (vector second) at hSecond
  rw [candidateANormalBoundaryInducedMetricMatrixFiberEvaluation_apply]
  simp_rw [hMetric]
  rw [← hFirst]
  simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro row _
  rw [← hSecond]
  simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, Finset.mul_sum,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro column _
  ring

section SameActionEffectiveThroatBridge

local instance (priority := 30000)
    sameActionBridgeEffectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel
      (MappingTorus (fixedEquatorData period hPeriod)) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.effectiveThroatChartedSpace
    period hPeriod

local instance (priority := 30000)
    sameActionBridgeEffectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (MappingTorus (fixedEquatorData period hPeriod)) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.effectiveThroatIsManifold
    period hPeriod

section OrientationDoubleIntrinsicCoverBridge

local instance (priority := 30000)
    sameActionBridgeEffectiveCoverChartedSpace :
    ChartedSpace CoverModel
      (MappingTorusCover (reflectedSphereData period hPeriod)) :=
  reflectedSphereCoverChartedSpace period hPeriod

local instance (priority := 30000)
    sameActionBridgeEffectiveCoverIsManifold :
    IsManifold coverModelWithCorners ω
      (MappingTorusCover (reflectedSphereData period hPeriod)) :=
  reflectedSphereCover_isManifold period hPeriod

local instance (priority := 30000)
    sameActionBridgeDoubledEffectiveCoverChartedSpace :
    ChartedSpace CoverModel
      (MappingTorusCover (reflectedSphereData
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))) :=
  reflectedSphereCoverChartedSpace
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)

local instance (priority := 30000)
    sameActionBridgeDoubledEffectiveCoverIsManifold :
    IsManifold coverModelWithCorners ω
      (MappingTorusCover (reflectedSphereData
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))) :=
  reflectedSphereCover_isManifold
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)

local instance (priority := 30000)
    sameActionBridgeDoubledEffectiveQuotientChartedSpace :
    ChartedSpace CoverModel
      (MappingTorus (reflectedSphereData
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))) :=
  reflectedSphereQuotientChartedSpace
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)

local instance (priority := 30000)
    sameActionBridgeDoubledEffectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (MappingTorus (reflectedSphereData
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))) :=
  reflectedSphereQuotient_isManifold
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)

set_option backward.isDefEq.respectTransparency false in
/-- The intrinsic cover metric is natural under the coordinate
identification from the doubled-period throat cover to the original one. -/
theorem intrinsicCoverThroatMetric_orientationDouble_natural
    (anchor : MappingTorusCover (orientationDoubleData period hPeriod))
    (first second : TangentSpace throatCoverModelWithCorners anchor) :
    intrinsicCoverLorentzTensor
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
        (fixedThroatCoverInclusion
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod) anchor)
        (mfderiv throatCoverModelWithCorners coverModelWithCorners
          (fixedThroatCoverInclusion
            (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
          anchor first)
        (mfderiv throatCoverModelWithCorners coverModelWithCorners
          (fixedThroatCoverInclusion
            (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
          anchor second) =
      intrinsicCoverLorentzTensor period hPeriod
        (fixedThroatCoverInclusion period hPeriod
          (orientationDoubleCoverHomeomorph period hPeriod anchor))
        (mfderiv throatCoverModelWithCorners coverModelWithCorners
          (fixedThroatCoverInclusion period hPeriod)
          (orientationDoubleCoverHomeomorph period hPeriod anchor)
          (mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
            (orientationDoubleCoverHomeomorph period hPeriod) anchor first))
        (mfderiv throatCoverModelWithCorners coverModelWithCorners
          (fixedThroatCoverInclusion period hPeriod)
          (orientationDoubleCoverHomeomorph period hPeriod anchor)
          (mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
            (orientationDoubleCoverHomeomorph period hPeriod) anchor
            second)) := by
  let sourceInclusion := fixedThroatCoverInclusion
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
  let targetInclusion := fixedThroatCoverInclusion period hPeriod
  let coverMap := orientationDoubleCoverHomeomorph period hPeriod
  let sourceProduct := coverHomeomorphProd (reflectedSphereData
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
  let targetProduct := coverHomeomorphProd
    (reflectedSphereData period hPeriod)
  have hSourceInclusion : MDifferentiableAt throatCoverModelWithCorners
      coverModelWithCorners sourceInclusion anchor :=
    (fixedThroatCoverInclusion_contMDiff
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
      |>.mdifferentiableAt (by simp)
  have hTargetInclusion : MDifferentiableAt throatCoverModelWithCorners
      coverModelWithCorners targetInclusion (coverMap anchor) :=
    (fixedThroatCoverInclusion_contMDiff period hPeriod)
      |>.mdifferentiableAt (by simp)
  have hCoverMap : MDifferentiableAt throatCoverModelWithCorners
      throatCoverModelWithCorners coverMap anchor :=
    (orientationDoubleCoverHomeomorph_contMDiff period hPeriod)
      |>.mdifferentiableAt (by simp)
  have hSourceProduct : MDifferentiableAt coverModelWithCorners
      coverModelWithCorners sourceProduct (sourceInclusion anchor) :=
    (chartedSpacePullback_toFun_contMDiff coverModelWithCorners ∞
      (coverHomeomorphProd (reflectedSphereData
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))))
      |>.mdifferentiableAt (by simp)
  have hTargetProduct : MDifferentiableAt coverModelWithCorners
      coverModelWithCorners targetProduct
        (targetInclusion (coverMap anchor)) :=
    (chartedSpacePullback_toFun_contMDiff coverModelWithCorners ∞
      (coverHomeomorphProd (reflectedSphereData period hPeriod)))
      |>.mdifferentiableAt (by simp)
  have hTargetComposite : MDifferentiableAt throatCoverModelWithCorners
      coverModelWithCorners (targetProduct ∘ targetInclusion)
        (coverMap anchor) :=
    hTargetProduct.comp (coverMap anchor) hTargetInclusion
  have hFunctions : sourceProduct ∘ sourceInclusion =
      (targetProduct ∘ targetInclusion) ∘ coverMap := by
    funext point
    rfl
  have hSourceChain := hSourceProduct.hasMFDerivAt.comp
    anchor hSourceInclusion.hasMFDerivAt
  have hTargetInnerChain := hTargetProduct.hasMFDerivAt.comp
    (coverMap anchor) hTargetInclusion.hasMFDerivAt
  have hTargetChain := hTargetComposite.hasMFDerivAt.comp
    anchor hCoverMap.hasMFDerivAt
  have hDerivative :
      (coverProductDerivative
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
          (sourceInclusion anchor)).comp
        (mfderiv throatCoverModelWithCorners coverModelWithCorners
          sourceInclusion anchor) =
      ((coverProductDerivative period hPeriod
          (targetInclusion (coverMap anchor))).comp
        (mfderiv throatCoverModelWithCorners coverModelWithCorners
          targetInclusion (coverMap anchor))).comp
        (mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
          coverMap anchor) := by
    change
      (mfderiv coverModelWithCorners coverModelWithCorners sourceProduct
          (sourceInclusion anchor)).comp
        (mfderiv throatCoverModelWithCorners coverModelWithCorners
          sourceInclusion anchor) =
      ((mfderiv coverModelWithCorners coverModelWithCorners targetProduct
          (targetInclusion (coverMap anchor))).comp
        (mfderiv throatCoverModelWithCorners coverModelWithCorners
          targetInclusion (coverMap anchor))).comp
        (mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
          coverMap anchor)
    rw [← hSourceChain.mfderiv]
    rw [hFunctions]
    rw [hTargetChain.mfderiv]
    rw [hTargetInnerChain.mfderiv]
  have hFirst := congrArg (fun derivative => derivative first) hDerivative
  have hSecond := congrArg (fun derivative => derivative second) hDerivative
  simp only [ContinuousLinearMap.comp_apply] at hFirst hSecond
  rw [intrinsicCoverLorentzTensor_apply,
    intrinsicCoverLorentzTensor_apply]
  rw [coverAmbientDerivative_apply_product,
    coverAmbientDerivative_apply_product,
    coverAmbientDerivative_apply_product,
    coverAmbientDerivative_apply_product]
  rw [hFirst, hSecond]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem intrinsicThroatMetric_orientationDouble_natural_mk
    (anchor : MappingTorusCover (fixedEquatorData
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)))
    (first second : TangentSpace throatCoverModelWithCorners anchor) :
    generalLorentzMetricThroatTraceValue
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
        (intrinsicSmoothGeneralLorentzMetric
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
        (mappingTorusMk (fixedEquatorData
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)) anchor)
        (mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
          (mappingTorusMk (fixedEquatorData
            (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)))
          anchor first)
        (mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
          (mappingTorusMk (fixedEquatorData
            (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)))
          anchor second) =
      generalLorentzMetricThroatTraceValue period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod)
        (mappingTorusMk (fixedEquatorData period hPeriod)
          (orientationDoubleCoverHomeomorph period hPeriod anchor))
        (mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
          (mappingTorusMk (fixedEquatorData period hPeriod))
          (orientationDoubleCoverHomeomorph period hPeriod anchor)
          (mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
            (orientationDoubleCoverHomeomorph period hPeriod) anchor first))
        (mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
          (mappingTorusMk (fixedEquatorData period hPeriod))
          (orientationDoubleCoverHomeomorph period hPeriod anchor)
          (mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
            (orientationDoubleCoverHomeomorph period hPeriod) anchor
            second)) := by
  let sourceProjection := mappingTorusMk
    (fixedEquatorData (doubledPeriod period)
      (doubledPeriod_ne_zero period hPeriod))
  let targetProjection := mappingTorusMk (fixedEquatorData period hPeriod)
  let sourceAmbientProjection := mappingTorusMk
    (reflectedSphereData (doubledPeriod period)
      (doubledPeriod_ne_zero period hPeriod))
  let targetAmbientProjection := mappingTorusMk
    (reflectedSphereData period hPeriod)
  let sourceInclusion := fixedThroatCoverInclusion
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
  let targetInclusion := fixedThroatCoverInclusion period hPeriod
  let sourceQuotientInclusion := fixedThroatQuotientInclusion
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
  let targetQuotientInclusion := fixedThroatQuotientInclusion
    period hPeriod
  let coverMap := orientationDoubleCoverHomeomorph period hPeriod
  have hSourceProjection : MDifferentiableAt throatCoverModelWithCorners
      throatCoverModelWithCorners sourceProjection anchor :=
    (fixedThroat_projection_isLocalDiffeomorph
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
      |>.contMDiff.mdifferentiableAt (by simp)
  have hTargetProjection : MDifferentiableAt throatCoverModelWithCorners
      throatCoverModelWithCorners targetProjection (coverMap anchor) :=
    (fixedThroat_projection_isLocalDiffeomorph period hPeriod)
      |>.contMDiff.mdifferentiableAt (by simp)
  have hSourceAmbientProjection : MDifferentiableAt coverModelWithCorners
      coverModelWithCorners sourceAmbientProjection
        (sourceInclusion anchor) :=
    (reflectedSphere_projection_isLocalDiffeomorph
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
      |>.contMDiff.mdifferentiableAt (by simp)
  have hTargetAmbientProjection : MDifferentiableAt coverModelWithCorners
      coverModelWithCorners targetAmbientProjection
        (targetInclusion (coverMap anchor)) :=
    (reflectedSphere_projection_isLocalDiffeomorph period hPeriod)
      |>.contMDiff.mdifferentiableAt (by simp)
  have hSourceInclusion : MDifferentiableAt throatCoverModelWithCorners
      coverModelWithCorners sourceInclusion anchor :=
    (fixedThroatCoverInclusion_contMDiff
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
      |>.mdifferentiableAt (by simp)
  have hTargetInclusion : MDifferentiableAt throatCoverModelWithCorners
      coverModelWithCorners targetInclusion (coverMap anchor) :=
    (fixedThroatCoverInclusion_contMDiff period hPeriod)
      |>.mdifferentiableAt (by simp)
  have hSourceQuotientInclusion : MDifferentiableAt
      throatCoverModelWithCorners coverModelWithCorners
      sourceQuotientInclusion (sourceProjection anchor) :=
    (fixedThroatQuotientInclusion_contMDiff
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
      |>.mdifferentiableAt (by simp)
  have hTargetQuotientInclusion : MDifferentiableAt
      throatCoverModelWithCorners coverModelWithCorners
      targetQuotientInclusion (targetProjection (coverMap anchor)) :=
    (fixedThroatQuotientInclusion_contMDiff period hPeriod)
      |>.mdifferentiableAt (by simp)
  have hSourceDerivative :
      (mfderiv coverModelWithCorners coverModelWithCorners
          sourceAmbientProjection (sourceInclusion anchor)).comp
        (mfderiv throatCoverModelWithCorners coverModelWithCorners
          sourceInclusion anchor) =
      (mfderiv throatCoverModelWithCorners coverModelWithCorners
          sourceQuotientInclusion (sourceProjection anchor)).comp
        (mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
          sourceProjection anchor) := by
    rw [← mfderiv_comp anchor hSourceAmbientProjection hSourceInclusion,
      ← mfderiv_comp anchor hSourceQuotientInclusion hSourceProjection]
    rfl
  have hTargetDerivative :
      (mfderiv coverModelWithCorners coverModelWithCorners
          targetAmbientProjection (targetInclusion (coverMap anchor))).comp
        (mfderiv throatCoverModelWithCorners coverModelWithCorners
          targetInclusion (coverMap anchor)) =
      (mfderiv throatCoverModelWithCorners coverModelWithCorners
          targetQuotientInclusion (targetProjection (coverMap anchor))).comp
        (mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
          targetProjection (coverMap anchor)) := by
    rw [← mfderiv_comp (coverMap anchor) hTargetAmbientProjection
        hTargetInclusion,
      ← mfderiv_comp (coverMap anchor) hTargetQuotientInclusion
        hTargetProjection]
    rfl
  have hSourcePoint :
      sourceAmbientProjection (sourceInclusion anchor) =
        sourceQuotientInclusion (sourceProjection anchor) := by
    rfl
  have hTargetPoint :
      targetAmbientProjection (targetInclusion (coverMap anchor)) =
        targetQuotientInclusion (targetProjection (coverMap anchor)) := by
    rfl
  dsimp only [sourceAmbientProjection, sourceInclusion,
    sourceQuotientInclusion, sourceProjection] at hSourcePoint
  dsimp only [targetAmbientProjection, targetInclusion,
    targetQuotientInclusion, targetProjection, coverMap] at hTargetPoint
  let inputFirst : TangentBundle throatCoverModelWithCorners
      (MappingTorusCover (fixedEquatorData
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))) :=
    ⟨anchor, first⟩
  let inputSecond : TangentBundle throatCoverModelWithCorners
      (MappingTorusCover (fixedEquatorData
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))) :=
    ⟨anchor, second⟩
  let sourceFirstCover := tangentMap coverModelWithCorners
    coverModelWithCorners sourceAmbientProjection
      (tangentMap throatCoverModelWithCorners coverModelWithCorners
        sourceInclusion inputFirst)
  let sourceSecondCover := tangentMap coverModelWithCorners
    coverModelWithCorners sourceAmbientProjection
      (tangentMap throatCoverModelWithCorners coverModelWithCorners
        sourceInclusion inputSecond)
  let sourceFirstQuotient := tangentMap throatCoverModelWithCorners
    coverModelWithCorners sourceQuotientInclusion
      (tangentMap throatCoverModelWithCorners throatCoverModelWithCorners
        sourceProjection inputFirst)
  let sourceSecondQuotient := tangentMap throatCoverModelWithCorners
    coverModelWithCorners sourceQuotientInclusion
      (tangentMap throatCoverModelWithCorners throatCoverModelWithCorners
        sourceProjection inputSecond)
  let targetFirstCover := tangentMap coverModelWithCorners
    coverModelWithCorners targetAmbientProjection
      (tangentMap throatCoverModelWithCorners coverModelWithCorners
        targetInclusion
        (tangentMap throatCoverModelWithCorners throatCoverModelWithCorners
          coverMap inputFirst))
  let targetSecondCover := tangentMap coverModelWithCorners
    coverModelWithCorners targetAmbientProjection
      (tangentMap throatCoverModelWithCorners coverModelWithCorners
        targetInclusion
        (tangentMap throatCoverModelWithCorners throatCoverModelWithCorners
          coverMap inputSecond))
  let targetFirstQuotient := tangentMap throatCoverModelWithCorners
    coverModelWithCorners targetQuotientInclusion
      (tangentMap throatCoverModelWithCorners throatCoverModelWithCorners
        targetProjection
        (tangentMap throatCoverModelWithCorners throatCoverModelWithCorners
          coverMap inputFirst))
  let targetSecondQuotient := tangentMap throatCoverModelWithCorners
    coverModelWithCorners targetQuotientInclusion
      (tangentMap throatCoverModelWithCorners throatCoverModelWithCorners
        targetProjection
        (tangentMap throatCoverModelWithCorners throatCoverModelWithCorners
          coverMap inputSecond))
  have hSourceFirstTangent : sourceFirstCover = sourceFirstQuotient := by
    dsimp only [sourceFirstCover, sourceFirstQuotient, inputFirst]
    apply Bundle.TotalSpace.ext
    · exact hSourcePoint
    · exact (congrArg (fun derivative => derivative first)
        hSourceDerivative).heq
  have hSourceSecondTangent : sourceSecondCover = sourceSecondQuotient := by
    dsimp only [sourceSecondCover, sourceSecondQuotient, inputSecond]
    apply Bundle.TotalSpace.ext
    · exact hSourcePoint
    · exact (congrArg (fun derivative => derivative second)
        hSourceDerivative).heq
  have hTargetFirstTangent : targetFirstCover = targetFirstQuotient := by
    dsimp only [targetFirstCover, targetFirstQuotient, inputFirst]
    apply Bundle.TotalSpace.ext
    · exact hTargetPoint
    · exact (congrArg (fun derivative => derivative
        (mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
          coverMap anchor first)) hTargetDerivative).heq
  have hTargetSecondTangent : targetSecondCover = targetSecondQuotient := by
    dsimp only [targetSecondCover, targetSecondQuotient, inputSecond]
    apply Bundle.TotalSpace.ext
    · exact hTargetPoint
    · exact (congrArg (fun derivative => derivative
        (mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
          coverMap anchor second)) hTargetDerivative).heq
  rw [generalLorentzMetricThroatTraceValue_apply,
    generalLorentzMetricThroatTraceValue_apply]
  simp only [orientationDoubleData]
  change
    (intrinsicSmoothGeneralLorentzMetric
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)).tensor.tensor
        sourceFirstQuotient.1 sourceFirstQuotient.2 sourceSecondQuotient.2 =
      (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor.tensor
        targetFirstQuotient.1 targetFirstQuotient.2 targetSecondQuotient.2
  rw [← hSourceFirstTangent, ← hSourceSecondTangent,
    ← hTargetFirstTangent, ← hTargetSecondTangent]
  dsimp only [sourceFirstCover, sourceSecondCover, targetFirstCover,
    targetSecondCover, inputFirst, inputSecond, tangentMap]
  change
    (intrinsicTensorQuotientDescent
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)).tensor
        (sourceAmbientProjection (sourceInclusion anchor))
        (mfderiv coverModelWithCorners coverModelWithCorners
          sourceAmbientProjection (sourceInclusion anchor)
          (mfderiv throatCoverModelWithCorners coverModelWithCorners
            sourceInclusion anchor first))
        (mfderiv coverModelWithCorners coverModelWithCorners
          sourceAmbientProjection (sourceInclusion anchor)
          (mfderiv throatCoverModelWithCorners coverModelWithCorners
            sourceInclusion anchor second)) =
      (intrinsicTensorQuotientDescent period hPeriod).tensor
        (targetAmbientProjection (targetInclusion (coverMap anchor)))
        (mfderiv coverModelWithCorners coverModelWithCorners
          targetAmbientProjection (targetInclusion (coverMap anchor))
          (mfderiv throatCoverModelWithCorners coverModelWithCorners
            targetInclusion (coverMap anchor)
            (mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
              coverMap anchor first)))
        (mfderiv coverModelWithCorners coverModelWithCorners
          targetAmbientProjection (targetInclusion (coverMap anchor))
          (mfderiv throatCoverModelWithCorners coverModelWithCorners
            targetInclusion (coverMap anchor)
            (mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
              coverMap anchor second)))
  rw [(intrinsicTensorQuotientDescent
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)).pullback,
    (intrinsicTensorQuotientDescent period hPeriod).pullback]
  exact intrinsicCoverThroatMetric_orientationDouble_natural
    period hPeriod anchor first second

set_option backward.isDefEq.respectTransparency false in
theorem intrinsicThroatMetric_orientationDouble_natural
    (boundary : CutThroatBoundary period hPeriod)
    (first second : TangentSpace throatCoverModelWithCorners boundary) :
    generalLorentzMetricThroatTraceValue
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
        (intrinsicSmoothGeneralLorentzMetric
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
        boundary first second =
      generalLorentzMetricThroatTraceValue period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod)
        (orientationDoubleToThroat period hPeriod boundary)
        (normalBoundaryOrientationTangentEquiv period hPeriod boundary first)
        (normalBoundaryOrientationTangentEquiv period hPeriod boundary
          second) := by
  obtain ⟨anchor, rfl⟩ :=
    mappingTorusMk_surjective (orientationDoubleData period hPeriod) boundary
  let sourceProjection := mappingTorusMk
    (fixedEquatorData (doubledPeriod period)
      (doubledPeriod_ne_zero period hPeriod))
  let targetProjection := mappingTorusMk (fixedEquatorData period hPeriod)
  let coverMap := orientationDoubleCoverHomeomorph period hPeriod
  let orientationProjection := orientationDoubleToThroat period hPeriod
  let hSourceLocal := fixedThroat_projection_isLocalDiffeomorph
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
  obtain ⟨firstLift, hFirstLift⟩ :=
    (hSourceLocal.mfderivToContinuousLinearEquiv
      (by simp) anchor).surjective first
  obtain ⟨secondLift, hSecondLift⟩ :=
    (hSourceLocal.mfderivToContinuousLinearEquiv
      (by simp) anchor).surjective second
  have hFirstLift' :
      mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
        sourceProjection anchor firstLift = first := by
    rw [← hSourceLocal.mfderivToContinuousLinearEquiv_coe
      (by simp) anchor]
    exact hFirstLift
  have hSecondLift' :
      mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
        sourceProjection anchor secondLift = second := by
    rw [← hSourceLocal.mfderivToContinuousLinearEquiv_coe
      (by simp) anchor]
    exact hSecondLift
  have hSourceProjection : MDifferentiableAt throatCoverModelWithCorners
      throatCoverModelWithCorners sourceProjection anchor :=
    hSourceLocal.contMDiff.mdifferentiableAt (by simp)
  have hTargetProjection : MDifferentiableAt throatCoverModelWithCorners
      throatCoverModelWithCorners targetProjection (coverMap anchor) :=
    (fixedThroat_projection_isLocalDiffeomorph period hPeriod)
      |>.contMDiff.mdifferentiableAt (by simp)
  have hCoverMap : MDifferentiableAt throatCoverModelWithCorners
      throatCoverModelWithCorners coverMap anchor :=
    (orientationDoubleCoverHomeomorph_contMDiff period hPeriod)
      |>.mdifferentiableAt (by simp)
  have hOrientationProjection : MDifferentiableAt
      throatCoverModelWithCorners throatCoverModelWithCorners
      orientationProjection (sourceProjection anchor) :=
    (orientationDoubleToThroat_contMDiff period hPeriod)
      |>.mdifferentiableAt (by simp)
  have hFunctions : orientationProjection ∘ sourceProjection =
      targetProjection ∘ coverMap := by
    funext point
    rfl
  have hOrientationDerivative (vector : TangentSpace
      throatCoverModelWithCorners anchor) :
      mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
          orientationProjection (sourceProjection anchor)
          (mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
            sourceProjection anchor vector) =
        mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
          targetProjection (coverMap anchor)
          (mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
            coverMap anchor vector) := by
    have hLeft := mfderiv_comp_apply anchor hOrientationProjection
      hSourceProjection vector
    have hRight := mfderiv_comp_apply anchor hTargetProjection
      hCoverMap vector
    rw [hFunctions] at hLeft
    exact hLeft.symm.trans hRight
  have hTargetFirst :
      normalBoundaryOrientationTangentEquiv period hPeriod
          (mappingTorusMk (orientationDoubleData period hPeriod) anchor) first =
        mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
          targetProjection (coverMap anchor)
          (mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
            coverMap anchor firstLift) := by
    rw [normalBoundaryOrientationTangentEquiv_apply]
    rw [← hFirstLift']
    exact hOrientationDerivative firstLift
  have hTargetSecond :
      normalBoundaryOrientationTangentEquiv period hPeriod
          (mappingTorusMk (orientationDoubleData period hPeriod) anchor) second =
        mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
          targetProjection (coverMap anchor)
          (mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
            coverMap anchor secondLift) := by
    rw [normalBoundaryOrientationTangentEquiv_apply]
    rw [← hSecondLift']
    exact hOrientationDerivative secondLift
  have hLifted := intrinsicThroatMetric_orientationDouble_natural_mk
    period hPeriod anchor firstLift secondLift
  rw [hFirstLift', hSecondLift', ← hTargetFirst, ← hTargetSecond]
    at hLifted
  rw [orientationDoubleToThroat_mk]
  simp only [orientationDoubleData]
  convert hLifted using 1 <;> rfl

set_option backward.isDefEq.respectTransparency false in
theorem intrinsicSmoothNondegenerateThroatMetric_orientationDouble_natural
    (boundary : CutThroatBoundary period hPeriod)
    (first second : TangentSpace throatCoverModelWithCorners boundary) :
    (intrinsicSmoothNondegenerateThroatMetric
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)).1.tensor
        boundary first second =
      (intrinsicSmoothNondegenerateThroatMetric period hPeriod).1.tensor
        (orientationDoubleToThroat period hPeriod boundary)
        (normalBoundaryOrientationTangentEquiv period hPeriod boundary first)
        (normalBoundaryOrientationTangentEquiv period hPeriod boundary
          second) := by
  simpa [intrinsicSmoothNondegenerateThroatMetric,
    generalLorentzMetricNondegenerateThroatTrace,
    generalLorentzMetricThroatTrace] using
      intrinsicThroatMetric_orientationDouble_natural
        period hPeriod boundary first second

end OrientationDoubleIntrinsicCoverBridge

set_option backward.isDefEq.respectTransparency false in
/-- The derivative of the orientation-double graph is the chain-rule pullback
of the derivative of the pre-existing same-action normal graph. -/
theorem normalGraphOrientationDouble_mfderiv_eq_comp
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : CutThroatBoundary period hPeriod)
    (vector : TangentSpace throatCoverModelWithCorners boundary) :
    mfderiv throatCoverModelWithCorners coverModelWithCorners
        (fun current : CutThroatBoundary period hPeriod =>
          normalGraphOrientationDouble period hPeriod displacement
            (current, parameter)) boundary vector =
      mfderiv throatCoverModelWithCorners coverModelWithCorners
        (P0EFTJanusProgramPGlobalNormalDisplacementCollarGraph4D.normalGraph
          period hPeriod displacement parameter)
        (orientationDoubleToThroat period hPeriod boundary)
        (mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
          (orientationDoubleToThroat period hPeriod) boundary vector) := by
  let outer :=
    P0EFTJanusProgramPGlobalNormalDisplacementCollarGraph4D.normalGraph
      period hPeriod displacement parameter
  let inner := orientationDoubleToThroat period hPeriod
  have hOuter : MDifferentiableAt throatCoverModelWithCorners
      coverModelWithCorners outer (inner boundary) :=
    (normalGraph_fixedParameter_contMDiff period hPeriod displacement parameter)
      |>.mdifferentiableAt (by simp)
  have hInner : MDifferentiableAt throatCoverModelWithCorners
      throatCoverModelWithCorners inner boundary :=
    (orientationDoubleToThroat_contMDiff period hPeriod)
      |>.mdifferentiableAt (by simp)
  have hComp := mfderiv_comp boundary hOuter hInner
  have hApply := congrArg (fun derivative => derivative vector) hComp
  simpa only [outer, inner, normalGraphOrientationDouble, Function.comp_def,
    ContinuousLinearMap.comp_apply] using hApply

set_option backward.isDefEq.respectTransparency false in
/-- On the smooth core, the completed induced metric is the historical
same-action induced metric pulled back along the orientation double. -/
theorem candidateANormalBoundaryInducedMetricMatrixFiberEvaluation_smooth_eq_historical
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : CutThroatBoundary period hPeriod)
    (first second : NormalBoundaryTangentIndex period hPeriod) :
    let variation := smoothToCandidateANormalBoundaryFunctionalCore
      period hPeriod metric (tensor, displacement)
    let vector := fun index =>
      (finiteSmoothThroatGeneratingFrame
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)).vectorAt
          boundary index
    candidateANormalBoundaryInducedMetricMatrixFiberEvaluation period hPeriod
        metric (variation, parameter) first second boundary =
      normalGraphInducedMetricValue period hPeriod variedMetric displacement
        parameter (orientationDoubleToThroat period hPeriod boundary)
        (mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
          (orientationDoubleToThroat period hPeriod) boundary (vector first))
        (mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
          (orientationDoubleToThroat period hPeriod) boundary
            (vector second)) := by
  dsimp only
  have hCompleted :=
    candidateANormalBoundaryInducedMetricMatrixFiberEvaluation_smooth_eq_normalGraph
      period hPeriod metric tensor variedMetric hVaried displacement parameter
        boundary first second
  rw [normalGraphInducedMetricValue_apply]
  rw [← normalGraphOrientationDouble_mfderiv_eq_comp
      period hPeriod displacement parameter boundary,
    ← normalGraphOrientationDouble_mfderiv_eq_comp
      period hPeriod displacement parameter boundary]
  simpa only [normalGraphOrientationDouble] using hCompleted

/-- Pullback to the orientation double of the historical smooth induced
metric musical map. -/
def normalBoundarySmoothGraphInducedMetricMusical
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : CutThroatBoundary period hPeriod) :
    TangentSpace throatCoverModelWithCorners boundary →L[Real]
      (TangentSpace throatCoverModelWithCorners boundary →L[Real] Real) :=
  let tangentEquiv :=
    normalBoundaryOrientationTangentEquiv period hPeriod boundary
  (tangentEquiv.toContinuousLinearMap.precomp Real).comp
    ((normalGraphInducedMetricValue period hPeriod variedMetric displacement
      parameter (orientationDoubleToThroat period hPeriod boundary)).comp
        tangentEquiv.toContinuousLinearMap)

@[simp]
theorem normalBoundarySmoothGraphInducedMetricMusical_apply
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : CutThroatBoundary period hPeriod)
    (first second : TangentSpace throatCoverModelWithCorners boundary) :
    normalBoundarySmoothGraphInducedMetricMusical period hPeriod
        variedMetric displacement parameter boundary first second =
      normalGraphInducedMetricValue period hPeriod variedMetric displacement
        parameter (orientationDoubleToThroat period hPeriod boundary)
        (normalBoundaryOrientationTangentEquiv period hPeriod boundary first)
        (normalBoundaryOrientationTangentEquiv period hPeriod boundary second) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The completed smooth induced matrix is the pulled-back historical
bilinear form on the installed finite throat generators. -/
theorem candidateANormalBoundaryInducedMetricMatrixFiberEvaluation_smooth_eq_pulledBackMusical
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : CutThroatBoundary period hPeriod)
    (first second : NormalBoundaryTangentIndex period hPeriod) :
    let variation := smoothToCandidateANormalBoundaryFunctionalCore
      period hPeriod metric (tensor, displacement)
    let vector := fun index =>
      (finiteSmoothThroatGeneratingFrame
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)).vectorAt
          boundary index
    candidateANormalBoundaryInducedMetricMatrixFiberEvaluation period hPeriod
        metric (variation, parameter) first second boundary =
      normalBoundarySmoothGraphInducedMetricMusical period hPeriod
        variedMetric displacement parameter boundary
          (vector first) (vector second) := by
  dsimp only
  rw [candidateANormalBoundaryInducedMetricMatrixFiberEvaluation_smooth_eq_historical
    period hPeriod metric tensor variedMetric hVaried displacement parameter
      boundary first second]
  rw [normalBoundarySmoothGraphInducedMetricMusical_apply]
  rw [normalBoundaryOrientationTangentEquiv_apply,
    normalBoundaryOrientationTangentEquiv_apply]

/-- Relative induced-metric endomorphism on the orientation double, using
the already installed intrinsic inverse musical map. -/
def normalBoundarySmoothGraphRelativeEndomorphism
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : CutThroatBoundary period hPeriod) :
    TangentSpace throatCoverModelWithCorners boundary →L[Real]
      TangentSpace throatCoverModelWithCorners boundary :=
  (intrinsicThroatInverseMusical
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
      boundary).toContinuousLinearMap.comp
    (normalBoundarySmoothGraphInducedMetricMusical period hPeriod
      variedMetric displacement parameter boundary)

set_option backward.isDefEq.respectTransparency false in
/-- The orientation-double tangent equivalence intertwines the completed
relative endomorphism with the historical graph endomorphism. -/
theorem normalBoundarySmoothGraphRelativeEndomorphism_intertwines
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : CutThroatBoundary period hPeriod)
    (vector : TangentSpace throatCoverModelWithCorners boundary) :
    normalBoundaryOrientationTangentEquiv period hPeriod boundary
        (normalBoundarySmoothGraphRelativeEndomorphism period hPeriod
          variedMetric displacement parameter boundary vector) =
      normalGraphRelativeEndomorphism period hPeriod variedMetric displacement
        parameter (orientationDoubleToThroat period hPeriod boundary)
        (normalBoundaryOrientationTangentEquiv period hPeriod boundary
          vector) := by
  let tangentEquiv :=
    normalBoundaryOrientationTangentEquiv period hPeriod boundary
  let sourceRelative :=
    normalBoundarySmoothGraphRelativeEndomorphism period hPeriod
      variedMetric displacement parameter boundary
  let targetPoint := orientationDoubleToThroat period hPeriod boundary
  let targetRelative := normalGraphRelativeEndomorphism period hPeriod
    variedMetric displacement parameter targetPoint
  apply (intrinsicThroatMusical period hPeriod targetPoint).injective
  apply ContinuousLinearMap.ext
  intro targetSecond
  have hMetric :=
    intrinsicSmoothNondegenerateThroatMetric_orientationDouble_natural
      period hPeriod boundary (sourceRelative vector)
        (tangentEquiv.symm targetSecond)
  calc
    intrinsicThroatMusical period hPeriod targetPoint
        (tangentEquiv (sourceRelative vector)) targetSecond =
      (intrinsicSmoothNondegenerateThroatMetric period hPeriod).1.tensor
        targetPoint (tangentEquiv (sourceRelative vector)) targetSecond := by
      rw [intrinsicThroatMusical_apply]
    _ = (intrinsicSmoothNondegenerateThroatMetric
          (doubledPeriod period)
          (doubledPeriod_ne_zero period hPeriod)).1.tensor
            boundary (sourceRelative vector)
              (tangentEquiv.symm targetSecond) := by
      simpa only [tangentEquiv, ContinuousLinearEquiv.apply_symm_apply]
        using hMetric.symm
    _ = normalBoundarySmoothGraphInducedMetricMusical period hPeriod
          variedMetric displacement parameter boundary vector
            (tangentEquiv.symm targetSecond) := by
      change intrinsicThroatMusical
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
          boundary
          (intrinsicThroatInverseMusical
            (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
            boundary
            (normalBoundarySmoothGraphInducedMetricMusical period hPeriod
              variedMetric displacement parameter boundary vector))
          (tangentEquiv.symm targetSecond) = _
      rw [intrinsicThroatMusical_inverse_apply]
    _ = normalGraphInducedMetricValue period hPeriod variedMetric displacement
          parameter targetPoint (tangentEquiv vector) targetSecond := by
      rw [normalBoundarySmoothGraphInducedMetricMusical_apply]
      simp only [tangentEquiv, targetPoint,
        ContinuousLinearEquiv.apply_symm_apply]
    _ = intrinsicThroatMusical period hPeriod targetPoint
          (targetRelative (tangentEquiv vector)) targetSecond := by
      change _ = intrinsicThroatMusical period hPeriod targetPoint
        (intrinsicThroatInverseMusical period hPeriod targetPoint
          (normalGraphInducedMetricValue period hPeriod variedMetric
            displacement parameter targetPoint (tangentEquiv vector)))
        targetSecond
      rw [intrinsicThroatMusical_inverse_apply]

set_option backward.isDefEq.respectTransparency false in
/-- Consequently the completed relative determinant is the historical
frame-free determinant at the corresponding throat point. -/
theorem normalBoundarySmoothGraphRelativeEndomorphism_det_eq_historical
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : CutThroatBoundary period hPeriod) :
    LinearMap.det
        (normalBoundarySmoothGraphRelativeEndomorphism period hPeriod
          variedMetric displacement parameter boundary).toLinearMap =
      normalGraphRelativeDeterminant period hPeriod variedMetric displacement
        parameter (orientationDoubleToThroat period hPeriod boundary) := by
  let tangentEquiv :=
    normalBoundaryOrientationTangentEquiv period hPeriod boundary
  let sourceRelative :=
    normalBoundarySmoothGraphRelativeEndomorphism period hPeriod
      variedMetric displacement parameter boundary
  let targetPoint := orientationDoubleToThroat period hPeriod boundary
  let targetRelative := normalGraphRelativeEndomorphism period hPeriod
    variedMetric displacement parameter targetPoint
  have hConjugate : targetRelative.toLinearMap =
      tangentEquiv.toLinearEquiv.toLinearMap ∘ₗ sourceRelative.toLinearMap ∘ₗ
        tangentEquiv.symm.toLinearEquiv.toLinearMap := by
    apply LinearMap.ext
    intro targetVector
    change targetRelative targetVector =
      tangentEquiv (sourceRelative (tangentEquiv.symm targetVector))
    have hIntertwines :=
      normalBoundarySmoothGraphRelativeEndomorphism_intertwines
        period hPeriod variedMetric displacement parameter boundary
          (tangentEquiv.symm targetVector)
    simpa only [tangentEquiv, sourceRelative, targetPoint, targetRelative,
      ContinuousLinearEquiv.apply_symm_apply] using hIntertwines.symm
  unfold normalGraphRelativeDeterminant
  change LinearMap.det sourceRelative.toLinearMap =
    LinearMap.det targetRelative.toLinearMap
  rw [hConjugate]
  exact (LinearMap.det_conj sourceRelative.toLinearMap
    tangentEquiv.toLinearEquiv).symm

set_option backward.isDefEq.respectTransparency false in
/-- The smooth induced matrix is the faithful finite-frame encoding of the
preceding relative endomorphism. -/
theorem candidateANormalBoundaryInducedMetricMatrixFiberEvaluation_smooth_eq_encoding
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : CutThroatBoundary period hPeriod)
    (row column : NormalBoundaryTangentIndex period hPeriod) :
    let variation := smoothToCandidateANormalBoundaryFunctionalCore
      period hPeriod metric (tensor, displacement)
    candidateANormalBoundaryInducedMetricMatrixFiberEvaluation period hPeriod
        metric (variation, parameter) row column boundary =
      intrinsicThroatFiniteFrameEndomorphismMatrixAt
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
        (finiteSmoothThroatGeneratingFrame
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
        boundary
        ((intrinsicThroatFiniteFrameOperator
            (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
            (finiteSmoothThroatGeneratingFrame
              (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
            boundary).toLinearMap.comp
          (normalBoundarySmoothGraphRelativeEndomorphism period hPeriod
            variedMetric displacement parameter boundary).toLinearMap)
        row column := by
  dsimp only
  rw [candidateANormalBoundaryInducedMetricMatrixFiberEvaluation_smooth_eq_pulledBackMusical
    period hPeriod metric tensor variedMetric hVaried displacement parameter
      boundary row column]
  unfold normalBoundarySmoothGraphRelativeEndomorphism
  calc
    _ = normalBoundarySmoothGraphInducedMetricMusical period hPeriod
          variedMetric displacement parameter boundary
          ((finiteSmoothThroatGeneratingFrame
            (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
              |>.vectorAt boundary column)
          ((finiteSmoothThroatGeneratingFrame
            (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
              |>.vectorAt boundary row) := by
      rw [normalBoundarySmoothGraphInducedMetricMusical_apply,
        normalBoundarySmoothGraphInducedMetricMusical_apply]
      exact normalGraphInducedMetricValue_symmetric period hPeriod
        variedMetric displacement parameter _ _ _
    _ = _ := (intrinsicThroatFiniteFrameEndomorphismMatrixAt_relativeMusical_apply
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
      (finiteSmoothThroatGeneratingFrame
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
      boundary
      (normalBoundarySmoothGraphInducedMetricMusical period hPeriod
        variedMetric displacement parameter boundary)
      row column).symm

end SameActionEffectiveThroatBridge

/-- At the physical base point the completed finite-frame assembly is the
ambient metric applied to the two canonical horizontal collar lifts. -/
theorem candidateANormalBoundaryInducedMetricMatrixFiberEvaluation_zero_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (boundary : OrientationBoundary period hPeriod)
    (first second : NormalBoundaryTangentIndex period hPeriod) :
    candidateANormalBoundaryInducedMetricMatrixFiberEvaluation period hPeriod
        metric 0 first second boundary =
      metric.metric.tensor.tensor
        (normalBoundaryLatitudeFiberPoint period hPeriod boundary 0)
        (normalBoundaryLatitudeHorizontalFiberLift
          period hPeriod first (boundary, 0)).2
        (normalBoundaryLatitudeHorizontalFiberLift
          period hPeriod second (boundary, 0)).2 := by
  classical
  change candidateANormalBoundaryInducedMetricMatrixFiberEvaluation period
      hPeriod metric
        ((0 : CandidateANormalBoundaryFunctionalCore period hPeriod metric), 0)
        first second boundary = _
  rw [candidateANormalBoundaryInducedMetricMatrixFiberEvaluation_apply]
  rw [show
    ((0 : CandidateANormalBoundaryFunctionalCore period hPeriod metric),
      (0 : Real)) = 0 by rfl]
  simp only [
    candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation_zero_apply,
    candidateANormalBoundaryActualMetricMatrixFiberEvaluation_zero_apply]
  have hGraph :
      normalBoundaryC2Graph period hPeriod 0 0 boundary =
        normalBoundaryLatitudeFiberPoint period hPeriod boundary 0 := by
    symm
    simpa using normalBoundaryLatitudeFiberPoint_graph
      period hPeriod 0 0 boundary
  rw [hGraph]
  simp only [regularFrameMetricMatrix_apply]
  have hFirst :=
    normalBoundaryLatitudeHorizontalRegularFrame_reconstructs
      period hPeriod metric first (boundary, 0)
  change (normalBoundaryLatitudeHorizontalFiberLift
      period hPeriod first (boundary, 0)).2 =
    ∑ row : Fin 4,
      normalBoundaryLatitudeHorizontalRegularFrameCoefficient
          period hPeriod metric first row (boundary, 0) •
        metric.frame row
          (normalBoundaryLatitudeFiberPoint
            period hPeriod boundary 0) at hFirst
  have hSecond :=
    normalBoundaryLatitudeHorizontalRegularFrame_reconstructs
      period hPeriod metric second (boundary, 0)
  change (normalBoundaryLatitudeHorizontalFiberLift
      period hPeriod second (boundary, 0)).2 =
    ∑ column : Fin 4,
      normalBoundaryLatitudeHorizontalRegularFrameCoefficient
          period hPeriod metric second column (boundary, 0) •
        metric.frame column
          (normalBoundaryLatitudeFiberPoint
            period hPeriod boundary 0) at hSecond
  rw [hFirst]
  simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro row _
  rw [hSecond]
  simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, Finset.mul_sum,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro column _
  ring

attribute [-instance] orientationBoundaryMetricSpace
    orientationBoundaryChartedSpace in
/-- Pullback of the existing physical throat trace to the orientation double
through its already proved tangent equivalence. -/
def normalBoundaryBaseInducedMetricMusical
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (boundary : OrientationBoundary period hPeriod) :
    TangentSpace throatCoverModelWithCorners boundary →L[Real]
      (TangentSpace throatCoverModelWithCorners boundary →L[Real] Real) :=
  let tangentEquiv :=
    normalBoundaryOrientationTangentEquiv period hPeriod boundary
  (tangentEquiv.toContinuousLinearMap.precomp Real).comp
    ((generalLorentzMetricThroatTraceValue period hPeriod metric.metric
      (orientationDoubleToThroat period hPeriod boundary)).comp
        tangentEquiv.toContinuousLinearMap)

attribute [-instance] orientationBoundaryMetricSpace
    orientationBoundaryChartedSpace in
@[simp]
theorem normalBoundaryBaseInducedMetricMusical_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (boundary : OrientationBoundary period hPeriod)
    (first second : TangentSpace throatCoverModelWithCorners boundary) :
    normalBoundaryBaseInducedMetricMusical period hPeriod metric boundary
        first second =
      generalLorentzMetricThroatTraceValue period hPeriod metric.metric
        (orientationDoubleToThroat period hPeriod boundary)
        (normalBoundaryOrientationTangentEquiv period hPeriod boundary first)
        (normalBoundaryOrientationTangentEquiv period hPeriod boundary
          second) :=
  rfl

attribute [-instance] orientationBoundaryMetricSpace
    orientationBoundaryChartedSpace in
theorem normalBoundaryBaseInducedMetricMusical_symmetric
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (boundary : OrientationBoundary period hPeriod)
    (first second : TangentSpace throatCoverModelWithCorners boundary) :
    normalBoundaryBaseInducedMetricMusical period hPeriod metric boundary
        first second =
      normalBoundaryBaseInducedMetricMusical period hPeriod metric boundary
        second first := by
  rw [normalBoundaryBaseInducedMetricMusical_apply,
    normalBoundaryBaseInducedMetricMusical_apply]
  exact generalLorentzMetricThroatTraceValue_symmetric period hPeriod
    metric.metric _ _ _

attribute [-instance] orientationBoundaryMetricSpace
    orientationBoundaryChartedSpace in
/-- The finite induced matrix at the physical base is exactly the pullback
of the pre-existing general-Lorentz throat trace. -/
theorem candidateANormalBoundaryInducedMetricMatrixFiberEvaluation_zero_eq_trace
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (boundary : OrientationBoundary period hPeriod)
    (first second : NormalBoundaryTangentIndex period hPeriod) :
    candidateANormalBoundaryInducedMetricMatrixFiberEvaluation period hPeriod
        metric 0 first second boundary =
      normalBoundaryBaseInducedMetricMusical period hPeriod metric boundary
        ((finiteSmoothThroatGeneratingFrame
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
            |>.vectorAt boundary first)
        ((finiteSmoothThroatGeneratingFrame
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
            |>.vectorAt boundary second) := by
  rw [candidateANormalBoundaryInducedMetricMatrixFiberEvaluation_zero_apply,
    normalBoundaryBaseInducedMetricMusical_apply,
    generalLorentzMetricThroatTraceValue_apply,
    normalBoundaryLatitudeFiberPoint_zero]
  rw [normalBoundaryLatitudeHorizontalFiberLift_zero_eq_fixedThroat
      period hPeriod first boundary,
    normalBoundaryLatitudeHorizontalFiberLift_zero_eq_fixedThroat
      period hPeriod second boundary]
  rfl

attribute [-instance] orientationBoundaryMetricSpace
    orientationBoundaryChartedSpace in
/-- Existing throat transversality makes the pulled-back base metric
nondegenerate; no new regularity datum is introduced. -/
theorem normalBoundaryBaseInducedMetricMusical_injective
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric)
    (boundary : OrientationBoundary period hPeriod) :
    Function.Injective
      (normalBoundaryBaseInducedMetricMusical period hPeriod metric
        boundary) := by
  let tangentEquiv :=
    normalBoundaryOrientationTangentEquiv period hPeriod boundary
  have hTrace :=
    ((throatTrace_nondegenerate_iff_no_tangential_radical
      period hPeriod metric.metric).2 hTransverse)
      (orientationDoubleToThroat period hPeriod boundary)
  change Function.Injective
    (generalLorentzMetricThroatTraceValue period hPeriod metric.metric
      (orientationDoubleToThroat period hPeriod boundary)) at hTrace
  intro first second hEqual
  apply tangentEquiv.injective
  apply hTrace
  apply ContinuousLinearMap.ext
  intro tangent
  have hApplied := congrArg
    (fun covector => covector (tangentEquiv.symm tangent)) hEqual
  simpa only [normalBoundaryBaseInducedMetricMusical_apply,
    tangentEquiv, ContinuousLinearEquiv.apply_symm_apply] using hApplied

attribute [-instance] orientationBoundaryMetricSpace
    orientationBoundaryChartedSpace in
/-- Relative endomorphism of the physical base metric with respect to the
already installed intrinsic metric on the orientation double. -/
def normalBoundaryBaseRelativeEndomorphism
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (boundary : OrientationBoundary period hPeriod) :
    TangentSpace throatCoverModelWithCorners boundary →L[Real]
      TangentSpace throatCoverModelWithCorners boundary :=
  (intrinsicThroatInverseMusical
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
      boundary).toContinuousLinearMap.comp
    (normalBoundaryBaseInducedMetricMusical period hPeriod metric boundary)

attribute [-instance] orientationBoundaryMetricSpace
    orientationBoundaryChartedSpace in
@[simp]
theorem normalBoundaryBaseRelativeEndomorphism_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (boundary : OrientationBoundary period hPeriod)
    (vector : TangentSpace throatCoverModelWithCorners boundary) :
    normalBoundaryBaseRelativeEndomorphism period hPeriod metric boundary
        vector =
      intrinsicThroatInverseMusical
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
        boundary
        (normalBoundaryBaseInducedMetricMusical period hPeriod metric boundary
          vector) :=
  rfl

attribute [-instance] orientationBoundaryMetricSpace
    orientationBoundaryChartedSpace in
theorem normalBoundaryBaseRelativeEndomorphism_injective
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric)
    (boundary : OrientationBoundary period hPeriod) :
    Function.Injective
      (normalBoundaryBaseRelativeEndomorphism period hPeriod metric
        boundary) := by
  intro first second hEqual
  apply normalBoundaryBaseInducedMetricMusical_injective
    period hPeriod metric hTransverse boundary
  exact (intrinsicThroatInverseMusical
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
    boundary).injective hEqual

attribute [-instance] orientationBoundaryMetricSpace
    orientationBoundaryChartedSpace in
theorem normalBoundaryBaseRelativeEndomorphism_det_ne_zero
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric)
    (boundary : OrientationBoundary period hPeriod) :
    LinearMap.det
      (normalBoundaryBaseRelativeEndomorphism period hPeriod metric boundary
        |>.toLinearMap) ≠ 0 := by
  letI : FiniteDimensional Real
      (TangentSpace throatCoverModelWithCorners boundary) := by
    change FiniteDimensional Real ThroatCoverCoordinates
    infer_instance
  intro hDet
  have hKer : LinearMap.ker
      (normalBoundaryBaseRelativeEndomorphism period hPeriod metric boundary
        |>.toLinearMap) ≠ ⊥ :=
    (LinearMap.det_eq_zero_iff_ker_ne_bot).1 hDet
  exact hKer (LinearMap.ker_eq_bot.mpr
    (normalBoundaryBaseRelativeEndomorphism_injective
      period hPeriod metric hTransverse boundary))

/-! ### Faithful inverse on the redundant throat frame -/

/-- Fixed coefficient matrix implementing the reference inverse musical map
between the canonical redundant coefficient covectors. -/
def normalBoundaryReferenceDualCoefficientMatrix
    (row column : NormalBoundaryTangentIndex period hPeriod) :
    BoundedContinuousFunction (OrientationBoundary period hPeriod) Real := by
  let frame := finiteSmoothThroatGeneratingFrame
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
  let columnVector := smoothThroatFrameVectorSection
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
    frame column
  let solved := intrinsicThroatFiniteFrameSolve
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
    frame columnVector
  let coefficient := intrinsicThroatFiniteFrameCoefficient
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
    frame solved row
  exact BoundedContinuousFunction.mkOfCompact
    { toFun := coefficient.toFun
      continuous_toFun := coefficient.contMDiff_toFun.continuous }

@[simp]
theorem normalBoundaryReferenceDualCoefficientMatrix_apply
    (row column : NormalBoundaryTangentIndex period hPeriod)
    (boundary : OrientationBoundary period hPeriod) :
    normalBoundaryReferenceDualCoefficientMatrix
        period hPeriod row column boundary =
      intrinsicThroatFiniteFrameCoefficientAt
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
        (finiteSmoothThroatGeneratingFrame
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
        boundary row
        ((intrinsicThroatFiniteFrameOperator
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
          (finiteSmoothThroatGeneratingFrame
            (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
          boundary).inverse
            ((finiteSmoothThroatGeneratingFrame
              (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
              |>.vectorAt boundary column)) :=
  rfl

/-- Coefficient projector of the existing redundant throat frame. -/
def normalBoundaryReferenceProjectorMatrix
    (row column : NormalBoundaryTangentIndex period hPeriod) :
    BoundedContinuousFunction (OrientationBoundary period hPeriod) Real := by
  let frame := finiteSmoothThroatGeneratingFrame
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
  let columnVector := smoothThroatFrameVectorSection
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
    frame column
  let coefficient := intrinsicThroatFiniteFrameCoefficient
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
    frame columnVector row
  exact BoundedContinuousFunction.mkOfCompact
    { toFun := coefficient.toFun
      continuous_toFun := coefficient.contMDiff_toFun.continuous }

@[simp]
theorem normalBoundaryReferenceProjectorMatrix_apply
    (row column : NormalBoundaryTangentIndex period hPeriod)
    (boundary : OrientationBoundary period hPeriod) :
    normalBoundaryReferenceProjectorMatrix
        period hPeriod row column boundary =
      intrinsicThroatFiniteFrameCoefficientAt
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
        (finiteSmoothThroatGeneratingFrame
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
        boundary row
        ((finiteSmoothThroatGeneratingFrame
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
          |>.vectorAt boundary column) :=
  rfl

theorem normalBoundaryReferenceProjectorMatrix_apply_eq_finiteFrameProjector
    (row column : NormalBoundaryTangentIndex period hPeriod)
    (boundary : OrientationBoundary period hPeriod) :
    normalBoundaryReferenceProjectorMatrix period hPeriod row column boundary =
      intrinsicThroatFiniteFrameProjectorMatrixAt
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
        (finiteSmoothThroatGeneratingFrame
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
        boundary row column := by
  unfold intrinsicThroatFiniteFrameProjectorMatrixAt
  rw [intrinsicThroatFiniteFrameEndomorphismMatrixAt_apply]
  rfl

/-- The fixed dual coefficient matrix is the faithful finite-frame encoding
of the inverse reference frame operator. -/
theorem normalBoundaryReferenceDualCoefficientMatrix_apply_eq_encoding_inverse
    (row column : NormalBoundaryTangentIndex period hPeriod)
    (boundary : OrientationBoundary period hPeriod) :
    normalBoundaryReferenceDualCoefficientMatrix
        period hPeriod row column boundary =
      intrinsicThroatFiniteFrameEndomorphismMatrixAt
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
        (finiteSmoothThroatGeneratingFrame
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
        boundary
        ((intrinsicThroatFiniteFrameOperator
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
          (finiteSmoothThroatGeneratingFrame
            (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
          boundary).inverse.toLinearMap)
        row column := by
  rw [intrinsicThroatFiniteFrameEndomorphismMatrixAt_apply]
  rfl

attribute [-instance] orientationBoundaryMetricSpace
    orientationBoundaryChartedSpace in
/-- At the physical base, the induced matrix is the faithful encoding of the
reference frame operator followed by the relative metric endomorphism. -/
theorem candidateANormalBoundaryInducedMetricMatrixFiberEvaluation_zero_eq_encoding
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (boundary : OrientationBoundary period hPeriod)
    (row column : NormalBoundaryTangentIndex period hPeriod) :
    candidateANormalBoundaryInducedMetricMatrixFiberEvaluation period hPeriod
        metric 0 row column boundary =
      intrinsicThroatFiniteFrameEndomorphismMatrixAt
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
        (finiteSmoothThroatGeneratingFrame
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
        boundary
        ((intrinsicThroatFiniteFrameOperator
            (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
            (finiteSmoothThroatGeneratingFrame
              (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
            boundary).toLinearMap.comp
          (normalBoundaryBaseRelativeEndomorphism
            period hPeriod metric boundary).toLinearMap)
        row column := by
  rw [candidateANormalBoundaryInducedMetricMatrixFiberEvaluation_zero_eq_trace]
  unfold normalBoundaryBaseRelativeEndomorphism
  calc
    _ = normalBoundaryBaseInducedMetricMusical period hPeriod metric boundary
          ((finiteSmoothThroatGeneratingFrame
            (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
              |>.vectorAt boundary column)
          ((finiteSmoothThroatGeneratingFrame
            (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
              |>.vectorAt boundary row) :=
      normalBoundaryBaseInducedMetricMusical_symmetric
        period hPeriod metric boundary _ _
    _ = _ := (intrinsicThroatFiniteFrameEndomorphismMatrixAt_relativeMusical_apply
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
      (finiteSmoothThroatGeneratingFrame
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
      boundary
      (normalBoundaryBaseInducedMetricMusical period hPeriod metric boundary)
      row column).symm

/-- Ordinary finite matrix multiplication, disambiguated from pointwise
multiplication of the underlying function type. -/
def normalBoundaryRealMatrixMul
    (first second : Matrix (NormalBoundaryTangentIndex period hPeriod)
      (NormalBoundaryTangentIndex period hPeriod) Real) :
    Matrix (NormalBoundaryTangentIndex period hPeriod)
      (NormalBoundaryTangentIndex period hPeriod) Real :=
  @HMul.hMul _ _ _ Matrix.instHMulOfFintypeOfMulOfAddCommMonoid first second

theorem candidateANormalBoundaryMatrixFieldEvaluationRingHom_mapMatrix_mul
    (boundary : OrientationBoundary period hPeriod)
    (first second : CandidateANormalBoundaryInducedMetricMatrixField
      period hPeriod) :
    (candidateANormalBoundaryMatrixFieldEvaluationRingHom
        period hPeriod boundary).mapMatrix (first * second) =
      normalBoundaryRealMatrixMul period hPeriod
        (fun row column => first row column boundary)
        (fun row column => second row column boundary) := by
  rw [map_mul]
  rfl

theorem candidateANormalBoundaryMatrixFieldEvaluationRingHom_mapMatrix_mul_cut
    (boundary : CutThroatBoundary period hPeriod)
    (first second : CandidateANormalBoundaryInducedMetricMatrixField
      period hPeriod) :
    (candidateANormalBoundaryMatrixFieldEvaluationRingHom
        period hPeriod boundary).mapMatrix (first * second) =
      normalBoundaryRealMatrixMul period hPeriod
        (fun row column => first row column boundary)
        (fun row column => second row column boundary) :=
  candidateANormalBoundaryMatrixFieldEvaluationRingHom_mapMatrix_mul
    period hPeriod boundary first second

attribute [-instance] orientationBoundaryMetricSpace
    orientationBoundaryChartedSpace in
/-- At the physical base, the fixed dual coefficients cancel the reference
frame operator and leave precisely the relative metric endomorphism. -/
theorem normalBoundaryReferenceDual_mul_inducedMetric_zero
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (boundary : OrientationBoundary period hPeriod) :
    normalBoundaryRealMatrixMul period hPeriod
      ((fun row column =>
        normalBoundaryReferenceDualCoefficientMatrix
          period hPeriod row column boundary) :
        Matrix (NormalBoundaryTangentIndex period hPeriod)
          (NormalBoundaryTangentIndex period hPeriod) Real)
      ((fun row column =>
        candidateANormalBoundaryInducedMetricMatrixFiberEvaluation
          period hPeriod metric 0 row column boundary) :
        Matrix (NormalBoundaryTangentIndex period hPeriod)
          (NormalBoundaryTangentIndex period hPeriod) Real) =
      intrinsicThroatFiniteFrameEndomorphismMatrixAt
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
        (finiteSmoothThroatGeneratingFrame
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
        boundary
        (normalBoundaryBaseRelativeEndomorphism
          period hPeriod metric boundary).toLinearMap := by
  have hDual :
      (fun row column =>
          normalBoundaryReferenceDualCoefficientMatrix
            period hPeriod row column boundary) =
        intrinsicThroatFiniteFrameEndomorphismMatrixAt
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
          (finiteSmoothThroatGeneratingFrame
            (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
          boundary
          ((intrinsicThroatFiniteFrameOperator
            (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
            (finiteSmoothThroatGeneratingFrame
              (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
            boundary).inverse.toLinearMap) := by
    ext row column
    exact normalBoundaryReferenceDualCoefficientMatrix_apply_eq_encoding_inverse
      period hPeriod row column boundary
  have hMetric :
      (fun row column =>
          candidateANormalBoundaryInducedMetricMatrixFiberEvaluation
            period hPeriod metric 0 row column boundary) =
        intrinsicThroatFiniteFrameEndomorphismMatrixAt
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
          (finiteSmoothThroatGeneratingFrame
            (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
          boundary
          ((intrinsicThroatFiniteFrameOperator
              (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
              (finiteSmoothThroatGeneratingFrame
                (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
              boundary).toLinearMap.comp
            (normalBoundaryBaseRelativeEndomorphism
              period hPeriod metric boundary).toLinearMap) := by
    ext row column
    exact candidateANormalBoundaryInducedMetricMatrixFiberEvaluation_zero_eq_encoding
      period hPeriod metric boundary row column
  rw [hDual, hMetric]
  unfold normalBoundaryRealMatrixMul
  exact intrinsicThroatFiniteFrameEncoding_inverse_mul_operator_comp
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
    (finiteSmoothThroatGeneratingFrame
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
    boundary
    (normalBoundaryBaseRelativeEndomorphism
      period hPeriod metric boundary).toLinearMap

/-- Faithful identity extension of the induced-metric endomorphism relative
to the fixed intrinsic throat metric. -/
def candidateANormalBoundaryInducedRelativeLiftFiberEvaluation
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) :
    CandidateANormalBoundaryInducedMetricMatrixField period hPeriod :=
  fun row column =>
    (1 : CandidateANormalBoundaryInducedMetricMatrixField period hPeriod)
        row column -
      normalBoundaryReferenceProjectorMatrix
        period hPeriod row column +
      ∑ middle : NormalBoundaryTangentIndex period hPeriod,
        normalBoundaryReferenceDualCoefficientMatrix period hPeriod row middle *
          candidateANormalBoundaryInducedMetricMatrixFiberEvaluation
            period hPeriod metric current middle column

attribute [-instance] orientationBoundaryMetricSpace
    orientationBoundaryChartedSpace in
/-- The faithful candidate lift at the physical base is exactly the existing
finite-frame lift of the physical relative metric endomorphism. -/
theorem candidateANormalBoundaryInducedRelativeLiftFiberEvaluation_zero_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (boundary : OrientationBoundary period hPeriod)
    (row column : NormalBoundaryTangentIndex period hPeriod) :
    candidateANormalBoundaryInducedRelativeLiftFiberEvaluation
        period hPeriod metric 0 row column boundary =
      intrinsicThroatFiniteFrameLiftAt
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
        (finiteSmoothThroatGeneratingFrame
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
        boundary
        (normalBoundaryBaseRelativeEndomorphism
          period hPeriod metric boundary).toLinearMap
        row column := by
  classical
  have hProduct := congrArg
    (fun matrix : Matrix (NormalBoundaryTangentIndex period hPeriod)
        (NormalBoundaryTangentIndex period hPeriod) Real => matrix row column)
    (normalBoundaryReferenceDual_mul_inducedMetric_zero
      period hPeriod metric boundary)
  have hProductEntry :
      (∑ middle : NormalBoundaryTangentIndex period hPeriod,
        normalBoundaryReferenceDualCoefficientMatrix
            period hPeriod row middle boundary *
          candidateANormalBoundaryInducedMetricMatrixFiberEvaluation
            period hPeriod metric 0 middle column boundary) =
        intrinsicThroatFiniteFrameEndomorphismMatrixAt
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
          (finiteSmoothThroatGeneratingFrame
            (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
          boundary
          (normalBoundaryBaseRelativeEndomorphism
            period hPeriod metric boundary).toLinearMap row column := by
    simpa [normalBoundaryRealMatrixMul, Matrix.mul_apply] using hProduct
  unfold candidateANormalBoundaryInducedRelativeLiftFiberEvaluation
    intrinsicThroatFiniteFrameLiftAt redundantFiniteFrameLift
  simp only [BoundedContinuousFunction.add_apply,
    BoundedContinuousFunction.sub_apply, BoundedContinuousFunction.mul_apply,
    BoundedContinuousFunction.sum_apply, Matrix.add_apply, Matrix.sub_apply,
    Matrix.one_apply, BoundedContinuousFunction.coe_one,
    BoundedContinuousFunction.coe_zero, Pi.one_apply]
  rw [normalBoundaryReferenceProjectorMatrix_apply_eq_finiteFrameProjector,
    hProductEntry]
  unfold intrinsicThroatFiniteFrameProjectorMatrixAt
    intrinsicThroatFiniteFrameEndomorphismMatrixAt
  split_ifs <;> simp

theorem
    candidateANormalBoundaryInducedRelativeLiftFiberEvaluation_contDiff_two
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    ContDiff Real 2
      (candidateANormalBoundaryInducedRelativeLiftFiberEvaluation
        period hPeriod metric) := by
  have hInduced :=
    candidateANormalBoundaryInducedMetricMatrixFiberEvaluation_contDiff_two
      period hPeriod metric
  change @ContDiff Real _
    (Prod (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real)
    _ _
    (NormalBoundaryTangentIndex period hPeriod →
      NormalBoundaryTangentIndex period hPeriod →
      BoundedContinuousFunction (OrientationBoundary period hPeriod) Real)
    Pi.normedAddCommGroup Pi.normedSpace 2
    (candidateANormalBoundaryInducedRelativeLiftFiberEvaluation
      period hPeriod metric)
  rw [contDiff_pi]
  intro row
  rw [contDiff_pi]
  intro column
  unfold candidateANormalBoundaryInducedRelativeLiftFiberEvaluation
  exact (contDiff_const.sub contDiff_const).add (ContDiff.sum fun middle _ =>
    contDiff_const.mul
      (contDiff_pi.mp (contDiff_pi.mp hInduced middle) column))

set_option backward.isDefEq.respectTransparency false in
/-- On the smooth core, the completed relative lift is exactly the existing
faithful intrinsic lift of the pulled-back historical endomorphism. -/
theorem candidateANormalBoundaryInducedRelativeLiftFiberEvaluation_smooth_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : CutThroatBoundary period hPeriod)
    (row column : NormalBoundaryTangentIndex period hPeriod) :
    let variation := smoothToCandidateANormalBoundaryFunctionalCore
      period hPeriod metric (tensor, displacement)
    candidateANormalBoundaryInducedRelativeLiftFiberEvaluation period hPeriod
        metric (variation, parameter) row column boundary =
      intrinsicThroatFiniteFrameLiftAt
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
        (finiteSmoothThroatGeneratingFrame
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
        boundary
        (normalBoundarySmoothGraphRelativeEndomorphism period hPeriod
          variedMetric displacement parameter boundary).toLinearMap
        row column := by
  dsimp only
  classical
  let frame := finiteSmoothThroatGeneratingFrame
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
  let relative := normalBoundarySmoothGraphRelativeEndomorphism
    period hPeriod variedMetric displacement parameter boundary
  have hDual :
      (fun first second =>
          normalBoundaryReferenceDualCoefficientMatrix
            period hPeriod first second boundary) =
        intrinsicThroatFiniteFrameEndomorphismMatrixAt
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
          frame boundary
          ((intrinsicThroatFiniteFrameOperator
            (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
            frame boundary).inverse.toLinearMap) := by
    ext first second
    exact normalBoundaryReferenceDualCoefficientMatrix_apply_eq_encoding_inverse
      period hPeriod first second boundary
  have hMetric :
      (fun first second =>
          candidateANormalBoundaryInducedMetricMatrixFiberEvaluation
            period hPeriod metric
              (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod
                metric (tensor, displacement), parameter)
              first second boundary) =
        intrinsicThroatFiniteFrameEndomorphismMatrixAt
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
          frame boundary
          ((intrinsicThroatFiniteFrameOperator
              (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
              frame boundary).toLinearMap.comp relative.toLinearMap) := by
    ext first second
    exact candidateANormalBoundaryInducedMetricMatrixFiberEvaluation_smooth_eq_encoding
      period hPeriod metric tensor variedMetric hVaried displacement parameter
        boundary first second
  have hProduct :=
    intrinsicThroatFiniteFrameEncoding_inverse_mul_operator_comp
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
      frame boundary relative.toLinearMap
  rw [← hDual, ← hMetric] at hProduct
  have hProductEntry := congrArg
    (fun matrix : Matrix (NormalBoundaryTangentIndex period hPeriod)
        (NormalBoundaryTangentIndex period hPeriod) Real =>
      matrix row column) hProduct
  have hEntry :
      (∑ middle : NormalBoundaryTangentIndex period hPeriod,
        normalBoundaryReferenceDualCoefficientMatrix
            period hPeriod row middle boundary *
          candidateANormalBoundaryInducedMetricMatrixFiberEvaluation
            period hPeriod metric
              (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod
                metric (tensor, displacement), parameter)
              middle column boundary) =
        intrinsicThroatFiniteFrameEndomorphismMatrixAt
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
          frame boundary relative.toLinearMap row column := by
    simpa [Matrix.mul_apply] using hProductEntry
  unfold candidateANormalBoundaryInducedRelativeLiftFiberEvaluation
    intrinsicThroatFiniteFrameLiftAt redundantFiniteFrameLift
  simp only [BoundedContinuousFunction.add_apply,
    BoundedContinuousFunction.sub_apply, BoundedContinuousFunction.mul_apply,
    BoundedContinuousFunction.sum_apply, Matrix.add_apply, Matrix.sub_apply,
    Matrix.one_apply, BoundedContinuousFunction.coe_one,
    BoundedContinuousFunction.coe_zero, Pi.one_apply]
  rw [normalBoundaryReferenceProjectorMatrix_apply_eq_finiteFrameProjector,
    hEntry]
  unfold intrinsicThroatFiniteFrameProjectorMatrixAt
    intrinsicThroatFiniteFrameEndomorphismMatrixAt
  dsimp only [frame, relative]
  split_ifs <;> simp

/-- Determinant polynomial of the faithfully lifted induced metric. -/
def candidateANormalBoundaryInducedRelativeLiftDeterminant
    (matrix : CandidateANormalBoundaryInducedMetricMatrixField period hPeriod) :
    BoundedContinuousFunction (OrientationBoundary period hPeriod) Real :=
  Matrix.det matrix

theorem candidateANormalBoundaryInducedRelativeLiftDeterminant_contDiff :
    ContDiff Real ∞
      (candidateANormalBoundaryInducedRelativeLiftDeterminant
        period hPeriod) := by
  classical
  change ContDiff Real ∞
    (fun matrix : CandidateANormalBoundaryInducedMetricMatrixField
        period hPeriod => Matrix.det matrix)
  simp_rw [Matrix.det_apply']
  apply ContDiff.sum
  intro permutation _
  apply contDiff_const.mul
  apply contDiff_prod
  intro index _
  exact contDiff_apply_apply Real
    (BoundedContinuousFunction (OrientationBoundary period hPeriod) Real)
    (permutation index) index

/-- Determinant of the relative lift along the completed graph. -/
def candidateANormalBoundaryInducedRelativeLiftDeterminantFiberEvaluation
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) :
    BoundedContinuousFunction (OrientationBoundary period hPeriod) Real :=
  candidateANormalBoundaryInducedRelativeLiftDeterminant period hPeriod
    (candidateANormalBoundaryInducedRelativeLiftFiberEvaluation
      period hPeriod metric current)

set_option backward.isDefEq.respectTransparency false in
/-- The determinant of the completed smooth lift is the intrinsic determinant
of the pulled-back historical relative endomorphism. -/
theorem candidateANormalBoundaryInducedRelativeLiftDeterminantFiberEvaluation_smooth_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : CutThroatBoundary period hPeriod) :
    let variation := smoothToCandidateANormalBoundaryFunctionalCore
      period hPeriod metric (tensor, displacement)
    candidateANormalBoundaryInducedRelativeLiftDeterminantFiberEvaluation
        period hPeriod metric (variation, parameter) boundary =
      LinearMap.det
        (normalBoundarySmoothGraphRelativeEndomorphism period hPeriod
          variedMetric displacement parameter boundary).toLinearMap := by
  dsimp only
  have hMap :=
    (candidateANormalBoundaryMatrixFieldEvaluationRingHom
      period hPeriod boundary).map_det
        (candidateANormalBoundaryInducedRelativeLiftFiberEvaluation
          period hPeriod metric
            (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod
              metric (tensor, displacement), parameter))
  change
    (Matrix.det
      (candidateANormalBoundaryInducedRelativeLiftFiberEvaluation
        period hPeriod metric
          (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod
            metric (tensor, displacement), parameter))) boundary = _
  calc
    _ = Matrix.det (fun row column =>
        candidateANormalBoundaryInducedRelativeLiftFiberEvaluation
          period hPeriod metric
            (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod
              metric (tensor, displacement), parameter)
            row column boundary) := hMap
    _ = Matrix.det
        (intrinsicThroatFiniteFrameLiftAt
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
          (finiteSmoothThroatGeneratingFrame
            (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
          boundary
          (normalBoundarySmoothGraphRelativeEndomorphism period hPeriod
            variedMetric displacement parameter boundary).toLinearMap) := by
      congr 1
      funext row column
      exact candidateANormalBoundaryInducedRelativeLiftFiberEvaluation_smooth_apply
        period hPeriod metric tensor variedMetric hVaried displacement
          parameter boundary row column
    _ = _ := intrinsicThroatFiniteFrameLiftAt_det
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
      (finiteSmoothThroatGeneratingFrame
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
      boundary
      (normalBoundarySmoothGraphRelativeEndomorphism period hPeriod
        variedMetric displacement parameter boundary).toLinearMap

set_option backward.isDefEq.respectTransparency false in
/-- The completed smooth relative-lift determinant is exactly the historical
frame-free graph determinant at the corresponding throat point. -/
theorem candidateANormalBoundaryInducedRelativeLiftDeterminantFiberEvaluation_smooth_eq_historical
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : CutThroatBoundary period hPeriod) :
    let variation := smoothToCandidateANormalBoundaryFunctionalCore
      period hPeriod metric (tensor, displacement)
    candidateANormalBoundaryInducedRelativeLiftDeterminantFiberEvaluation
        period hPeriod metric (variation, parameter) boundary =
      normalGraphRelativeDeterminant period hPeriod variedMetric displacement
        parameter (orientationDoubleToThroat period hPeriod boundary) := by
  dsimp only
  rw [candidateANormalBoundaryInducedRelativeLiftDeterminantFiberEvaluation_smooth_apply
    period hPeriod metric tensor variedMetric hVaried displacement parameter
      boundary]
  exact
    normalBoundarySmoothGraphRelativeEndomorphism_det_eq_historical
      period hPeriod variedMetric displacement parameter boundary

attribute [-instance] orientationBoundaryMetricSpace
    orientationBoundaryChartedSpace in
/-- The determinant of the physical base lift is the determinant of the
physical relative metric endomorphism. -/
theorem
    candidateANormalBoundaryInducedRelativeLiftDeterminantFiberEvaluation_zero_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (boundary : OrientationBoundary period hPeriod) :
    candidateANormalBoundaryInducedRelativeLiftDeterminantFiberEvaluation
        period hPeriod metric 0 boundary =
      LinearMap.det
        (normalBoundaryBaseRelativeEndomorphism
          period hPeriod metric boundary).toLinearMap := by
  have hMap :=
    (candidateANormalBoundaryMatrixFieldEvaluationRingHom
      period hPeriod boundary).map_det
        (candidateANormalBoundaryInducedRelativeLiftFiberEvaluation
          period hPeriod metric 0)
  change
    (Matrix.det
      (candidateANormalBoundaryInducedRelativeLiftFiberEvaluation
        period hPeriod metric 0)) boundary =
      Matrix.det (fun row column =>
        candidateANormalBoundaryInducedRelativeLiftFiberEvaluation
          period hPeriod metric 0 row column boundary) at hMap
  change
    (Matrix.det
      (candidateANormalBoundaryInducedRelativeLiftFiberEvaluation
        period hPeriod metric 0)) boundary = _
  calc
    _ = Matrix.det (fun row column =>
        candidateANormalBoundaryInducedRelativeLiftFiberEvaluation
          period hPeriod metric 0 row column boundary) := hMap
    _ = Matrix.det
        (intrinsicThroatFiniteFrameLiftAt
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
          (finiteSmoothThroatGeneratingFrame
            (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
          boundary
          (normalBoundaryBaseRelativeEndomorphism
            period hPeriod metric boundary).toLinearMap) := by
      congr 1
      funext row column
      exact candidateANormalBoundaryInducedRelativeLiftFiberEvaluation_zero_apply
        period hPeriod metric boundary row column
    _ = _ := intrinsicThroatFiniteFrameLiftAt_det
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
      (finiteSmoothThroatGeneratingFrame
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
      boundary
      (normalBoundaryBaseRelativeEndomorphism
        period hPeriod metric boundary).toLinearMap

attribute [-instance] orientationBoundaryMetricSpace
    orientationBoundaryChartedSpace in
theorem
    candidateANormalBoundaryInducedRelativeLiftDeterminantFiberEvaluation_zero_ne_zero
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric)
    (boundary : OrientationBoundary period hPeriod) :
    candidateANormalBoundaryInducedRelativeLiftDeterminantFiberEvaluation
        period hPeriod metric 0 boundary ≠ 0 := by
  rw [candidateANormalBoundaryInducedRelativeLiftDeterminantFiberEvaluation_zero_apply]
  exact normalBoundaryBaseRelativeEndomorphism_det_ne_zero
    period hPeriod metric hTransverse boundary

private theorem boundedContinuousFunction_isUnit_of_forall_ne_zero
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (function : BoundedContinuousFunction X Real)
    (hNonzero : ∀ point, function point ≠ 0) :
    IsUnit function := by
  let inverse : BoundedContinuousFunction X Real :=
    BoundedContinuousFunction.mkOfCompact
      { toFun := fun point => (function point)⁻¹
        continuous_toFun := function.continuous.inv₀ hNonzero }
  refine ⟨{
    val := function
    inv := inverse
    val_inv := ?_
    inv_val := ?_ }, rfl⟩
  · ext point
    simp [inverse, hNonzero point]
  · ext point
    simp [inverse, hNonzero point]

theorem
    candidateANormalBoundaryInducedRelativeLiftDeterminantFiberEvaluation_contDiff_two
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    ContDiff Real 2
      (candidateANormalBoundaryInducedRelativeLiftDeterminantFiberEvaluation
        period hPeriod metric) := by
  have hDet : ContDiff Real 2
      (candidateANormalBoundaryInducedRelativeLiftDeterminant
        period hPeriod) :=
    (candidateANormalBoundaryInducedRelativeLiftDeterminant_contDiff
      period hPeriod).of_le
        (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  exact hDet.comp
    (candidateANormalBoundaryInducedRelativeLiftFiberEvaluation_contDiff_two
      period hPeriod metric)

/-- Natural open domain where the determinant of the faithful lift is a
unit. -/
def candidateANormalBoundaryInducedMetricDomain
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    Set (Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) :=
  {current | IsUnit
    (candidateANormalBoundaryInducedRelativeLiftDeterminantFiberEvaluation
      period hPeriod metric current)}

/-- Existing throat transversality places the physical base point in the
natural inverse-metric domain. -/
theorem zero_mem_candidateANormalBoundaryInducedMetricDomain
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric) :
    (0 : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) ∈
      candidateANormalBoundaryInducedMetricDomain period hPeriod metric := by
  change IsUnit
    (candidateANormalBoundaryInducedRelativeLiftDeterminantFiberEvaluation
      period hPeriod metric 0)
  apply boundedContinuousFunction_isUnit_of_forall_ne_zero
  intro boundary
  exact
    candidateANormalBoundaryInducedRelativeLiftDeterminantFiberEvaluation_zero_ne_zero
      period hPeriod metric hTransverse boundary

theorem candidateANormalBoundaryInducedMetricDomain_isOpen
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    IsOpen (candidateANormalBoundaryInducedMetricDomain
      period hPeriod metric) := by
  exact Units.isOpen.preimage
    (candidateANormalBoundaryInducedRelativeLiftDeterminantFiberEvaluation_contDiff_two
      period hPeriod metric).continuous

theorem
    candidateANormalBoundaryInducedRelativeLiftDeterminant_ne_zero_of_mem
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real)
    (hCurrent : current ∈
      candidateANormalBoundaryInducedMetricDomain period hPeriod metric)
    (boundary : OrientationBoundary period hPeriod) :
    candidateANormalBoundaryInducedRelativeLiftDeterminantFiberEvaluation
        period hPeriod metric current boundary ≠ 0 := by
  change IsUnit
    (candidateANormalBoundaryInducedRelativeLiftDeterminantFiberEvaluation
      period hPeriod metric current) at hCurrent
  rcases hCurrent with ⟨unit, hUnit⟩
  intro hZero
  have hValueZero : (unit : BoundedContinuousFunction
      (OrientationBoundary period hPeriod) Real) boundary = 0 := by
    rw [hUnit]
    exact hZero
  have hInverse := congrArg
    (fun function : BoundedContinuousFunction
      (OrientationBoundary period hPeriod) Real => function boundary)
    unit.val_inv
  change (unit : BoundedContinuousFunction
      (OrientationBoundary period hPeriod) Real) boundary *
        (↑unit⁻¹ : BoundedContinuousFunction
          (OrientationBoundary period hPeriod) Real) boundary = 1 at hInverse
  rw [hValueZero, zero_mul] at hInverse
  exact zero_ne_one hInverse

theorem normalBoundaryRealMatrix_mulVec_injective_of_det_ne_zero
    (matrix : Matrix (NormalBoundaryTangentIndex period hPeriod)
      (NormalBoundaryTangentIndex period hPeriod) Real)
    (hDet : Matrix.det matrix ≠ 0) :
    Function.Injective matrix.mulVec := by
  apply Matrix.mulVec_injective_iff_isUnit.mpr
  exact matrix.isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hDet)

theorem normalGraphRelativeDeterminant_ne_zero_of_candidate_mem
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hCurrent :
      (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) ∈
        candidateANormalBoundaryInducedMetricDomain period hPeriod metric)
    (boundary : OrientationBoundary period hPeriod) :
    normalGraphRelativeDeterminant period hPeriod variedMetric displacement
        parameter (orientationDoubleToThroat period hPeriod boundary) ≠ 0 := by
  rw [← candidateANormalBoundaryInducedRelativeLiftDeterminantFiberEvaluation_smooth_eq_historical
    period hPeriod metric tensor variedMetric hVaried displacement parameter
      boundary]
  exact
    candidateANormalBoundaryInducedRelativeLiftDeterminant_ne_zero_of_mem
      period hPeriod metric _ hCurrent boundary

local instance candidateAEffectiveThroatTangentFiniteDimensional
    (point : MappingTorus (fixedEquatorData period hPeriod)) :
    FiniteDimensional Real
      (TangentSpace throatCoverModelWithCorners point) := by
  change FiniteDimensional Real ThroatCoverCoordinates
  infer_instance

theorem normalGraphRelativeEndomorphism_injective_of_det_ne_zero
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (point : MappingTorus (fixedEquatorData period hPeriod))
    (hDet : normalGraphRelativeDeterminant period hPeriod metric displacement
      parameter point ≠ 0) :
    Function.Injective
      (normalGraphRelativeEndomorphism period hPeriod metric displacement
        parameter point) := by
  have hUnit : IsUnit
      (normalGraphRelativeEndomorphism period hPeriod metric displacement
        parameter point).toLinearMap := by
    apply (LinearMap.isUnit_iff_isUnit_det _).2
    exact isUnit_iff_ne_zero.2 (by
      simpa only [normalGraphRelativeDeterminant] using hDet)
  have hKer := (LinearMap.isUnit_iff_ker_eq_bot _).1 hUnit
  rw [LinearMap.ker_eq_bot] at hKer
  exact hKer

theorem normalGraphInducedMetricValue_injective_of_relativeDet_ne_zero
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (point : MappingTorus (fixedEquatorData period hPeriod))
    (hDet : normalGraphRelativeDeterminant period hPeriod metric displacement
      parameter point ≠ 0) :
    Function.Injective
      (normalGraphInducedMetricValue period hPeriod metric displacement
        parameter point) := by
  intro first second hEqual
  apply normalGraphRelativeEndomorphism_injective_of_det_ne_zero
    period hPeriod metric displacement parameter point hDet
  change intrinsicThroatInverseMusical period hPeriod point
      (normalGraphInducedMetricValue period hPeriod metric displacement
        parameter point first) =
    intrinsicThroatInverseMusical period hPeriod point
      (normalGraphInducedMetricValue period hPeriod metric displacement
        parameter point second)
  rw [hEqual]

theorem normalGraphNonNullAt_of_candidate_inducedMetric_mem
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hCurrent :
      (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) ∈
        candidateANormalBoundaryInducedMetricDomain period hPeriod metric) :
    NormalGraphNonNullAt period hPeriod variedMetric displacement parameter := by
  intro point
  rcases orientationDoubleToThroat_surjective period hPeriod point with
    ⟨boundary, hBoundary⟩
  have hDet := normalGraphRelativeDeterminant_ne_zero_of_candidate_mem
    period hPeriod metric tensor variedMetric hVaried displacement parameter
      hCurrent boundary
  rw [hBoundary] at hDet
  exact normalGraphInducedMetricValue_injective_of_relativeDet_ne_zero
    period hPeriod variedMetric displacement parameter point hDet

/-- Inverse determinant in the existing scalar Banach algebra. -/
def candidateANormalBoundaryInducedRelativeLiftDeterminantInverseFiberEvaluation
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) :
    BoundedContinuousFunction (OrientationBoundary period hPeriod) Real :=
  Ring.inverse
    (candidateANormalBoundaryInducedRelativeLiftDeterminantFiberEvaluation
      period hPeriod metric current)

theorem
    candidateANormalBoundaryInducedRelativeLiftDeterminantInverseFiberEvaluation_contDiffOn_two
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    ContDiffOn Real 2
      (candidateANormalBoundaryInducedRelativeLiftDeterminantInverseFiberEvaluation
        period hPeriod metric)
      (candidateANormalBoundaryInducedMetricDomain
        period hPeriod metric) := by
  intro current hCurrent
  have hUnit : IsUnit
      (candidateANormalBoundaryInducedRelativeLiftDeterminantFiberEvaluation
        period hPeriod metric current) := hCurrent
  have hInverse : ContDiffAt Real 2 Ring.inverse
      (candidateANormalBoundaryInducedRelativeLiftDeterminantFiberEvaluation
        period hPeriod metric current) := by
    simpa using (contDiffAt_ringInverse Real hUnit.unit :
      ContDiffAt Real 2 Ring.inverse
        (hUnit.unit : BoundedContinuousFunction
          (OrientationBoundary period hPeriod) Real))
  exact hInverse.comp_contDiffWithinAt current
    ((candidateANormalBoundaryInducedRelativeLiftDeterminantFiberEvaluation_contDiff_two
      period hPeriod metric).contDiffWithinAt)

/-- Adjugate polynomial on the redundant finite coefficient space. -/
def candidateANormalBoundaryInducedRelativeLiftAdjugate
    (matrix : CandidateANormalBoundaryInducedMetricMatrixField period hPeriod) :
    CandidateANormalBoundaryInducedMetricMatrixField period hPeriod :=
  Matrix.adjugate matrix

theorem candidateANormalBoundaryInducedRelativeLiftAdjugate_contDiff :
    ContDiff Real ∞
      (candidateANormalBoundaryInducedRelativeLiftAdjugate
        period hPeriod) := by
  classical
  change @ContDiff Real _
    (NormalBoundaryTangentIndex period hPeriod →
      NormalBoundaryTangentIndex period hPeriod →
      BoundedContinuousFunction (OrientationBoundary period hPeriod) Real)
    Pi.normedAddCommGroup Pi.normedSpace
    (NormalBoundaryTangentIndex period hPeriod →
      NormalBoundaryTangentIndex period hPeriod →
      BoundedContinuousFunction (OrientationBoundary period hPeriod) Real)
    Pi.normedAddCommGroup Pi.normedSpace ∞
    (fun matrix row column => Matrix.adjugate matrix row column)
  rw [contDiff_pi]
  intro row
  rw [contDiff_pi]
  intro column
  have hUpdate : ContDiff Real ∞
      (fun matrix : CandidateANormalBoundaryInducedMetricMatrixField
          period hPeriod =>
        Matrix.updateRow matrix column (Pi.single row 1)) := by
    change @ContDiff Real _
      (NormalBoundaryTangentIndex period hPeriod →
        NormalBoundaryTangentIndex period hPeriod →
        BoundedContinuousFunction (OrientationBoundary period hPeriod) Real)
      Pi.normedAddCommGroup Pi.normedSpace
      (NormalBoundaryTangentIndex period hPeriod →
        NormalBoundaryTangentIndex period hPeriod →
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
    (fun matrix : CandidateANormalBoundaryInducedMetricMatrixField
        period hPeriod => Matrix.adjugate matrix row column)
  rw [show (fun matrix : CandidateANormalBoundaryInducedMetricMatrixField
      period hPeriod => Matrix.adjugate matrix row column) =
    fun matrix => candidateANormalBoundaryInducedRelativeLiftDeterminant
      period hPeriod
      (Matrix.updateRow matrix column (Pi.single row 1)) by
        funext matrix
        exact Matrix.adjugate_apply matrix row column]
  exact (candidateANormalBoundaryInducedRelativeLiftDeterminant_contDiff
    period hPeriod).comp hUpdate

/-- Inverse of the faithful relative induced-metric lift. -/
def candidateANormalBoundaryInducedRelativeLiftInverseFiberEvaluation
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) :
    CandidateANormalBoundaryInducedMetricMatrixField period hPeriod :=
  (candidateANormalBoundaryInducedRelativeLiftFiberEvaluation
    period hPeriod metric current)⁻¹

theorem
    candidateANormalBoundaryInducedRelativeLiftInverseFiberEvaluation_contDiffOn_two
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    ContDiffOn Real 2
      (candidateANormalBoundaryInducedRelativeLiftInverseFiberEvaluation
        period hPeriod metric)
      (candidateANormalBoundaryInducedMetricDomain
        period hPeriod metric) := by
  have hDetInverse :=
    candidateANormalBoundaryInducedRelativeLiftDeterminantInverseFiberEvaluation_contDiffOn_two
      period hPeriod metric
  have hAdjugate : ContDiff Real 2 (fun current =>
      candidateANormalBoundaryInducedRelativeLiftAdjugate period hPeriod
        (candidateANormalBoundaryInducedRelativeLiftFiberEvaluation
          period hPeriod metric current)) :=
    (candidateANormalBoundaryInducedRelativeLiftAdjugate_contDiff
      period hPeriod).of_le
        (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top) |>.comp
      (candidateANormalBoundaryInducedRelativeLiftFiberEvaluation_contDiff_two
        period hPeriod metric)
  rw [show
      candidateANormalBoundaryInducedRelativeLiftInverseFiberEvaluation
          period hPeriod metric =
        fun current =>
          candidateANormalBoundaryInducedRelativeLiftDeterminantInverseFiberEvaluation
              period hPeriod metric current •
            candidateANormalBoundaryInducedRelativeLiftAdjugate period hPeriod
              (candidateANormalBoundaryInducedRelativeLiftFiberEvaluation
                period hPeriod metric current) by
    funext current
    exact Matrix.inv_def _]
  change @ContDiffOn Real _
    (Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real)
    _ _
    (NormalBoundaryTangentIndex period hPeriod →
      NormalBoundaryTangentIndex period hPeriod →
      BoundedContinuousFunction (OrientationBoundary period hPeriod) Real)
    Pi.normedAddCommGroup Pi.normedSpace 2
    (fun current row column =>
      candidateANormalBoundaryInducedRelativeLiftDeterminantInverseFiberEvaluation
          period hPeriod metric current *
        candidateANormalBoundaryInducedRelativeLiftAdjugate period hPeriod
          (candidateANormalBoundaryInducedRelativeLiftFiberEvaluation
            period hPeriod metric current) row column)
    (candidateANormalBoundaryInducedMetricDomain period hPeriod metric)
  rw [contDiffOn_pi]
  intro row
  rw [contDiffOn_pi]
  intro column
  exact hDetInverse.mul
    (contDiffOn_pi.mp (contDiffOn_pi.mp hAdjugate.contDiffOn row) column)

theorem candidateANormalBoundaryInducedRelativeLift_mul_inverse
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real)
    (hCurrent : current ∈ candidateANormalBoundaryInducedMetricDomain
      period hPeriod metric) :
    candidateANormalBoundaryInducedRelativeLiftFiberEvaluation
          period hPeriod metric current *
        candidateANormalBoundaryInducedRelativeLiftInverseFiberEvaluation
          period hPeriod metric current = 1 :=
  by
    change candidateANormalBoundaryInducedRelativeLiftFiberEvaluation
          period hPeriod metric current *
        (candidateANormalBoundaryInducedRelativeLiftFiberEvaluation
          period hPeriod metric current)⁻¹ = 1
    apply Matrix.mul_nonsing_inv
    exact hCurrent

theorem candidateANormalBoundaryInducedRelativeLift_inverse_mul
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real)
    (hCurrent : current ∈ candidateANormalBoundaryInducedMetricDomain
      period hPeriod metric) :
    candidateANormalBoundaryInducedRelativeLiftInverseFiberEvaluation
          period hPeriod metric current *
        candidateANormalBoundaryInducedRelativeLiftFiberEvaluation
          period hPeriod metric current = 1 :=
  by
    change (candidateANormalBoundaryInducedRelativeLiftFiberEvaluation
          period hPeriod metric current)⁻¹ *
        candidateANormalBoundaryInducedRelativeLiftFiberEvaluation
          period hPeriod metric current = 1
    apply Matrix.nonsing_inv_mul
    exact hCurrent

/-- The contravariant ambient metric uses the same inverse order as the
installed regular chart: `(1 + g₀⁻¹h)⁻¹ g₀⁻¹`. -/
def candidateANormalBoundaryActualInverseMetricMatrixFiberEvaluation
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) :
    CandidateANormalBoundaryMatrixField period hPeriod :=
  candidateANormalBoundaryTotalRelativeMetricInverseMatrixFiberEvaluation
        period hPeriod metric current *
    candidateANormalBoundaryBaseInverseMetricMatrixFiberEvaluation period
      hPeriod metric current

theorem candidateANormalBoundaryActualInverseMetricMatrixFiberEvaluation_contDiffOn_two
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    ContDiffOn Real 2
      (candidateANormalBoundaryActualInverseMetricMatrixFiberEvaluation
        period hPeriod metric)
      (candidateANormalBoundaryMetricParameterDomain
        period hPeriod metric) := by
  have hRelative :=
    candidateANormalBoundaryTotalRelativeMetricInverseMatrixFiberEvaluation_contDiffOn_two
      period hPeriod metric
  have hBase :=
    candidateANormalBoundaryBaseInverseMetricMatrixFiberEvaluation_contDiff_two
      period hPeriod metric
  change @ContDiffOn Real _
    (Prod (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real)
    _ _
    (Fin 4 → Fin 4 →
      BoundedContinuousFunction (OrientationBoundary period hPeriod) Real)
    Pi.normedAddCommGroup Pi.normedSpace 2
    (fun current =>
      candidateANormalBoundaryTotalRelativeMetricInverseMatrixFiberEvaluation
          period hPeriod metric current *
        candidateANormalBoundaryBaseInverseMetricMatrixFiberEvaluation period
          hPeriod metric current)
    (candidateANormalBoundaryMetricParameterDomain period hPeriod metric)
  rw [contDiffOn_pi]
  intro row
  rw [contDiffOn_pi]
  intro column
  simp_rw [Matrix.mul_apply]
  apply ContDiffOn.sum
  intro middle _
  exact
    ((contDiffOn_pi.mp (contDiffOn_pi.mp hRelative row) middle).mul
      (contDiff_pi.mp (contDiff_pi.mp hBase middle) column).contDiffOn)

/-- On the admissible domain, the completed ambient inverse is exactly the
installed inverse-metric C2 matrix evaluated on the same graph. -/
theorem
    candidateANormalBoundaryActualInverseMetricMatrixFiberEvaluation_eq_c2Graph
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real)
    (hCurrent : current ∈
      candidateANormalBoundaryMetricParameterDomain period hPeriod metric) :
    candidateANormalBoundaryActualInverseMetricMatrixFiberEvaluation
        period hPeriod metric current =
      candidateANormalBoundaryC2MatrixGraphEvaluation period hPeriod
        current.1.2 current.2
        (regularGeneralMetricC2InverseMetricMatrix period hPeriod metric
          (regularGeneralMetricBoundaryC3CoreToC2
            period hPeriod metric current.1.1)) := by
  unfold candidateANormalBoundaryActualInverseMetricMatrixFiberEvaluation
  rw [candidateANormalBoundaryTotalRelativeMetricInverseMatrixFiberEvaluation_eq_c2Inverse
    period hPeriod metric current hCurrent]
  unfold candidateANormalBoundaryC2InverseMatrixFiberEvaluation
  rw [regularGeneralMetricC2InverseMetricMatrix,
    candidateANormalBoundaryC2MatrixGraphEvaluation_product,
    candidateANormalBoundaryC2MatrixGraphEvaluation_baseInverseMetric]

/-- Scalar form of the same exact inverse-metric agreement. -/
theorem candidateANormalBoundaryActualInverseMetricMatrixFiberEvaluation_eq_existing
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real)
    (hCurrent : current ∈
      candidateANormalBoundaryMetricParameterDomain period hPeriod metric)
    (row column : Fin 4) (boundary : OrientationBoundary period hPeriod) :
    candidateANormalBoundaryActualInverseMetricMatrixFiberEvaluation
        period hPeriod metric current row column boundary =
      regularGeneralMetricC0InverseMetricCoefficient period hPeriod metric
        (regularGeneralMetricBoundaryC3CoreToC2
          period hPeriod metric current.1.1)
        row column
        (normalBoundaryC2Graph period hPeriod current.1.2 current.2
          boundary) := by
  rw [candidateANormalBoundaryActualInverseMetricMatrixFiberEvaluation_eq_c2Graph
    period hPeriod metric current hCurrent]
  rfl

/-- Existing nonholonomic regular-frame structure coefficient, evaluated on
the same completed moving graph. -/
def candidateANormalBoundaryRegularFrameStructureCoefficientFiberEvaluation
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (first second upper : Fin 4)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) :
    BoundedContinuousFunction (OrientationBoundary period hPeriod) Real :=
  candidateANormalBoundarySmoothFieldFiberEvaluation period hPeriod
    metric.metric
    (regularFrameStructureCoefficient period hPeriod metric first second upper)
    (current.1.2, current.2)

theorem
    candidateANormalBoundaryRegularFrameStructureCoefficientFiberEvaluation_contDiff_two
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (first second upper : Fin 4) :
    ContDiff Real 2
      (candidateANormalBoundaryRegularFrameStructureCoefficientFiberEvaluation
        period hPeriod metric first second upper) :=
  (candidateANormalBoundarySmoothFieldFiberEvaluation_contDiff_two
    period hPeriod metric.metric
      (regularFrameStructureCoefficient
        period hPeriod metric first second upper)).comp
    ((contDiff_snd.comp contDiff_fst).prodMk contDiff_snd)

@[simp]
theorem
    candidateANormalBoundaryRegularFrameStructureCoefficientFiberEvaluation_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (first second upper : Fin 4)
    (variation : CandidateANormalBoundaryFunctionalCore period hPeriod metric)
    (parameter : Real) (boundary : OrientationBoundary period hPeriod) :
    candidateANormalBoundaryRegularFrameStructureCoefficientFiberEvaluation
        period hPeriod metric first second upper (variation, parameter)
          boundary =
      regularFrameStructureCoefficient period hPeriod metric first second upper
        (normalBoundaryC2Graph period hPeriod variation.2 parameter
          boundary) :=
  candidateANormalBoundarySmoothFieldFiberEvaluation_apply period hPeriod
    metric.metric _ variation.2 parameter boundary

/-- Completed lowered Koszul coefficient in the installed regular frame. -/
def candidateANormalBoundaryKoszulLowerFiberEvaluation
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (first second lower : Fin 4)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) :
    BoundedContinuousFunction (OrientationBoundary period hPeriod) Real :=
  (1 / 2 : Real) •
    (candidateANormalBoundaryActualMetricRegularFirstMatrixFiberEvaluation
          period hPeriod metric first current second lower +
      candidateANormalBoundaryActualMetricRegularFirstMatrixFiberEvaluation
          period hPeriod metric second current lower first -
      candidateANormalBoundaryActualMetricRegularFirstMatrixFiberEvaluation
          period hPeriod metric lower current first second -
      ∑ contracted : Fin 4,
        candidateANormalBoundaryRegularFrameStructureCoefficientFiberEvaluation
              period hPeriod metric second lower contracted current *
          candidateANormalBoundaryActualMetricMatrixFiberEvaluation
            period hPeriod metric current first contracted +
      ∑ contracted : Fin 4,
        candidateANormalBoundaryRegularFrameStructureCoefficientFiberEvaluation
              period hPeriod metric lower first contracted current *
          candidateANormalBoundaryActualMetricMatrixFiberEvaluation
            period hPeriod metric current second contracted +
      ∑ contracted : Fin 4,
        candidateANormalBoundaryRegularFrameStructureCoefficientFiberEvaluation
              period hPeriod metric first second contracted current *
          candidateANormalBoundaryActualMetricMatrixFiberEvaluation
            period hPeriod metric current lower contracted)

theorem candidateANormalBoundaryKoszulLowerFiberEvaluation_contDiff_two
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (first second lower : Fin 4) :
    ContDiff Real 2
      (candidateANormalBoundaryKoszulLowerFiberEvaluation
        period hPeriod metric first second lower) := by
  have hDerivative (direction row column : Fin 4) :=
    contDiff_pi.mp (contDiff_pi.mp
      (candidateANormalBoundaryActualMetricRegularFirstMatrixFiberEvaluation_contDiff_two
        period hPeriod metric direction) row) column
  have hMetric (row column : Fin 4) :=
    contDiff_pi.mp (contDiff_pi.mp
      (candidateANormalBoundaryActualMetricMatrixFiberEvaluation_contDiff_two
        period hPeriod metric) row) column
  have hStructure (left right upper : Fin 4) :=
    candidateANormalBoundaryRegularFrameStructureCoefficientFiberEvaluation_contDiff_two
      period hPeriod metric left right upper
  apply ContDiff.const_smul
  apply ContDiff.add
  · apply ContDiff.add
    · apply ContDiff.sub
      · apply ContDiff.sub
        · exact (hDerivative first second lower).add
            (hDerivative second lower first)
        · exact hDerivative lower first second
      · apply ContDiff.sum
        intro contracted _
        exact (hStructure second lower contracted).mul
          (hMetric first contracted)
    · apply ContDiff.sum
      intro contracted _
      exact (hStructure lower first contracted).mul
        (hMetric second contracted)
  · apply ContDiff.sum
    intro contracted _
    exact (hStructure first second contracted).mul
      (hMetric lower contracted)

/-- Exact agreement of the completed lowered Koszul coefficient with the
already installed Levi--Civita coefficient on the same graph. -/
theorem candidateANormalBoundaryKoszulLowerFiberEvaluation_eq_existing
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (first second lower : Fin 4)
    (variation : CandidateANormalBoundaryFunctionalCore period hPeriod metric)
    (parameter : Real) (boundary : OrientationBoundary period hPeriod) :
    candidateANormalBoundaryKoszulLowerFiberEvaluation period hPeriod metric
        first second lower (variation, parameter) boundary =
      regularGeneralMetricC0KoszulLower period hPeriod metric
        (regularGeneralMetricBoundaryC3CoreToC2
          period hPeriod metric variation.1)
        first second lower
        (normalBoundaryC2Graph period hPeriod variation.2 parameter
          boundary) := by
  unfold candidateANormalBoundaryKoszulLowerFiberEvaluation
    regularGeneralMetricC0KoszulLower
  simp only [BoundedContinuousFunction.smul_apply,
    BoundedContinuousFunction.add_apply,
    BoundedContinuousFunction.sub_apply,
    BoundedContinuousFunction.mul_apply,
    BoundedContinuousFunction.sum_apply,
    ContinuousMap.smul_apply, ContinuousMap.add_apply,
    ContinuousMap.sub_apply, ContinuousMap.mul_apply,
    ContinuousMap.sum_apply, smul_eq_mul]
  rw [candidateANormalBoundaryActualMetricRegularFirstMatrixFiberEvaluation_eq_existing
      period hPeriod metric first variation parameter boundary second lower,
    candidateANormalBoundaryActualMetricRegularFirstMatrixFiberEvaluation_eq_existing
      period hPeriod metric second variation parameter boundary lower first,
    candidateANormalBoundaryActualMetricRegularFirstMatrixFiberEvaluation_eq_existing
      period hPeriod metric lower variation parameter boundary first second]
  simp_rw [candidateANormalBoundaryRegularFrameStructureCoefficientFiberEvaluation_apply,
    candidateANormalBoundaryActualMetricMatrixFiberEvaluation_eq_existing]
  simp only [regularFrameStructureCoefficientContinuous_apply]

/-- Completed Levi-Civita coefficient.  It is the existing Koszul formula
with the already completed actual inverse metric. -/
def candidateANormalBoundaryChristoffelFiberEvaluation
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (upper first second : Fin 4)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) :
    BoundedContinuousFunction (OrientationBoundary period hPeriod) Real :=
  ∑ lower : Fin 4,
    candidateANormalBoundaryActualInverseMetricMatrixFiberEvaluation
          period hPeriod metric current upper lower *
      candidateANormalBoundaryKoszulLowerFiberEvaluation
        period hPeriod metric first second lower current

theorem candidateANormalBoundaryChristoffelFiberEvaluation_contDiffOn_two
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (upper first second : Fin 4) :
    ContDiffOn Real 2
      (candidateANormalBoundaryChristoffelFiberEvaluation
        period hPeriod metric upper first second)
      (candidateANormalBoundaryMetricParameterDomain
        period hPeriod metric) := by
  have hInverse :=
    candidateANormalBoundaryActualInverseMetricMatrixFiberEvaluation_contDiffOn_two
      period hPeriod metric
  unfold candidateANormalBoundaryChristoffelFiberEvaluation
  apply ContDiffOn.sum
  intro lower _
  exact (contDiffOn_pi.mp (contDiffOn_pi.mp hInverse upper) lower).mul
    (candidateANormalBoundaryKoszulLowerFiberEvaluation_contDiff_two
      period hPeriod metric first second lower).contDiffOn

/-- Exact admissible-domain agreement of the completed Christoffel
coefficient with the installed regular-metric Levi--Civita coefficient. -/
theorem candidateANormalBoundaryChristoffelFiberEvaluation_eq_existing
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (upper first second : Fin 4)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real)
    (hCurrent : current ∈
      candidateANormalBoundaryMetricParameterDomain period hPeriod metric)
    (boundary : OrientationBoundary period hPeriod) :
    candidateANormalBoundaryChristoffelFiberEvaluation period hPeriod metric
        upper first second current boundary =
      regularGeneralMetricC0Christoffel period hPeriod metric
        (regularGeneralMetricBoundaryC3CoreToC2
          period hPeriod metric current.1.1)
        upper first second
        (normalBoundaryC2Graph period hPeriod current.1.2 current.2
          boundary) := by
  unfold candidateANormalBoundaryChristoffelFiberEvaluation
    regularGeneralMetricC0Christoffel
  simp only [BoundedContinuousFunction.sum_apply,
    BoundedContinuousFunction.mul_apply, ContinuousMap.sum_apply,
    ContinuousMap.mul_apply]
  apply Finset.sum_congr rfl
  intro lower _
  rw [candidateANormalBoundaryActualInverseMetricMatrixFiberEvaluation_eq_existing
      period hPeriod metric current hCurrent upper lower boundary,
    candidateANormalBoundaryKoszulLowerFiberEvaluation_eq_existing
      period hPeriod metric first second lower current.1 current.2 boundary]

/-- Completed covariant acceleration of the moving graph in the installed
regular frame.  This is the graph second derivative plus the same
Levi--Civita coefficient already identified above. -/
def
    candidateANormalBoundaryGraphCovariantAccelerationRegularFrameCoefficientFiberEvaluation
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (outer inner : NormalBoundaryTangentIndex period hPeriod)
    (upper : Fin 4)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) :
    BoundedContinuousFunction (OrientationBoundary period hPeriod) Real :=
  candidateANormalBoundaryGraphTangentRegularFrameSpatialDerivativeFiberEvaluation
      period hPeriod metric outer inner upper current +
    ∑ first : Fin 4, ∑ second : Fin 4,
      candidateANormalBoundaryChristoffelFiberEvaluation
            period hPeriod metric upper first second current *
        candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation
            period hPeriod metric outer first current *
          candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation
            period hPeriod metric inner second current

theorem
    candidateANormalBoundaryGraphCovariantAccelerationRegularFrameCoefficientFiberEvaluation_contDiffOn_two
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (outer inner : NormalBoundaryTangentIndex period hPeriod)
    (upper : Fin 4) :
    ContDiffOn Real 2
      (candidateANormalBoundaryGraphCovariantAccelerationRegularFrameCoefficientFiberEvaluation
        period hPeriod metric outer inner upper)
      (candidateANormalBoundaryMetricParameterDomain
        period hPeriod metric) := by
  have hDerivative :=
    candidateANormalBoundaryGraphTangentRegularFrameSpatialDerivativeFiberEvaluation_contDiff_two
      period hPeriod metric outer inner upper
  have hChristoffel :=
    candidateANormalBoundaryChristoffelFiberEvaluation_contDiffOn_two
      period hPeriod metric
  have hOuter (first : Fin 4) :=
    candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation_contDiff_two
      period hPeriod metric outer first
  have hInner (second : Fin 4) :=
    candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation_contDiff_two
      period hPeriod metric inner second
  unfold
    candidateANormalBoundaryGraphCovariantAccelerationRegularFrameCoefficientFiberEvaluation
  exact hDerivative.contDiffOn.add (ContDiffOn.sum fun first _ =>
    ContDiffOn.sum fun second _ =>
      (((hChristoffel upper first second).mul
        (hOuter first).contDiffOn).mul
            (hInner second).contDiffOn))

/-- Pointwise expansion through the already installed regular-metric
Levi--Civita coefficient; no second connection is introduced. -/
theorem
    candidateANormalBoundaryGraphCovariantAccelerationRegularFrameCoefficientFiberEvaluation_eq_existing
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (outer inner : NormalBoundaryTangentIndex period hPeriod)
    (upper : Fin 4)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real)
    (hCurrent : current ∈
      candidateANormalBoundaryMetricParameterDomain period hPeriod metric)
    (boundary : OrientationBoundary period hPeriod) :
    candidateANormalBoundaryGraphCovariantAccelerationRegularFrameCoefficientFiberEvaluation
        period hPeriod metric outer inner upper current boundary =
      candidateANormalBoundaryGraphTangentRegularFrameSpatialDerivativeFiberEvaluation
          period hPeriod metric outer inner upper current boundary +
        ∑ first : Fin 4, ∑ second : Fin 4,
          regularGeneralMetricC0Christoffel period hPeriod metric
                (regularGeneralMetricBoundaryC3CoreToC2
                  period hPeriod metric current.1.1)
                upper first second
                (normalBoundaryC2Graph period hPeriod current.1.2 current.2
                  boundary) *
            candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation
                period hPeriod metric outer first current boundary *
              candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation
                period hPeriod metric inner second current boundary := by
  unfold
    candidateANormalBoundaryGraphCovariantAccelerationRegularFrameCoefficientFiberEvaluation
  simp only [BoundedContinuousFunction.add_apply,
    BoundedContinuousFunction.sum_apply,
    BoundedContinuousFunction.mul_apply, ContinuousMap.add_apply,
    ContinuousMap.sum_apply, ContinuousMap.mul_apply]
  apply congrArg₂ (· + ·) rfl
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  rw [candidateANormalBoundaryChristoffelFiberEvaluation_eq_existing
    period hPeriod metric upper first second current hCurrent boundary]

/-! ### Completed metric normal and Gauss second form -/

/-- Common existing domain on which both the ambient and induced inverse
metrics are available. -/
def candidateANormalBoundaryGeometryParameterDomain
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    Set (Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) :=
  candidateANormalBoundaryMetricParameterDomain period hPeriod metric ∩
    candidateANormalBoundaryInducedMetricDomain period hPeriod metric

theorem candidateANormalBoundaryGeometryParameterDomain_isOpen
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    IsOpen (candidateANormalBoundaryGeometryParameterDomain
      period hPeriod metric) :=
  (candidateANormalBoundaryMetricParameterDomain_isOpen
    period hPeriod metric).inter
      (candidateANormalBoundaryInducedMetricDomain_isOpen
        period hPeriod metric)

theorem zero_mem_candidateANormalBoundaryGeometryParameterDomain
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric) :
    (0 : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) ∈
      candidateANormalBoundaryGeometryParameterDomain
        period hPeriod metric :=
  ⟨zero_mem_candidateANormalBoundaryMetricParameterDomain
      period hPeriod metric,
    zero_mem_candidateANormalBoundaryInducedMetricDomain
      period hPeriod metric hTransverse⟩

/-- Pairing of the canonical latitude-transverse vector with one completed
graph tangent. -/
def candidateANormalBoundaryVerticalTangentialPairingFiberEvaluation
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (index : NormalBoundaryTangentIndex period hPeriod)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) :
    BoundedContinuousFunction (OrientationBoundary period hPeriod) Real :=
  ∑ first : Fin 4, ∑ second : Fin 4,
    candidateANormalBoundaryVerticalRegularFrameCoefficientFiberEvaluation
          period hPeriod metric first current *
      candidateANormalBoundaryActualMetricMatrixFiberEvaluation
          period hPeriod metric current first second *
        candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation
          period hPeriod metric index second current

theorem
    candidateANormalBoundaryVerticalTangentialPairingFiberEvaluation_contDiff_two
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (index : NormalBoundaryTangentIndex period hPeriod) :
    ContDiff Real 2
      (candidateANormalBoundaryVerticalTangentialPairingFiberEvaluation
        period hPeriod metric index) := by
  have hVertical (first : Fin 4) :=
    candidateANormalBoundaryVerticalRegularFrameCoefficientFiberEvaluation_contDiff_two
      period hPeriod metric first
  have hMetric :=
    candidateANormalBoundaryActualMetricMatrixFiberEvaluation_contDiff_two
      period hPeriod metric
  have hTangent (second : Fin 4) :=
    candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation_contDiff_two
      period hPeriod metric index second
  unfold candidateANormalBoundaryVerticalTangentialPairingFiberEvaluation
  exact ContDiff.sum fun first _ => ContDiff.sum fun second _ =>
    (((hVertical first).mul
      (contDiff_pi.mp (contDiff_pi.mp hMetric first) second)).mul
        (hTangent second))

/-- Canonical reference-dual conversion of the preceding tangent covector
into the redundant analysis coordinates. -/
def candidateANormalBoundaryVerticalTangentialReferenceDualFiberEvaluation
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (row : NormalBoundaryTangentIndex period hPeriod)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) :
    BoundedContinuousFunction (OrientationBoundary period hPeriod) Real :=
  ∑ column : NormalBoundaryTangentIndex period hPeriod,
    normalBoundaryReferenceDualCoefficientMatrix
          period hPeriod row column *
      candidateANormalBoundaryVerticalTangentialPairingFiberEvaluation
        period hPeriod metric column current

theorem
    candidateANormalBoundaryVerticalTangentialReferenceDualFiberEvaluation_contDiff_two
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (row : NormalBoundaryTangentIndex period hPeriod) :
    ContDiff Real 2
      (candidateANormalBoundaryVerticalTangentialReferenceDualFiberEvaluation
        period hPeriod metric row) := by
  unfold
    candidateANormalBoundaryVerticalTangentialReferenceDualFiberEvaluation
  exact ContDiff.sum fun column _ => contDiff_const.mul
    (candidateANormalBoundaryVerticalTangentialPairingFiberEvaluation_contDiff_two
      period hPeriod metric column)

/-- Tangential projection coefficients obtained from the already constructed
inverse of the faithful induced-metric lift. -/
def candidateANormalBoundaryTangentialProjectionCoefficientFiberEvaluation
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (row : NormalBoundaryTangentIndex period hPeriod)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) :
    BoundedContinuousFunction (OrientationBoundary period hPeriod) Real :=
  ∑ middle : NormalBoundaryTangentIndex period hPeriod,
    candidateANormalBoundaryInducedRelativeLiftInverseFiberEvaluation
          period hPeriod metric current row middle *
      candidateANormalBoundaryVerticalTangentialReferenceDualFiberEvaluation
        period hPeriod metric middle current

theorem
    candidateANormalBoundaryTangentialProjectionCoefficientFiberEvaluation_contDiffOn_two
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (row : NormalBoundaryTangentIndex period hPeriod) :
    ContDiffOn Real 2
      (candidateANormalBoundaryTangentialProjectionCoefficientFiberEvaluation
        period hPeriod metric row)
      (candidateANormalBoundaryInducedMetricDomain
        period hPeriod metric) := by
  have hInverse :=
    candidateANormalBoundaryInducedRelativeLiftInverseFiberEvaluation_contDiffOn_two
      period hPeriod metric
  unfold
    candidateANormalBoundaryTangentialProjectionCoefficientFiberEvaluation
  exact ContDiffOn.sum fun middle _ =>
    (contDiffOn_pi.mp (contDiffOn_pi.mp hInverse row) middle).mul
      (candidateANormalBoundaryVerticalTangentialReferenceDualFiberEvaluation_contDiff_two
        period hPeriod metric middle).contDiffOn

/-- Coefficients of the metric-normal projection of the canonical latitude
vector.  The projection uses only the graph, actual metric and faithful
induced inverse already present above. -/
def candidateANormalBoundaryMetricNormalRegularFrameCoefficientFiberEvaluation
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (upper : Fin 4)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) :
    BoundedContinuousFunction (OrientationBoundary period hPeriod) Real :=
  candidateANormalBoundaryVerticalRegularFrameCoefficientFiberEvaluation
      period hPeriod metric upper current -
    ∑ index : NormalBoundaryTangentIndex period hPeriod,
      candidateANormalBoundaryTangentialProjectionCoefficientFiberEvaluation
            period hPeriod metric index current *
        candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation
          period hPeriod metric index upper current

theorem
    candidateANormalBoundaryMetricNormalRegularFrameCoefficientFiberEvaluation_contDiffOn_two
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (upper : Fin 4) :
    ContDiffOn Real 2
      (candidateANormalBoundaryMetricNormalRegularFrameCoefficientFiberEvaluation
        period hPeriod metric upper)
      (candidateANormalBoundaryInducedMetricDomain
        period hPeriod metric) := by
  unfold
    candidateANormalBoundaryMetricNormalRegularFrameCoefficientFiberEvaluation
  exact
    (candidateANormalBoundaryVerticalRegularFrameCoefficientFiberEvaluation_contDiff_two
      period hPeriod metric upper).contDiffOn.sub
        (ContDiffOn.sum fun index _ =>
          (candidateANormalBoundaryTangentialProjectionCoefficientFiberEvaluation_contDiffOn_two
              period hPeriod metric index).mul
            (candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation_contDiff_two
              period hPeriod metric index upper).contDiffOn)

/-- Metric square of the completed (not yet normalized) projected normal. -/
def candidateANormalBoundaryMetricNormalSquareFiberEvaluation
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) :
    BoundedContinuousFunction (OrientationBoundary period hPeriod) Real :=
  ∑ first : Fin 4, ∑ second : Fin 4,
    candidateANormalBoundaryMetricNormalRegularFrameCoefficientFiberEvaluation
          period hPeriod metric first current *
      candidateANormalBoundaryActualMetricMatrixFiberEvaluation
          period hPeriod metric current first second *
        candidateANormalBoundaryMetricNormalRegularFrameCoefficientFiberEvaluation
          period hPeriod metric second current

theorem
    candidateANormalBoundaryMetricNormalSquareFiberEvaluation_contDiffOn_two
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    ContDiffOn Real 2
      (candidateANormalBoundaryMetricNormalSquareFiberEvaluation
        period hPeriod metric)
      (candidateANormalBoundaryInducedMetricDomain
        period hPeriod metric) := by
  have hNormal :=
    candidateANormalBoundaryMetricNormalRegularFrameCoefficientFiberEvaluation_contDiffOn_two
      period hPeriod metric
  have hMetric :=
    candidateANormalBoundaryActualMetricMatrixFiberEvaluation_contDiff_two
      period hPeriod metric
  unfold candidateANormalBoundaryMetricNormalSquareFiberEvaluation
  exact ContDiffOn.sum fun first _ => ContDiffOn.sum fun second _ =>
    (((hNormal first).mul
      (contDiff_pi.mp (contDiff_pi.mp hMetric first) second).contDiffOn).mul
        (hNormal second))

/-- Raw Gauss pairing with the completed projected normal and completed
covariant graph acceleration. -/
def candidateANormalBoundaryGaussRawExtrinsicCurvatureFiberEvaluation
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (outer inner : NormalBoundaryTangentIndex period hPeriod)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) :
    BoundedContinuousFunction (OrientationBoundary period hPeriod) Real :=
  -∑ first : Fin 4, ∑ second : Fin 4,
    candidateANormalBoundaryMetricNormalRegularFrameCoefficientFiberEvaluation
          period hPeriod metric first current *
      candidateANormalBoundaryActualMetricMatrixFiberEvaluation
          period hPeriod metric current first second *
        candidateANormalBoundaryGraphCovariantAccelerationRegularFrameCoefficientFiberEvaluation
          period hPeriod metric outer inner second current

theorem
    candidateANormalBoundaryGaussRawExtrinsicCurvatureFiberEvaluation_contDiffOn_two
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (outer inner : NormalBoundaryTangentIndex period hPeriod) :
    ContDiffOn Real 2
      (candidateANormalBoundaryGaussRawExtrinsicCurvatureFiberEvaluation
        period hPeriod metric outer inner)
      (candidateANormalBoundaryGeometryParameterDomain
        period hPeriod metric) := by
  have hNormal :=
    candidateANormalBoundaryMetricNormalRegularFrameCoefficientFiberEvaluation_contDiffOn_two
      period hPeriod metric
  have hMetric :=
    candidateANormalBoundaryActualMetricMatrixFiberEvaluation_contDiff_two
      period hPeriod metric
  have hAcceleration :=
    candidateANormalBoundaryGraphCovariantAccelerationRegularFrameCoefficientFiberEvaluation_contDiffOn_two
      period hPeriod metric
  unfold candidateANormalBoundaryGaussRawExtrinsicCurvatureFiberEvaluation
  exact (ContDiffOn.sum fun first _ => ContDiffOn.sum fun second _ =>
    ((((hNormal first).mono Set.inter_subset_right).mul
      (contDiff_pi.mp (contDiff_pi.mp hMetric first) second).contDiffOn).mul
        ((hAcceleration outer inner second).mono
          Set.inter_subset_left))).neg

/-- Symmetric completed second fundamental form before unit normalization. -/
def candidateANormalBoundaryGaussExtrinsicCurvatureFiberEvaluation
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (outer inner : NormalBoundaryTangentIndex period hPeriod)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) :
    BoundedContinuousFunction (OrientationBoundary period hPeriod) Real :=
  (1 / 2 : Real) •
    (candidateANormalBoundaryGaussRawExtrinsicCurvatureFiberEvaluation
          period hPeriod metric outer inner current +
      candidateANormalBoundaryGaussRawExtrinsicCurvatureFiberEvaluation
        period hPeriod metric inner outer current)

theorem
    candidateANormalBoundaryGaussExtrinsicCurvatureFiberEvaluation_contDiffOn_two
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (outer inner : NormalBoundaryTangentIndex period hPeriod) :
    ContDiffOn Real 2
      (candidateANormalBoundaryGaussExtrinsicCurvatureFiberEvaluation
        period hPeriod metric outer inner)
      (candidateANormalBoundaryGeometryParameterDomain
        period hPeriod metric) := by
  unfold candidateANormalBoundaryGaussExtrinsicCurvatureFiberEvaluation
  exact ContDiffOn.const_smul (1 / 2 : Real)
    ((candidateANormalBoundaryGaussRawExtrinsicCurvatureFiberEvaluation_contDiffOn_two
        period hPeriod metric outer inner).add
      (candidateANormalBoundaryGaussRawExtrinsicCurvatureFiberEvaluation_contDiffOn_two
        period hPeriod metric inner outer))

theorem candidateANormalBoundaryGaussExtrinsicCurvatureFiberEvaluation_symmetric
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (outer inner : NormalBoundaryTangentIndex period hPeriod) :
    candidateANormalBoundaryGaussExtrinsicCurvatureFiberEvaluation
        period hPeriod metric outer inner =
      candidateANormalBoundaryGaussExtrinsicCurvatureFiberEvaluation
        period hPeriod metric inner outer := by
  funext current
  unfold candidateANormalBoundaryGaussExtrinsicCurvatureFiberEvaluation
  rw [add_comm]

/-- Public completed graph-connection gate: spatial graph-tangent
derivatives are C2, Christoffel coefficients are C2 on the existing
admissible metric domain, and those coefficients are exactly the installed
regular-metric Levi--Civita coefficients. -/
theorem candidate_a_normal_boundary_graph_connection_fiber_c2_gate
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    (∀ outer inner : NormalBoundaryTangentIndex period hPeriod,
      ∀ row : Fin 4,
        ContDiff Real 2
          (candidateANormalBoundaryGraphTangentRegularFrameSpatialDerivativeFiberEvaluation
            period hPeriod metric outer inner row)) ∧
      (∀ upper first second : Fin 4,
        ContDiffOn Real 2
          (candidateANormalBoundaryChristoffelFiberEvaluation
            period hPeriod metric upper first second)
          (candidateANormalBoundaryMetricParameterDomain
            period hPeriod metric)) ∧
      (∀ outer inner : NormalBoundaryTangentIndex period hPeriod,
        ∀ upper : Fin 4,
          ContDiffOn Real 2
            (candidateANormalBoundaryGraphCovariantAccelerationRegularFrameCoefficientFiberEvaluation
              period hPeriod metric outer inner upper)
            (candidateANormalBoundaryMetricParameterDomain
              period hPeriod metric)) ∧
      ∀ current,
        current ∈ candidateANormalBoundaryMetricParameterDomain
            period hPeriod metric →
          ∀ upper first second : Fin 4,
            ∀ boundary : OrientationBoundary period hPeriod,
              candidateANormalBoundaryChristoffelFiberEvaluation
                  period hPeriod metric upper first second current boundary =
                regularGeneralMetricC0Christoffel period hPeriod metric
                  (regularGeneralMetricBoundaryC3CoreToC2
                    period hPeriod metric current.1.1)
                  upper first second
                  (normalBoundaryC2Graph period hPeriod current.1.2 current.2
                    boundary) :=
  ⟨candidateANormalBoundaryGraphTangentRegularFrameSpatialDerivativeFiberEvaluation_contDiff_two
      period hPeriod metric,
    candidateANormalBoundaryChristoffelFiberEvaluation_contDiffOn_two
      period hPeriod metric,
    candidateANormalBoundaryGraphCovariantAccelerationRegularFrameCoefficientFiberEvaluation_contDiffOn_two
      period hPeriod metric,
    fun current hCurrent upper first second boundary =>
      candidateANormalBoundaryChristoffelFiberEvaluation_eq_existing
        period hPeriod metric upper first second current hCurrent boundary⟩

/-- Public raw Gauss-form gate on the completed metric-normal core.  It uses
the common ambient/induced inverse domain and the existing faithful redundant
frame; unit normalization and same-action identification are deliberately
left to the next gate. -/
theorem candidate_a_normal_boundary_gauss_raw_second_form_fiber_c2_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric) :
    IsOpen
        (candidateANormalBoundaryGeometryParameterDomain
          period hPeriod metric) ∧
      (0 : Prod
        (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) ∈
        candidateANormalBoundaryGeometryParameterDomain
          period hPeriod metric ∧
      (∀ upper : Fin 4,
        ContDiffOn Real 2
          (candidateANormalBoundaryMetricNormalRegularFrameCoefficientFiberEvaluation
            period hPeriod metric upper)
          (candidateANormalBoundaryInducedMetricDomain
            period hPeriod metric)) ∧
      ContDiffOn Real 2
        (candidateANormalBoundaryMetricNormalSquareFiberEvaluation
          period hPeriod metric)
        (candidateANormalBoundaryInducedMetricDomain
          period hPeriod metric) ∧
      ∀ outer inner : NormalBoundaryTangentIndex period hPeriod,
        ContDiffOn Real 2
            (candidateANormalBoundaryGaussExtrinsicCurvatureFiberEvaluation
              period hPeriod metric outer inner)
            (candidateANormalBoundaryGeometryParameterDomain
              period hPeriod metric) ∧
          candidateANormalBoundaryGaussExtrinsicCurvatureFiberEvaluation
              period hPeriod metric outer inner =
            candidateANormalBoundaryGaussExtrinsicCurvatureFiberEvaluation
              period hPeriod metric inner outer :=
  ⟨candidateANormalBoundaryGeometryParameterDomain_isOpen
      period hPeriod metric,
    zero_mem_candidateANormalBoundaryGeometryParameterDomain
      period hPeriod metric hTransverse,
    candidateANormalBoundaryMetricNormalRegularFrameCoefficientFiberEvaluation_contDiffOn_two
      period hPeriod metric,
    candidateANormalBoundaryMetricNormalSquareFiberEvaluation_contDiffOn_two
      period hPeriod metric,
    fun outer inner =>
      ⟨candidateANormalBoundaryGaussExtrinsicCurvatureFiberEvaluation_contDiffOn_two
          period hPeriod metric outer inner,
        candidateANormalBoundaryGaussExtrinsicCurvatureFiberEvaluation_symmetric
          period hPeriod metric outer inner⟩⟩

/-- Public actual-metric gate.  It is the existing regular metric chart,
not a second metric representation. -/
theorem candidate_a_normal_boundary_actual_metric_matrix_fiber_c2_gate
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    ContDiff Real 2
        (candidateANormalBoundaryActualMetricMatrixFiberEvaluation
          period hPeriod metric) ∧
      ContDiffOn Real 2
        (candidateANormalBoundaryActualInverseMetricMatrixFiberEvaluation
          period hPeriod metric)
        (candidateANormalBoundaryMetricParameterDomain
          period hPeriod metric) :=
  ⟨candidateANormalBoundaryActualMetricMatrixFiberEvaluation_contDiff_two
      period hPeriod metric,
    candidateANormalBoundaryActualInverseMetricMatrixFiberEvaluation_contDiffOn_two
      period hPeriod metric⟩

/-- Public completed-graph tangent and induced-metric gate. -/
theorem candidate_a_normal_boundary_induced_metric_fiber_c2_gate
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    (∀ index : NormalBoundaryTangentIndex period hPeriod,
      ∀ row : Fin 4,
        ContDiff Real 2
          (candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation
            period hPeriod metric index row)) ∧
      ContDiff Real 2
        (candidateANormalBoundaryInducedMetricMatrixFiberEvaluation
          period hPeriod metric) :=
  ⟨candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation_contDiff_two
      period hPeriod metric,
    candidateANormalBoundaryInducedMetricMatrixFiberEvaluation_contDiff_two
      period hPeriod metric⟩

/-- Public faithful inverse gate for the induced metric in the existing
redundant throat frame. -/
theorem candidate_a_normal_boundary_induced_metric_inverse_fiber_c2_gate
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    IsOpen
        (candidateANormalBoundaryInducedMetricDomain
          period hPeriod metric) ∧
      ContDiffOn Real 2
        (candidateANormalBoundaryInducedRelativeLiftInverseFiberEvaluation
          period hPeriod metric)
        (candidateANormalBoundaryInducedMetricDomain
          period hPeriod metric) ∧
      ∀ current,
        current ∈ candidateANormalBoundaryInducedMetricDomain
            period hPeriod metric →
          candidateANormalBoundaryInducedRelativeLiftFiberEvaluation
                period hPeriod metric current *
              candidateANormalBoundaryInducedRelativeLiftInverseFiberEvaluation
                period hPeriod metric current = 1 ∧
            candidateANormalBoundaryInducedRelativeLiftInverseFiberEvaluation
                  period hPeriod metric current *
                candidateANormalBoundaryInducedRelativeLiftFiberEvaluation
                  period hPeriod metric current = 1 :=
  ⟨candidateANormalBoundaryInducedMetricDomain_isOpen
      period hPeriod metric,
    candidateANormalBoundaryInducedRelativeLiftInverseFiberEvaluation_contDiffOn_two
      period hPeriod metric,
    fun current hCurrent =>
      ⟨candidateANormalBoundaryInducedRelativeLift_mul_inverse
          period hPeriod metric current hCurrent,
        candidateANormalBoundaryInducedRelativeLift_inverse_mul
          period hPeriod metric current hCurrent⟩⟩

attribute [-instance] orientationBoundaryMetricSpace
    orientationBoundaryChartedSpace in
/-- Public physical-base part of H10: existing transversality, rather than a
new boundary axiom, puts zero in the faithful inverse domain. -/
theorem candidate_a_normal_boundary_induced_metric_physical_base_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric) :
    (0 : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) ∈
        candidateANormalBoundaryInducedMetricDomain period hPeriod metric ∧
      ∀ boundary : OrientationBoundary period hPeriod,
        candidateANormalBoundaryInducedRelativeLiftDeterminantFiberEvaluation
              period hPeriod metric 0 boundary =
            LinearMap.det
              (normalBoundaryBaseRelativeEndomorphism
                period hPeriod metric boundary).toLinearMap ∧
          candidateANormalBoundaryInducedRelativeLiftDeterminantFiberEvaluation
              period hPeriod metric 0 boundary ≠ 0 :=
  ⟨zero_mem_candidateANormalBoundaryInducedMetricDomain
      period hPeriod metric hTransverse,
    fun boundary =>
      ⟨candidateANormalBoundaryInducedRelativeLiftDeterminantFiberEvaluation_zero_apply
          period hPeriod metric boundary,
        candidateANormalBoundaryInducedRelativeLiftDeterminantFiberEvaluation_zero_ne_zero
          period hPeriod metric hTransverse boundary⟩⟩

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

/-! ### Local scalar root in the existing bounded boundary algebra -/

/-- The scalar Banach algebra already used by every completed boundary
coefficient. -/
abbrev CandidateANormalBoundaryScalarField :=
  BoundedContinuousFunction (OrientationBoundary period hPeriod) Real

/-- Pointwise square in the existing scalar boundary algebra. -/
def candidateANormalBoundaryScalarFieldSquare
    (field : CandidateANormalBoundaryScalarField period hPeriod) :
    CandidateANormalBoundaryScalarField period hPeriod :=
  field * field

/-- Fréchet derivative of pointwise squaring. -/
def candidateANormalBoundaryScalarFieldSylvesterOperator
    (root : CandidateANormalBoundaryScalarField period hPeriod) :
    CandidateANormalBoundaryScalarField period hPeriod →L[Real]
      CandidateANormalBoundaryScalarField period hPeriod :=
  ContinuousLinearMap.mul Real
      (CandidateANormalBoundaryScalarField period hPeriod) root +
    (ContinuousLinearMap.mul Real
      (CandidateANormalBoundaryScalarField period hPeriod)).flip root

theorem candidateANormalBoundaryScalarFieldSquare_hasFDerivAt
    (root : CandidateANormalBoundaryScalarField period hPeriod) :
    HasFDerivAt
      (candidateANormalBoundaryScalarFieldSquare period hPeriod)
      (candidateANormalBoundaryScalarFieldSylvesterOperator
        period hPeriod root) root := by
  have hIdentity : HasFDerivAt
      (fun field : CandidateANormalBoundaryScalarField period hPeriod => field)
      (ContinuousLinearMap.id Real
        (CandidateANormalBoundaryScalarField period hPeriod)) root :=
    hasFDerivAt_id root
  exact (hIdentity.mul' hIdentity).congr_fderiv rfl

theorem candidateANormalBoundaryScalarFieldSquare_contDiff_two :
    ContDiff Real 2
      (candidateANormalBoundaryScalarFieldSquare period hPeriod) := by
  change ContDiff Real 2
    (fun field : CandidateANormalBoundaryScalarField period hPeriod =>
      field * field)
  simpa using (contDiff_id.mul contDiff_id :
    ContDiff Real 2
      (fun field : CandidateANormalBoundaryScalarField period hPeriod =>
        field * field))

/-- Explicit inverse of the Sylvester derivative at a unit scalar field. -/
private def candidateANormalBoundaryScalarFieldSylvesterInverseOperator
    (root : CandidateANormalBoundaryScalarField period hPeriod) :
    CandidateANormalBoundaryScalarField period hPeriod →L[Real]
      CandidateANormalBoundaryScalarField period hPeriod :=
  (1 / 2 : Real) •
    ContinuousLinearMap.mul Real
      (CandidateANormalBoundaryScalarField period hPeriod) (Ring.inverse root)

/-- A nowhere-zero scalar boundary field is a regular root for squaring. -/
def candidateANormalBoundaryScalarFieldSylvesterEquiv
    (root : CandidateANormalBoundaryScalarField period hPeriod)
    (hUnit : IsUnit root) :
    CandidateANormalBoundaryScalarField period hPeriod ≃L[Real]
      CandidateANormalBoundaryScalarField period hPeriod :=
  ContinuousLinearEquiv.equivOfInverse
    (candidateANormalBoundaryScalarFieldSylvesterOperator
      period hPeriod root)
    (candidateANormalBoundaryScalarFieldSylvesterInverseOperator
      period hPeriod root)
    (by
      intro field
      change (1 / 2 : Real) •
          (Ring.inverse root * (root * field + field * root)) = field
      have hInverse := Ring.inverse_mul_cancel root hUnit
      ext boundary
      have hInverseAt := congrArg
        (fun current : CandidateANormalBoundaryScalarField period hPeriod =>
          current boundary) hInverse
      change (1 / 2 : Real) *
          (Ring.inverse root boundary *
            (root boundary * field boundary +
              field boundary * root boundary)) = field boundary
      change Ring.inverse root boundary * root boundary = 1 at hInverseAt
      calc
        (1 / 2) *
              (Ring.inverse root boundary *
                (root boundary * field boundary +
                  field boundary * root boundary)) =
            (1 / 2) *
              ((Ring.inverse root boundary * root boundary) * field boundary +
                (Ring.inverse root boundary * root boundary) *
                  field boundary) := by ring
        _ = field boundary := by rw [hInverseAt]; ring)
    (by
      intro field
      change root * ((1 / 2 : Real) • (Ring.inverse root * field)) +
          ((1 / 2 : Real) • (Ring.inverse root * field)) * root = field
      have hInverse := Ring.inverse_mul_cancel root hUnit
      ext boundary
      have hInverseAt := congrArg
        (fun current : CandidateANormalBoundaryScalarField period hPeriod =>
          current boundary) hInverse
      change root boundary *
            ((1 / 2 : Real) * (Ring.inverse root boundary * field boundary)) +
          ((1 / 2 : Real) *
            (Ring.inverse root boundary * field boundary)) * root boundary =
        field boundary
      change Ring.inverse root boundary * root boundary = 1 at hInverseAt
      calc
        root boundary *
              ((1 / 2) * (Ring.inverse root boundary * field boundary)) +
            (1 / 2) * (Ring.inverse root boundary * field boundary) *
              root boundary =
            (1 / 2) *
              ((Ring.inverse root boundary * root boundary) * field boundary +
                (Ring.inverse root boundary * root boundary) *
                  field boundary) := by ring
        _ = field boundary := by rw [hInverseAt]; ring)

theorem candidateANormalBoundaryScalarFieldSylvesterEquiv_forward_eq
    (root : CandidateANormalBoundaryScalarField period hPeriod)
    (hUnit : IsUnit root) :
    (candidateANormalBoundaryScalarFieldSylvesterEquiv
        period hPeriod root hUnit :
      CandidateANormalBoundaryScalarField period hPeriod →L[Real]
        CandidateANormalBoundaryScalarField period hPeriod) =
      candidateANormalBoundaryScalarFieldSylvesterOperator
        period hPeriod root :=
  rfl

/-- Open locus on which the square derivative stays invertible. -/
def candidateANormalBoundaryScalarFieldSylvesterRegularSet :
    Set (CandidateANormalBoundaryScalarField period hPeriod) :=
  {field | IsUnit field}

theorem candidateANormalBoundaryScalarFieldSylvesterRegularSet_isOpen :
    IsOpen
      (candidateANormalBoundaryScalarFieldSylvesterRegularSet
        period hPeriod) :=
  Units.isOpen

/-- IFT square chart centered at the positive unit field. -/
def candidateANormalBoundaryScalarFieldBaseSquareChart :
    OpenPartialHomeomorph
      (CandidateANormalBoundaryScalarField period hPeriod)
      (CandidateANormalBoundaryScalarField period hPeriod) :=
  (candidateANormalBoundaryScalarFieldSquare_contDiff_two
      period hPeriod).contDiffAt.toOpenPartialHomeomorph
    (candidateANormalBoundaryScalarFieldSquare period hPeriod)
    ((candidateANormalBoundaryScalarFieldSquare_hasFDerivAt
        period hPeriod 1).congr_fderiv
      (candidateANormalBoundaryScalarFieldSylvesterEquiv_forward_eq
        period hPeriod 1 isUnit_one).symm)
    (by norm_num)

/-- Restriction of the local square chart to regular roots. -/
def candidateANormalBoundaryScalarFieldLocalSquareChart :
    OpenPartialHomeomorph
      (CandidateANormalBoundaryScalarField period hPeriod)
      (CandidateANormalBoundaryScalarField period hPeriod) :=
  (candidateANormalBoundaryScalarFieldBaseSquareChart
    period hPeriod).restrOpen
      (candidateANormalBoundaryScalarFieldSylvesterRegularSet
        period hPeriod)
      (candidateANormalBoundaryScalarFieldSylvesterRegularSet_isOpen
        period hPeriod)

/-- Open target of the positive local square-root branch. -/
def candidateANormalBoundaryScalarFieldLocalRootTarget :
    Set (CandidateANormalBoundaryScalarField period hPeriod) :=
  (candidateANormalBoundaryScalarFieldLocalSquareChart
    period hPeriod).target

theorem candidateANormalBoundaryScalarFieldLocalRootTarget_isOpen :
    IsOpen
      (candidateANormalBoundaryScalarFieldLocalRootTarget
        period hPeriod) :=
  (candidateANormalBoundaryScalarFieldLocalSquareChart
    period hPeriod).open_target

theorem candidateANormalBoundaryScalarFieldOne_mem_localSquareChart_source :
    (1 : CandidateANormalBoundaryScalarField period hPeriod) ∈
      (candidateANormalBoundaryScalarFieldLocalSquareChart
        period hPeriod).source := by
  rw [candidateANormalBoundaryScalarFieldLocalSquareChart,
    OpenPartialHomeomorph.restrOpen_source]
  exact ⟨
    (candidateANormalBoundaryScalarFieldSquare_contDiff_two
        period hPeriod).contDiffAt.mem_toOpenPartialHomeomorph_source
      ((candidateANormalBoundaryScalarFieldSquare_hasFDerivAt
          period hPeriod 1).congr_fderiv
        (candidateANormalBoundaryScalarFieldSylvesterEquiv_forward_eq
          period hPeriod 1 isUnit_one).symm)
      (by norm_num),
    isUnit_one⟩

@[simp]
theorem candidateANormalBoundaryScalarFieldSquare_one :
    candidateANormalBoundaryScalarFieldSquare period hPeriod 1 = 1 := by
  simp [candidateANormalBoundaryScalarFieldSquare]

theorem candidateANormalBoundaryScalarFieldOne_mem_localRootTarget :
    (1 : CandidateANormalBoundaryScalarField period hPeriod) ∈
      candidateANormalBoundaryScalarFieldLocalRootTarget
        period hPeriod := by
  rw [← candidateANormalBoundaryScalarFieldSquare_one period hPeriod]
  exact (candidateANormalBoundaryScalarFieldLocalSquareChart
    period hPeriod).map_source
      (candidateANormalBoundaryScalarFieldOne_mem_localSquareChart_source
        period hPeriod)

/-- Positive local square-root branch in the bounded boundary algebra. -/
def candidateANormalBoundaryScalarFieldLocalRootBranch :
    CandidateANormalBoundaryScalarField period hPeriod →
      CandidateANormalBoundaryScalarField period hPeriod :=
  (candidateANormalBoundaryScalarFieldLocalSquareChart
    period hPeriod).symm

theorem candidateANormalBoundaryScalarFieldLocalRootBranch_square
    {nearby : CandidateANormalBoundaryScalarField period hPeriod}
    (hNearby : nearby ∈
      candidateANormalBoundaryScalarFieldLocalRootTarget
        period hPeriod) :
    candidateANormalBoundaryScalarFieldSquare period hPeriod
        (candidateANormalBoundaryScalarFieldLocalRootBranch
          period hPeriod nearby) = nearby :=
  (candidateANormalBoundaryScalarFieldLocalSquareChart
    period hPeriod).right_inv hNearby

@[simp]
theorem candidateANormalBoundaryScalarFieldLocalRootBranch_at_one :
    candidateANormalBoundaryScalarFieldLocalRootBranch period hPeriod 1 =
      (1 : CandidateANormalBoundaryScalarField period hPeriod) := by
  calc
    candidateANormalBoundaryScalarFieldLocalRootBranch period hPeriod 1 =
        candidateANormalBoundaryScalarFieldLocalRootBranch period hPeriod
          (candidateANormalBoundaryScalarFieldSquare period hPeriod 1) := by
      rw [candidateANormalBoundaryScalarFieldSquare_one]
    _ = 1 :=
      (candidateANormalBoundaryScalarFieldLocalSquareChart
        period hPeriod).left_inv
          (candidateANormalBoundaryScalarFieldOne_mem_localSquareChart_source
            period hPeriod)

theorem candidateANormalBoundaryScalarFieldLocalRootBranch_contDiffAt
    (nearby : CandidateANormalBoundaryScalarField period hPeriod)
    (hNearby : nearby ∈
      candidateANormalBoundaryScalarFieldLocalRootTarget
        period hPeriod) :
    ContDiffAt Real 2
      (candidateANormalBoundaryScalarFieldLocalRootBranch period hPeriod)
      nearby := by
  have hSource :=
    (candidateANormalBoundaryScalarFieldLocalSquareChart
      period hPeriod).map_target hNearby
  rw [candidateANormalBoundaryScalarFieldLocalSquareChart,
    OpenPartialHomeomorph.restrOpen_source] at hSource
  apply (candidateANormalBoundaryScalarFieldLocalSquareChart
    period hPeriod).contDiffAt_symm hNearby
      (f₀' := candidateANormalBoundaryScalarFieldSylvesterEquiv
        period hPeriod
        ((candidateANormalBoundaryScalarFieldLocalSquareChart
          period hPeriod).symm nearby) hSource.2)
  · exact (candidateANormalBoundaryScalarFieldSquare_hasFDerivAt
      period hPeriod
      ((candidateANormalBoundaryScalarFieldLocalSquareChart
        period hPeriod).symm nearby)).congr_fderiv
        (candidateANormalBoundaryScalarFieldSylvesterEquiv_forward_eq
          period hPeriod
          ((candidateANormalBoundaryScalarFieldLocalSquareChart
            period hPeriod).symm nearby) hSource.2).symm
  · exact (candidateANormalBoundaryScalarFieldSquare_contDiff_two
      period hPeriod).contDiffAt

theorem candidateANormalBoundaryScalarFieldLocalRootBranch_contDiffOn :
    ContDiffOn Real 2
      (candidateANormalBoundaryScalarFieldLocalRootBranch period hPeriod)
      (candidateANormalBoundaryScalarFieldLocalRootTarget
        period hPeriod) := by
  intro nearby hNearby
  exact (candidateANormalBoundaryScalarFieldLocalRootBranch_contDiffAt
    period hPeriod nearby hNearby).contDiffWithinAt

/-! ### Physical-base identification of the completed projected normal -/

/-- Ambient vector reconstructed from the completed normal coefficients at
the physical base. -/
def candidateANormalBoundaryMetricNormalVectorAtBase
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (boundary : OrientationBoundary period hPeriod) :
    TangentSpace coverModelWithCorners
      (normalBoundaryLatitudeFiberPoint period hPeriod boundary 0) :=
  ∑ upper : Fin 4,
    candidateANormalBoundaryMetricNormalRegularFrameCoefficientFiberEvaluation
          period hPeriod metric upper 0 boundary •
      metric.frame upper
        (normalBoundaryLatitudeFiberPoint period hPeriod boundary 0)

/-- The scalar completed square is exactly the metric square of the
reconstructed ambient vector at the base. -/
theorem
    candidateANormalBoundaryMetricNormalSquareFiberEvaluation_zero_apply_eq_vector
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (boundary : OrientationBoundary period hPeriod) :
    candidateANormalBoundaryMetricNormalSquareFiberEvaluation
        period hPeriod metric 0 boundary =
      metric.metric.tensor.tensor
        (normalBoundaryLatitudeFiberPoint period hPeriod boundary 0)
        (candidateANormalBoundaryMetricNormalVectorAtBase
          period hPeriod metric boundary)
        (candidateANormalBoundaryMetricNormalVectorAtBase
          period hPeriod metric boundary) := by
  classical
  unfold candidateANormalBoundaryMetricNormalSquareFiberEvaluation
    candidateANormalBoundaryMetricNormalVectorAtBase
  simp only [BoundedContinuousFunction.sum_apply,
    BoundedContinuousFunction.mul_apply]
  have hGraph :
      normalBoundaryC2Graph period hPeriod 0 0 boundary =
        normalBoundaryLatitudeFiberPoint period hPeriod boundary 0 := by
    symm
    simpa using normalBoundaryLatitudeFiberPoint_graph
      period hPeriod 0 0 boundary
  simp_rw [candidateANormalBoundaryActualMetricMatrixFiberEvaluation_zero_apply,
    hGraph, regularFrameMetricMatrix_apply]
  rw [map_sum]
  simp only [map_smul, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro first _
  rw [map_sum]
  simp only [map_smul, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, Finset.mul_sum,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro second _
  rw [metric.metric.tensor.symmetric]
  ring

attribute [-instance] orientationBoundaryMetricSpace
    orientationBoundaryChartedSpace in
/-- Pairing of the canonical base latitude vector with the differential of
the zero collar slice. -/
def candidateANormalBoundaryBaseVerticalTangentialCovector
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (boundary : OrientationBoundary period hPeriod) :
    TangentSpace throatCoverModelWithCorners boundary →L[Real] Real := by
  letI : TopologicalSpace (OrientationBoundary period hPeriod) :=
    instTopologicalSpaceQuotient
  letI : ChartedSpace ThroatCoverModel
      (OrientationBoundary period hPeriod) :=
    AddAction.instChartedSpaceQuotient
  exact (metric.metric.tensor.tensor
      (normalBoundaryLatitudeFiberPoint period hPeriod boundary 0)
      (normalBoundaryLatitudeFiberLift period hPeriod boundary 0).2).comp
    (mfderiv throatCoverModelWithCorners coverModelWithCorners
      (fun point : OrientationBoundary period hPeriod =>
        normalBoundaryLatitudeFiberPoint period hPeriod point 0) boundary)

attribute [-instance] orientationBoundaryMetricSpace
    orientationBoundaryChartedSpace in
/-- At zero the completed vertical--tangent pairing is the preceding genuine
ambient pairing on every installed throat generator. -/
theorem
    candidateANormalBoundaryVerticalTangentialPairingFiberEvaluation_zero_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (index : NormalBoundaryTangentIndex period hPeriod)
    (boundary : OrientationBoundary period hPeriod) :
    candidateANormalBoundaryVerticalTangentialPairingFiberEvaluation
        period hPeriod metric index 0 boundary =
      candidateANormalBoundaryBaseVerticalTangentialCovector
        period hPeriod metric boundary
        ((finiteSmoothThroatGeneratingFrame
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
            |>.vectorAt boundary index) := by
  classical
  have hVerticalCoefficient (row : Fin 4) :
      candidateANormalBoundaryVerticalRegularFrameCoefficientFiberEvaluation
          period hPeriod metric row 0 boundary =
        normalBoundaryLatitudeVerticalRegularFrameCoefficient period hPeriod
          metric row (boundary, 0) := by
    change candidateANormalBoundaryVerticalRegularFrameCoefficientFiberEvaluation
      period hPeriod metric row (0, 0) boundary = _
    rw [candidateANormalBoundaryVerticalRegularFrameCoefficientFiberEvaluation_apply]
    simp
  unfold candidateANormalBoundaryVerticalTangentialPairingFiberEvaluation
  simp only [BoundedContinuousFunction.sum_apply,
    BoundedContinuousFunction.mul_apply,
    candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation_zero_apply]
  simp_rw [hVerticalCoefficient]
  have hGraph :
      normalBoundaryC2Graph period hPeriod 0 0 boundary =
        normalBoundaryLatitudeFiberPoint period hPeriod boundary 0 := by
    symm
    simpa using normalBoundaryLatitudeFiberPoint_graph
      period hPeriod 0 0 boundary
  simp_rw [candidateANormalBoundaryActualMetricMatrixFiberEvaluation_zero_apply,
    hGraph, regularFrameMetricMatrix_apply]
  have hVertical := normalBoundaryLatitudeVerticalRegularFrame_reconstructs
    period hPeriod metric (boundary, 0)
  rw [normalBoundaryLatitudeFiberLift_base] at hVertical
  simp only [regularGeneralLorentzMetricSmoothD8Frame] at hVertical
  have hTangent := normalBoundaryLatitudeHorizontalRegularFrame_reconstructs
    period hPeriod metric index (boundary, 0)
  rw [normalBoundaryLatitudeHorizontalFiberLift_base] at hTangent
  simp only [regularGeneralLorentzMetricSmoothD8Frame] at hTangent
  have hHorizontal :=
    normalBoundaryLatitudeHorizontalFiberLift_zero_tangentMap
      period hPeriod index boundary
  unfold candidateANormalBoundaryBaseVerticalTangentialCovector
  simp only [ContinuousLinearMap.comp_apply]
  change _ = metric.metric.tensor.tensor
    (normalBoundaryLatitudeFiberPoint period hPeriod boundary 0)
    (normalBoundaryLatitudeFiberLift period hPeriod boundary 0).2
    (normalBoundaryLatitudeZeroHorizontalTangentMap
      period hPeriod index boundary).2
  rw [← hHorizontal, hVertical, hTangent]
  simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul,
    Finset.mul_sum, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  ring

attribute [-instance] orientationBoundaryMetricSpace
    orientationBoundaryChartedSpace in
/-- At the physical base the fixed reference-dual conversion is exactly the
canonical finite-frame analysis of the raised genuine tangent covector. -/
theorem
    candidateANormalBoundaryVerticalTangentialReferenceDualFiberEvaluation_zero_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (row : NormalBoundaryTangentIndex period hPeriod)
    (boundary : OrientationBoundary period hPeriod) :
    candidateANormalBoundaryVerticalTangentialReferenceDualFiberEvaluation
        period hPeriod metric row 0 boundary =
      intrinsicThroatFiniteFrameAnalysisAt
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
        (finiteSmoothThroatGeneratingFrame
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
        boundary
        (intrinsicThroatInverseMusical
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
          boundary
          (candidateANormalBoundaryBaseVerticalTangentialCovector
            period hPeriod metric boundary)) row := by
  classical
  have hApplied := congrFun
    (intrinsicThroatFiniteFrameEndomorphismMatrixAt_inverseOperator_mulVec
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
      (finiteSmoothThroatGeneratingFrame
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
      boundary
      (candidateANormalBoundaryBaseVerticalTangentialCovector
        period hPeriod metric boundary)) row
  unfold
    candidateANormalBoundaryVerticalTangentialReferenceDualFiberEvaluation
  simp only [BoundedContinuousFunction.sum_apply,
    BoundedContinuousFunction.mul_apply,
    candidateANormalBoundaryVerticalTangentialPairingFiberEvaluation_zero_apply,
    normalBoundaryReferenceDualCoefficientMatrix_apply_eq_encoding_inverse]
  unfold Matrix.mulVec dotProduct at hApplied
  convert hApplied using 1 <;> rfl

attribute [-instance] orientationBoundaryMetricSpace
    orientationBoundaryChartedSpace in
/-- Genuine throat tangent reconstructed from the completed projection
coefficients at the physical base. -/
def candidateANormalBoundaryTangentialProjectionVectorAtBase
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (boundary : OrientationBoundary period hPeriod) :
    TangentSpace throatCoverModelWithCorners boundary :=
  intrinsicThroatFiniteFrameSynthesisAt
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
    (finiteSmoothThroatGeneratingFrame
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
    boundary
    (fun row =>
      candidateANormalBoundaryTangentialProjectionCoefficientFiberEvaluation
        period hPeriod metric row 0 boundary)

attribute [-instance] orientationBoundaryMetricSpace
    orientationBoundaryChartedSpace in
/-- The faithful matrix solve reconstructs the intrinsic raised vertical
pairing, rather than merely solving in redundant coefficients. -/
theorem candidateANormalBoundaryTangentialProjectionVectorAtBase_relative
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric)
    (boundary : OrientationBoundary period hPeriod) :
    normalBoundaryBaseRelativeEndomorphism period hPeriod metric boundary
        (candidateANormalBoundaryTangentialProjectionVectorAtBase
          period hPeriod metric boundary) =
      intrinsicThroatInverseMusical
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
        boundary
        (candidateANormalBoundaryBaseVerticalTangentialCovector
          period hPeriod metric boundary) := by
  classical
  let lift := candidateANormalBoundaryInducedRelativeLiftFiberEvaluation
    period hPeriod metric 0
  let inverse :=
    candidateANormalBoundaryInducedRelativeLiftInverseFiberEvaluation
      period hPeriod metric 0
  let reference := fun row : NormalBoundaryTangentIndex period hPeriod =>
    candidateANormalBoundaryVerticalTangentialReferenceDualFiberEvaluation
      period hPeriod metric row 0
  let coefficients := fun row : NormalBoundaryTangentIndex period hPeriod =>
    candidateANormalBoundaryTangentialProjectionCoefficientFiberEvaluation
      period hPeriod metric row 0
  have hCoefficients : coefficients = inverse.mulVec reference := by
    funext row
    unfold coefficients inverse reference
      candidateANormalBoundaryTangentialProjectionCoefficientFiberEvaluation
      Matrix.mulVec dotProduct
    rfl
  have hInverse := candidateANormalBoundaryInducedRelativeLift_mul_inverse
    period hPeriod metric 0
      (zero_mem_candidateANormalBoundaryInducedMetricDomain
        period hPeriod metric hTransverse)
  have hSolve : lift.mulVec coefficients = reference := by
    rw [hCoefficients, Matrix.mulVec_mulVec]
    have hProduct : lift * inverse = 1 := by
      simpa only [lift, inverse] using hInverse
    rw [hProduct, Matrix.one_mulVec]
  have hSolveAt :
      (intrinsicThroatFiniteFrameLiftAt
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
        (finiteSmoothThroatGeneratingFrame
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
        boundary
        (normalBoundaryBaseRelativeEndomorphism
          period hPeriod metric boundary).toLinearMap).mulVec
          (fun row => coefficients row boundary) =
        intrinsicThroatFiniteFrameAnalysisAt
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
          (finiteSmoothThroatGeneratingFrame
            (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
          boundary
          (intrinsicThroatInverseMusical
            (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
            boundary
            (candidateANormalBoundaryBaseVerticalTangentialCovector
              period hPeriod metric boundary)) := by
    funext row
    have hApplied := congrArg
      (fun field : BoundedContinuousFunction
          (OrientationBoundary period hPeriod) Real => field boundary)
      (congrFun hSolve row)
    unfold lift reference at hApplied
    unfold Matrix.mulVec dotProduct at hApplied ⊢
    simp only [BoundedContinuousFunction.sum_apply,
      BoundedContinuousFunction.mul_apply,
      candidateANormalBoundaryInducedRelativeLiftFiberEvaluation_zero_apply,
      candidateANormalBoundaryVerticalTangentialReferenceDualFiberEvaluation_zero_apply]
      at hApplied
    convert hApplied using 1 <;> rfl
  have hSynthesis := congrArg
    (intrinsicThroatFiniteFrameSynthesisAt
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
      (finiteSmoothThroatGeneratingFrame
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
      boundary) hSolveAt
  rw [intrinsicThroatFiniteFrameSynthesisAt_liftAt_mulVec] at hSynthesis
  have hReconstruct := LinearMap.congr_fun
    (intrinsicThroatFiniteFrameSynthesisAt_comp_analysisAt
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
      (finiteSmoothThroatGeneratingFrame
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
      boundary)
    (intrinsicThroatInverseMusical
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
      boundary
      (candidateANormalBoundaryBaseVerticalTangentialCovector
        period hPeriod metric boundary))
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at hReconstruct
  rw [hReconstruct] at hSynthesis
  dsimp only [coefficients] at hSynthesis
  unfold candidateANormalBoundaryTangentialProjectionVectorAtBase
  convert hSynthesis using 1 <;> rfl

attribute [-instance] orientationBoundaryMetricSpace
    orientationBoundaryChartedSpace in
/-- The reconstructed projection solves the genuine pulled-back induced
musical equation. -/
theorem candidateANormalBoundaryTangentialProjectionVectorAtBase_musical
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric)
    (boundary : OrientationBoundary period hPeriod) :
    normalBoundaryBaseInducedMetricMusical period hPeriod metric boundary
        (candidateANormalBoundaryTangentialProjectionVectorAtBase
          period hPeriod metric boundary) =
      candidateANormalBoundaryBaseVerticalTangentialCovector
        period hPeriod metric boundary := by
  have hRelative :=
    candidateANormalBoundaryTangentialProjectionVectorAtBase_relative
      period hPeriod metric hTransverse boundary
  rw [normalBoundaryBaseRelativeEndomorphism_apply] at hRelative
  exact (intrinsicThroatInverseMusical
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
    boundary).injective hRelative

attribute [-instance] orientationBoundaryMetricSpace
    orientationBoundaryChartedSpace in
/-- The differential of the zero latitude slice factors through the installed
orientation tangent equivalence for every tangent, not only frame generators. -/
theorem normalBoundaryLatitudeZeroDerivative_eq_fixedThroat
    (boundary : OrientationBoundary period hPeriod)
    (vector : TangentSpace throatCoverModelWithCorners boundary) :
    mfderiv throatCoverModelWithCorners coverModelWithCorners
        (fun point : OrientationBoundary period hPeriod =>
          normalBoundaryLatitudeFiberPoint period hPeriod point 0)
        boundary vector =
      mfderiv throatCoverModelWithCorners coverModelWithCorners
        (fixedThroatQuotientInclusion period hPeriod)
        (orientationDoubleToThroat period hPeriod boundary)
        (normalBoundaryOrientationTangentEquiv period hPeriod boundary vector) := by
  letI : TopologicalSpace (OrientationBoundary period hPeriod) :=
    instTopologicalSpaceQuotient
  letI : ChartedSpace ThroatCoverModel
      (OrientationBoundary period hPeriod) :=
    AddAction.instChartedSpaceQuotient
  have hOuter : MDifferentiableAt throatCoverModelWithCorners
      coverModelWithCorners (fixedThroatQuotientInclusion period hPeriod)
      (orientationDoubleToThroat period hPeriod boundary) :=
    (fixedThroatQuotientInclusion_contMDiff period hPeriod)
      |>.mdifferentiableAt (by simp)
  have hInner : MDifferentiableAt throatCoverModelWithCorners
      throatCoverModelWithCorners (orientationDoubleToThroat period hPeriod)
      boundary :=
    (orientationDoubleToThroat_contMDiff period hPeriod)
      |>.mdifferentiableAt (by simp)
  have hComp := mfderiv_comp_apply boundary hOuter hInner vector
  have hMap :
      fixedThroatQuotientInclusion period hPeriod ∘
          orientationDoubleToThroat period hPeriod =
        fun point : OrientationBoundary period hPeriod =>
          normalBoundaryLatitudeFiberPoint period hPeriod point 0 := by
    funext point
    exact (normalBoundaryLatitudeFiberPoint_zero period hPeriod point).symm
  rw [hMap] at hComp
  rw [normalBoundaryOrientationTangentEquiv_apply] at ⊢
  exact hComp

attribute [-instance] orientationBoundaryMetricSpace
    orientationBoundaryChartedSpace in
/-- Total tangent-bundle form of the preceding zero-slice factorization. -/
theorem normalBoundaryLatitudeZeroTangentMap_eq_fixedThroat
    (boundary : OrientationBoundary period hPeriod)
    (vector : TangentSpace throatCoverModelWithCorners boundary) :
    tangentMap throatCoverModelWithCorners coverModelWithCorners
        (fun point : OrientationBoundary period hPeriod =>
          normalBoundaryLatitudeFiberPoint period hPeriod point 0)
        ⟨boundary, vector⟩ =
      tangentMap throatCoverModelWithCorners coverModelWithCorners
        (fixedThroatQuotientInclusion period hPeriod)
        ⟨orientationDoubleToThroat period hPeriod boundary,
          normalBoundaryOrientationTangentEquiv period hPeriod boundary vector⟩ := by
  apply Bundle.TotalSpace.ext
  · exact normalBoundaryLatitudeFiberPoint_zero period hPeriod boundary
  · exact (normalBoundaryLatitudeZeroDerivative_eq_fixedThroat
      period hPeriod boundary vector).heq

attribute [-instance] orientationBoundaryMetricSpace
    orientationBoundaryChartedSpace in
/-- The pulled-back base musical is the actual ambient metric on zero-slice
differentials. -/
theorem normalBoundaryBaseInducedMetricMusical_apply_eq_zeroDerivative
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (boundary : OrientationBoundary period hPeriod)
    (first second : TangentSpace throatCoverModelWithCorners boundary) :
    normalBoundaryBaseInducedMetricMusical period hPeriod metric boundary
        first second =
      metric.metric.tensor.tensor
        (normalBoundaryLatitudeFiberPoint period hPeriod boundary 0)
        (mfderiv throatCoverModelWithCorners coverModelWithCorners
          (fun point : OrientationBoundary period hPeriod =>
            normalBoundaryLatitudeFiberPoint period hPeriod point 0)
          boundary first)
        (mfderiv throatCoverModelWithCorners coverModelWithCorners
          (fun point : OrientationBoundary period hPeriod =>
            normalBoundaryLatitudeFiberPoint period hPeriod point 0)
          boundary second) := by
  rw [normalBoundaryBaseInducedMetricMusical_apply,
    generalLorentzMetricThroatTraceValue_apply]
  change metric.metric.tensor.tensor
      (tangentMap throatCoverModelWithCorners coverModelWithCorners
        (fixedThroatQuotientInclusion period hPeriod)
        ⟨orientationDoubleToThroat period hPeriod boundary,
          normalBoundaryOrientationTangentEquiv period hPeriod boundary first⟩).1
      (tangentMap throatCoverModelWithCorners coverModelWithCorners
        (fixedThroatQuotientInclusion period hPeriod)
        ⟨orientationDoubleToThroat period hPeriod boundary,
          normalBoundaryOrientationTangentEquiv period hPeriod boundary first⟩).2
      (tangentMap throatCoverModelWithCorners coverModelWithCorners
        (fixedThroatQuotientInclusion period hPeriod)
        ⟨orientationDoubleToThroat period hPeriod boundary,
          normalBoundaryOrientationTangentEquiv period hPeriod boundary second⟩).2 =
    metric.metric.tensor.tensor
      (tangentMap throatCoverModelWithCorners coverModelWithCorners
        (fun point : OrientationBoundary period hPeriod =>
          normalBoundaryLatitudeFiberPoint period hPeriod point 0)
        ⟨boundary, first⟩).1
      (tangentMap throatCoverModelWithCorners coverModelWithCorners
        (fun point : OrientationBoundary period hPeriod =>
          normalBoundaryLatitudeFiberPoint period hPeriod point 0)
        ⟨boundary, first⟩).2
      (tangentMap throatCoverModelWithCorners coverModelWithCorners
        (fun point : OrientationBoundary period hPeriod =>
          normalBoundaryLatitudeFiberPoint period hPeriod point 0)
        ⟨boundary, second⟩).2
  rw [normalBoundaryLatitudeZeroTangentMap_eq_fixedThroat,
    normalBoundaryLatitudeZeroTangentMap_eq_fixedThroat]

attribute [-instance] orientationBoundaryMetricSpace
    orientationBoundaryChartedSpace in
/-- Each installed throat generator, differentiated through the zero collar
slice, is reconstructed by its already available ambient regular-frame
coefficients. -/
theorem normalBoundaryLatitudeZeroDerivative_frame_eq_regularFrameSum
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (index : NormalBoundaryTangentIndex period hPeriod)
    (boundary : OrientationBoundary period hPeriod) :
    mfderiv throatCoverModelWithCorners coverModelWithCorners
        (fun point : OrientationBoundary period hPeriod =>
          normalBoundaryLatitudeFiberPoint period hPeriod point 0)
        boundary
        ((finiteSmoothThroatGeneratingFrame
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)).vectorAt
            boundary index) =
      ∑ row : Fin 4,
        normalBoundaryLatitudeHorizontalRegularFrameCoefficient
              period hPeriod metric index row (boundary, 0) •
          metric.frame row
            (normalBoundaryLatitudeFiberPoint period hPeriod boundary 0) := by
  have hTangent := normalBoundaryLatitudeHorizontalRegularFrame_reconstructs
    period hPeriod metric index (boundary, 0)
  rw [normalBoundaryLatitudeHorizontalFiberLift_base] at hTangent
  simp only [regularGeneralLorentzMetricSmoothD8Frame] at hTangent
  have hHorizontal :=
    normalBoundaryLatitudeHorizontalFiberLift_zero_tangentMap
      period hPeriod index boundary
  change (normalBoundaryLatitudeZeroHorizontalTangentMap
      period hPeriod index boundary).2 = _
  rw [← hHorizontal, hTangent]

attribute [-instance] orientationBoundaryMetricSpace
    orientationBoundaryChartedSpace in
/-- Ambient zero-slice differential of the reconstructed tangential
projection. -/
def candidateANormalBoundaryTangentialProjectionAmbientVectorAtBase
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (boundary : OrientationBoundary period hPeriod) :
    TangentSpace coverModelWithCorners
      (normalBoundaryLatitudeFiberPoint period hPeriod boundary 0) :=
  mfderiv throatCoverModelWithCorners coverModelWithCorners
    (fun point : OrientationBoundary period hPeriod =>
      normalBoundaryLatitudeFiberPoint period hPeriod point 0)
    boundary
    (candidateANormalBoundaryTangentialProjectionVectorAtBase
      period hPeriod metric boundary)

attribute [-instance] orientationBoundaryMetricSpace
    orientationBoundaryChartedSpace in
/-- The ambient projection is the finite linear combination of the fixed-base
zero-slice derivatives of the intrinsic throat frame. -/
theorem candidateANormalBoundaryTangentialProjectionAmbientVectorAtBase_eq_sum
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (boundary : OrientationBoundary period hPeriod) :
    candidateANormalBoundaryTangentialProjectionAmbientVectorAtBase
        period hPeriod metric boundary =
      ∑ index : NormalBoundaryTangentIndex period hPeriod,
        candidateANormalBoundaryTangentialProjectionCoefficientFiberEvaluation
              period hPeriod metric index 0 boundary •
          mfderiv throatCoverModelWithCorners coverModelWithCorners
            (fun point : OrientationBoundary period hPeriod =>
              normalBoundaryLatitudeFiberPoint period hPeriod point 0)
            boundary
            ((finiteSmoothThroatGeneratingFrame
              (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)).vectorAt
                boundary index) := by
  classical
  let derivative := mfderiv throatCoverModelWithCorners coverModelWithCorners
    (fun point : OrientationBoundary period hPeriod =>
      normalBoundaryLatitudeFiberPoint period hPeriod point 0) boundary
  have hSynthesis := intrinsicThroatFiniteFrameSynthesisAt_apply
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
    (finiteSmoothThroatGeneratingFrame
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
    boundary
    (fun row =>
      candidateANormalBoundaryTangentialProjectionCoefficientFiberEvaluation
        period hPeriod metric row 0 boundary)
  unfold candidateANormalBoundaryTangentialProjectionAmbientVectorAtBase
    candidateANormalBoundaryTangentialProjectionVectorAtBase
  change derivative
      (intrinsicThroatFiniteFrameSynthesisAt
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
        (finiteSmoothThroatGeneratingFrame
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
        boundary
        (fun row =>
          candidateANormalBoundaryTangentialProjectionCoefficientFiberEvaluation
            period hPeriod metric row 0 boundary)) = _
  calc
    _ = derivative
        (∑ index : NormalBoundaryTangentIndex period hPeriod,
          candidateANormalBoundaryTangentialProjectionCoefficientFiberEvaluation
                period hPeriod metric index 0 boundary •
            (finiteSmoothThroatGeneratingFrame
              (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)).vectorAt
                boundary index) := congrArg derivative hSynthesis
    _ = ∑ index : NormalBoundaryTangentIndex period hPeriod,
          derivative
            (candidateANormalBoundaryTangentialProjectionCoefficientFiberEvaluation
                  period hPeriod metric index 0 boundary •
              (finiteSmoothThroatGeneratingFrame
                (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)).vectorAt
                  boundary index) := map_sum derivative _ Finset.univ
    _ = _ := by
      apply Finset.sum_congr rfl
      intro index _
      exact map_smul derivative
        (candidateANormalBoundaryTangentialProjectionCoefficientFiberEvaluation
          period hPeriod metric index 0 boundary)
        ((finiteSmoothThroatGeneratingFrame
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)).vectorAt
            boundary index)

attribute [-instance] orientationBoundaryMetricSpace
    orientationBoundaryChartedSpace in
/-- At the physical base the completed finite-frame normal is the canonical
latitude vector minus its reconstructed tangential projection. -/
theorem candidateANormalBoundaryMetricNormalVectorAtBase_eq_vertical_sub_projection
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (boundary : OrientationBoundary period hPeriod) :
    candidateANormalBoundaryMetricNormalVectorAtBase
        period hPeriod metric boundary =
      (∑ row : Fin 4,
        normalBoundaryLatitudeVerticalRegularFrameCoefficient
              period hPeriod metric row (boundary, 0) •
          metric.frame row
            (normalBoundaryLatitudeFiberPoint period hPeriod boundary 0)) -
        candidateANormalBoundaryTangentialProjectionAmbientVectorAtBase
          period hPeriod metric boundary := by
  classical
  have hVerticalCoefficient (row : Fin 4) :
      candidateANormalBoundaryVerticalRegularFrameCoefficientFiberEvaluation
          period hPeriod metric row 0 boundary =
        normalBoundaryLatitudeVerticalRegularFrameCoefficient period hPeriod
          metric row (boundary, 0) := by
    change candidateANormalBoundaryVerticalRegularFrameCoefficientFiberEvaluation
      period hPeriod metric row (0, 0) boundary = _
    rw [candidateANormalBoundaryVerticalRegularFrameCoefficientFiberEvaluation_apply]
    simp
  have hProjection :=
    candidateANormalBoundaryTangentialProjectionAmbientVectorAtBase_eq_sum
      period hPeriod metric boundary
  have hFrame (index : NormalBoundaryTangentIndex period hPeriod) :=
    normalBoundaryLatitudeZeroDerivative_frame_eq_regularFrameSum
      period hPeriod metric index boundary
  have hProjectionExpansion :
      candidateANormalBoundaryTangentialProjectionAmbientVectorAtBase
          period hPeriod metric boundary =
        ∑ index : NormalBoundaryTangentIndex period hPeriod,
          candidateANormalBoundaryTangentialProjectionCoefficientFiberEvaluation
                period hPeriod metric index 0 boundary •
            ∑ row : Fin 4,
              normalBoundaryLatitudeHorizontalRegularFrameCoefficient
                    period hPeriod metric index row (boundary, 0) •
                metric.frame row
                  (normalBoundaryLatitudeFiberPoint
                    period hPeriod boundary 0) := by
    rw [hProjection]
    apply Finset.sum_congr rfl
    intro index _
    rw [hFrame index]
  rw [hProjectionExpansion]
  unfold candidateANormalBoundaryMetricNormalVectorAtBase
    candidateANormalBoundaryMetricNormalRegularFrameCoefficientFiberEvaluation
  simp only [BoundedContinuousFunction.sub_apply,
    BoundedContinuousFunction.sum_apply, BoundedContinuousFunction.mul_apply,
    hVerticalCoefficient,
    candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation_zero_apply]
  simp only [sub_smul, Finset.sum_sub_distrib, Finset.sum_smul,
    Finset.smul_sum, smul_smul]
  congr 1
  rw [Finset.sum_comm]

attribute [-instance] orientationBoundaryMetricSpace
    orientationBoundaryChartedSpace in
/-- The reconstructed completed normal is orthogonal to every tangent of the
physical zero slice. -/
theorem candidateANormalBoundaryMetricNormalVectorAtBase_orthogonal
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric)
    (boundary : OrientationBoundary period hPeriod)
    (tangent : TangentSpace throatCoverModelWithCorners boundary) :
    metric.metric.tensor.tensor
        (normalBoundaryLatitudeFiberPoint period hPeriod boundary 0)
        (candidateANormalBoundaryMetricNormalVectorAtBase
          period hPeriod metric boundary)
        (mfderiv throatCoverModelWithCorners coverModelWithCorners
          (fun point : OrientationBoundary period hPeriod =>
            normalBoundaryLatitudeFiberPoint period hPeriod point 0)
          boundary tangent) = 0 := by
  have hVertical := normalBoundaryLatitudeVerticalRegularFrame_reconstructs
    period hPeriod metric (boundary, 0)
  rw [normalBoundaryLatitudeFiberLift_base] at hVertical
  simp only [regularGeneralLorentzMetricSmoothD8Frame] at hVertical
  have hMusical := congrArg
    (fun covector : TangentSpace throatCoverModelWithCorners boundary →L[Real] Real =>
      covector tangent)
    (candidateANormalBoundaryTangentialProjectionVectorAtBase_musical
      period hPeriod metric hTransverse boundary)
  rw [normalBoundaryBaseInducedMetricMusical_apply_eq_zeroDerivative]
    at hMusical
  unfold candidateANormalBoundaryBaseVerticalTangentialCovector at hMusical
  simp only [ContinuousLinearMap.comp_apply] at hMusical
  change metric.metric.tensor.tensor
      (normalBoundaryLatitudeFiberPoint period hPeriod boundary 0)
      (candidateANormalBoundaryTangentialProjectionAmbientVectorAtBase
        period hPeriod metric boundary)
      (mfderiv throatCoverModelWithCorners coverModelWithCorners
        (fun point : OrientationBoundary period hPeriod =>
          normalBoundaryLatitudeFiberPoint period hPeriod point 0)
        boundary tangent) =
    metric.metric.tensor.tensor
      (normalBoundaryLatitudeFiberPoint period hPeriod boundary 0)
      (normalBoundaryLatitudeFiberLift period hPeriod boundary 0).2
      (mfderiv throatCoverModelWithCorners coverModelWithCorners
        (fun point : OrientationBoundary period hPeriod =>
          normalBoundaryLatitudeFiberPoint period hPeriod point 0)
        boundary tangent) at hMusical
  rw [candidateANormalBoundaryMetricNormalVectorAtBase_eq_vertical_sub_projection,
    ← hVertical]
  simp only [map_sub, ContinuousLinearMap.sub_apply]
  rw [hMusical]
  exact sub_self _

/-- On the dense smooth core, the same-action canonical latitude lift is
exactly the latitude lift used by the fiber substitution at the same graph. -/
theorem normalGraphCanonicalLatitudeLift_smooth_eq_normalBoundaryLatitudeFiberLift
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : OrientationBoundary period hPeriod) :
    normalGraphCanonicalLatitudeLift period hPeriod displacement parameter boundary =
      normalBoundaryLatitudeFiberLift period hPeriod boundary
        (Real.arctan (parameter * normalBoundaryC2JetCoreValueAt period hPeriod
          boundary (smoothNormalDisplacementToBoundaryC2JetCore
            period hPeriod displacement))) := by
  refine Quotient.inductionOn boundary ?_
  intro point
  rw [normalGraphCanonicalLatitudeLift_mk,
    normalBoundaryLatitudeFiberLift_mk]
  unfold normalGraphCanonicalLatitudeLiftCover
    normalBoundaryLatitudeFiberLiftCover canonicalLatitudeNormalLift
    canonicalLatitudeNormalVector
  dsimp only
  rw [normalBoundaryC2JetCoreValueAt_smooth,
    normalDisplacementOrientationScalar_mk,
    canonicalLatitudeAnchor_baseCover]
  rfl

/-- The fiber-corrected canonical latitude vector is the vertical vector of
the completed boundary substitution along every smooth graph. -/
theorem normalGraphCanonicalLatitudeVector_smooth_heq_normalBoundaryLatitudeFiberLift
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : OrientationBoundary period hPeriod) :
    HEq
      (normalGraphCanonicalLatitudeVector period hPeriod displacement parameter
        boundary)
      (normalBoundaryLatitudeFiberLift period hPeriod boundary
        (Real.arctan (parameter *
          normalDisplacementOrientationScalar period hPeriod displacement
            boundary))).2 := by
  have hLift :=
    normalGraphCanonicalLatitudeLift_smooth_eq_normalBoundaryLatitudeFiberLift
      period hPeriod displacement parameter boundary
  rw [normalBoundaryC2JetCoreValueAt_smooth] at hLift
  have hTotal :=
    (normalGraphCanonicalLatitudeVector_total period hPeriod displacement
      parameter boundary).trans hLift
  exact (Bundle.TotalSpace.ext_iff.mp hTotal).2

/-- The faithful ambient-frame synthesis of the completed vertical
coefficients reconstructs the historical canonical latitude vector. -/
theorem candidateANormalBoundaryVertical_smooth_reconstructs
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : OrientationBoundary period hPeriod) :
    let variation := smoothToCandidateANormalBoundaryFunctionalCore
      period hPeriod metric (tensor, displacement)
    let point := normalGraphOrientationDouble period hPeriod displacement
      (boundary, parameter)
    (∑ row : Fin 4,
      candidateANormalBoundaryVerticalRegularFrameCoefficientFiberEvaluation
          period hPeriod metric row (variation, parameter) boundary •
        metric.frame row point) =
      normalGraphCanonicalLatitudeVector period hPeriod displacement parameter
        boundary := by
  dsimp only
  classical
  let variation := smoothToCandidateANormalBoundaryFunctionalCore
    period hPeriod metric (tensor, displacement)
  let normal := smoothNormalDisplacementToBoundaryC2JetCore
    period hPeriod displacement
  let latitude := Real.arctan (parameter *
    normalDisplacementOrientationScalar period hPeriod displacement boundary)
  let point := normalGraphOrientationDouble period hPeriod displacement
    (boundary, parameter)
  have hCoefficient (row : Fin 4) :
      candidateANormalBoundaryVerticalRegularFrameCoefficientFiberEvaluation
          period hPeriod metric row (variation, parameter) boundary =
        normalBoundaryLatitudeVerticalRegularFrameCoefficient period hPeriod
          metric row (boundary, latitude) := by
    rw [candidateANormalBoundaryVerticalRegularFrameCoefficientFiberEvaluation_apply]
    change normalBoundaryLatitudeVerticalRegularFrameCoefficient period hPeriod
        metric row
          (boundary, Real.arctan (parameter *
            normalBoundaryC2JetCoreValueAt period hPeriod boundary normal)) =
      normalBoundaryLatitudeVerticalRegularFrameCoefficient period hPeriod
        metric row (boundary, latitude)
    dsimp only [latitude, normal]
    rw [normalBoundaryC2JetCoreValueAt_smooth]
  have hPoint :
      normalBoundaryLatitudeFiberPoint period hPeriod boundary latitude =
        point := by
    dsimp only [latitude, point]
    rw [show normalDisplacementOrientationScalar period hPeriod displacement
          boundary = normalBoundaryC2JetCoreValueAt period hPeriod boundary
          normal by
      exact (normalBoundaryC2JetCoreValueAt_smooth
        period hPeriod displacement boundary).symm]
    rw [← normalBoundaryRawFiberPoint_eq_latitude,
      normalBoundaryRawFiberPoint_graph, normalBoundaryC2Graph_smooth]
  have hVertical := normalBoundaryLatitudeVerticalRegularFrame_reconstructs
    period hPeriod metric (boundary, latitude)
  rw [normalBoundaryLatitudeFiberLift_base, hPoint] at hVertical
  simp only [regularGeneralLorentzMetricSmoothD8Frame] at hVertical
  have hCanonical :=
    normalGraphCanonicalLatitudeVector_smooth_heq_normalBoundaryLatitudeFiberLift
      period hPeriod displacement parameter boundary
  change (∑ row : Fin 4,
      candidateANormalBoundaryVerticalRegularFrameCoefficientFiberEvaluation
          period hPeriod metric row (variation, parameter) boundary •
        metric.frame row point) =
    normalGraphCanonicalLatitudeVector period hPeriod displacement parameter
      boundary
  simp_rw [hCoefficient]
  exact eq_of_heq ((heq_of_eq hVertical.symm).trans hCanonical.symm)

/-- At zero graph parameter the same-action canonical latitude lift is exactly
the already installed latitude lift used by the fiber substitution. -/
theorem normalGraphCanonicalLatitudeLiftCover_zero_eq_normalBoundaryLatitudeFiberLiftCover
    (displacement : SmoothNormalDisplacement period hPeriod)
    (point : OrientationBoundaryCover period hPeriod) :
    normalGraphCanonicalLatitudeLiftCover period hPeriod displacement 0 point =
      normalBoundaryLatitudeFiberLiftCover period hPeriod (point, 0) := by
  unfold normalGraphCanonicalLatitudeLiftCover
    normalBoundaryLatitudeFiberLiftCover canonicalLatitudeNormalLift
    canonicalLatitudeNormalVector
  dsimp only
  rw [P0EFTJanusProgramPGlobalNormalDisplacementCollarGraph4D.normalGraphCoordinate_zero,
    canonicalLatitudeAnchor_baseCover]

/-- Descended form of the preceding zero-parameter lift agreement. -/
theorem normalGraphCanonicalLatitudeLift_zero_eq_normalBoundaryLatitudeFiberLift
    (displacement : SmoothNormalDisplacement period hPeriod)
    (boundary : OrientationBoundary period hPeriod) :
    normalGraphCanonicalLatitudeLift period hPeriod displacement 0 boundary =
      normalBoundaryLatitudeFiberLift period hPeriod boundary 0 := by
  refine Quotient.inductionOn boundary ?_
  intro point
  rw [normalGraphCanonicalLatitudeLift_mk,
    normalBoundaryLatitudeFiberLift_mk,
    normalGraphCanonicalLatitudeLiftCover_zero_eq_normalBoundaryLatitudeFiberLiftCover]

/-- Fiberwise form of the zero-parameter lift agreement, retaining the
dependent base point as a heterogeneous equality. -/
theorem normalGraphCanonicalLatitudeVector_zero_heq_normalBoundaryLatitudeFiberLift
    (displacement : SmoothNormalDisplacement period hPeriod)
    (boundary : OrientationBoundary period hPeriod) :
    HEq (normalGraphCanonicalLatitudeVector period hPeriod displacement 0 boundary)
      (normalBoundaryLatitudeFiberLift period hPeriod boundary 0).2 := by
  refine Quotient.inductionOn boundary ?_
  intro point
  have hVector := normalGraphCanonicalLatitudeVector_mk_heq_cover
    period hPeriod displacement 0 point
  have hCover := normalGraphCanonicalLatitudeVectorCover_heq_lift
    period hPeriod displacement 0 point
  rw [normalGraphCanonicalLatitudeLiftCover_zero_eq_normalBoundaryLatitudeFiberLiftCover]
    at hCover
  rw [normalBoundaryLatitudeFiberLift_mk]
  exact hVector.trans hCover

attribute [-instance] orientationBoundaryMetricSpace
    orientationBoundaryChartedSpace in
/-- The completed base normal is nonzero: otherwise the already proved
canonical latitude transversality would be lost. -/
theorem candidateANormalBoundaryMetricNormalVectorAtBase_ne_zero
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (boundary : OrientationBoundary period hPeriod) :
    candidateANormalBoundaryMetricNormalVectorAtBase
      period hPeriod metric boundary ≠ 0 := by
  intro hZero
  let displacement : SmoothNormalDisplacement period hPeriod := 0
  have hDecomposition :=
    candidateANormalBoundaryMetricNormalVectorAtBase_eq_vertical_sub_projection
      period hPeriod metric boundary
  rw [hZero] at hDecomposition
  have hVerticalProjection := sub_eq_zero.mp hDecomposition.symm
  have hVertical := normalBoundaryLatitudeVerticalRegularFrame_reconstructs
    period hPeriod metric (boundary, 0)
  rw [normalBoundaryLatitudeFiberLift_base] at hVertical
  simp only [regularGeneralLorentzMetricSmoothD8Frame] at hVertical
  have hCanonicalHEq :=
    normalGraphCanonicalLatitudeVector_zero_heq_normalBoundaryLatitudeFiberLift
      period hPeriod displacement boundary
  have hCanonicalVerticalHEq :
      HEq (normalGraphCanonicalLatitudeVector
          period hPeriod displacement 0 boundary)
        (∑ row : Fin 4,
          normalBoundaryLatitudeVerticalRegularFrameCoefficient
                period hPeriod metric row (boundary, 0) •
            metric.frame row
              (normalBoundaryLatitudeFiberPoint period hPeriod boundary 0)) :=
    hCanonicalHEq.trans (heq_of_eq hVertical)
  apply normalGraphCanonicalLatitudeVector_transverse
    period hPeriod displacement 0 boundary
  refine ⟨normalBoundaryOrientationTangentEquiv period hPeriod boundary
    (candidateANormalBoundaryTangentialProjectionVectorAtBase
      period hPeriod metric boundary), ?_⟩
  have hGraph :
      P0EFTJanusProgramPGlobalNormalDisplacementCollarGraph4D.normalGraph
          period hPeriod displacement 0 =
        fixedThroatQuotientInclusion period hPeriod := by
    funext point
    exact P0EFTJanusProgramPGlobalNormalDisplacementCollarGraph4D.normalGraph_zero
      period hPeriod displacement point
  have hGraphDerivative :
      mfderiv throatCoverModelWithCorners coverModelWithCorners
          (P0EFTJanusProgramPGlobalNormalDisplacementCollarGraph4D.normalGraph
            period hPeriod displacement 0)
          (orientationDoubleToThroat period hPeriod boundary)
          (normalBoundaryOrientationTangentEquiv period hPeriod boundary
            (candidateANormalBoundaryTangentialProjectionVectorAtBase
              period hPeriod metric boundary)) =
        mfderiv throatCoverModelWithCorners coverModelWithCorners
          (fixedThroatQuotientInclusion period hPeriod)
          (orientationDoubleToThroat period hPeriod boundary)
          (normalBoundaryOrientationTangentEquiv period hPeriod boundary
            (candidateANormalBoundaryTangentialProjectionVectorAtBase
              period hPeriod metric boundary)) := by
    rw [hGraph]
  have hFixedProjection :
      HEq (mfderiv throatCoverModelWithCorners coverModelWithCorners
          (fixedThroatQuotientInclusion period hPeriod)
          (orientationDoubleToThroat period hPeriod boundary)
          (normalBoundaryOrientationTangentEquiv period hPeriod boundary
            (candidateANormalBoundaryTangentialProjectionVectorAtBase
              period hPeriod metric boundary)))
        (candidateANormalBoundaryTangentialProjectionAmbientVectorAtBase
          period hPeriod metric boundary) :=
    heq_of_eq
      (normalBoundaryLatitudeZeroDerivative_eq_fixedThroat period hPeriod
        boundary
        (candidateANormalBoundaryTangentialProjectionVectorAtBase
          period hPeriod metric boundary)).symm
  exact eq_of_heq <|
    (heq_of_eq hGraphDerivative).trans <|
      hFixedProjection.trans <|
        (heq_of_eq hVerticalProjection.symm).trans hCanonicalVerticalHEq.symm

private theorem candidateANormalBoundaryDependentBilinApply_heq
    {α : Sort _} {β : α → Sort _}
    (function : (point : α) → β point → β point → Real)
    {source target : α} (hBase : source = target)
    {firstSource secondSource : β source}
    {firstTarget secondTarget : β target}
    (hFirst : HEq firstSource firstTarget)
    (hSecond : HEq secondSource secondTarget) :
    HEq (function source firstSource secondSource)
      (function target firstTarget secondTarget) := by
  cases hBase
  cases hFirst
  cases hSecond
  rfl

attribute [-instance] orientationBoundaryMetricSpace
    orientationBoundaryChartedSpace in
/-- The physical-base completed normal square is pointwise nonzero.  This is
deduced from the existing same-action normal-class theorem. -/
theorem candidateANormalBoundaryMetricNormalSquareFiberEvaluation_zero_apply_ne_zero
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric)
    (boundary : OrientationBoundary period hPeriod) :
    candidateANormalBoundaryMetricNormalSquareFiberEvaluation
      period hPeriod metric 0 boundary ≠ 0 := by
  classical
  let displacement : SmoothNormalDisplacement period hPeriod := 0
  let throat := orientationDoubleToThroat period hPeriod boundary
  let graph :=
    P0EFTJanusProgramPGlobalNormalDisplacementCollarGraph4D.normalGraph
      period hPeriod displacement 0 throat
  have hBase : graph =
      normalBoundaryLatitudeFiberPoint period hPeriod boundary 0 := by
    unfold graph throat
    rw [P0EFTJanusProgramPGlobalNormalDisplacementCollarGraph4D.normalGraph_zero,
      normalBoundaryLatitudeFiberPoint_zero]
  let candidate : TangentSpace coverModelWithCorners graph :=
    cast (congrArg (fun point => TangentSpace coverModelWithCorners point)
      hBase).symm
      (candidateANormalBoundaryMetricNormalVectorAtBase
        period hPeriod metric boundary)
  have hCandidateHEq : HEq candidate
      (candidateANormalBoundaryMetricNormalVectorAtBase
        period hPeriod metric boundary) := by
    unfold candidate
    rw [cast_heq_iff_heq]
  have hCandidateNe : candidate ≠ 0 := by
    intro hZero
    apply candidateANormalBoundaryMetricNormalVectorAtBase_ne_zero
      period hPeriod metric boundary
    exact eq_of_heq (hCandidateHEq.symm.trans (heq_of_eq hZero))
  have hNonNull : NormalGraphNonNullAt period hPeriod metric.metric
      displacement 0 :=
    zero_mem_normalGraphNonNullDomain period hPeriod metric.metric
      displacement hTransverse
  have hGraphMap :
      P0EFTJanusProgramPGlobalNormalDisplacementCollarGraph4D.normalGraph
          period hPeriod displacement 0 =
        fixedThroatQuotientInclusion period hPeriod := by
    funext point
    exact P0EFTJanusProgramPGlobalNormalDisplacementCollarGraph4D.normalGraph_zero
      period hPeriod displacement point
  have hOrthogonal (tangent : ThroatTangentFiber period hPeriod throat) :
      metric.metric.tensor.tensor graph candidate
          (mfderiv throatCoverModelWithCorners coverModelWithCorners
            (P0EFTJanusProgramPGlobalNormalDisplacementCollarGraph4D.normalGraph
              period hPeriod displacement 0) throat tangent) = 0 := by
    let source := (normalBoundaryOrientationTangentEquiv
      period hPeriod boundary).symm tangent
    have hSource :=
      candidateANormalBoundaryMetricNormalVectorAtBase_orthogonal
        period hPeriod metric hTransverse boundary source
    have hDerivative := normalBoundaryLatitudeZeroDerivative_eq_fixedThroat
      period hPeriod boundary source
    have hForward : normalBoundaryOrientationTangentEquiv
        period hPeriod boundary source = tangent := by
      exact (normalBoundaryOrientationTangentEquiv
        period hPeriod boundary).apply_symm_apply tangent
    rw [hForward] at hDerivative
    have hGraphDerivative :
        mfderiv throatCoverModelWithCorners coverModelWithCorners
            (P0EFTJanusProgramPGlobalNormalDisplacementCollarGraph4D.normalGraph
              period hPeriod displacement 0) throat tangent =
          mfderiv throatCoverModelWithCorners coverModelWithCorners
            (fixedThroatQuotientInclusion period hPeriod) throat tangent := by
      rw [hGraphMap]
    have hTangentHEq : HEq
        (mfderiv throatCoverModelWithCorners coverModelWithCorners
          (P0EFTJanusProgramPGlobalNormalDisplacementCollarGraph4D.normalGraph
            period hPeriod displacement 0) throat tangent)
        (mfderiv throatCoverModelWithCorners coverModelWithCorners
          (fun point : OrientationBoundary period hPeriod =>
            normalBoundaryLatitudeFiberPoint period hPeriod point 0)
          boundary source) :=
      (heq_of_eq hGraphDerivative).trans (heq_of_eq hDerivative.symm)
    have hPairHEq : HEq
        (metric.metric.tensor.tensor graph candidate
          (mfderiv throatCoverModelWithCorners coverModelWithCorners
            (P0EFTJanusProgramPGlobalNormalDisplacementCollarGraph4D.normalGraph
              period hPeriod displacement 0) throat tangent))
        (metric.metric.tensor.tensor
          (normalBoundaryLatitudeFiberPoint period hPeriod boundary 0)
          (candidateANormalBoundaryMetricNormalVectorAtBase
            period hPeriod metric boundary)
          (mfderiv throatCoverModelWithCorners coverModelWithCorners
            (fun point : OrientationBoundary period hPeriod =>
              normalBoundaryLatitudeFiberPoint period hPeriod point 0)
            boundary source)) :=
      candidateANormalBoundaryDependentBilinApply_heq
        (fun point first second =>
          metric.metric.tensor.tensor point first second)
        hBase hCandidateHEq hTangentHEq
    exact (eq_of_heq hPairHEq).trans hSource
  have hPairing :
      normalGraphTangentialPairing period hPeriod metric.metric displacement 0
          throat candidate = 0 := by
    apply ContinuousLinearMap.ext
    intro tangent
    exact hOrthogonal tangent
  have hMetricNormal :
      normalGraphMetricNormal period hPeriod metric.metric displacement 0
          hNonNull throat candidate = candidate := by
    unfold normalGraphMetricNormal normalGraphTangentialProjection
    rw [hPairing, map_zero, map_zero, sub_zero]
  let normalClass : MovingGraphDifferentialNormalFiber period hPeriod
      displacement 0 throat := Submodule.Quotient.mk candidate
  have hClass : normalClass ≠ 0 := by
    intro hZero
    have hImageZero :
        normalGraphMetricNormalFromClass period hPeriod metric.metric
            displacement 0 hNonNull throat normalClass = 0 := by
      rw [hZero, map_zero]
    unfold normalClass at hImageZero
    rw [normalGraphMetricNormalFromClass_mk, hMetricNormal] at hImageZero
    exact hCandidateNe hImageZero
  have hSquare := normalGraphMetricNormalSquare_ne_zero
    period hPeriod metric.metric displacement 0 hNonNull throat normalClass hClass
  unfold normalGraphMetricNormalSquare normalClass at hSquare
  rw [normalGraphMetricNormalFromClass_mk, hMetricNormal] at hSquare
  have hSquareHEq : HEq
      (metric.metric.tensor.tensor graph candidate candidate)
      (metric.metric.tensor.tensor
        (normalBoundaryLatitudeFiberPoint period hPeriod boundary 0)
        (candidateANormalBoundaryMetricNormalVectorAtBase
          period hPeriod metric boundary)
        (candidateANormalBoundaryMetricNormalVectorAtBase
          period hPeriod metric boundary)) := by
    exact candidateANormalBoundaryDependentBilinApply_heq
      (fun point first second =>
        metric.metric.tensor.tensor point first second)
      hBase hCandidateHEq hCandidateHEq
  rw [candidateANormalBoundaryMetricNormalSquareFiberEvaluation_zero_apply_eq_vector]
  intro hZero
  apply hSquare
  exact (eq_of_heq hSquareHEq).trans hZero

/-- The completed normal square at the physical base is a unit of the existing
bounded scalar boundary algebra. -/
theorem candidateANormalBoundaryMetricNormalSquareFiberEvaluation_zero_isUnit
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric) :
    IsUnit (candidateANormalBoundaryMetricNormalSquareFiberEvaluation
      period hPeriod metric 0) := by
  apply boundedContinuousFunction_isUnit_of_forall_ne_zero
  intro boundary
  exact candidateANormalBoundaryMetricNormalSquareFiberEvaluation_zero_apply_ne_zero
    period hPeriod metric hTransverse boundary

/-- Normal square relative to its physical-base value.  It equals one at the
base and is the scalar input of the already constructed local root chart. -/
def candidateANormalBoundaryMetricNormalRelativeSquareFiberEvaluation
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) :
    CandidateANormalBoundaryScalarField period hPeriod :=
  candidateANormalBoundaryMetricNormalSquareFiberEvaluation
      period hPeriod metric current *
    Ring.inverse
      (candidateANormalBoundaryMetricNormalSquareFiberEvaluation
        period hPeriod metric 0)

theorem candidateANormalBoundaryMetricNormalRelativeSquareFiberEvaluation_contDiffOn_two
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    ContDiffOn Real 2
      (candidateANormalBoundaryMetricNormalRelativeSquareFiberEvaluation
        period hPeriod metric)
      (candidateANormalBoundaryInducedMetricDomain
        period hPeriod metric) := by
  unfold candidateANormalBoundaryMetricNormalRelativeSquareFiberEvaluation
  exact
    (candidateANormalBoundaryMetricNormalSquareFiberEvaluation_contDiffOn_two
      period hPeriod metric).mul contDiffOn_const

@[simp]
theorem candidateANormalBoundaryMetricNormalRelativeSquareFiberEvaluation_zero
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric) :
    candidateANormalBoundaryMetricNormalRelativeSquareFiberEvaluation
        period hPeriod metric 0 = 1 := by
  unfold candidateANormalBoundaryMetricNormalRelativeSquareFiberEvaluation
  exact Ring.mul_inverse_cancel _
    (candidateANormalBoundaryMetricNormalSquareFiberEvaluation_zero_isUnit
      period hPeriod metric hTransverse)

/-- Explicit open neighborhood on which both the induced inverse and the
positive relative scalar root are available. -/
def candidateANormalBoundaryMetricNormalRootDomain
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    Set (Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) :=
  candidateANormalBoundaryGeometryParameterDomain period hPeriod metric ∩
    candidateANormalBoundaryMetricNormalRelativeSquareFiberEvaluation
        period hPeriod metric ⁻¹'
      candidateANormalBoundaryScalarFieldLocalRootTarget period hPeriod

theorem candidateANormalBoundaryMetricNormalRootDomain_isOpen
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    IsOpen (candidateANormalBoundaryMetricNormalRootDomain
      period hPeriod metric) := by
  unfold candidateANormalBoundaryMetricNormalRootDomain
  exact
    (candidateANormalBoundaryMetricNormalRelativeSquareFiberEvaluation_contDiffOn_two
      period hPeriod metric).continuousOn.mono Set.inter_subset_right
        |>.isOpen_inter_preimage
        (candidateANormalBoundaryGeometryParameterDomain_isOpen
          period hPeriod metric)
        (candidateANormalBoundaryScalarFieldLocalRootTarget_isOpen
          period hPeriod)

theorem zero_mem_candidateANormalBoundaryMetricNormalRootDomain
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric) :
    (0 : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) ∈
      candidateANormalBoundaryMetricNormalRootDomain
        period hPeriod metric := by
  constructor
  · exact zero_mem_candidateANormalBoundaryGeometryParameterDomain
      period hPeriod metric hTransverse
  · change candidateANormalBoundaryMetricNormalRelativeSquareFiberEvaluation
        period hPeriod metric 0 ∈
      candidateANormalBoundaryScalarFieldLocalRootTarget period hPeriod
    rw [candidateANormalBoundaryMetricNormalRelativeSquareFiberEvaluation_zero
      period hPeriod metric hTransverse]
    exact candidateANormalBoundaryScalarFieldOne_mem_localRootTarget
      period hPeriod

/-- Selected positive relative magnitude branch on the preceding open
neighborhood. -/
def candidateANormalBoundaryMetricNormalRelativeRootFiberEvaluation
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) :
    CandidateANormalBoundaryScalarField period hPeriod :=
  candidateANormalBoundaryScalarFieldLocalRootBranch period hPeriod
    (candidateANormalBoundaryMetricNormalRelativeSquareFiberEvaluation
      period hPeriod metric current)

theorem candidateANormalBoundaryMetricNormalRelativeRootFiberEvaluation_square
    (metric : RegularGeneralLorentzMetric period hPeriod)
    {current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real}
    (hCurrent : current ∈ candidateANormalBoundaryMetricNormalRootDomain
      period hPeriod metric) :
    candidateANormalBoundaryScalarFieldSquare period hPeriod
        (candidateANormalBoundaryMetricNormalRelativeRootFiberEvaluation
          period hPeriod metric current) =
      candidateANormalBoundaryMetricNormalRelativeSquareFiberEvaluation
        period hPeriod metric current := by
  exact candidateANormalBoundaryScalarFieldLocalRootBranch_square
    period hPeriod hCurrent.2

@[simp]
theorem candidateANormalBoundaryMetricNormalRelativeRootFiberEvaluation_zero
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric) :
    candidateANormalBoundaryMetricNormalRelativeRootFiberEvaluation
        period hPeriod metric 0 = 1 := by
  unfold candidateANormalBoundaryMetricNormalRelativeRootFiberEvaluation
  rw [candidateANormalBoundaryMetricNormalRelativeSquareFiberEvaluation_zero
      period hPeriod metric hTransverse,
    candidateANormalBoundaryScalarFieldLocalRootBranch_at_one]

theorem candidateANormalBoundaryMetricNormalRelativeRootFiberEvaluation_contDiffOn_two
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    ContDiffOn Real 2
      (candidateANormalBoundaryMetricNormalRelativeRootFiberEvaluation
        period hPeriod metric)
      (candidateANormalBoundaryMetricNormalRootDomain period hPeriod metric) := by
  unfold candidateANormalBoundaryMetricNormalRelativeRootFiberEvaluation
  change ContDiffOn Real 2
    (candidateANormalBoundaryScalarFieldLocalRootBranch period hPeriod ∘
      candidateANormalBoundaryMetricNormalRelativeSquareFiberEvaluation
        period hPeriod metric)
    (candidateANormalBoundaryMetricNormalRootDomain period hPeriod metric)
  exact (candidateANormalBoundaryScalarFieldLocalRootBranch_contDiffOn
      period hPeriod).comp
    ((candidateANormalBoundaryMetricNormalRelativeSquareFiberEvaluation_contDiffOn_two
      period hPeriod metric).mono (fun _ hCurrent => hCurrent.1.2))
    (fun _ hCurrent => hCurrent.2)

/-- Pointwise absolute value of the physical-base normal square. -/
def candidateANormalBoundaryMetricNormalBaseAbsoluteSquare
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    CandidateANormalBoundaryScalarField period hPeriod :=
  BoundedContinuousFunction.mkOfCompact
    { toFun := fun boundary =>
        |candidateANormalBoundaryMetricNormalSquareFiberEvaluation
          period hPeriod metric 0 boundary|
      continuous_toFun :=
        (candidateANormalBoundaryMetricNormalSquareFiberEvaluation
          period hPeriod metric 0).continuous.abs }

@[simp]
theorem candidateANormalBoundaryMetricNormalBaseAbsoluteSquare_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (boundary : OrientationBoundary period hPeriod) :
    candidateANormalBoundaryMetricNormalBaseAbsoluteSquare
        period hPeriod metric boundary =
      |candidateANormalBoundaryMetricNormalSquareFiberEvaluation
        period hPeriod metric 0 boundary| :=
  rfl

/-- Positive physical-base magnitude, constructed pointwise from the proved
nonzero square. -/
def candidateANormalBoundaryMetricNormalBaseMagnitude
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    CandidateANormalBoundaryScalarField period hPeriod :=
  BoundedContinuousFunction.mkOfCompact
    { toFun := fun boundary => Real.sqrt
        |candidateANormalBoundaryMetricNormalSquareFiberEvaluation
          period hPeriod metric 0 boundary|
      continuous_toFun :=
        (candidateANormalBoundaryMetricNormalSquareFiberEvaluation
          period hPeriod metric 0).continuous.abs.sqrt }

@[simp]
theorem candidateANormalBoundaryMetricNormalBaseMagnitude_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (boundary : OrientationBoundary period hPeriod) :
    candidateANormalBoundaryMetricNormalBaseMagnitude
        period hPeriod metric boundary =
      Real.sqrt
        |candidateANormalBoundaryMetricNormalSquareFiberEvaluation
          period hPeriod metric 0 boundary| :=
  rfl

theorem candidateANormalBoundaryMetricNormalBaseMagnitude_square
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    candidateANormalBoundaryScalarFieldSquare period hPeriod
        (candidateANormalBoundaryMetricNormalBaseMagnitude
          period hPeriod metric) =
      candidateANormalBoundaryMetricNormalBaseAbsoluteSquare
        period hPeriod metric := by
  ext boundary
  change Real.sqrt
        |candidateANormalBoundaryMetricNormalSquareFiberEvaluation
          period hPeriod metric 0 boundary| *
      Real.sqrt
        |candidateANormalBoundaryMetricNormalSquareFiberEvaluation
          period hPeriod metric 0 boundary| = _
  exact Real.mul_self_sqrt (abs_nonneg _)

theorem candidateANormalBoundaryMetricNormalBaseAbsoluteSquare_isUnit
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric) :
    IsUnit (candidateANormalBoundaryMetricNormalBaseAbsoluteSquare
      period hPeriod metric) := by
  apply boundedContinuousFunction_isUnit_of_forall_ne_zero
  intro boundary
  rw [candidateANormalBoundaryMetricNormalBaseAbsoluteSquare_apply]
  exact abs_ne_zero.mpr
    (candidateANormalBoundaryMetricNormalSquareFiberEvaluation_zero_apply_ne_zero
      period hPeriod metric hTransverse boundary)

theorem candidateANormalBoundaryMetricNormalBaseMagnitude_isUnit
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric) :
    IsUnit (candidateANormalBoundaryMetricNormalBaseMagnitude
      period hPeriod metric) := by
  apply boundedContinuousFunction_isUnit_of_forall_ne_zero
  intro boundary
  rw [candidateANormalBoundaryMetricNormalBaseMagnitude_apply]
  exact ne_of_gt (Real.sqrt_pos.2 (abs_pos.mpr
    (candidateANormalBoundaryMetricNormalSquareFiberEvaluation_zero_apply_ne_zero
      period hPeriod metric hTransverse boundary)))

/-- Derived causal sign of the physical-base normal square. -/
def candidateANormalBoundaryMetricNormalBaseCausalSign
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    CandidateANormalBoundaryScalarField period hPeriod :=
  candidateANormalBoundaryMetricNormalSquareFiberEvaluation
      period hPeriod metric 0 *
    Ring.inverse
      (candidateANormalBoundaryMetricNormalBaseAbsoluteSquare
        period hPeriod metric)

/-- Full positive magnitude: fixed physical magnitude times the selected
relative root. -/
def candidateANormalBoundaryMetricNormalMagnitudeFiberEvaluation
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) :
    CandidateANormalBoundaryScalarField period hPeriod :=
  candidateANormalBoundaryMetricNormalBaseMagnitude period hPeriod metric *
    candidateANormalBoundaryMetricNormalRelativeRootFiberEvaluation
      period hPeriod metric current

theorem candidateANormalBoundaryMetricNormalRelativeRootFiberEvaluation_isUnit
    (metric : RegularGeneralLorentzMetric period hPeriod)
    {current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real}
    (hCurrent : current ∈ candidateANormalBoundaryMetricNormalRootDomain
      period hPeriod metric) :
    IsUnit (candidateANormalBoundaryMetricNormalRelativeRootFiberEvaluation
      period hPeriod metric current) := by
  have hSource :=
    (candidateANormalBoundaryScalarFieldLocalSquareChart
      period hPeriod).map_target hCurrent.2
  rw [candidateANormalBoundaryScalarFieldLocalSquareChart,
    OpenPartialHomeomorph.restrOpen_source] at hSource
  exact hSource.2

theorem candidateANormalBoundaryMetricNormalMagnitudeFiberEvaluation_isUnit
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric)
    {current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real}
    (hCurrent : current ∈ candidateANormalBoundaryMetricNormalRootDomain
      period hPeriod metric) :
    IsUnit (candidateANormalBoundaryMetricNormalMagnitudeFiberEvaluation
      period hPeriod metric current) :=
  (candidateANormalBoundaryMetricNormalBaseMagnitude_isUnit
    period hPeriod metric hTransverse).mul
      (candidateANormalBoundaryMetricNormalRelativeRootFiberEvaluation_isUnit
        period hPeriod metric hCurrent)

theorem candidateANormalBoundaryMetricNormalMagnitudeFiberEvaluation_contDiffOn_two
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    ContDiffOn Real 2
      (candidateANormalBoundaryMetricNormalMagnitudeFiberEvaluation
        period hPeriod metric)
      (candidateANormalBoundaryMetricNormalRootDomain period hPeriod metric) := by
  unfold candidateANormalBoundaryMetricNormalMagnitudeFiberEvaluation
  exact contDiffOn_const.mul
    (candidateANormalBoundaryMetricNormalRelativeRootFiberEvaluation_contDiffOn_two
      period hPeriod metric)

theorem candidateANormalBoundaryMetricNormalMagnitudeFiberEvaluation_square
    (metric : RegularGeneralLorentzMetric period hPeriod)
    {current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real}
    (hCurrent : current ∈ candidateANormalBoundaryMetricNormalRootDomain
      period hPeriod metric) :
    candidateANormalBoundaryScalarFieldSquare period hPeriod
        (candidateANormalBoundaryMetricNormalMagnitudeFiberEvaluation
          period hPeriod metric current) =
      candidateANormalBoundaryMetricNormalBaseAbsoluteSquare
          period hPeriod metric *
        candidateANormalBoundaryMetricNormalRelativeSquareFiberEvaluation
          period hPeriod metric current := by
  unfold candidateANormalBoundaryMetricNormalMagnitudeFiberEvaluation
  rw [show candidateANormalBoundaryScalarFieldSquare period hPeriod
      (candidateANormalBoundaryMetricNormalBaseMagnitude
        period hPeriod metric *
       candidateANormalBoundaryMetricNormalRelativeRootFiberEvaluation
        period hPeriod metric current) =
      candidateANormalBoundaryScalarFieldSquare period hPeriod
          (candidateANormalBoundaryMetricNormalBaseMagnitude
            period hPeriod metric) *
        candidateANormalBoundaryScalarFieldSquare period hPeriod
          (candidateANormalBoundaryMetricNormalRelativeRootFiberEvaluation
            period hPeriod metric current) by
      unfold candidateANormalBoundaryScalarFieldSquare
      ring]
  rw [candidateANormalBoundaryMetricNormalBaseMagnitude_square,
    candidateANormalBoundaryMetricNormalRelativeRootFiberEvaluation_square
      period hPeriod metric hCurrent]

/-- On the selected nonnegative branch, the completed normal magnitude is the
ordinary square root of the absolute completed normal square. -/
theorem candidateANormalBoundaryMetricNormalMagnitude_eq_sqrt_abs
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric)
    {current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real}
    (hCurrent : current ∈ candidateANormalBoundaryMetricNormalRootDomain
      period hPeriod metric)
    (boundary : OrientationBoundary period hPeriod)
    (hRootNonneg : 0 ≤
      candidateANormalBoundaryMetricNormalRelativeRootFiberEvaluation
        period hPeriod metric current boundary) :
    candidateANormalBoundaryMetricNormalMagnitudeFiberEvaluation
        period hPeriod metric current boundary =
      Real.sqrt
        |candidateANormalBoundaryMetricNormalSquareFiberEvaluation
          period hPeriod metric current boundary| := by
  let square := candidateANormalBoundaryMetricNormalSquareFiberEvaluation
    period hPeriod metric current
  let baseSquare := candidateANormalBoundaryMetricNormalSquareFiberEvaluation
    period hPeriod metric 0
  let relative :=
    candidateANormalBoundaryMetricNormalRelativeSquareFiberEvaluation
      period hPeriod metric current
  have hBaseUnit : IsUnit baseSquare :=
    candidateANormalBoundaryMetricNormalSquareFiberEvaluation_zero_isUnit
      period hPeriod metric hTransverse
  have hRelativeBase : relative * baseSquare = square := by
    change (square * Ring.inverse baseSquare) * baseSquare = square
    calc
      (square * Ring.inverse baseSquare) * baseSquare =
          square * (baseSquare * Ring.inverse baseSquare) := by
        ac_rfl
      _ = square * 1 := by
        rw [Ring.mul_inverse_cancel baseSquare hBaseUnit]
      _ = square := mul_one _
  have hRelativeBaseAt := congrArg (fun field => field boundary) hRelativeBase
  change relative boundary * baseSquare boundary = square boundary
    at hRelativeBaseAt
  have hRootSquareAt := congrArg (fun field => field boundary)
    (candidateANormalBoundaryMetricNormalRelativeRootFiberEvaluation_square
      period hPeriod metric hCurrent)
  change
    candidateANormalBoundaryMetricNormalRelativeRootFiberEvaluation
          period hPeriod metric current boundary *
        candidateANormalBoundaryMetricNormalRelativeRootFiberEvaluation
          period hPeriod metric current boundary =
      relative boundary at hRootSquareAt
  have hRelativeNonneg : 0 ≤ relative boundary := by
    rw [← hRootSquareAt]
    positivity
  have hAbsSquare : |square boundary| =
      relative boundary * |baseSquare boundary| := by
    calc
      |square boundary| = |relative boundary * baseSquare boundary| := by
        rw [hRelativeBaseAt]
      _ = |relative boundary| * |baseSquare boundary| := abs_mul _ _
      _ = relative boundary * |baseSquare boundary| := by
        rw [abs_of_nonneg hRelativeNonneg]
  have hMagnitudeSquareAt := congrArg (fun field => field boundary)
    (candidateANormalBoundaryMetricNormalMagnitudeFiberEvaluation_square
      period hPeriod metric hCurrent)
  change
    candidateANormalBoundaryMetricNormalMagnitudeFiberEvaluation
          period hPeriod metric current boundary *
        candidateANormalBoundaryMetricNormalMagnitudeFiberEvaluation
          period hPeriod metric current boundary =
      |baseSquare boundary| * relative boundary at hMagnitudeSquareAt
  have hMagnitudeSquare :
      candidateANormalBoundaryMetricNormalMagnitudeFiberEvaluation
            period hPeriod metric current boundary *
          candidateANormalBoundaryMetricNormalMagnitudeFiberEvaluation
            period hPeriod metric current boundary =
        |square boundary| := by
    calc
      _ = |baseSquare boundary| * relative boundary := hMagnitudeSquareAt
      _ = relative boundary * |baseSquare boundary| := mul_comm _ _
      _ = |square boundary| := hAbsSquare.symm
  have hMagnitudeNonneg : 0 ≤
      candidateANormalBoundaryMetricNormalMagnitudeFiberEvaluation
        period hPeriod metric current boundary := by
    change 0 ≤ Real.sqrt |baseSquare boundary| *
      candidateANormalBoundaryMetricNormalRelativeRootFiberEvaluation
        period hPeriod metric current boundary
    exact mul_nonneg (Real.sqrt_nonneg _) hRootNonneg
  calc
    candidateANormalBoundaryMetricNormalMagnitudeFiberEvaluation
        period hPeriod metric current boundary =
      Real.sqrt
        (candidateANormalBoundaryMetricNormalMagnitudeFiberEvaluation
          period hPeriod metric current boundary ^ 2) := by
      exact (Real.sqrt_sq hMagnitudeNonneg).symm
    _ = Real.sqrt |square boundary| := by
      rw [pow_two, hMagnitudeSquare]

/-- Pointwise inverse of the selected positive normal magnitude. -/
def candidateANormalBoundaryMetricNormalMagnitudeInverseFiberEvaluation
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) :
    CandidateANormalBoundaryScalarField period hPeriod :=
  Ring.inverse
    (candidateANormalBoundaryMetricNormalMagnitudeFiberEvaluation
      period hPeriod metric current)

theorem
    candidateANormalBoundaryMetricNormalMagnitudeInverseFiberEvaluation_contDiffOn_two
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric) :
    ContDiffOn Real 2
      (candidateANormalBoundaryMetricNormalMagnitudeInverseFiberEvaluation
        period hPeriod metric)
      (candidateANormalBoundaryMetricNormalRootDomain
        period hPeriod metric) := by
  intro current hCurrent
  have hUnit :=
    candidateANormalBoundaryMetricNormalMagnitudeFiberEvaluation_isUnit
      period hPeriod metric hTransverse hCurrent
  have hInverse : ContDiffAt Real 2 Ring.inverse
      (candidateANormalBoundaryMetricNormalMagnitudeFiberEvaluation
        period hPeriod metric current) := by
    simpa using (contDiffAt_ringInverse Real hUnit.unit :
      ContDiffAt Real 2 Ring.inverse
        (hUnit.unit : CandidateANormalBoundaryScalarField period hPeriod))
  exact hInverse.comp_contDiffWithinAt current
    ((candidateANormalBoundaryMetricNormalMagnitudeFiberEvaluation_contDiffOn_two
      period hPeriod metric).contDiffWithinAt hCurrent)

/-- Regular-frame coefficients of the completed unit normal.  This only
rescales the already constructed metric-normal projection. -/
def candidateANormalBoundaryMetricUnitNormalRegularFrameCoefficientFiberEvaluation
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (upper : Fin 4)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) :
    CandidateANormalBoundaryScalarField period hPeriod :=
  candidateANormalBoundaryMetricNormalMagnitudeInverseFiberEvaluation
      period hPeriod metric current *
    candidateANormalBoundaryMetricNormalRegularFrameCoefficientFiberEvaluation
      period hPeriod metric upper current

theorem
    candidateANormalBoundaryMetricUnitNormalRegularFrameCoefficientFiberEvaluation_contDiffOn_two
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric)
    (upper : Fin 4) :
    ContDiffOn Real 2
      (candidateANormalBoundaryMetricUnitNormalRegularFrameCoefficientFiberEvaluation
        period hPeriod metric upper)
      (candidateANormalBoundaryMetricNormalRootDomain
        period hPeriod metric) := by
  unfold
    candidateANormalBoundaryMetricUnitNormalRegularFrameCoefficientFiberEvaluation
  exact
    (candidateANormalBoundaryMetricNormalMagnitudeInverseFiberEvaluation_contDiffOn_two
      period hPeriod metric hTransverse).mul
        ((candidateANormalBoundaryMetricNormalRegularFrameCoefficientFiberEvaluation_contDiffOn_two
          period hPeriod metric upper).mono (fun _ hCurrent => hCurrent.1.2))

/-- Metric square of the completed unit normal, contracted in the installed
regular frame. -/
def candidateANormalBoundaryMetricUnitNormalSquareFiberEvaluation
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) :
    CandidateANormalBoundaryScalarField period hPeriod :=
  ∑ first : Fin 4, ∑ second : Fin 4,
    candidateANormalBoundaryMetricUnitNormalRegularFrameCoefficientFiberEvaluation
          period hPeriod metric first current *
      candidateANormalBoundaryActualMetricMatrixFiberEvaluation
          period hPeriod metric current first second *
        candidateANormalBoundaryMetricUnitNormalRegularFrameCoefficientFiberEvaluation
          period hPeriod metric second current

theorem
    candidateANormalBoundaryMetricUnitNormalSquareFiberEvaluation_contDiffOn_two
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric) :
    ContDiffOn Real 2
      (candidateANormalBoundaryMetricUnitNormalSquareFiberEvaluation
        period hPeriod metric)
      (candidateANormalBoundaryMetricNormalRootDomain
        period hPeriod metric) := by
  have hNormal :=
    candidateANormalBoundaryMetricUnitNormalRegularFrameCoefficientFiberEvaluation_contDiffOn_two
      period hPeriod metric hTransverse
  have hMetric :=
    candidateANormalBoundaryActualMetricMatrixFiberEvaluation_contDiff_two
      period hPeriod metric
  unfold candidateANormalBoundaryMetricUnitNormalSquareFiberEvaluation
  exact ContDiffOn.sum fun first _ => ContDiffOn.sum fun second _ =>
    (((hNormal first).mul
      (contDiff_pi.mp (contDiff_pi.mp hMetric first) second).contDiffOn).mul
        (hNormal second))

theorem
    candidateANormalBoundaryMetricUnitNormalSquareFiberEvaluation_eq_scaled
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) :
    candidateANormalBoundaryMetricUnitNormalSquareFiberEvaluation
        period hPeriod metric current =
      candidateANormalBoundaryMetricNormalMagnitudeInverseFiberEvaluation
          period hPeriod metric current *
        candidateANormalBoundaryMetricNormalMagnitudeInverseFiberEvaluation
          period hPeriod metric current *
        candidateANormalBoundaryMetricNormalSquareFiberEvaluation
          period hPeriod metric current := by
  classical
  unfold candidateANormalBoundaryMetricUnitNormalSquareFiberEvaluation
    candidateANormalBoundaryMetricUnitNormalRegularFrameCoefficientFiberEvaluation
    candidateANormalBoundaryMetricNormalSquareFiberEvaluation
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  ring

/-- The completed unit normal has the causal sign fixed by the physical-base
normal square. -/
theorem candidateANormalBoundaryMetricUnitNormalSquareFiberEvaluation_eq_baseCausalSign
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric)
    {current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real}
    (hCurrent : current ∈ candidateANormalBoundaryMetricNormalRootDomain
      period hPeriod metric) :
    candidateANormalBoundaryMetricUnitNormalSquareFiberEvaluation
        period hPeriod metric current =
      candidateANormalBoundaryMetricNormalBaseCausalSign
        period hPeriod metric := by
  rw [candidateANormalBoundaryMetricUnitNormalSquareFiberEvaluation_eq_scaled]
  let magnitude :=
    candidateANormalBoundaryMetricNormalMagnitudeFiberEvaluation
      period hPeriod metric current
  let square :=
    candidateANormalBoundaryMetricNormalSquareFiberEvaluation
      period hPeriod metric current
  let baseSquare :=
    candidateANormalBoundaryMetricNormalSquareFiberEvaluation
      period hPeriod metric 0
  let baseAbsolute :=
    candidateANormalBoundaryMetricNormalBaseAbsoluteSquare
      period hPeriod metric
  change Ring.inverse magnitude * Ring.inverse magnitude * square =
    baseSquare * Ring.inverse baseAbsolute
  have hMagnitude : IsUnit magnitude :=
    candidateANormalBoundaryMetricNormalMagnitudeFiberEvaluation_isUnit
      period hPeriod metric hTransverse hCurrent
  have hBaseSquare : IsUnit baseSquare :=
    candidateANormalBoundaryMetricNormalSquareFiberEvaluation_zero_isUnit
      period hPeriod metric hTransverse
  have hBaseAbsolute : IsUnit baseAbsolute :=
    candidateANormalBoundaryMetricNormalBaseAbsoluteSquare_isUnit
      period hPeriod metric hTransverse
  have hMagnitudeSquare :=
    candidateANormalBoundaryMetricNormalMagnitudeFiberEvaluation_square
      period hPeriod metric hCurrent
  change magnitude * magnitude =
    baseAbsolute * (square * Ring.inverse baseSquare) at hMagnitudeSquare
  have hMagnitudeInverse := Ring.inverse_mul_cancel magnitude hMagnitude
  have hBaseSquareInverse := Ring.inverse_mul_cancel baseSquare hBaseSquare
  have hBaseAbsoluteInverse :=
    Ring.mul_inverse_cancel baseAbsolute hBaseAbsolute
  have hSquare : square =
      magnitude * magnitude * (baseSquare * Ring.inverse baseAbsolute) := by
    calc
      square =
          (baseAbsolute * Ring.inverse baseAbsolute) * square *
            (Ring.inverse baseSquare * baseSquare) := by
              rw [hBaseAbsoluteInverse, hBaseSquareInverse]
              ring
      _ = (baseAbsolute * (square * Ring.inverse baseSquare)) *
            (baseSquare * Ring.inverse baseAbsolute) := by ring
      _ = magnitude * magnitude *
            (baseSquare * Ring.inverse baseAbsolute) := by
              rw [← hMagnitudeSquare]
  rw [hSquare]
  calc
    Ring.inverse magnitude * Ring.inverse magnitude *
          (magnitude * magnitude *
            (baseSquare * Ring.inverse baseAbsolute)) =
        (Ring.inverse magnitude * magnitude) *
          (Ring.inverse magnitude * magnitude) *
            (baseSquare * Ring.inverse baseAbsolute) := by ring
    _ = baseSquare * Ring.inverse baseAbsolute := by
      rw [hMagnitudeInverse]
      ring

/-- Raw Gauss form paired with the completed unit normal.  It is the existing
raw Gauss form rescaled by the selected magnitude. -/
def candidateANormalBoundaryMetricUnitGaussRawExtrinsicCurvatureFiberEvaluation
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (outer inner : NormalBoundaryTangentIndex period hPeriod)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) :
    CandidateANormalBoundaryScalarField period hPeriod :=
  candidateANormalBoundaryMetricNormalMagnitudeInverseFiberEvaluation
      period hPeriod metric current *
    candidateANormalBoundaryGaussRawExtrinsicCurvatureFiberEvaluation
      period hPeriod metric outer inner current

theorem
    candidateANormalBoundaryMetricUnitGaussRawExtrinsicCurvatureFiberEvaluation_contDiffOn_two
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric)
    (outer inner : NormalBoundaryTangentIndex period hPeriod) :
    ContDiffOn Real 2
      (candidateANormalBoundaryMetricUnitGaussRawExtrinsicCurvatureFiberEvaluation
        period hPeriod metric outer inner)
      (candidateANormalBoundaryMetricNormalRootDomain
        period hPeriod metric) := by
  unfold
    candidateANormalBoundaryMetricUnitGaussRawExtrinsicCurvatureFiberEvaluation
  exact
    (candidateANormalBoundaryMetricNormalMagnitudeInverseFiberEvaluation_contDiffOn_two
      period hPeriod metric hTransverse).mul
        ((candidateANormalBoundaryGaussRawExtrinsicCurvatureFiberEvaluation_contDiffOn_two
          period hPeriod metric outer inner).mono (fun _ hCurrent => hCurrent.1))

/-- Symmetric completed second fundamental form with unit normal. -/
def candidateANormalBoundaryMetricUnitGaussExtrinsicCurvatureFiberEvaluation
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (outer inner : NormalBoundaryTangentIndex period hPeriod)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) :
    CandidateANormalBoundaryScalarField period hPeriod :=
  (1 / 2 : Real) •
    (candidateANormalBoundaryMetricUnitGaussRawExtrinsicCurvatureFiberEvaluation
          period hPeriod metric outer inner current +
      candidateANormalBoundaryMetricUnitGaussRawExtrinsicCurvatureFiberEvaluation
        period hPeriod metric inner outer current)

theorem candidateANormalBoundaryMetricUnitGaussExtrinsicCurvatureFiberEvaluation_contDiffOn_two
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric)
    (outer inner : NormalBoundaryTangentIndex period hPeriod) :
    ContDiffOn Real 2
      (candidateANormalBoundaryMetricUnitGaussExtrinsicCurvatureFiberEvaluation
        period hPeriod metric outer inner)
      (candidateANormalBoundaryMetricNormalRootDomain
        period hPeriod metric) := by
  unfold candidateANormalBoundaryMetricUnitGaussExtrinsicCurvatureFiberEvaluation
  exact ContDiffOn.const_smul (1 / 2 : Real)
    ((candidateANormalBoundaryMetricUnitGaussRawExtrinsicCurvatureFiberEvaluation_contDiffOn_two
        period hPeriod metric hTransverse outer inner).add
      (candidateANormalBoundaryMetricUnitGaussRawExtrinsicCurvatureFiberEvaluation_contDiffOn_two
        period hPeriod metric hTransverse inner outer))

theorem
    candidateANormalBoundaryMetricUnitGaussExtrinsicCurvatureFiberEvaluation_symmetric
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (outer inner : NormalBoundaryTangentIndex period hPeriod) :
    candidateANormalBoundaryMetricUnitGaussExtrinsicCurvatureFiberEvaluation
        period hPeriod metric outer inner =
      candidateANormalBoundaryMetricUnitGaussExtrinsicCurvatureFiberEvaluation
        period hPeriod metric inner outer := by
  funext current
  unfold candidateANormalBoundaryMetricUnitGaussExtrinsicCurvatureFiberEvaluation
  rw [add_comm]

/-- Faithful redundant-frame encoding of the unit second fundamental form
after raising one index with the fixed intrinsic throat metric. -/
def candidateANormalBoundaryMetricUnitGaussRelativeEndomorphismMatrixFiberEvaluation
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) :
    CandidateANormalBoundaryInducedMetricMatrixField period hPeriod :=
  fun row column =>
    ∑ middle : NormalBoundaryTangentIndex period hPeriod,
      normalBoundaryReferenceDualCoefficientMatrix
          period hPeriod row middle *
        candidateANormalBoundaryMetricUnitGaussExtrinsicCurvatureFiberEvaluation
          period hPeriod metric middle column current

theorem
    candidateANormalBoundaryMetricUnitGaussRelativeEndomorphismMatrixFiberEvaluation_contDiffOn_two
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric) :
    ContDiffOn Real 2
      (candidateANormalBoundaryMetricUnitGaussRelativeEndomorphismMatrixFiberEvaluation
        period hPeriod metric)
      (candidateANormalBoundaryMetricNormalRootDomain
        period hPeriod metric) := by
  change @ContDiffOn Real _
    (Prod (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real)
    _ _
    (NormalBoundaryTangentIndex period hPeriod →
      NormalBoundaryTangentIndex period hPeriod →
      CandidateANormalBoundaryScalarField period hPeriod)
    Pi.normedAddCommGroup Pi.normedSpace 2
    (candidateANormalBoundaryMetricUnitGaussRelativeEndomorphismMatrixFiberEvaluation
      period hPeriod metric)
    (candidateANormalBoundaryMetricNormalRootDomain period hPeriod metric)
  rw [contDiffOn_pi]
  intro row
  rw [contDiffOn_pi]
  intro column
  unfold
    candidateANormalBoundaryMetricUnitGaussRelativeEndomorphismMatrixFiberEvaluation
  exact ContDiffOn.sum fun middle _ => contDiffOn_const.mul
    (candidateANormalBoundaryMetricUnitGaussExtrinsicCurvatureFiberEvaluation_contDiffOn_two
      period hPeriod metric hTransverse middle column)

/-- Mean curvature of the completed unit-normal graph.  The trace is taken
through the existing faithful inverse lift of the induced metric. -/
def candidateANormalBoundaryMetricUnitGaussMeanCurvatureFiberEvaluation
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) :
    CandidateANormalBoundaryScalarField period hPeriod :=
  Matrix.trace
    (candidateANormalBoundaryInducedRelativeLiftInverseFiberEvaluation
        period hPeriod metric current *
      candidateANormalBoundaryMetricUnitGaussRelativeEndomorphismMatrixFiberEvaluation
        period hPeriod metric current)

theorem candidateANormalBoundaryMetricUnitGaussMeanCurvatureFiberEvaluation_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real)
    (boundary : OrientationBoundary period hPeriod) :
    candidateANormalBoundaryMetricUnitGaussMeanCurvatureFiberEvaluation
        period hPeriod metric current boundary =
      Matrix.trace (fun row column =>
        (candidateANormalBoundaryInducedRelativeLiftInverseFiberEvaluation
            period hPeriod metric current *
          candidateANormalBoundaryMetricUnitGaussRelativeEndomorphismMatrixFiberEvaluation
            period hPeriod metric current) row column boundary) := by
  unfold candidateANormalBoundaryMetricUnitGaussMeanCurvatureFiberEvaluation
  exact AddMonoidHom.map_trace
    (candidateANormalBoundaryMatrixFieldEvaluationRingHom
      period hPeriod boundary).toAddMonoidHom _

theorem candidateANormalBoundaryMetricUnitGaussMeanCurvatureFiberEvaluation_apply_cut
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real)
    (boundary : CutThroatBoundary period hPeriod) :
    candidateANormalBoundaryMetricUnitGaussMeanCurvatureFiberEvaluation
        period hPeriod metric current boundary =
      Matrix.trace (fun row column =>
        (candidateANormalBoundaryInducedRelativeLiftInverseFiberEvaluation
            period hPeriod metric current *
          candidateANormalBoundaryMetricUnitGaussRelativeEndomorphismMatrixFiberEvaluation
            period hPeriod metric current) row column boundary) :=
  candidateANormalBoundaryMetricUnitGaussMeanCurvatureFiberEvaluation_apply
    period hPeriod metric current boundary

theorem candidateANormalBoundaryMetricUnitGaussMeanCurvatureFiberEvaluation_contDiffOn_two
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric) :
    ContDiffOn Real 2
      (candidateANormalBoundaryMetricUnitGaussMeanCurvatureFiberEvaluation
        period hPeriod metric)
      (candidateANormalBoundaryMetricNormalRootDomain
        period hPeriod metric) := by
  have hInverse :=
    candidateANormalBoundaryInducedRelativeLiftInverseFiberEvaluation_contDiffOn_two
      period hPeriod metric
  have hGauss :=
    candidateANormalBoundaryMetricUnitGaussRelativeEndomorphismMatrixFiberEvaluation_contDiffOn_two
      period hPeriod metric hTransverse
  unfold candidateANormalBoundaryMetricUnitGaussMeanCurvatureFiberEvaluation
    Matrix.trace
  exact ContDiffOn.sum fun row _ => by
    simp only [Matrix.diag_apply, Matrix.mul_apply]
    exact ContDiffOn.sum fun column _ =>
      ((contDiffOn_pi.mp (contDiffOn_pi.mp hInverse row) column).mono
          (fun _ hCurrent => hCurrent.1.2)).mul
        (contDiffOn_pi.mp (contDiffOn_pi.mp hGauss column) row)

/-- Relative induced determinant normalized by its physical-base value. -/
def candidateANormalBoundaryInducedRelativeDeterminantRatioFiberEvaluation
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) :
    CandidateANormalBoundaryScalarField period hPeriod :=
  candidateANormalBoundaryInducedRelativeLiftDeterminantFiberEvaluation
      period hPeriod metric current *
    Ring.inverse
      (candidateANormalBoundaryInducedRelativeLiftDeterminantFiberEvaluation
        period hPeriod metric 0)

theorem
    candidateANormalBoundaryInducedRelativeDeterminantRatioFiberEvaluation_contDiff_two
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    ContDiff Real 2
      (candidateANormalBoundaryInducedRelativeDeterminantRatioFiberEvaluation
        period hPeriod metric) := by
  unfold candidateANormalBoundaryInducedRelativeDeterminantRatioFiberEvaluation
  exact
    (candidateANormalBoundaryInducedRelativeLiftDeterminantFiberEvaluation_contDiff_two
      period hPeriod metric).mul contDiff_const

@[simp]
theorem
    candidateANormalBoundaryInducedRelativeDeterminantRatioFiberEvaluation_zero
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric) :
    candidateANormalBoundaryInducedRelativeDeterminantRatioFiberEvaluation
        period hPeriod metric 0 = 1 := by
  unfold candidateANormalBoundaryInducedRelativeDeterminantRatioFiberEvaluation
  exact Ring.mul_inverse_cancel _
    (zero_mem_candidateANormalBoundaryInducedMetricDomain
      period hPeriod metric hTransverse)

/-- Common admissible neighborhood for the unit normal and the induced
volume-density root. -/
def candidateANormalBoundaryGHYDomain
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    Set (Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) :=
  candidateANormalBoundaryMetricNormalRootDomain period hPeriod metric ∩
    candidateANormalBoundaryInducedRelativeDeterminantRatioFiberEvaluation
        period hPeriod metric ⁻¹'
      candidateANormalBoundaryScalarFieldLocalRootTarget period hPeriod

theorem candidateANormalBoundaryGHYDomain_isOpen
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    IsOpen (candidateANormalBoundaryGHYDomain period hPeriod metric) := by
  unfold candidateANormalBoundaryGHYDomain
  exact (candidateANormalBoundaryMetricNormalRootDomain_isOpen
      period hPeriod metric).inter
    ((candidateANormalBoundaryScalarFieldLocalRootTarget_isOpen
      period hPeriod).preimage
        (candidateANormalBoundaryInducedRelativeDeterminantRatioFiberEvaluation_contDiff_two
          period hPeriod metric).continuous)

theorem zero_mem_candidateANormalBoundaryGHYDomain
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric) :
    (0 : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) ∈
      candidateANormalBoundaryGHYDomain period hPeriod metric := by
  constructor
  · exact zero_mem_candidateANormalBoundaryMetricNormalRootDomain
      period hPeriod metric hTransverse
  · change
      candidateANormalBoundaryInducedRelativeDeterminantRatioFiberEvaluation
          period hPeriod metric 0 ∈
        candidateANormalBoundaryScalarFieldLocalRootTarget period hPeriod
    rw [candidateANormalBoundaryInducedRelativeDeterminantRatioFiberEvaluation_zero
      period hPeriod metric hTransverse]
    exact candidateANormalBoundaryScalarFieldOne_mem_localRootTarget
      period hPeriod

theorem normalGraphNonNullAt_of_candidate_GHY_mem
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hCurrent :
      (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) ∈
        candidateANormalBoundaryGHYDomain period hPeriod metric) :
    NormalGraphNonNullAt period hPeriod variedMetric displacement parameter := by
  apply normalGraphNonNullAt_of_candidate_inducedMetric_mem period hPeriod
    metric tensor variedMetric hVaried displacement parameter
  exact hCurrent.1.1.2

/-- Selected local square root of the normalized induced determinant. -/
def candidateANormalBoundaryInducedRelativeVolumeRootFiberEvaluation
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) :
    CandidateANormalBoundaryScalarField period hPeriod :=
  candidateANormalBoundaryScalarFieldLocalRootBranch period hPeriod
    (candidateANormalBoundaryInducedRelativeDeterminantRatioFiberEvaluation
      period hPeriod metric current)

theorem
    candidateANormalBoundaryInducedRelativeVolumeRootFiberEvaluation_square
    (metric : RegularGeneralLorentzMetric period hPeriod)
    {current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real}
    (hCurrent : current ∈ candidateANormalBoundaryGHYDomain
      period hPeriod metric) :
    candidateANormalBoundaryScalarFieldSquare period hPeriod
        (candidateANormalBoundaryInducedRelativeVolumeRootFiberEvaluation
          period hPeriod metric current) =
      candidateANormalBoundaryInducedRelativeDeterminantRatioFiberEvaluation
        period hPeriod metric current :=
  candidateANormalBoundaryScalarFieldLocalRootBranch_square
    period hPeriod hCurrent.2

@[simp]
theorem candidateANormalBoundaryInducedRelativeVolumeRootFiberEvaluation_zero
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric) :
    candidateANormalBoundaryInducedRelativeVolumeRootFiberEvaluation
        period hPeriod metric 0 = 1 := by
  unfold candidateANormalBoundaryInducedRelativeVolumeRootFiberEvaluation
  rw [candidateANormalBoundaryInducedRelativeDeterminantRatioFiberEvaluation_zero
      period hPeriod metric hTransverse,
    candidateANormalBoundaryScalarFieldLocalRootBranch_at_one]

theorem
    candidateANormalBoundaryInducedRelativeVolumeRootFiberEvaluation_contDiffOn_two
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    ContDiffOn Real 2
      (candidateANormalBoundaryInducedRelativeVolumeRootFiberEvaluation
        period hPeriod metric)
      (candidateANormalBoundaryGHYDomain period hPeriod metric) := by
  unfold candidateANormalBoundaryInducedRelativeVolumeRootFiberEvaluation
  exact (candidateANormalBoundaryScalarFieldLocalRootBranch_contDiffOn
      period hPeriod).comp
    (candidateANormalBoundaryInducedRelativeDeterminantRatioFiberEvaluation_contDiff_two
      period hPeriod metric).contDiffOn
    (fun _ hCurrent => hCurrent.2)

/-- Absolute physical-base determinant of the faithful induced lift. -/
def candidateANormalBoundaryInducedBaseAbsoluteDeterminant
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    CandidateANormalBoundaryScalarField period hPeriod :=
  BoundedContinuousFunction.mkOfCompact
    { toFun := fun boundary =>
        |candidateANormalBoundaryInducedRelativeLiftDeterminantFiberEvaluation
          period hPeriod metric 0 boundary|
      continuous_toFun :=
        (candidateANormalBoundaryInducedRelativeLiftDeterminantFiberEvaluation
          period hPeriod metric 0).continuous.abs }

@[simp]
theorem candidateANormalBoundaryInducedBaseAbsoluteDeterminant_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (boundary : OrientationBoundary period hPeriod) :
    candidateANormalBoundaryInducedBaseAbsoluteDeterminant
        period hPeriod metric boundary =
      |candidateANormalBoundaryInducedRelativeLiftDeterminantFiberEvaluation
        period hPeriod metric 0 boundary| :=
  rfl

/-- Positive physical-base induced-volume density. -/
def candidateANormalBoundaryInducedBaseVolumeDensity
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    CandidateANormalBoundaryScalarField period hPeriod :=
  BoundedContinuousFunction.mkOfCompact
    { toFun := fun boundary => Real.sqrt
        |candidateANormalBoundaryInducedRelativeLiftDeterminantFiberEvaluation
          period hPeriod metric 0 boundary|
      continuous_toFun :=
        (candidateANormalBoundaryInducedRelativeLiftDeterminantFiberEvaluation
          period hPeriod metric 0).continuous.abs.sqrt }

@[simp]
theorem candidateANormalBoundaryInducedBaseVolumeDensity_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (boundary : OrientationBoundary period hPeriod) :
    candidateANormalBoundaryInducedBaseVolumeDensity
        period hPeriod metric boundary =
      Real.sqrt
        |candidateANormalBoundaryInducedRelativeLiftDeterminantFiberEvaluation
          period hPeriod metric 0 boundary| :=
  rfl

theorem candidateANormalBoundaryInducedBaseVolumeDensity_square
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    candidateANormalBoundaryScalarFieldSquare period hPeriod
        (candidateANormalBoundaryInducedBaseVolumeDensity
          period hPeriod metric) =
      candidateANormalBoundaryInducedBaseAbsoluteDeterminant
        period hPeriod metric := by
  ext boundary
  change Real.sqrt
        |candidateANormalBoundaryInducedRelativeLiftDeterminantFiberEvaluation
          period hPeriod metric 0 boundary| *
      Real.sqrt
        |candidateANormalBoundaryInducedRelativeLiftDeterminantFiberEvaluation
          period hPeriod metric 0 boundary| = _
  exact Real.mul_self_sqrt (abs_nonneg _)

theorem candidateANormalBoundaryInducedBaseVolumeDensity_isUnit
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric) :
    IsUnit (candidateANormalBoundaryInducedBaseVolumeDensity
      period hPeriod metric) := by
  apply boundedContinuousFunction_isUnit_of_forall_ne_zero
  intro boundary
  rw [candidateANormalBoundaryInducedBaseVolumeDensity_apply]
  exact ne_of_gt (Real.sqrt_pos.2 (abs_pos.mpr
    (candidateANormalBoundaryInducedRelativeLiftDeterminantFiberEvaluation_zero_ne_zero
      period hPeriod metric hTransverse boundary)))

theorem
    candidateANormalBoundaryInducedRelativeVolumeRootFiberEvaluation_isUnit
    (metric : RegularGeneralLorentzMetric period hPeriod)
    {current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real}
    (hCurrent : current ∈ candidateANormalBoundaryGHYDomain
      period hPeriod metric) :
    IsUnit (candidateANormalBoundaryInducedRelativeVolumeRootFiberEvaluation
      period hPeriod metric current) := by
  have hSource :=
    (candidateANormalBoundaryScalarFieldLocalSquareChart
      period hPeriod).map_target hCurrent.2
  rw [candidateANormalBoundaryScalarFieldLocalSquareChart,
    OpenPartialHomeomorph.restrOpen_source] at hSource
  exact hSource.2

/-- Completed induced-volume density on the common GHY chart. -/
def candidateANormalBoundaryInducedVolumeDensityFiberEvaluation
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) :
    CandidateANormalBoundaryScalarField period hPeriod :=
  candidateANormalBoundaryInducedBaseVolumeDensity period hPeriod metric *
    candidateANormalBoundaryInducedRelativeVolumeRootFiberEvaluation
      period hPeriod metric current

theorem
    candidateANormalBoundaryInducedVolumeDensityFiberEvaluation_contDiffOn_two
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    ContDiffOn Real 2
      (candidateANormalBoundaryInducedVolumeDensityFiberEvaluation
        period hPeriod metric)
      (candidateANormalBoundaryGHYDomain period hPeriod metric) := by
  unfold candidateANormalBoundaryInducedVolumeDensityFiberEvaluation
  exact contDiffOn_const.mul
    (candidateANormalBoundaryInducedRelativeVolumeRootFiberEvaluation_contDiffOn_two
      period hPeriod metric)

theorem candidateANormalBoundaryInducedVolumeDensityFiberEvaluation_square
    (metric : RegularGeneralLorentzMetric period hPeriod)
    {current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real}
    (hCurrent : current ∈ candidateANormalBoundaryGHYDomain
      period hPeriod metric) :
    candidateANormalBoundaryScalarFieldSquare period hPeriod
        (candidateANormalBoundaryInducedVolumeDensityFiberEvaluation
          period hPeriod metric current) =
      candidateANormalBoundaryInducedBaseAbsoluteDeterminant
          period hPeriod metric *
        candidateANormalBoundaryInducedRelativeDeterminantRatioFiberEvaluation
          period hPeriod metric current := by
  unfold candidateANormalBoundaryInducedVolumeDensityFiberEvaluation
  rw [show candidateANormalBoundaryScalarFieldSquare period hPeriod
      (candidateANormalBoundaryInducedBaseVolumeDensity period hPeriod metric *
       candidateANormalBoundaryInducedRelativeVolumeRootFiberEvaluation
        period hPeriod metric current) =
      candidateANormalBoundaryScalarFieldSquare period hPeriod
          (candidateANormalBoundaryInducedBaseVolumeDensity
            period hPeriod metric) *
        candidateANormalBoundaryScalarFieldSquare period hPeriod
          (candidateANormalBoundaryInducedRelativeVolumeRootFiberEvaluation
            period hPeriod metric current) by
      unfold candidateANormalBoundaryScalarFieldSquare
      ring]
  rw [candidateANormalBoundaryInducedBaseVolumeDensity_square,
    candidateANormalBoundaryInducedRelativeVolumeRootFiberEvaluation_square
      period hPeriod metric hCurrent]

/-- Whenever the selected local root has its physical sign, the completed
density is the canonical positive square root of the full determinant. -/
theorem candidateANormalBoundaryInducedVolumeDensity_eq_sqrt_abs
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric)
    {current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real}
    (hCurrent : current ∈ candidateANormalBoundaryGHYDomain
      period hPeriod metric)
    (boundary : OrientationBoundary period hPeriod)
    (hRootNonneg : 0 ≤
      candidateANormalBoundaryInducedRelativeVolumeRootFiberEvaluation
        period hPeriod metric current boundary) :
    candidateANormalBoundaryInducedVolumeDensityFiberEvaluation
        period hPeriod metric current boundary =
      Real.sqrt
        |candidateANormalBoundaryInducedRelativeLiftDeterminantFiberEvaluation
          period hPeriod metric current boundary| := by
  let determinant :=
    candidateANormalBoundaryInducedRelativeLiftDeterminantFiberEvaluation
      period hPeriod metric current
  let baseDeterminant :=
    candidateANormalBoundaryInducedRelativeLiftDeterminantFiberEvaluation
      period hPeriod metric 0
  let ratio :=
    candidateANormalBoundaryInducedRelativeDeterminantRatioFiberEvaluation
      period hPeriod metric current
  have hBaseUnit : IsUnit baseDeterminant := by
    change (0 : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) ∈
        candidateANormalBoundaryInducedMetricDomain period hPeriod metric
    exact zero_mem_candidateANormalBoundaryInducedMetricDomain
      period hPeriod metric hTransverse
  have hRatioBase : ratio * baseDeterminant = determinant := by
    change
      (candidateANormalBoundaryInducedRelativeLiftDeterminantFiberEvaluation
          period hPeriod metric current *
        Ring.inverse baseDeterminant) * baseDeterminant = determinant
    calc
      (determinant * Ring.inverse baseDeterminant) * baseDeterminant =
          determinant * (baseDeterminant * Ring.inverse baseDeterminant) := by
        ac_rfl
      _ = determinant * 1 := by
        rw [Ring.mul_inverse_cancel baseDeterminant hBaseUnit]
      _ = determinant := mul_one _
  have hRatioBaseAt := congrArg (fun field => field boundary) hRatioBase
  change ratio boundary * baseDeterminant boundary =
    determinant boundary at hRatioBaseAt
  have hRootSquareAt := congrArg (fun field => field boundary)
    (candidateANormalBoundaryInducedRelativeVolumeRootFiberEvaluation_square
      period hPeriod metric hCurrent)
  change
    candidateANormalBoundaryInducedRelativeVolumeRootFiberEvaluation
          period hPeriod metric current boundary *
        candidateANormalBoundaryInducedRelativeVolumeRootFiberEvaluation
          period hPeriod metric current boundary =
      ratio boundary at hRootSquareAt
  have hRatioNonneg : 0 ≤ ratio boundary := by
    rw [← hRootSquareAt]
    positivity
  have hAbsDeterminant :
      |determinant boundary| =
        ratio boundary * |baseDeterminant boundary| := by
    calc
      |determinant boundary| =
          |ratio boundary * baseDeterminant boundary| := by
        rw [hRatioBaseAt]
      _ = |ratio boundary| * |baseDeterminant boundary| := abs_mul _ _
      _ = ratio boundary * |baseDeterminant boundary| := by
        rw [abs_of_nonneg hRatioNonneg]
  have hDensitySquareAt := congrArg (fun field => field boundary)
    (candidateANormalBoundaryInducedVolumeDensityFiberEvaluation_square
      period hPeriod metric hCurrent)
  change
    candidateANormalBoundaryInducedVolumeDensityFiberEvaluation
          period hPeriod metric current boundary *
        candidateANormalBoundaryInducedVolumeDensityFiberEvaluation
          period hPeriod metric current boundary =
      |baseDeterminant boundary| * ratio boundary at hDensitySquareAt
  have hDensitySquare :
      candidateANormalBoundaryInducedVolumeDensityFiberEvaluation
            period hPeriod metric current boundary *
          candidateANormalBoundaryInducedVolumeDensityFiberEvaluation
            period hPeriod metric current boundary =
        |determinant boundary| := by
    calc
      _ = |baseDeterminant boundary| * ratio boundary := hDensitySquareAt
      _ = ratio boundary * |baseDeterminant boundary| := mul_comm _ _
      _ = |determinant boundary| := hAbsDeterminant.symm
  have hDensityNonneg : 0 ≤
      candidateANormalBoundaryInducedVolumeDensityFiberEvaluation
        period hPeriod metric current boundary := by
    change 0 ≤
      Real.sqrt |baseDeterminant boundary| *
        candidateANormalBoundaryInducedRelativeVolumeRootFiberEvaluation
          period hPeriod metric current boundary
    exact mul_nonneg (Real.sqrt_nonneg _) hRootNonneg
  calc
    candidateANormalBoundaryInducedVolumeDensityFiberEvaluation
        period hPeriod metric current boundary =
      Real.sqrt
        (candidateANormalBoundaryInducedVolumeDensityFiberEvaluation
          period hPeriod metric current boundary ^ 2) := by
      exact (Real.sqrt_sq hDensityNonneg).symm
    _ = Real.sqrt |determinant boundary| := by
      rw [pow_two, hDensitySquare]

/-- The local root selected at `1` retains its positive pointwise sign on a
genuine neighborhood of the physical base point. -/
theorem candidateANormalBoundaryInducedRelativeVolumeRoot_eventually_pos
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric) :
    ∀ᶠ current in 𝓝
        (0 : Prod
          (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real),
      current ∈ candidateANormalBoundaryGHYDomain period hPeriod metric ∧
        ∀ boundary : OrientationBoundary period hPeriod,
          0 <
            candidateANormalBoundaryInducedRelativeVolumeRootFiberEvaluation
              period hPeriod metric current boundary := by
  let root :=
    candidateANormalBoundaryInducedRelativeVolumeRootFiberEvaluation
      period hPeriod metric
  have hZero := zero_mem_candidateANormalBoundaryGHYDomain
    period hPeriod metric hTransverse
  have hDomain : ∀ᶠ current in 𝓝
      (0 : Prod
        (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real),
      current ∈ candidateANormalBoundaryGHYDomain period hPeriod metric :=
    (candidateANormalBoundaryGHYDomain_isOpen period hPeriod metric).mem_nhds
      hZero
  have hRootContinuous : ContinuousAt root 0 :=
    ((candidateANormalBoundaryInducedRelativeVolumeRootFiberEvaluation_contDiffOn_two
      period hPeriod metric).contDiffAt
        ((candidateANormalBoundaryGHYDomain_isOpen period hPeriod metric).mem_nhds
          hZero)).continuousAt
  have hNear : ∀ᶠ current in 𝓝
      (0 : Prod
        (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real),
      root current ∈ Metric.ball (root 0) 1 :=
    hRootContinuous (Metric.ball_mem_nhds _ one_pos)
  filter_upwards [hDomain, hNear] with current hCurrent hCurrentNear
  refine ⟨hCurrent, ?_⟩
  intro boundary
  have hRootZero : root 0 = 1 :=
    candidateANormalBoundaryInducedRelativeVolumeRootFiberEvaluation_zero
      period hPeriod metric hTransverse
  rw [hRootZero] at hCurrentNear
  have hCurrentNear' : dist (root current) 1 < 1 := hCurrentNear
  rw [dist_eq_norm] at hCurrentNear'
  have hEvaluation := (root current - 1).norm_coe_le_norm boundary
  change |root current boundary - 1| ≤ ‖root current - 1‖ at hEvaluation
  have hPointwise : |root current boundary - 1| < 1 :=
    lt_of_le_of_lt hEvaluation hCurrentNear'
  linarith [abs_lt.mp hPointwise |>.1]

/-- The independently selected normal-magnitude root also retains its positive
pointwise sign on a genuine neighborhood of the physical base point. -/
theorem candidateANormalBoundaryMetricNormalRelativeRoot_eventually_pos
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric) :
    ∀ᶠ current in 𝓝
        (0 : Prod
          (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real),
      current ∈ candidateANormalBoundaryGHYDomain period hPeriod metric ∧
        ∀ boundary : OrientationBoundary period hPeriod,
          0 < candidateANormalBoundaryMetricNormalRelativeRootFiberEvaluation
            period hPeriod metric current boundary := by
  let root := candidateANormalBoundaryMetricNormalRelativeRootFiberEvaluation
    period hPeriod metric
  have hZeroGHY := zero_mem_candidateANormalBoundaryGHYDomain
    period hPeriod metric hTransverse
  have hDomain : ∀ᶠ current in 𝓝
      (0 : Prod
        (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real),
      current ∈ candidateANormalBoundaryGHYDomain period hPeriod metric :=
    (candidateANormalBoundaryGHYDomain_isOpen period hPeriod metric).mem_nhds
      hZeroGHY
  have hZeroRootDomain :=
    zero_mem_candidateANormalBoundaryMetricNormalRootDomain
      period hPeriod metric hTransverse
  have hRootContinuous : ContinuousAt root 0 :=
    ((candidateANormalBoundaryMetricNormalRelativeRootFiberEvaluation_contDiffOn_two
      period hPeriod metric).contDiffAt
        ((candidateANormalBoundaryMetricNormalRootDomain_isOpen
          period hPeriod metric).mem_nhds hZeroRootDomain)).continuousAt
  have hNear : ∀ᶠ current in 𝓝
      (0 : Prod
        (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real),
      root current ∈ Metric.ball (root 0) 1 :=
    hRootContinuous (Metric.ball_mem_nhds _ one_pos)
  filter_upwards [hDomain, hNear] with current hCurrent hCurrentNear
  refine ⟨hCurrent, ?_⟩
  intro boundary
  have hRootZero : root 0 = 1 :=
    candidateANormalBoundaryMetricNormalRelativeRootFiberEvaluation_zero
      period hPeriod metric hTransverse
  rw [hRootZero] at hCurrentNear
  have hCurrentNear' : dist (root current) 1 < 1 := hCurrentNear
  rw [dist_eq_norm] at hCurrentNear'
  have hEvaluation := (root current - 1).norm_coe_le_norm boundary
  change |root current boundary - 1| ≤ ‖root current - 1‖ at hEvaluation
  have hPointwise : |root current boundary - 1| < 1 :=
    lt_of_le_of_lt hEvaluation hCurrentNear'
  linarith [abs_lt.mp hPointwise |>.1]

/-- On the positive smooth germ, the completed density is exactly the
historical frame-free graph density. -/
theorem candidateANormalBoundaryInducedVolumeDensity_smooth_eq_historical
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : CutThroatBoundary period hPeriod)
    (hCurrent :
      (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) ∈
        candidateANormalBoundaryGHYDomain period hPeriod metric)
    (hRootNonneg : 0 ≤
      candidateANormalBoundaryInducedRelativeVolumeRootFiberEvaluation
        period hPeriod metric
        (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) boundary) :
    candidateANormalBoundaryInducedVolumeDensityFiberEvaluation
        period hPeriod metric
        (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) boundary =
      normalGraphRelativeVolumeDensity period hPeriod variedMetric displacement
        parameter (orientationDoubleToThroat period hPeriod boundary) := by
  rw [normalGraphRelativeVolumeDensity]
  rw [← candidateANormalBoundaryInducedRelativeLiftDeterminantFiberEvaluation_smooth_eq_historical
    period hPeriod metric tensor variedMetric hVaried displacement parameter
      boundary]
  exact candidateANormalBoundaryInducedVolumeDensity_eq_sqrt_abs
    period hPeriod metric hTransverse hCurrent boundary hRootNonneg

/-! ### Smooth-graph identification of the completed metric unit normal -/

def normalBoundarySmoothGraphVerticalTangentialCovector
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : CutThroatBoundary period hPeriod) :
    TangentSpace throatCoverModelWithCorners boundary →L[Real] Real :=
  (variedMetric.tensor.tensor
      (normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter))
      (normalGraphCanonicalLatitudeVector period hPeriod displacement parameter
        boundary)).comp
    (mfderiv throatCoverModelWithCorners coverModelWithCorners
      (fun current : CutThroatBoundary period hPeriod =>
        normalGraphOrientationDouble period hPeriod displacement
          (current, parameter)) boundary)

theorem candidateANormalBoundaryVerticalTangentialPairing_smooth_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : CutThroatBoundary period hPeriod)
    (index : NormalBoundaryTangentIndex period hPeriod) :
    let variation := smoothToCandidateANormalBoundaryFunctionalCore
      period hPeriod metric (tensor, displacement)
    let vector :=
      (finiteSmoothThroatGeneratingFrame
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)).vectorAt
          boundary index
    candidateANormalBoundaryVerticalTangentialPairingFiberEvaluation
        period hPeriod metric index (variation, parameter) boundary =
      normalBoundarySmoothGraphVerticalTangentialCovector period hPeriod
        variedMetric displacement parameter boundary vector := by
  dsimp only
  classical
  let point := normalGraphOrientationDouble period hPeriod displacement
    (boundary, parameter)
  let vector :=
    (finiteSmoothThroatGeneratingFrame
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)).vectorAt
        boundary index
  have hMetric (first second : Fin 4) :=
    candidateANormalBoundaryActualMetricMatrixFiberEvaluation_eq_variedMetric
      period hPeriod metric tensor variedMetric hVaried displacement parameter
        boundary first second
  have hVertical := candidateANormalBoundaryVertical_smooth_reconstructs
    period hPeriod metric tensor displacement parameter boundary
  have hTangent := candidateANormalBoundaryGraphTangent_smooth_reconstructs
    period hPeriod metric tensor displacement parameter boundary index
  unfold candidateANormalBoundaryVerticalTangentialPairingFiberEvaluation
    normalBoundarySmoothGraphVerticalTangentialCovector
  simp only [BoundedContinuousFunction.sum_apply,
    BoundedContinuousFunction.mul_apply, ContinuousLinearMap.comp_apply]
  simp_rw [hMetric]
  change _ = variedMetric.tensor.tensor point
    (normalGraphCanonicalLatitudeVector period hPeriod displacement parameter
      boundary)
    (mfderiv throatCoverModelWithCorners coverModelWithCorners
      (fun current : CutThroatBoundary period hPeriod =>
        normalGraphOrientationDouble period hPeriod displacement
          (current, parameter)) boundary vector)
  rw [← hVertical, ← hTangent]
  simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul,
    Finset.mul_sum, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  ring

theorem candidateANormalBoundaryVerticalTangentialReferenceDual_smooth_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : CutThroatBoundary period hPeriod)
    (row : NormalBoundaryTangentIndex period hPeriod) :
    let variation := smoothToCandidateANormalBoundaryFunctionalCore
      period hPeriod metric (tensor, displacement)
    candidateANormalBoundaryVerticalTangentialReferenceDualFiberEvaluation
        period hPeriod metric row (variation, parameter) boundary =
      intrinsicThroatFiniteFrameAnalysisAt
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
        (finiteSmoothThroatGeneratingFrame
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
        boundary
        (intrinsicThroatInverseMusical
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
          boundary
          (normalBoundarySmoothGraphVerticalTangentialCovector
            period hPeriod variedMetric displacement parameter boundary)) row := by
  dsimp only
  classical
  have hApplied := congrFun
    (intrinsicThroatFiniteFrameEndomorphismMatrixAt_inverseOperator_mulVec
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
      (finiteSmoothThroatGeneratingFrame
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
      boundary
      (normalBoundarySmoothGraphVerticalTangentialCovector
        period hPeriod variedMetric displacement parameter boundary)) row
  unfold candidateANormalBoundaryVerticalTangentialReferenceDualFiberEvaluation
  simp only [BoundedContinuousFunction.sum_apply,
    BoundedContinuousFunction.mul_apply,
    normalBoundaryReferenceDualCoefficientMatrix_apply_eq_encoding_inverse]
  simp_rw [candidateANormalBoundaryVerticalTangentialPairing_smooth_apply
    period hPeriod metric tensor variedMetric hVaried displacement parameter
      boundary]
  unfold Matrix.mulVec dotProduct at hApplied
  convert hApplied using 1 <;> rfl

def candidateANormalBoundaryTangentialProjectionVectorFiberEvaluation
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real)
    (boundary : CutThroatBoundary period hPeriod) :
    TangentSpace throatCoverModelWithCorners boundary :=
  intrinsicThroatFiniteFrameSynthesisAt
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
    (finiteSmoothThroatGeneratingFrame
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
    boundary
    (fun row =>
      candidateANormalBoundaryTangentialProjectionCoefficientFiberEvaluation
        period hPeriod metric row current boundary)

set_option backward.isDefEq.respectTransparency false in
theorem candidateANormalBoundaryTangentialProjectionVector_smooth_relative
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : CutThroatBoundary period hPeriod)
    (hCurrent :
      (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) ∈
        candidateANormalBoundaryInducedMetricDomain period hPeriod metric) :
    normalBoundarySmoothGraphRelativeEndomorphism period hPeriod
        variedMetric displacement parameter boundary
        (candidateANormalBoundaryTangentialProjectionVectorFiberEvaluation
          period hPeriod metric
            (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
              (tensor, displacement), parameter) boundary) =
      intrinsicThroatInverseMusical
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
        boundary
        (normalBoundarySmoothGraphVerticalTangentialCovector period hPeriod
          variedMetric displacement parameter boundary) := by
  classical
  let current :=
    (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
      (tensor, displacement), parameter)
  let lift := candidateANormalBoundaryInducedRelativeLiftFiberEvaluation
    period hPeriod metric current
  let inverse :=
    candidateANormalBoundaryInducedRelativeLiftInverseFiberEvaluation
      period hPeriod metric current
  let reference := fun row : NormalBoundaryTangentIndex period hPeriod =>
    candidateANormalBoundaryVerticalTangentialReferenceDualFiberEvaluation
      period hPeriod metric row current
  let coefficients := fun row : NormalBoundaryTangentIndex period hPeriod =>
    candidateANormalBoundaryTangentialProjectionCoefficientFiberEvaluation
      period hPeriod metric row current
  have hCoefficients : coefficients = inverse.mulVec reference := by
    funext row
    unfold coefficients inverse reference
      candidateANormalBoundaryTangentialProjectionCoefficientFiberEvaluation
      Matrix.mulVec dotProduct
    rfl
  have hInverse := candidateANormalBoundaryInducedRelativeLift_mul_inverse
    period hPeriod metric current hCurrent
  have hSolve : lift.mulVec coefficients = reference := by
    rw [hCoefficients, Matrix.mulVec_mulVec]
    have hProduct : lift * inverse = 1 := by
      simpa only [lift, inverse] using hInverse
    rw [hProduct, Matrix.one_mulVec]
  have hSolveAt :
      (intrinsicThroatFiniteFrameLiftAt
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
        (finiteSmoothThroatGeneratingFrame
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
        boundary
        (normalBoundarySmoothGraphRelativeEndomorphism period hPeriod
          variedMetric displacement parameter boundary).toLinearMap).mulVec
          (fun row => coefficients row boundary) =
        intrinsicThroatFiniteFrameAnalysisAt
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
          (finiteSmoothThroatGeneratingFrame
            (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
          boundary
          (intrinsicThroatInverseMusical
            (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
            boundary
            (normalBoundarySmoothGraphVerticalTangentialCovector
              period hPeriod variedMetric displacement parameter boundary)) := by
    have hLiftEntry (first second : NormalBoundaryTangentIndex period hPeriod) :
        candidateANormalBoundaryInducedRelativeLiftFiberEvaluation
              period hPeriod metric current first second boundary =
          intrinsicThroatFiniteFrameLiftAt
            (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
            (finiteSmoothThroatGeneratingFrame
              (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
            boundary
            (normalBoundarySmoothGraphRelativeEndomorphism period hPeriod
              variedMetric displacement parameter boundary).toLinearMap
            first second := by
      exact candidateANormalBoundaryInducedRelativeLiftFiberEvaluation_smooth_apply
        period hPeriod metric tensor variedMetric hVaried displacement parameter
          boundary first second
    have hReferenceEntry (index : NormalBoundaryTangentIndex period hPeriod) :
        candidateANormalBoundaryVerticalTangentialReferenceDualFiberEvaluation
              period hPeriod metric index current boundary =
          intrinsicThroatFiniteFrameAnalysisAt
            (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
            (finiteSmoothThroatGeneratingFrame
              (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
            boundary
            (intrinsicThroatInverseMusical
              (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
              boundary
              (normalBoundarySmoothGraphVerticalTangentialCovector
                period hPeriod variedMetric displacement parameter boundary))
            index := by
      exact
        candidateANormalBoundaryVerticalTangentialReferenceDual_smooth_apply
          period hPeriod metric tensor variedMetric hVaried displacement parameter
            boundary index
    funext row
    have hApplied := congrArg
      (fun field : BoundedContinuousFunction
          (CutThroatBoundary period hPeriod) Real => field boundary)
      (congrFun hSolve row)
    unfold lift reference at hApplied
    unfold Matrix.mulVec dotProduct at hApplied ⊢
    simp only [BoundedContinuousFunction.sum_apply,
      BoundedContinuousFunction.mul_apply] at hApplied
    simp_rw [hLiftEntry, hReferenceEntry] at hApplied
    convert hApplied using 1 <;> rfl
  have hSynthesis := congrArg
    (intrinsicThroatFiniteFrameSynthesisAt
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
      (finiteSmoothThroatGeneratingFrame
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
      boundary) hSolveAt
  rw [intrinsicThroatFiniteFrameSynthesisAt_liftAt_mulVec] at hSynthesis
  have hReconstruct := LinearMap.congr_fun
    (intrinsicThroatFiniteFrameSynthesisAt_comp_analysisAt
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
      (finiteSmoothThroatGeneratingFrame
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))
      boundary)
    (intrinsicThroatInverseMusical
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
      boundary
      (normalBoundarySmoothGraphVerticalTangentialCovector period hPeriod
        variedMetric displacement parameter boundary))
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at hReconstruct
  rw [hReconstruct] at hSynthesis
  dsimp only [coefficients] at hSynthesis
  unfold candidateANormalBoundaryTangentialProjectionVectorFiberEvaluation
  convert hSynthesis using 1 <;> rfl

theorem candidateANormalBoundaryTangentialProjectionVector_smooth_musical
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : CutThroatBoundary period hPeriod)
    (hCurrent :
      (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) ∈
        candidateANormalBoundaryInducedMetricDomain period hPeriod metric) :
    normalBoundarySmoothGraphInducedMetricMusical period hPeriod
        variedMetric displacement parameter boundary
        (candidateANormalBoundaryTangentialProjectionVectorFiberEvaluation
          period hPeriod metric
            (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
              (tensor, displacement), parameter) boundary) =
      normalBoundarySmoothGraphVerticalTangentialCovector period hPeriod
        variedMetric displacement parameter boundary := by
  have hRelative :=
    candidateANormalBoundaryTangentialProjectionVector_smooth_relative
      period hPeriod metric tensor variedMetric hVaried displacement parameter
        boundary hCurrent
  unfold normalBoundarySmoothGraphRelativeEndomorphism at hRelative
  exact (intrinsicThroatInverseMusical
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
    boundary).injective hRelative

set_option backward.isDefEq.respectTransparency false in
theorem candidateANormalBoundaryTangentialProjectionVector_smooth_eq_historical
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : CutThroatBoundary period hPeriod)
    (hCurrent :
      (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) ∈
        candidateANormalBoundaryInducedMetricDomain period hPeriod metric)
    (hNonNull : NormalGraphNonNullAt period hPeriod variedMetric displacement
      parameter) :
    normalBoundaryOrientationTangentEquiv period hPeriod boundary
        (candidateANormalBoundaryTangentialProjectionVectorFiberEvaluation
          period hPeriod metric
            (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
              (tensor, displacement), parameter) boundary) =
      normalGraphInducedMetricInverse period hPeriod variedMetric displacement
        parameter hNonNull (orientationDoubleToThroat period hPeriod boundary)
        (normalGraphTangentialPairing period hPeriod variedMetric displacement
          parameter (orientationDoubleToThroat period hPeriod boundary)
          (normalGraphCanonicalLatitudeVector period hPeriod displacement
            parameter boundary)) := by
  let tangentEquiv :=
    normalBoundaryOrientationTangentEquiv period hPeriod boundary
  let target := orientationDoubleToThroat period hPeriod boundary
  let projection :=
    candidateANormalBoundaryTangentialProjectionVectorFiberEvaluation
      period hPeriod metric
        (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) boundary
  let vertical := normalGraphCanonicalLatitudeVector period hPeriod displacement
    parameter boundary
  apply (normalGraphInducedMetricEquiv period hPeriod variedMetric displacement
    parameter hNonNull target).injective
  rw [normalGraphInducedMetricEquiv_apply,
    normalGraphInducedMetricEquiv_apply,
    normalGraphInducedMetric_metricInverse]
  apply ContinuousLinearMap.ext
  intro targetSecond
  have hMusical := congrArg
    (fun covector : TangentSpace throatCoverModelWithCorners boundary →L[Real]
        Real => covector (tangentEquiv.symm targetSecond))
    (candidateANormalBoundaryTangentialProjectionVector_smooth_musical
      period hPeriod metric tensor variedMetric hVaried displacement parameter
        boundary hCurrent)
  rw [normalBoundarySmoothGraphInducedMetricMusical_apply] at hMusical
  unfold normalBoundarySmoothGraphVerticalTangentialCovector at hMusical
  simp only [ContinuousLinearMap.comp_apply] at hMusical
  rw [normalGraphOrientationDouble_mfderiv_eq_comp,
    ← normalBoundaryOrientationTangentEquiv_apply,
    ContinuousLinearEquiv.apply_symm_apply] at hMusical
  exact hMusical

def candidateANormalBoundaryTangentialProjectionAmbientVector_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : CutThroatBoundary period hPeriod) :
    TangentSpace coverModelWithCorners
      (normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter)) :=
  mfderiv throatCoverModelWithCorners coverModelWithCorners
    (fun current : CutThroatBoundary period hPeriod =>
      normalGraphOrientationDouble period hPeriod displacement
        (current, parameter)) boundary
    (candidateANormalBoundaryTangentialProjectionVectorFiberEvaluation
      period hPeriod metric
        (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) boundary)

set_option backward.isDefEq.respectTransparency false in
theorem candidateANormalBoundaryTangentialProjectionAmbientVector_smooth_eq_historical
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : CutThroatBoundary period hPeriod)
    (hCurrent :
      (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) ∈
        candidateANormalBoundaryInducedMetricDomain period hPeriod metric)
    (hNonNull : NormalGraphNonNullAt period hPeriod variedMetric displacement
      parameter) :
    candidateANormalBoundaryTangentialProjectionAmbientVector_smooth
        period hPeriod metric tensor displacement parameter boundary =
      normalGraphTangentialProjection period hPeriod variedMetric displacement
        parameter hNonNull (orientationDoubleToThroat period hPeriod boundary)
        (normalGraphCanonicalLatitudeVector period hPeriod displacement
          parameter boundary) := by
  unfold candidateANormalBoundaryTangentialProjectionAmbientVector_smooth
    normalGraphTangentialProjection
  rw [normalGraphOrientationDouble_mfderiv_eq_comp,
    ← normalBoundaryOrientationTangentEquiv_apply]
  rw [candidateANormalBoundaryTangentialProjectionVector_smooth_eq_historical
    period hPeriod metric tensor variedMetric hVaried displacement parameter
      boundary hCurrent hNonNull]

set_option backward.isDefEq.respectTransparency false in
theorem candidateANormalBoundaryTangentialProjectionAmbientVector_smooth_eq_sum
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : CutThroatBoundary period hPeriod) :
    let current :=
      (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
        (tensor, displacement), parameter)
    let point := normalGraphOrientationDouble period hPeriod displacement
      (boundary, parameter)
    candidateANormalBoundaryTangentialProjectionAmbientVector_smooth
        period hPeriod metric tensor displacement parameter boundary =
      ∑ index : NormalBoundaryTangentIndex period hPeriod,
        candidateANormalBoundaryTangentialProjectionCoefficientFiberEvaluation
              period hPeriod metric index current boundary •
          ∑ row : Fin 4,
            candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation
                  period hPeriod metric index row current boundary •
              metric.frame row point := by
  dsimp only
  classical
  let current :=
    (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
      (tensor, displacement), parameter)
  let frame := finiteSmoothThroatGeneratingFrame
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
  let coefficients := fun index : NormalBoundaryTangentIndex period hPeriod =>
    candidateANormalBoundaryTangentialProjectionCoefficientFiberEvaluation
      period hPeriod metric index current boundary
  let projection :=
    candidateANormalBoundaryTangentialProjectionVectorFiberEvaluation
      period hPeriod metric current boundary
  let derivative := mfderiv throatCoverModelWithCorners coverModelWithCorners
    (fun point : CutThroatBoundary period hPeriod =>
      normalGraphOrientationDouble period hPeriod displacement
        (point, parameter)) boundary
  have hSynthesis : projection =
      ∑ index : NormalBoundaryTangentIndex period hPeriod,
        coefficients index • frame.vectorAt boundary index := by
    unfold projection
      candidateANormalBoundaryTangentialProjectionVectorFiberEvaluation
    exact intrinsicThroatFiniteFrameSynthesisAt_apply
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
      frame boundary coefficients
  have hDerivative := congrArg derivative hSynthesis
  rw [map_sum] at hDerivative
  simp only [map_smul] at hDerivative
  unfold candidateANormalBoundaryTangentialProjectionAmbientVector_smooth
  change derivative projection = _
  rw [hDerivative]
  apply Finset.sum_congr rfl
  intro index _
  rw [candidateANormalBoundaryGraphTangent_smooth_reconstructs
    period hPeriod metric tensor displacement parameter boundary index]

def candidateANormalBoundaryMetricNormalVector_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : CutThroatBoundary period hPeriod) :
    TangentSpace coverModelWithCorners
      (normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter)) :=
  ∑ upper : Fin 4,
    candidateANormalBoundaryMetricNormalRegularFrameCoefficientFiberEvaluation
          period hPeriod metric upper
          (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
            (tensor, displacement), parameter) boundary •
      metric.frame upper
        (normalGraphOrientationDouble period hPeriod displacement
          (boundary, parameter))

set_option backward.isDefEq.respectTransparency false in
theorem candidateANormalBoundaryMetricNormalVector_smooth_eq_historical
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : CutThroatBoundary period hPeriod)
    (hCurrent :
      (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) ∈
        candidateANormalBoundaryInducedMetricDomain period hPeriod metric)
    (hNonNull : NormalGraphNonNullAt period hPeriod variedMetric displacement
      parameter) :
    candidateANormalBoundaryMetricNormalVector_smooth period hPeriod metric
        tensor displacement parameter boundary =
      normalGraphMetricNormal period hPeriod variedMetric displacement parameter
        hNonNull (orientationDoubleToThroat period hPeriod boundary)
        (normalGraphCanonicalLatitudeVector period hPeriod displacement
          parameter boundary) := by
  classical
  let current :=
    (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
      (tensor, displacement), parameter)
  let point := normalGraphOrientationDouble period hPeriod displacement
    (boundary, parameter)
  have hAlgebra :
      (∑ upper : Fin 4,
        candidateANormalBoundaryMetricNormalRegularFrameCoefficientFiberEvaluation
              period hPeriod metric upper current boundary •
          metric.frame upper point) =
        (∑ upper : Fin 4,
          candidateANormalBoundaryVerticalRegularFrameCoefficientFiberEvaluation
                period hPeriod metric upper current boundary •
            metric.frame upper point) -
          ∑ index : NormalBoundaryTangentIndex period hPeriod,
            candidateANormalBoundaryTangentialProjectionCoefficientFiberEvaluation
                  period hPeriod metric index current boundary •
              ∑ upper : Fin 4,
                candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation
                      period hPeriod metric index upper current boundary •
                  metric.frame upper point := by
    unfold candidateANormalBoundaryMetricNormalRegularFrameCoefficientFiberEvaluation
    simp only [BoundedContinuousFunction.sub_apply,
      BoundedContinuousFunction.sum_apply, BoundedContinuousFunction.mul_apply]
    simp only [sub_smul, Finset.sum_sub_distrib, Finset.sum_smul,
      Finset.smul_sum, smul_smul]
    congr 1
    rw [Finset.sum_comm]
  have hVertical := candidateANormalBoundaryVertical_smooth_reconstructs
    period hPeriod metric tensor displacement parameter boundary
  have hProjectionSum :=
    candidateANormalBoundaryTangentialProjectionAmbientVector_smooth_eq_sum
      period hPeriod metric tensor displacement parameter boundary
  have hProjectionHistorical :=
    candidateANormalBoundaryTangentialProjectionAmbientVector_smooth_eq_historical
      period hPeriod metric tensor variedMetric hVaried displacement parameter
        boundary hCurrent hNonNull
  unfold candidateANormalBoundaryMetricNormalVector_smooth
    normalGraphMetricNormal
  rw [hAlgebra, hVertical, ← hProjectionSum, hProjectionHistorical]

theorem candidateANormalBoundaryMetricNormalSquare_smooth_eq_vector
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : CutThroatBoundary period hPeriod) :
    candidateANormalBoundaryMetricNormalSquareFiberEvaluation
        period hPeriod metric
        (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) boundary =
      variedMetric.tensor.tensor
        (normalGraphOrientationDouble period hPeriod displacement
          (boundary, parameter))
        (candidateANormalBoundaryMetricNormalVector_smooth period hPeriod
          metric tensor displacement parameter boundary)
        (candidateANormalBoundaryMetricNormalVector_smooth period hPeriod
          metric tensor displacement parameter boundary) := by
  classical
  unfold candidateANormalBoundaryMetricNormalSquareFiberEvaluation
    candidateANormalBoundaryMetricNormalVector_smooth
  simp only [BoundedContinuousFunction.sum_apply,
    BoundedContinuousFunction.mul_apply]
  simp_rw [candidateANormalBoundaryActualMetricMatrixFiberEvaluation_eq_variedMetric
    period hPeriod metric tensor variedMetric hVaried displacement parameter
      boundary]
  rw [map_sum]
  simp only [map_smul, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro first _
  rw [map_sum]
  simp only [map_smul, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, Finset.mul_sum,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro second _
  rw [variedMetric.tensor.symmetric]
  ring

set_option backward.isDefEq.respectTransparency false in
theorem candidateANormalBoundaryMetricNormalSquare_smooth_eq_historical
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : CutThroatBoundary period hPeriod)
    (hCurrent :
      (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) ∈
        candidateANormalBoundaryInducedMetricDomain period hPeriod metric)
    (hNonNull : NormalGraphNonNullAt period hPeriod variedMetric displacement
      parameter) :
    candidateANormalBoundaryMetricNormalSquareFiberEvaluation
        period hPeriod metric
        (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) boundary =
      normalGraphMetricNormalSquare period hPeriod variedMetric displacement
        parameter hNonNull (orientationDoubleToThroat period hPeriod boundary)
        (normalGraphCanonicalNormalClass period hPeriod displacement parameter
          boundary) := by
  rw [candidateANormalBoundaryMetricNormalSquare_smooth_eq_vector
    period hPeriod metric tensor variedMetric hVaried displacement parameter
      boundary]
  rw [candidateANormalBoundaryMetricNormalVector_smooth_eq_historical
    period hPeriod metric tensor variedMetric hVaried displacement parameter
      boundary hCurrent hNonNull]
  unfold normalGraphMetricNormalSquare normalGraphCanonicalNormalClass
  rw [normalGraphMetricNormalFromClass_mk]
  rfl

def candidateANormalBoundaryMetricUnitNormalVector_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : CutThroatBoundary period hPeriod) :
    TangentSpace coverModelWithCorners
      (normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter)) :=
  ∑ upper : Fin 4,
    candidateANormalBoundaryMetricUnitNormalRegularFrameCoefficientFiberEvaluation
          period hPeriod metric upper
          (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
            (tensor, displacement), parameter) boundary •
      metric.frame upper
        (normalGraphOrientationDouble period hPeriod displacement
          (boundary, parameter))

theorem candidateANormalBoundaryMetricUnitNormalVector_smooth_eq_scaled
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : CutThroatBoundary period hPeriod) :
    let current :=
      (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
        (tensor, displacement), parameter)
    candidateANormalBoundaryMetricUnitNormalVector_smooth period hPeriod
        metric tensor displacement parameter boundary =
      candidateANormalBoundaryMetricNormalMagnitudeInverseFiberEvaluation
          period hPeriod metric current boundary •
        candidateANormalBoundaryMetricNormalVector_smooth period hPeriod
          metric tensor displacement parameter boundary := by
  dsimp only
  classical
  unfold candidateANormalBoundaryMetricUnitNormalVector_smooth
    candidateANormalBoundaryMetricNormalVector_smooth
    candidateANormalBoundaryMetricUnitNormalRegularFrameCoefficientFiberEvaluation
  simp only [BoundedContinuousFunction.mul_apply]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro upper _
  rw [smul_smul]

set_option backward.isDefEq.respectTransparency false in
theorem candidateANormalBoundaryMetricNormalMagnitudeInverseFiberEvaluation_eq_historical
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : CutThroatBoundary period hPeriod)
    (hCurrent :
      (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) ∈
        candidateANormalBoundaryMetricNormalRootDomain period hPeriod metric)
    (hNonNull : NormalGraphNonNullAt period hPeriod variedMetric displacement
      parameter)
    (hRootNonneg : 0 ≤
      candidateANormalBoundaryMetricNormalRelativeRootFiberEvaluation
        period hPeriod metric
          (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
            (tensor, displacement), parameter) boundary) :
    candidateANormalBoundaryMetricNormalMagnitudeInverseFiberEvaluation
          period hPeriod metric
          (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
            (tensor, displacement), parameter) boundary =
      (Real.sqrt
        |normalGraphMetricNormalSquare period hPeriod variedMetric displacement
          parameter hNonNull (orientationDoubleToThroat period hPeriod boundary)
          (normalGraphCanonicalNormalClass period hPeriod displacement parameter
            boundary)|)⁻¹ := by
  let current :=
    (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
      (tensor, displacement), parameter)
  let magnitude :=
    candidateANormalBoundaryMetricNormalMagnitudeFiberEvaluation
      period hPeriod metric current
  let root := Real.sqrt
    |normalGraphMetricNormalSquare period hPeriod variedMetric displacement
      parameter hNonNull (orientationDoubleToThroat period hPeriod boundary)
      (normalGraphCanonicalNormalClass period hPeriod displacement parameter
        boundary)|
  have hMagnitudeHistorical : magnitude boundary = root := by
    unfold magnitude root
    rw [candidateANormalBoundaryMetricNormalMagnitude_eq_sqrt_abs
      period hPeriod metric hTransverse hCurrent boundary hRootNonneg]
    rw [candidateANormalBoundaryMetricNormalSquare_smooth_eq_historical
      period hPeriod metric tensor variedMetric hVaried displacement parameter
        boundary hCurrent.1.2 hNonNull]
  have hMagnitudeUnit : IsUnit magnitude :=
    candidateANormalBoundaryMetricNormalMagnitudeFiberEvaluation_isUnit
      period hPeriod metric hTransverse hCurrent
  have hInverse := Ring.inverse_mul_cancel magnitude hMagnitudeUnit
  have hInverseAt := congrArg (fun field => field boundary) hInverse
  change Ring.inverse magnitude boundary * magnitude boundary = 1 at hInverseAt
  rw [hMagnitudeHistorical] at hInverseAt
  have hRootNe : root ≠ 0 := by
    intro hZero
    rw [hZero, mul_zero] at hInverseAt
    exact zero_ne_one hInverseAt
  change Ring.inverse magnitude boundary = root⁻¹
  calc
    Ring.inverse magnitude boundary =
        Ring.inverse magnitude boundary * (root * root⁻¹) := by
      rw [mul_inv_cancel₀ hRootNe, mul_one]
    _ = (Ring.inverse magnitude boundary * root) * root⁻¹ := by ring
    _ = root⁻¹ := by rw [hInverseAt, one_mul]

set_option backward.isDefEq.respectTransparency false in
theorem candidateANormalBoundaryMetricUnitNormalVector_smooth_eq_historical
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : CutThroatBoundary period hPeriod)
    (hCurrent :
      (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) ∈
        candidateANormalBoundaryMetricNormalRootDomain period hPeriod metric)
    (hNonNull : NormalGraphNonNullAt period hPeriod variedMetric displacement
      parameter)
    (hRootNonneg : 0 ≤
      candidateANormalBoundaryMetricNormalRelativeRootFiberEvaluation
        period hPeriod metric
          (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
            (tensor, displacement), parameter) boundary) :
    candidateANormalBoundaryMetricUnitNormalVector_smooth period hPeriod
        metric tensor displacement parameter boundary =
      normalGraphCanonicalMetricUnitNormal period hPeriod variedMetric
        displacement parameter hNonNull boundary := by
  rw [candidateANormalBoundaryMetricUnitNormalVector_smooth_eq_scaled]
  rw [
    candidateANormalBoundaryMetricNormalMagnitudeInverseFiberEvaluation_eq_historical
      period hPeriod metric hTransverse tensor variedMetric hVaried displacement
        parameter boundary hCurrent hNonNull hRootNonneg]
  rw [candidateANormalBoundaryMetricNormalVector_smooth_eq_historical
    period hPeriod metric tensor variedMetric hVaried displacement parameter
      boundary hCurrent.1.2 hNonNull]
  unfold normalGraphCanonicalMetricUnitNormal normalGraphMetricUnitNormal
    normalGraphCanonicalNormalClass
  rw [normalGraphMetricNormalFromClass_mk]

/-- Smooth-core synthesis of the completed covariant graph acceleration in
the installed regular frame. -/
def candidateANormalBoundaryGraphCovariantAccelerationVector_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (outer inner : NormalBoundaryTangentIndex period hPeriod)
    (boundary : CutThroatBoundary period hPeriod) :
    TangentSpace coverModelWithCorners
      (normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter)) :=
  ∑ upper : Fin 4,
    candidateANormalBoundaryGraphCovariantAccelerationRegularFrameCoefficientFiberEvaluation
          period hPeriod metric outer inner upper
          (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
            (tensor, displacement), parameter) boundary •
      metric.frame upper
        (normalGraphOrientationDouble period hPeriod displacement
          (boundary, parameter))

/-- The finite raw Gauss contraction is exactly the ambient metric pairing
of the reconstructed metric normal and covariant graph acceleration. -/
theorem candidateANormalBoundaryGaussRaw_smooth_eq_vector
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (outer inner : NormalBoundaryTangentIndex period hPeriod)
    (boundary : CutThroatBoundary period hPeriod) :
    candidateANormalBoundaryGaussRawExtrinsicCurvatureFiberEvaluation
        period hPeriod metric outer inner
        (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) boundary =
      -variedMetric.tensor.tensor
        (normalGraphOrientationDouble period hPeriod displacement
          (boundary, parameter))
        (candidateANormalBoundaryMetricNormalVector_smooth period hPeriod
          metric tensor displacement parameter boundary)
        (candidateANormalBoundaryGraphCovariantAccelerationVector_smooth
          period hPeriod metric tensor displacement parameter outer inner
            boundary) := by
  classical
  unfold candidateANormalBoundaryGaussRawExtrinsicCurvatureFiberEvaluation
    candidateANormalBoundaryMetricNormalVector_smooth
    candidateANormalBoundaryGraphCovariantAccelerationVector_smooth
  simp only [BoundedContinuousFunction.neg_apply,
    BoundedContinuousFunction.sum_apply, BoundedContinuousFunction.mul_apply]
  simp_rw [candidateANormalBoundaryActualMetricMatrixFiberEvaluation_eq_variedMetric
    period hPeriod metric tensor variedMetric hVaried displacement parameter
      boundary]
  rw [map_sum]
  simp only [map_smul, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  congr 1
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro first _
  rw [map_sum]
  simp only [map_smul, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, Finset.mul_sum,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro second _
  rw [variedMetric.tensor.symmetric]
  ring

/-- After the already constructed magnitude rescaling, the raw Gauss scalar
uses exactly the reconstructed unit normal. -/
theorem candidateANormalBoundaryMetricUnitGaussRaw_smooth_eq_vector
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (outer inner : NormalBoundaryTangentIndex period hPeriod)
    (boundary : CutThroatBoundary period hPeriod) :
    candidateANormalBoundaryMetricUnitGaussRawExtrinsicCurvatureFiberEvaluation
        period hPeriod metric outer inner
        (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) boundary =
      -variedMetric.tensor.tensor
        (normalGraphOrientationDouble period hPeriod displacement
          (boundary, parameter))
        (candidateANormalBoundaryMetricUnitNormalVector_smooth period
          hPeriod metric tensor displacement parameter boundary)
        (candidateANormalBoundaryGraphCovariantAccelerationVector_smooth
          period hPeriod metric tensor displacement parameter outer inner
            boundary) := by
  unfold
    candidateANormalBoundaryMetricUnitGaussRawExtrinsicCurvatureFiberEvaluation
  simp only [BoundedContinuousFunction.mul_apply]
  rw [candidateANormalBoundaryGaussRaw_smooth_eq_vector
    period hPeriod metric tensor variedMetric hVaried displacement parameter
      outer inner boundary]
  rw [candidateANormalBoundaryMetricUnitNormalVector_smooth_eq_scaled]
  simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem candidateANormalBoundaryMetricUnitGauss_smooth_eq_vector
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor = metric.metric.tensor + tensor)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (outer inner : NormalBoundaryTangentIndex period hPeriod)
    (boundary : CutThroatBoundary period hPeriod) :
    candidateANormalBoundaryMetricUnitGaussExtrinsicCurvatureFiberEvaluation
        period hPeriod metric outer inner
        (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) boundary =
      (1 / 2 : Real) *
        (-variedMetric.tensor.tensor
            (normalGraphOrientationDouble period hPeriod displacement
              (boundary, parameter))
            (candidateANormalBoundaryMetricUnitNormalVector_smooth period
              hPeriod metric tensor displacement parameter boundary)
            (candidateANormalBoundaryGraphCovariantAccelerationVector_smooth
              period hPeriod metric tensor displacement parameter outer inner
                boundary) +
          -variedMetric.tensor.tensor
            (normalGraphOrientationDouble period hPeriod displacement
              (boundary, parameter))
            (candidateANormalBoundaryMetricUnitNormalVector_smooth period
              hPeriod metric tensor displacement parameter boundary)
            (candidateANormalBoundaryGraphCovariantAccelerationVector_smooth
              period hPeriod metric tensor displacement parameter inner outer
                boundary)) := by
  unfold candidateANormalBoundaryMetricUnitGaussExtrinsicCurvatureFiberEvaluation
  simp only [BoundedContinuousFunction.smul_apply, smul_eq_mul,
    BoundedContinuousFunction.add_apply]
  rw [candidateANormalBoundaryMetricUnitGaussRaw_smooth_eq_vector
      period hPeriod metric tensor variedMetric hVaried displacement parameter
        outer inner boundary,
    candidateANormalBoundaryMetricUnitGaussRaw_smooth_eq_vector
      period hPeriod metric tensor variedMetric hVaried displacement parameter
        inner outer boundary]

/-- Completed first-sheet GHY integrand relative to the installed canonical
latitude measure. -/
def candidateANormalBoundaryGHYIntegrandFiberEvaluation
    (einsteinScale : Real)
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) :
    CandidateANormalBoundaryScalarField period hPeriod :=
  einsteinScale •
    (candidateANormalBoundaryInducedVolumeDensityFiberEvaluation
          period hPeriod metric current *
      candidateANormalBoundaryMetricUnitGaussMeanCurvatureFiberEvaluation
        period hPeriod metric current)

theorem candidateANormalBoundaryGHYIntegrandFiberEvaluation_contDiffOn_two
    (einsteinScale : Real)
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric) :
    ContDiffOn Real 2
      (candidateANormalBoundaryGHYIntegrandFiberEvaluation
        period hPeriod einsteinScale metric)
      (candidateANormalBoundaryGHYDomain period hPeriod metric) := by
  unfold candidateANormalBoundaryGHYIntegrandFiberEvaluation
  exact ContDiffOn.const_smul einsteinScale
    ((candidateANormalBoundaryInducedVolumeDensityFiberEvaluation_contDiffOn_two
        period hPeriod metric).mul
      ((candidateANormalBoundaryMetricUnitGaussMeanCurvatureFiberEvaluation_contDiffOn_two
        period hPeriod metric hTransverse).mono (fun _ hCurrent => hCurrent.1)))

/-! ### Continuous first-sheet integration and the completed GHY action -/

open MeasureTheory

local instance candidateANormalBoundaryMeasurableSpace :
    MeasurableSpace (OrientationBoundary period hPeriod) :=
  borel _

local instance candidateANormalBoundaryBorelSpace :
    BorelSpace (OrientationBoundary period hPeriod) where
  measurable_eq := rfl

local instance candidateANormalBoundaryCanonicalLatitudeBaseMeasureFinite :
    IsFiniteMeasure (canonicalLatitudeBaseMeasure period) :=
  canonicalLatitudeBaseMeasure_isFinite period

/-- Canonical first-sheet measure, using the already installed latitude
fundamental-domain parametrization. -/
def candidateANormalBoundaryFirstSheetMeasure :
    Measure (OrientationBoundary period hPeriod) :=
  Measure.map (canonicalLatitudeCutBoundaryFirstLift period hPeriod)
    (canonicalLatitudeBaseMeasure period)

local instance candidateANormalBoundaryFirstSheetMeasureFinite :
    IsFiniteMeasure
      (candidateANormalBoundaryFirstSheetMeasure period hPeriod) :=
  Measure.isFiniteMeasure_map _ _

/-- Continuous integration of completed boundary scalar fields on the first
sheet. -/
def candidateANormalBoundaryFirstSheetIntegralCLM :
    CandidateANormalBoundaryScalarField period hPeriod →L[Real] Real :=
  (L1.integralCLM
      (α := OrientationBoundary period hPeriod)
      (E := Real)
      (μ := candidateANormalBoundaryFirstSheetMeasure period hPeriod)).comp
    (BoundedContinuousFunction.toLp (1 : ENNReal)
      (candidateANormalBoundaryFirstSheetMeasure period hPeriod) Real)

theorem candidateANormalBoundaryFirstSheetIntegralCLM_apply
    (field : CandidateANormalBoundaryScalarField period hPeriod) :
    candidateANormalBoundaryFirstSheetIntegralCLM period hPeriod field =
      ∫ boundary, field boundary
        ∂candidateANormalBoundaryFirstSheetMeasure period hPeriod := by
  unfold candidateANormalBoundaryFirstSheetIntegralCLM
  rw [ContinuousLinearMap.comp_apply, ← L1.integral_eq,
    L1.integral_eq_integral]
  exact integral_congr_ae
    (BoundedContinuousFunction.coeFn_toLp (1 : ENNReal)
      (candidateANormalBoundaryFirstSheetMeasure period hPeriod) Real field)

/-- Completed first-sheet GHY action. -/
def candidateANormalBoundaryFirstSheetGHYActionFiberEvaluation
    (einsteinScale : Real)
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) :
    Real :=
  candidateANormalBoundaryFirstSheetIntegralCLM period hPeriod
    (candidateANormalBoundaryGHYIntegrandFiberEvaluation
      period hPeriod einsteinScale metric current)

theorem
    candidateANormalBoundaryFirstSheetGHYActionFiberEvaluation_eq_integral
    (einsteinScale : Real)
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) :
    candidateANormalBoundaryFirstSheetGHYActionFiberEvaluation
        period hPeriod einsteinScale metric current =
      ∫ base,
        candidateANormalBoundaryGHYIntegrandFiberEvaluation
            period hPeriod einsteinScale metric current
          (canonicalLatitudeCutBoundaryFirstLift period hPeriod base)
        ∂canonicalLatitudeBaseMeasure period := by
  rw [candidateANormalBoundaryFirstSheetGHYActionFiberEvaluation,
    candidateANormalBoundaryFirstSheetIntegralCLM_apply]
  unfold candidateANormalBoundaryFirstSheetMeasure
  rw [integral_map
    (continuous_canonicalLatitudeCutBoundaryFirstLift period hPeriod
      |>.measurable.aemeasurable)
    (candidateANormalBoundaryGHYIntegrandFiberEvaluation
      period hPeriod einsteinScale metric current).continuous.aestronglyMeasurable]

theorem
    candidateANormalBoundaryFirstSheetGHYActionFiberEvaluation_contDiffOn_two
    (einsteinScale : Real)
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric) :
    ContDiffOn Real 2
      (candidateANormalBoundaryFirstSheetGHYActionFiberEvaluation
        period hPeriod einsteinScale metric)
      (candidateANormalBoundaryGHYDomain period hPeriod metric) :=
  (candidateANormalBoundaryFirstSheetIntegralCLM
      period hPeriod).contDiff.contDiffOn.comp
    (candidateANormalBoundaryGHYIntegrandFiberEvaluation_contDiffOn_two
      period hPeriod einsteinScale metric hTransverse)
    (fun _ _ => Set.mem_univ _)

/-- Completed two-sheet GHY action with the already proved multiplicity two. -/
def candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation
    (einsteinScale : Real)
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) :
    Real :=
  2 * candidateANormalBoundaryFirstSheetGHYActionFiberEvaluation
    period hPeriod einsteinScale metric current

@[simp] theorem candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation_apply
    (einsteinScale : Real)
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) :
    candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation
        period hPeriod einsteinScale metric current =
      2 * candidateANormalBoundaryFirstSheetGHYActionFiberEvaluation
        period hPeriod einsteinScale metric current := by
  rfl

theorem candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation_contDiffOn_two
    (einsteinScale : Real)
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric) :
    ContDiffOn Real 2
      (candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation
        period hPeriod einsteinScale metric)
      (candidateANormalBoundaryGHYDomain period hPeriod metric) := by
  unfold candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation
  exact contDiffOn_const.mul
    (candidateANormalBoundaryFirstSheetGHYActionFiberEvaluation_contDiffOn_two
      period hPeriod einsteinScale metric hTransverse)

theorem candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation_contDiffAt_two
    (einsteinScale : Real)
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric) :
    ContDiffAt Real 2
      (candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation
        period hPeriod einsteinScale metric) 0 :=
  (candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation_contDiffOn_two
      period hPeriod einsteinScale metric hTransverse).contDiffAt
    ((candidateANormalBoundaryGHYDomain_isOpen period hPeriod metric).mem_nhds
      (zero_mem_candidateANormalBoundaryGHYDomain
        period hPeriod metric hTransverse))

/-- Genuine second Fréchet derivative of the completed two-sheet GHY action. -/
def candidateANormalBoundaryTwoSheetGHYActionHessian
    (einsteinScale : Real)
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    Prod (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real →L[Real]
      (Prod (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real →L[Real]
        Real) :=
  fderiv Real
    (fderiv Real
      (candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation
        period hPeriod einsteinScale metric)) 0

theorem candidateANormalBoundaryTwoSheetGHYActionHessian_symmetric
    (einsteinScale : Real)
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric)
    (first second : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) :
    candidateANormalBoundaryTwoSheetGHYActionHessian
          period hPeriod einsteinScale metric first second =
      candidateANormalBoundaryTwoSheetGHYActionHessian
          period hPeriod einsteinScale metric second first := by
  have hSmooth : minSmoothness Real 2 ≤ (2 : ℕ∞ω) := by
    simp [minSmoothness_of_isRCLikeNormedField]
  have hSymmetric :=
    (candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation_contDiffAt_two
      period hPeriod einsteinScale metric hTransverse).isSymmSndFDerivAt
        hSmooth
  exact hSymmetric first second

/-- Public completed-action certificate for the local GHY chart. -/
theorem candidate_a_normal_boundary_ghy_second_frechet_gate
    (einsteinScale : Real)
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric) :
    IsOpen (candidateANormalBoundaryGHYDomain period hPeriod metric) ∧
      (0 : Prod
        (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real) ∈
        candidateANormalBoundaryGHYDomain period hPeriod metric ∧
      ContDiffAt Real 2
        (candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation
          period hPeriod einsteinScale metric) 0 ∧
      ∀ first second,
        candidateANormalBoundaryTwoSheetGHYActionHessian
              period hPeriod einsteinScale metric first second =
          candidateANormalBoundaryTwoSheetGHYActionHessian
              period hPeriod einsteinScale metric second first :=
  ⟨candidateANormalBoundaryGHYDomain_isOpen period hPeriod metric,
    zero_mem_candidateANormalBoundaryGHYDomain
      period hPeriod metric hTransverse,
    candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation_contDiffAt_two
      period hPeriod einsteinScale metric hTransverse,
    candidateANormalBoundaryTwoSheetGHYActionHessian_symmetric
      period hPeriod einsteinScale metric hTransverse⟩

/-! ### Production normal-germ bridge: regular-frame coefficient -/

def candidateANormalBoundarySmoothMetricUnitNormalRegularFrameCoefficient
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod variedMetric displacement
      parameter)
    (row : Fin 4) (boundary : CutThroatBoundary period hPeriod) : Real :=
  normalBoundaryRegularFrameCoefficient period hPeriod metric
    (fun current : CutThroatBoundary period hPeriod × Real =>
      normalGraphCanonicalMetricUnitNormalLift period hPeriod variedMetric
        displacement parameter hNonNull current.1)
    row (boundary, 0)

theorem candidateANormalBoundarySmoothMetricUnitNormalRegularFrameCoefficient_contMDiff
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod variedMetric displacement
      parameter)
    (row : Fin 4) :
    ContMDiff throatCoverModelWithCorners (modelWithCornersSelf Real Real) ∞
      (candidateANormalBoundarySmoothMetricUnitNormalRegularFrameCoefficient
        period hPeriod metric variedMetric displacement parameter hNonNull row) := by
  have hLift : ContMDiff
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      coverModelWithCorners.tangent ∞
      (fun current : CutThroatBoundary period hPeriod × Real =>
        normalGraphCanonicalMetricUnitNormalLift period hPeriod variedMetric
          displacement parameter hNonNull current.1) :=
    (normalGraphCanonicalMetricUnitNormalLift_contMDiff period hPeriod
      variedMetric displacement parameter hNonNull).comp contMDiff_fst
  have hCoefficient := normalBoundaryRegularFrameCoefficient_contMDiff
    period hPeriod metric _ hLift row
  exact hCoefficient.comp (contMDiff_id.prodMk contMDiff_const)

theorem candidateANormalBoundarySmoothMetricUnitNormalRegularFrameCoefficient_reconstructs
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod variedMetric displacement
      parameter)
    (boundary : CutThroatBoundary period hPeriod) :
    (∑ row : Fin 4,
      candidateANormalBoundarySmoothMetricUnitNormalRegularFrameCoefficient
          period hPeriod metric variedMetric displacement parameter hNonNull
            row boundary •
        metric.frame row
          (normalGraphOrientationDouble period hPeriod displacement
            (boundary, parameter))) =
      normalGraphCanonicalMetricUnitNormal period hPeriod variedMetric
        displacement parameter hNonNull boundary := by
  symm
  exact generalMetricFiniteFrameCoefficientAt_reconstructs period hPeriod
    (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
    metric.metric
    (normalGraphOrientationDouble period hPeriod displacement
      (boundary, parameter))
    (normalGraphCanonicalMetricUnitNormal period hPeriod variedMetric
      displacement parameter hNonNull boundary)

set_option backward.isDefEq.respectTransparency false in
/-- Directional derivatives of boundary coefficients commute with the already
installed local orientation section. -/
theorem candidateANormalBoundarySmoothCoefficient_localSection_mfderiv
    (coefficient : CutThroatBoundary period hPeriod → Real)
    (hCoefficient : ContMDiff throatCoverModelWithCorners
      (modelWithCornersSelf Real Real) ∞ coefficient)
    (boundary : CutThroatBoundary period hPeriod)
    (vector : TangentSpace throatCoverModelWithCorners boundary) :
    mfderiv throatCoverModelWithCorners (modelWithCornersSelf Real Real)
        coefficient boundary vector =
      mfderiv throatCoverModelWithCorners (modelWithCornersSelf Real Real)
        (coefficient ∘ normalGraphOrientationLocalSection period hPeriod boundary)
        (orientationDoubleToThroat period hPeriod boundary)
        (normalBoundaryOrientationTangentEquiv period hPeriod boundary vector) := by
  have hSection : MDifferentiableAt throatCoverModelWithCorners
      throatCoverModelWithCorners
      (normalGraphOrientationLocalSection period hPeriod boundary)
      (orientationDoubleToThroat period hPeriod boundary) :=
    (normalGraphOrientationLocalSection_contMDiffAt period hPeriod boundary)
      |>.mdifferentiableAt (by simp)
  have hBase :
      normalGraphOrientationLocalSection period hPeriod boundary
        (orientationDoubleToThroat period hPeriod boundary) = boundary :=
    normalGraphOrientationLocalSection_base period hPeriod boundary
  have hCoefficientAt : MDifferentiableAt throatCoverModelWithCorners
      (modelWithCornersSelf Real Real) coefficient
        (normalGraphOrientationLocalSection period hPeriod boundary
          (orientationDoubleToThroat period hPeriod boundary)) := by
    rw [hBase]
    exact hCoefficient.mdifferentiableAt (by simp)
  have hChain := mfderiv_comp_apply
    (orientationDoubleToThroat period hPeriod boundary)
    hCoefficientAt hSection
    (normalBoundaryOrientationTangentEquiv period hPeriod boundary vector)
  rw [normalGraphOrientationLocalSection_mfderiv_tangentEquiv] at hChain
  rw [hBase] at hChain
  exact hChain.symm

local instance (priority := 30000) hessianHistoricalOrientationBoundaryChartedSpace :
    ChartedSpace ThroatCoverModel (CutThroatBoundary period hPeriod) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryChartedSpace
    period hPeriod

local instance (priority := 30000) hessianHistoricalOrientationBoundaryIsManifold :
    IsManifold throatCoverModelWithCorners ω (CutThroatBoundary period hPeriod) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryIsManifold
    period hPeriod

local instance (priority := 30000) hessianHistoricalEffectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel
      (MappingTorus (fixedEquatorData period hPeriod)) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.effectiveThroatChartedSpace
    period hPeriod

local instance (priority := 30000) hessianHistoricalEffectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (MappingTorus (fixedEquatorData period hPeriod)) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.effectiveThroatIsManifold
    period hPeriod

def candidateANormalBoundaryGraphTangentCoordinates_historical
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (index : NormalBoundaryTangentIndex period hPeriod)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real)
    (boundary : CutThroatBoundary period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4) :
    TangentSpace
      (modelWithCornersSelf Real
        P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D.Vector4)
      coordinate :=
  ∑ row : Fin 4,
      candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation
        period hPeriod metric index row current boundary •
      pulledRegularFrameVector period hPeriod metric patch row coordinate

@[simp] theorem candidateANormalBoundaryGraphTangentCoordinates_historical_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (index : NormalBoundaryTangentIndex period hPeriod)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real)
    (boundary : CutThroatBoundary period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4) :
    candidateANormalBoundaryGraphTangentCoordinates_historical period hPeriod
      metric index current boundary patch coordinate =
      ∑ row : Fin 4,
        candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation
          period hPeriod metric index row current boundary •
        pulledRegularFrameVector period hPeriod metric patch row coordinate := by
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem candidateANormalBoundaryGraphTangentCoordinates_historical_eq_source
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (boundary : CutThroatBoundary period hPeriod)
    (index : NormalBoundaryTangentIndex period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4)
    (hAt : patch.coordinateMap coordinate =
      normalGraphOrientationDouble period hPeriod displacement
        (boundary, parameter)) :
    let sourceVector : TangentSpace throatCoverModelWithCorners boundary :=
      (finiteSmoothThroatGeneratingFrame
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)).vectorAt
          boundary index
    let targetVector : TangentSpace throatCoverModelWithCorners
        (orientationDoubleToThroat period hPeriod boundary) :=
      normalBoundaryOrientationTangentEquiv period hPeriod boundary sourceVector
    let base : MappingTorus (fixedEquatorData period hPeriod) × Real :=
      (orientationDoubleToThroat period hPeriod boundary, parameter)
    candidateANormalBoundaryGraphTangentCoordinates_historical period hPeriod
        metric index
          (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
            (tensor, displacement), parameter)
          boundary patch coordinate =
      normalGraphHolonomicSourceFirstDerivativeCoordinatesAt period hPeriod
        displacement base patch coordinate targetVector := by
  dsimp only
  classical
  let sourceVector : TangentSpace throatCoverModelWithCorners boundary :=
    (finiteSmoothThroatGeneratingFrame
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)).vectorAt
        boundary index
  let targetVector : TangentSpace throatCoverModelWithCorners
      (orientationDoubleToThroat period hPeriod boundary) :=
    normalBoundaryOrientationTangentEquiv period hPeriod boundary sourceVector
  let base : MappingTorus (fixedEquatorData period hPeriod) × Real :=
    (orientationDoubleToThroat period hPeriod boundary, parameter)
  let derivativeEquiv :=
    (patch.coordinateMap_isLocalDiffeomorph coordinate)
      |>.mfderivToContinuousLinearEquiv (by simp)
  apply derivativeEquiv.injective
  change derivativeEquiv.toContinuousLinearMap _ =
    derivativeEquiv.toContinuousLinearMap _
  rw [show derivativeEquiv.toContinuousLinearMap =
      mfderiv (modelWithCornersSelf Real
          P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D.Vector4)
        coverModelWithCorners patch.coordinateMap coordinate by
    exact (patch.coordinateMap_isLocalDiffeomorph coordinate)
      |>.mfderivToContinuousLinearEquiv_coe (by simp)]
  unfold candidateANormalBoundaryGraphTangentCoordinates_historical
  rw [map_sum]
  simp_rw [map_smul, coordinateMap_mfderiv_pulledRegularFrameVector]
  have hCandidate :=
    candidateANormalBoundaryGraphTangent_smooth_reconstructs period hPeriod
      metric tensor displacement parameter boundary index
  have hComp := normalGraphOrientationDouble_mfderiv_eq_comp period hPeriod
    displacement parameter boundary sourceVector
  have hTarget : targetVector =
      mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
        (orientationDoubleToThroat period hPeriod) boundary sourceVector := by
    simpa only [targetVector] using
      (normalBoundaryOrientationTangentEquiv_apply period hPeriod boundary
        sourceVector)
  have hChart : base.1 ∈
      (chartAt ThroatCoverModel base.1).source :=
    mem_chart_source ThroatCoverModel base.1
  have hTrivialized :
      (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) base.1).symm base.1 targetVector =
        targetVector := by
    change
      (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) base.1).symmL Real base.1
            targetVector = targetVector
    rw [TangentBundle.symmL_trivializationAt hChart,
      mfderivWithin_range_extChartAt_symm]
    rfl
  have hGraph : patch.coordinateMap coordinate =
      normalGraph period hPeriod displacement base.2 base.1 := by
    simpa only [base, normalGraphOrientationDouble] using hAt
  rw [normalGraphHolonomicSourceFirstDerivativeCoordinatesAt_eq_family period
    hPeriod displacement base patch coordinate hGraph]
  rw [normalGraphHolonomicFamilyDerivativeCoordinates_reconstructs period
    hPeriod displacement base patch coordinate hGraph]
  rw [hTrivialized]
  dsimp only [base]
  rw [hAt, hTarget, ← hComp]
  simpa only [sourceVector] using hCandidate

/-- Transport of a smooth variation from the regular-frame interface to the
canonical Gauss/GHY interface.  The metric projection is the metric already
stored inside `RegularGeneralLorentzMetric`; no new choice is introduced. -/
def candidateANormalBoundaryCanonicalTransport
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variation : SmoothSymmetricCovariantTwoTensor period hPeriod ×
      SmoothNormalDisplacement period hPeriod)
    (parameter : Real) :
    SmoothGeneralLorentzMetric period hPeriod ×
      SmoothNormalDisplacement period hPeriod × Real :=
  (metric.metric, variation.2, parameter)

@[simp] theorem candidateANormalBoundaryCanonicalTransport_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (variation : SmoothSymmetricCovariantTwoTensor period hPeriod ×
      SmoothNormalDisplacement period hPeriod)
    (parameter : Real) :
    candidateANormalBoundaryCanonicalTransport period hPeriod metric variation
      parameter = (metric.metric, variation.2, parameter) := by
  rfl

theorem candidateANormalBoundaryCanonicalTransport_zero_nonNull
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (hTransverse : HasNoTangentialRadical period hPeriod metric.metric) :
    NormalGraphNonNullAt period hPeriod metric.metric displacement 0 := by
  exact zero_mem_normalGraphNonNullDomain period hPeriod metric.metric
    displacement hTransverse

end
end P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
end JanusFormal
