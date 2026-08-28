import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaussNormalLineDescent4D
import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusSmoothNormalVectorBundle
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusProjectedSeedGeometricNormalQuadraticBundleCore

/-!
# Smooth D8 bundle for the actual throat Gauss quadratic

The oriented Gauss quadratic is odd under the orientation deck involution.
Consequently its local oriented representatives glue through the sign
transition of the genuine D8 normal line.  Smoothness is stated under the
exact chartwise regularity hypothesis that is still needed from the analytic
Gauss construction; no smoothness of a set-theoretic lift is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatGaussNormalQuadraticSmoothBundle4D

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

open Set Filter Bundle Module
open scoped Manifold ContDiff Bundle RealInnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusOrientationDoubleCover
open P0EFTJanusMappingTorusCutThroatBoundaryDoubleCover4D
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothNormalVectorBundle
open P0EFTJanusNormalBundleOrientationCover
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusRieszShapeOperatorSmoothDependence
open P0EFTJanusPhysicalSecondJetSmoothSectionAssembly
open P0EFTJanusProjectedSeedGeometricNormalQuadraticBundleCore
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalMetricChartwiseSecondOrderJetExtraction4D
open P0EFTJanusProgramPActualThroatOrientedGaussNormalBackgroundBridge4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ThroatData := fixedEquatorData period hPeriod
private abbrev ThroatCover := MappingTorusCover (ThroatData period hPeriod)
private abbrev EffectiveThroat := MappingTorus (ThroatData period hPeriod)
private abbrev OrientationData := orientationDoubleData period hPeriod

abbrev ActualThroatGaussNormalQuadratic :=
  ContinuousSecondFundamentalForm (Tangent := EuclideanR3) (Normal := Real)

private abbrev throatProjectionLocalHomeomorph :
    IsLocalHomeomorph (mappingTorusMk (ThroatData period hPeriod)) :=
  (mappingTorusMk_isCoveringMap (ThroatData period hPeriod)).isLocalHomeomorph

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance actualGaussQuadraticNormedAddCommGroup :
    NormedAddCommGroup ActualThroatGaussNormalQuadratic := inferInstance

local instance actualGaussQuadraticNormedSpace :
    NormedSpace Real ActualThroatGaussNormalQuadratic := inferInstance

local instance actualGaussQuadraticTopologicalSpace :
    TopologicalSpace ActualThroatGaussNormalQuadratic :=
  actualGaussQuadraticNormedAddCommGroup.toPseudoMetricSpace
    |>.toUniformSpace.toTopologicalSpace

local instance actualGaussQuadraticAddCommMonoid :
    AddCommMonoid ActualThroatGaussNormalQuadratic :=
  actualGaussQuadraticNormedAddCommGroup.toAddCommMonoid

local instance actualGaussQuadraticModule :
    Module Real ActualThroatGaussNormalQuadratic :=
  actualGaussQuadraticNormedSpace.toModule

/-- The sign-clutched normal line, functorially applied to normal-valued
quadratic forms. -/
def actualThroatGaussNormalQuadraticCore :
    VectorBundleCore Real (EffectiveThroat period hPeriod)
      ActualThroatGaussNormalQuadratic (ThroatCover period hPeriod) := by
  let normalCore := fixedThroatNormalVectorBundleCore period hPeriod
  exact
    { baseSet := normalCore.baseSet
      isOpen_baseSet := normalCore.isOpen_baseSet
      indexAt := normalCore.indexAt
      mem_baseSet_at := normalCore.mem_baseSet_at
      coordChange := fun first second base =>
        continuousSecondFundamentalFormTransportCLM
          (normalCore.coordChange first second base)
      coordChange_self := by
        intro chart base hBase form
        apply ContinuousLinearMap.ext
        intro first
        apply ContinuousLinearMap.ext
        intro second
        exact normalCore.coordChange_self chart base hBase (form first second)
      continuousOn_coordChange := by
        intro first second
        exact continuousSecondFundamentalFormTransportOperator.continuous.comp_continuousOn
          (normalCore.continuousOn_coordChange first second)
      coordChange_comp := by
        intro first second third base hBase form
        apply ContinuousLinearMap.ext
        intro x
        apply ContinuousLinearMap.ext
        intro y
        exact normalCore.coordChange_comp first second third base hBase (form x y) }

/-- The induced D8 quadratic core is analytic because its sign transitions
are the smooth transitions of the actual normal line. -/
theorem actualThroatGaussNormalQuadraticCore_isContMDiff :
    (actualThroatGaussNormalQuadraticCore period hPeriod).IsContMDiff
      throatCoverModelWithCorners ω := by
  let normalCore := fixedThroatNormalVectorBundleCore period hPeriod
  letI normalCoreSmooth : normalCore.IsContMDiff
      throatCoverModelWithCorners ω :=
    fixedThroatNormalVectorBundleCore_isContMDiff period hPeriod
  constructor
  intro first second base hBase
  exact (continuousSecondFundamentalFormTransportOperator
      (Tangent := EuclideanR3) (Normal := Real)).contDiff
    |>.comp_contMDiffWithinAt
      ((normalCore.contMDiffOn_coordChange throatCoverModelWithCorners
        first second) base hBase)

/-- Orientation-double-cover point represented by a universal throat-cover
point. -/
def actualThroatOrientationBoundaryOfCover
    (anchor : ThroatCover period hPeriod) :
    CutThroatBoundary period hPeriod :=
  mappingTorusMk (OrientationData period hPeriod)
    ((orientationDoubleCoverHomeomorph period hPeriod).symm anchor)

@[simp]
theorem actualThroatOrientationBoundaryOfCover_projection
    (anchor : ThroatCover period hPeriod) :
    orientationDoubleToThroat period hPeriod
        (actualThroatOrientationBoundaryOfCover period hPeriod anchor) =
      mappingTorusMk (ThroatData period hPeriod) anchor := by
  simp [actualThroatOrientationBoundaryOfCover]

private theorem orientationDoubleCoverHomeomorph_deck
    (point : MappingTorusCover (OrientationData period hPeriod)) :
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

private theorem actualThroatOrientationBoundaryOfCover_even
    (winding : Int) (hEven : Even winding)
    (anchor : ThroatCover period hPeriod) :
    actualThroatOrientationBoundaryOfCover period hPeriod
        (winding +ᵥ anchor) =
      actualThroatOrientationBoundaryOfCover period hPeriod anchor := by
  rcases hEven with ⟨half, rfl⟩
  rw [actualThroatOrientationBoundaryOfCover,
    actualThroatOrientationBoundaryOfCover,
    mappingTorusMk_eq_iff_exists_vadd]
  refine ⟨half, ?_⟩
  apply (orientationDoubleCoverHomeomorph period hPeriod).injective
  rw [orientationDoubleCover_even_equivariant]
  simp [two_mul]

private theorem actualThroatOrientationBoundaryOfCover_odd
    (winding : Int) (hOdd : ¬ Even winding)
    (anchor : ThroatCover period hPeriod) :
    actualThroatOrientationBoundaryOfCover period hPeriod
        (winding +ᵥ anchor) =
      orientationDeck period hPeriod
        (actualThroatOrientationBoundaryOfCover period hPeriod anchor) := by
  rcases Int.even_or_odd' winding with ⟨half, hEven | hOddEq⟩
  · exact (hOdd ⟨half, by simpa [two_mul] using hEven⟩).elim
  · rw [actualThroatOrientationBoundaryOfCover,
      actualThroatOrientationBoundaryOfCover, orientationDeck_mk,
      mappingTorusMk_eq_iff_exists_vadd]
    refine ⟨half, ?_⟩
    apply (orientationDoubleCoverHomeomorph period hPeriod).injective
    rw [orientationDoubleCover_even_equivariant,
      orientationDoubleCoverHomeomorph_deck]
    rw [hOddEq]
    simp [add_vadd]

/-- The actual oriented Gauss quadratic regarded as a function on the
universal cover. -/
def actualThroatGaussNormalQuadraticOnCover
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (sector : Sector) (anchor : ThroatCover period hPeriod) :
    ActualThroatGaussNormalQuadratic :=
  actualThroatSectorGaussNormalQuadraticAt period hPeriod configuration
    (actualThroatOrientationBoundaryOfCover period hPeriod anchor) sector

/-- Every cover winding acts on the actual Gauss quadratic through the exact
D8 sign representation. -/
theorem actualThroatGaussNormalQuadraticOnCover_vadd
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (hTransverse : ∀ sector,
      HasNoTangentialRadical period hPeriod
        (globalGaugeFixedBulkMetricBySector period hPeriod configuration sector))
    (sector : Sector) (winding : Int)
    (anchor : ThroatCover period hPeriod) :
    actualThroatGaussNormalQuadraticOnCover period hPeriod configuration sector
        (winding +ᵥ anchor) =
      continuousSecondFundamentalFormTransportCLM
        (normalSignCLM winding)
        (actualThroatGaussNormalQuadraticOnCover period hPeriod configuration
          sector anchor) := by
  classical
  by_cases hEven : Even winding
  · rw [actualThroatGaussNormalQuadraticOnCover,
      actualThroatOrientationBoundaryOfCover_even period hPeriod winding hEven]
    apply ContinuousLinearMap.ext
    intro first
    apply ContinuousLinearMap.ext
    intro second
    simp [normalSignCLM_apply, normal_sign_even winding hEven,
      actualThroatGaussNormalQuadraticOnCover]
  · rw [actualThroatGaussNormalQuadraticOnCover,
      actualThroatOrientationBoundaryOfCover_odd period hPeriod winding hEven,
      actualThroatSectorGaussNormalQuadraticAt_deck period hPeriod
        configuration hTransverse]
    apply ContinuousLinearMap.ext
    intro first
    apply ContinuousLinearMap.ext
    intro second
    simp [normalSignCLM_apply, normal_sign_odd winding hEven,
      actualThroatGaussNormalQuadraticOnCover]

/-- Covering lift selected by one D8 bundle chart. -/
def actualThroatGaussNormalLocalLift
    (anchor : ThroatCover period hPeriod)
    (base : EffectiveThroat period hPeriod) : ThroatCover period hPeriod :=
  (throatProjectionLocalHomeomorph period hPeriod).localInverseAt anchor base

theorem actualThroatGaussNormalLocalLift_projects
    (anchor : ThroatCover period hPeriod)
    (base : EffectiveThroat period hPeriod)
    (hBase : base ∈ normalBundleBaseSet period hPeriod anchor) :
    mappingTorusMk (ThroatData period hPeriod)
        (actualThroatGaussNormalLocalLift period hPeriod anchor base) = base :=
  (throatProjectionLocalHomeomorph period hPeriod).apply_localInverseAt_of_mem hBase

/-- Actual oriented Gauss coordinate in one D8 bundle chart. -/
def actualThroatGaussNormalQuadraticLocalCoordinate
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (sector : Sector) (anchor : ThroatCover period hPeriod)
    (base : EffectiveThroat period hPeriod) :
    ActualThroatGaussNormalQuadratic :=
  actualThroatGaussNormalQuadraticOnCover period hPeriod configuration sector
    (actualThroatGaussNormalLocalLift period hPeriod anchor base)

/-- The local actual Gauss representatives satisfy the exact overlap law of
the induced D8 quadratic core. -/
theorem actualThroatGaussNormalQuadraticLocalCoordinate_transition
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (hTransverse : ∀ sector,
      HasNoTangentialRadical period hPeriod
        (globalGaugeFixedBulkMetricBySector period hPeriod configuration sector))
    (sector : Sector) (first second : ThroatCover period hPeriod)
    (base : EffectiveThroat period hPeriod)
    (hBase : base ∈ normalBundleBaseSet period hPeriod first ∩
      normalBundleBaseSet period hPeriod second) :
    (actualThroatGaussNormalQuadraticCore period hPeriod).coordChange
        first second base
        (actualThroatGaussNormalQuadraticLocalCoordinate period hPeriod
          configuration sector first base) =
      actualThroatGaussNormalQuadraticLocalCoordinate period hPeriod
        configuration sector second base := by
  let winding := localTransitionWinding period hPeriod first second base
  have hLift := localTransitionWinding_vadd period hPeriod first second base hBase
  change winding +ᵥ
      actualThroatGaussNormalLocalLift period hPeriod first base =
    actualThroatGaussNormalLocalLift period hPeriod second base at hLift
  change continuousSecondFundamentalFormTransportCLM
      (normalSignCLM winding)
      (actualThroatGaussNormalQuadraticOnCover period hPeriod configuration
        sector (actualThroatGaussNormalLocalLift period hPeriod first base)) =
    actualThroatGaussNormalQuadraticOnCover period hPeriod configuration sector
      (actualThroatGaussNormalLocalLift period hPeriod second base)
  rw [← hLift]
  exact (actualThroatGaussNormalQuadraticOnCover_vadd period hPeriod
    configuration hTransverse sector winding _).symm

/-- Exact analytic premise needed to upgrade the pointwise Gauss descent.
It asks only for smoothness of the genuine oriented coordinates on each
covering chart. -/
structure ActualThroatGaussNormalQuadraticRegularity
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (sector : Sector) : Prop where
  localCoordinate_contMDiffOn : ∀ anchor,
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, ActualThroatGaussNormalQuadratic) ∞
      (actualThroatGaussNormalQuadraticLocalCoordinate period hPeriod
        configuration sector anchor)
      (normalBundleBaseSet period hPeriod anchor)

/-- Smooth local coordinates of the actual Gauss quadratic in the genuine
nonorientable D8 quadratic bundle. -/
def actualThroatGaussNormalQuadraticSmoothCoordinates
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (hTransverse : ∀ sector,
      HasNoTangentialRadical period hPeriod
        (globalGaugeFixedBulkMetricBySector period hPeriod configuration sector))
    (sector : Sector)
    (regularity : ActualThroatGaussNormalQuadraticRegularity period hPeriod
      configuration sector) :
    SmoothCoreSectionCoordinates throatCoverModelWithCorners
      (actualThroatGaussNormalQuadraticCore period hPeriod) :=
  smoothCoreSectionCoordinatesOfLocalRepresentatives
    throatCoverModelWithCorners
    (actualThroatGaussNormalQuadraticCore period hPeriod)
    (actualThroatGaussNormalQuadraticLocalCoordinate period hPeriod
      configuration sector)
    (actualThroatGaussNormalQuadraticLocalCoordinate_transition period hPeriod
      configuration hTransverse sector)
    regularity.localCoordinate_contMDiffOn

/-- In every valid oriented chart, the coordinate is the actual Gauss
quadratic evaluated at that chart's genuine orientation lift. -/
@[simp]
theorem actualThroatGaussNormalQuadraticSmoothCoordinates_extractor
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (hTransverse : ∀ sector,
      HasNoTangentialRadical period hPeriod
        (globalGaugeFixedBulkMetricBySector period hPeriod configuration sector))
    (sector : Sector)
    (regularity : ActualThroatGaussNormalQuadraticRegularity period hPeriod
      configuration sector)
    (anchor : ThroatCover period hPeriod)
    (base : EffectiveThroat period hPeriod) :
    (actualThroatGaussNormalQuadraticSmoothCoordinates period hPeriod
      configuration hTransverse sector regularity).extractor anchor base =
      actualThroatSectorGaussNormalQuadraticAt period hPeriod configuration
        (actualThroatOrientationBoundaryOfCover period hPeriod
          (actualThroatGaussNormalLocalLift period hPeriod anchor base)) sector :=
  rfl

/-- In an oriented chart centered at `anchor`, the section coordinate is
exactly the previously constructed actual Gauss quadratic. -/
theorem actualThroatGaussNormalQuadraticSmoothCoordinates_at_anchor
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (hTransverse : ∀ sector,
      HasNoTangentialRadical period hPeriod
        (globalGaugeFixedBulkMetricBySector period hPeriod configuration sector))
    (sector : Sector)
    (regularity : ActualThroatGaussNormalQuadraticRegularity period hPeriod
      configuration sector)
    (anchor : ThroatCover period hPeriod) :
    (actualThroatGaussNormalQuadraticSmoothCoordinates period hPeriod
      configuration hTransverse sector regularity).extractor anchor
        (mappingTorusMk (ThroatData period hPeriod) anchor) =
      actualThroatSectorGaussNormalQuadraticAt period hPeriod configuration
        (actualThroatOrientationBoundaryOfCover period hPeriod anchor) sector := by
  change actualThroatGaussNormalQuadraticOnCover period hPeriod configuration
      sector
        ((throatProjectionLocalHomeomorph period hPeriod).localInverseAt anchor
          (mappingTorusMk (ThroatData period hPeriod) anchor)) = _
  rw [(throatProjectionLocalHomeomorph period hPeriod).localInverseAt_apply_self]
  rfl

/-- A one-loop chart change negates the complete quadratic coordinate. -/
theorem actualThroatGaussNormalQuadraticSmoothCoordinates_oneLoop
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (hTransverse : ∀ sector,
      HasNoTangentialRadical period hPeriod
        (globalGaugeFixedBulkMetricBySector period hPeriod configuration sector))
    (sector : Sector)
    (regularity : ActualThroatGaussNormalQuadraticRegularity period hPeriod
      configuration sector)
    (anchor : ThroatCover period hPeriod) :
    let base := mappingTorusMk (ThroatData period hPeriod) anchor
    (actualThroatGaussNormalQuadraticSmoothCoordinates period hPeriod
      configuration hTransverse sector regularity).extractor
        ((1 : Int) +ᵥ anchor) base =
      -(actualThroatGaussNormalQuadraticSmoothCoordinates period hPeriod
        configuration hTransverse sector regularity).extractor anchor base := by
  dsimp only
  have hFirst :
      (throatProjectionLocalHomeomorph period hPeriod).localInverseAt anchor
          (mappingTorusMk (ThroatData period hPeriod) anchor) = anchor :=
    (throatProjectionLocalHomeomorph period hPeriod).localInverseAt_apply_self
  have hProjection :
      mappingTorusMk (ThroatData period hPeriod) ((1 : Int) +ᵥ anchor) =
        mappingTorusMk (ThroatData period hPeriod) anchor :=
    (mappingTorusMk_isAddQuotientCoveringMap
      (ThroatData period hPeriod)).map_vadd 1
  have hSecond :
      (throatProjectionLocalHomeomorph period hPeriod).localInverseAt
          ((1 : Int) +ᵥ anchor)
          (mappingTorusMk (ThroatData period hPeriod) anchor) =
        (1 : Int) +ᵥ anchor := by
    rw [← hProjection]
    exact (throatProjectionLocalHomeomorph period hPeriod).localInverseAt_apply_self
  change actualThroatGaussNormalQuadraticOnCover period hPeriod configuration
      sector
        ((throatProjectionLocalHomeomorph period hPeriod).localInverseAt
          ((1 : Int) +ᵥ anchor)
          (mappingTorusMk (ThroatData period hPeriod) anchor)) =
    -actualThroatGaussNormalQuadraticOnCover period hPeriod configuration
      sector
        ((throatProjectionLocalHomeomorph period hPeriod).localInverseAt anchor
          (mappingTorusMk (ThroatData period hPeriod) anchor))
  rw [hFirst, hSecond]
  have hDeck := actualThroatGaussNormalQuadraticOnCover_vadd period hPeriod
    configuration hTransverse sector (1 : Int) anchor
  rw [hDeck]
  apply ContinuousLinearMap.ext
  intro first
  apply ContinuousLinearMap.ext
  intro second
  simp [normalSignCLM_apply, normalSignRepresentation]

local instance actualThroatGaussNormalQuadraticCoreSmooth :
    (actualThroatGaussNormalQuadraticCore period hPeriod).IsContMDiff
      throatCoverModelWithCorners ω :=
  actualThroatGaussNormalQuadraticCore_isContMDiff period hPeriod

local instance actualThroatGaussNormalQuadraticTotalSpaceTopology :
    TopologicalSpace
      (Bundle.TotalSpace ActualThroatGaussNormalQuadratic
        (actualThroatGaussNormalQuadraticCore period hPeriod).Fiber) :=
  (actualThroatGaussNormalQuadraticCore period hPeriod).toTopologicalSpace

local instance actualThroatGaussNormalQuadraticFiberBundle :
    FiberBundle ActualThroatGaussNormalQuadratic
      (actualThroatGaussNormalQuadraticCore period hPeriod).Fiber :=
  (actualThroatGaussNormalQuadraticCore period hPeriod).fiberBundle

local instance actualThroatGaussNormalQuadraticVectorBundle :
    VectorBundle Real ActualThroatGaussNormalQuadratic
      (actualThroatGaussNormalQuadraticCore period hPeriod).Fiber :=
  (actualThroatGaussNormalQuadraticCore period hPeriod).vectorBundle

/-- Genuine total-space section selected from the compatible local actual
Gauss representatives. -/
def actualThroatGaussNormalQuadraticBundleSection
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (hTransverse : ∀ sector,
      HasNoTangentialRadical period hPeriod
        (globalGaugeFixedBulkMetricBySector period hPeriod configuration sector))
    (sector : Sector)
    (regularity : ActualThroatGaussNormalQuadraticRegularity period hPeriod
      configuration sector) :
    EffectiveThroat period hPeriod →
      Bundle.TotalSpace ActualThroatGaussNormalQuadratic
        (actualThroatGaussNormalQuadraticCore period hPeriod).Fiber :=
  fun base =>
    ⟨base, (actualThroatGaussNormalQuadraticSmoothCoordinates period hPeriod
      configuration hTransverse sector regularity).value base⟩

@[simp]
theorem actualThroatGaussNormalQuadraticBundleSection_proj
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (hTransverse : ∀ sector,
      HasNoTangentialRadical period hPeriod
        (globalGaugeFixedBulkMetricBySector period hPeriod configuration sector))
    (sector : Sector)
    (regularity : ActualThroatGaussNormalQuadraticRegularity period hPeriod
      configuration sector) :
    Bundle.TotalSpace.proj ∘
      actualThroatGaussNormalQuadraticBundleSection period hPeriod
        configuration hTransverse sector regularity = id :=
  rfl

/-- The total-space Gauss quadratic section is globally smooth. -/
theorem actualThroatGaussNormalQuadraticBundleSection_contMDiff
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (hTransverse : ∀ sector,
      HasNoTangentialRadical period hPeriod
        (globalGaugeFixedBulkMetricBySector period hPeriod configuration sector))
    (sector : Sector)
    (regularity : ActualThroatGaussNormalQuadraticRegularity period hPeriod
      configuration sector) :
    ContMDiff throatCoverModelWithCorners
      (throatCoverModelWithCorners.prod
        𝓘(Real, ActualThroatGaussNormalQuadratic)) ∞
      (actualThroatGaussNormalQuadraticBundleSection period hPeriod
        configuration hTransverse sector regularity) := by
  let core := actualThroatGaussNormalQuadraticCore period hPeriod
  let coordinates := actualThroatGaussNormalQuadraticSmoothCoordinates
    period hPeriod configuration hTransverse sector regularity
  intro base
  let chart := core.indexAt base
  let localTriv := core.localTriv chart
  letI : MemTrivializationAtlas localTriv := by
    refine ⟨⟨chart, ?_⟩⟩
    rfl
  have hBase : base ∈ core.baseSet chart := core.mem_baseSet_at base
  have hSource :
      actualThroatGaussNormalQuadraticBundleSection period hPeriod
          configuration hTransverse sector regularity base ∈
        localTriv.source := by
    rw [localTriv.mem_source]
    exact hBase
  rw [localTriv.contMDiffAt_iff hSource]
  constructor
  · exact contMDiffAt_id
  · have hLocalSmooth : ContMDiffAt throatCoverModelWithCorners
        𝓘(Real, ActualThroatGaussNormalQuadratic) ∞
        (coordinates.extractor chart) base :=
      (coordinates.extractor_contMDiffOn chart).contMDiffAt
        (core.isOpen_baseSet chart |>.mem_nhds hBase)
    apply hLocalSmooth.congr_of_eventuallyEq
    filter_upwards [(core.isOpen_baseSet chart).mem_nhds hBase]
      with nearby hNearby
    change core.coordChange (core.indexAt nearby) chart nearby
        (coordinates.value nearby) = coordinates.extractor chart nearby
    exact coordinates.coordinate_eq chart nearby hNearby

/-- Bundled smooth section of the D8/nonorientable normal quadratic bundle. -/
def actualThroatGaussNormalQuadraticSmoothSection
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (hTransverse : ∀ sector,
      HasNoTangentialRadical period hPeriod
        (globalGaugeFixedBulkMetricBySector period hPeriod configuration sector))
    (sector : Sector)
    (regularity : ActualThroatGaussNormalQuadraticRegularity period hPeriod
      configuration sector) :
    ContMDiffSection throatCoverModelWithCorners
      ActualThroatGaussNormalQuadratic ∞
      (actualThroatGaussNormalQuadraticCore period hPeriod).Fiber :=
  ⟨(actualThroatGaussNormalQuadraticSmoothCoordinates period hPeriod
      configuration hTransverse sector regularity).value,
    actualThroatGaussNormalQuadraticBundleSection_contMDiff period hPeriod
      configuration hTransverse sector regularity⟩

end
end P0EFTJanusProgramPActualThroatGaussNormalQuadraticSmoothBundle4D
end JanusFormal
