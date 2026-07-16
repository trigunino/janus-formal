#!/usr/bin/env python3
"""Integrity checks for the effective D8 mapping-torus quotient gate."""

from __future__ import annotations

import re
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
GATE = Path(
    "JanusFormal/Branches/FundamentalGeometryD8TopologyRepresentation/"
    "Gates/P0EFTJanusMappingTorusQuotient.lean"
)
NORMAL_LINE_GATE = Path(
    "JanusFormal/Branches/FundamentalGeometryD8TopologyRepresentation/"
    "Gates/P0EFTJanusMappingTorusNormalLine.lean"
)
PT_GATE = Path(
    "JanusFormal/Branches/FundamentalGeometryD8TopologyRepresentation/"
    "Gates/P0EFTJanusMappingTorusPTInvolution.lean"
)
ORIENTATION_DOUBLE_GATE = Path(
    "JanusFormal/Branches/FundamentalGeometryD8TopologyRepresentation/"
    "Gates/P0EFTJanusMappingTorusOrientationDoubleCover.lean"
)
THROAT_COMPLEMENT_GATE = Path(
    "JanusFormal/Branches/FundamentalGeometryD8TopologyRepresentation/"
    "Gates/P0EFTJanusMappingTorusThroatComplementSides.lean"
)
THROAT_COMPLEMENT_CONNECTED_GATE = Path(
    "JanusFormal/Branches/FundamentalGeometryD8TopologyRepresentation/"
    "Gates/P0EFTJanusMappingTorusThroatComplementConnected.lean"
)
SMOOTH_ATLAS_FRONTIER_GATE = Path(
    "JanusFormal/Branches/FundamentalGeometryD8TopologyRepresentation/"
    "Gates/P0EFTJanusMappingTorusSmoothAtlasFrontier.lean"
)
SMOOTH_DECK_DESCENT_GATE = Path(
    "JanusFormal/Branches/FundamentalGeometryD8TopologyRepresentation/"
    "Gates/P0EFTJanusMappingTorusSmoothQuotient.lean"
)
SMOOTH_QUOTIENT_MANIFOLD_GATE = Path(
    "JanusFormal/Branches/FundamentalGeometryD8TopologyRepresentation/"
    "Gates/P0EFTJanusMappingTorusSmoothQuotientManifold.lean"
)
FACADE = Path(
    "JanusFormal/Branches/FundamentalGeometryD8TopologyRepresentation.lean"
)

DECLARATIONS = (
    "structure MappingTorusData",
    "theorem vadd_eq_self_iff",
    "theorem mappingTorusMk_isCoveringMap",
    "theorem mappingTorus_has_chartedSpace",
    "theorem equatorialSphereInclusion_injective",
    "theorem continuous_fixedThroatQuotientInclusion",
    "theorem fixedThroatQuotientInclusion_injective",
)

STATUSES = (
    "effectiveTopologicalMappingTorusQuotientConstructed",
    "mappingTorusCoveringAndChartedSpaceProved",
    "fixedThroatQuotientInclusionInjectiveProved",
)

NORMAL_LINE_DECLARATIONS = (
    "abbrev MappingTorusNormalLine",
    "def normalLineProjection",
    "theorem continuous_normalLineProjection",
    "def normalLineZeroSection",
    "theorem continuous_normalLineZeroSection",
    "theorem normalLineProjection_zeroSection",
    "theorem one_loop_normal_flip",
    "theorem two_loops_restore_normal",
    "theorem mapping_torus_normal_line_closure",
)

NORMAL_LINE_STATUSES = (
    "associatedNormalLineOrbitQuotientConstructed",
    "associatedNormalLineProjectionContinuousSurjectiveProved",
    "associatedNormalLineZeroSectionConstructed",
    "associatedNormalLineOneLoopFlipProved",
    "associatedNormalLineTwoLoopRestorationProved",
)

PT_DECLARATIONS = (
    "def mappingTorusTimeReversal",
    "theorem continuous_mappingTorusTimeReversal",
    "theorem mappingTorusTimeReversal_involutive",
    "def reflectedSpherePT",
    "theorem continuous_reflectedSpherePT",
    "theorem reflectedSpherePT_involutive",
    "def fixedThroatPT",
    "theorem continuous_fixedThroatPT",
    "theorem fixedThroatPT_involutive",
    "theorem fixedThroatQuotientInclusion_pt_equivariant",
)

PT_STATUSES = (
    "mappingTorusTimeReversalContinuousProved",
    "mappingTorusTimeReversalInvolutiveProved",
    "fixedThroatQuotientInclusionPTEquivariantProved",
)

ORIENTATION_DOUBLE_DECLARATIONS = (
    "abbrev OrientationDoubleThroat",
    "def orientationDoubleToThroat",
    "theorem orientationDoubleToThroat_isCoveringMap",
    "theorem orientationDouble_fiber_equiv_two",
    "theorem orientationDeck_involutive",
    "theorem orientationDeck_ne_self",
    "def orientationNormalTrivialization",
    "theorem orientationDouble_normal_pullback_closure",
)

ORIENTATION_DOUBLE_STATUSES = (
    "effectiveThroatOrientationDoubleCoveringMapProved",
    "throatOrientationDoubleCoverFiberTwoProved",
    "throatOrientationDeckInvolutionFreeProved",
    "throatNormalPullbackTopologicallyTrivializedProved",
)

THROAT_COMPLEMENT_DECLARATIONS = (
    "theorem positiveSphereSide_isOpen",
    "theorem negativeSphereSide_isOpen",
    "theorem positiveSphereSide_nonempty",
    "theorem negativeSphereSide_nonempty",
    "theorem sphere_complement_eq_two_sides",
    "theorem positive_negative_disjoint",
    "theorem sphereReflection_image_positive",
    "theorem one_vadd_mem_negative_iff",
    "theorem mappingTorusMk_preimage_effectiveThroat",
    "theorem image_positiveCoverSide_eq_effective_complement",
    "theorem image_negativeCoverSide_eq_effective_complement",
    "theorem quotient_images_of_sides_coincide",
    "theorem reflectedSpherePT_mem_effective_complement_iff",
)

THROAT_COMPLEMENT_STATUSES = (
    "equatorialSphereComplementTwoOpenSidesProved",
    "reflectionAndDeckExchangeCoverSidesProved",
    "effectiveThroatComplementOneSidedImageProved",
    "effectiveThroatComplementPTInvariantProved",
)

THROAT_COMPLEMENT_CONNECTED_DECLARATIONS = (
    "theorem positiveSphereSide_isPathConnected",
    "theorem negativeSphereSide_isPathConnected",
    "theorem connectedComponentIn_throat_complement_positivePole",
    "theorem connectedComponentIn_throat_complement_negativePole",
    "theorem positiveCoverSide_isPathConnected",
    "theorem effectiveThroat_complement_isPathConnected",
    "theorem effectiveThroat_complement_isConnected",
)

SMOOTH_ATLAS_FRONTIER_DECLARATIONS = (
    "def unitThreeSphereHomeomorph",
    "instance unitThreeSphereIsManifold",
    "def equatorialTwoSphereHomeomorph",
    "instance equatorialTwoSphereIsManifold",
    "theorem unitThreeSphere_prod_real_isManifold",
    "theorem fixedThroatCover_isManifold",
    "theorem fixedThroatCoverInclusion_isEmbedding",
    "theorem fixedThroatCoverInclusion_contMDiff_zero",
    "theorem fixedThroat_quotient_isTopologicalManifold",
    "theorem fixedThroatQuotientInclusion_contMDiff_zero",
    "theorem reflectedSphere_quotient_isTopologicalManifold",
    "theorem reflectedSphere_projection_isLocalHomeomorph",
    "theorem reflectedSphere_projection_contMDiff_zero",
    "theorem reflectedSphere_projection_topological_atlas_closure",
)

SMOOTH_ATLAS_FRONTIER_STATUSES = (
    "algebraicSphereCoversAnalyticManifoldsProved",
    "throatCoverTopologicalEmbeddingAndC0Proved",
    "effectiveMappingTorusTopologicalManifoldProved",
    "effectiveThroatTopologicalManifoldProved",
    "quotientProjectionLocalHomeomorphAndC0Proved",
)

SMOOTH_DECK_DESCENT_DECLARATIONS = (
    "theorem sphereReflection_contMDiff",
    "theorem reflectedSphereCover_deck_contMDiff",
    "theorem fixedThroatCover_deck_contMDiff",
    "theorem fixedThroatCoverInclusion_contMDiff",
    "theorem localInverseAt_eventuallyEq_vadd",
    "theorem smoothHomeomorph_coordinateChange_mem_groupoid",
)

SMOOTH_QUOTIENT_MANIFOLD_DECLARATIONS = (
    "theorem mappingTorus_isManifold_of_smooth_deck",
    "def mappingTorusLocalSectionPartialDiffeomorph",
    "theorem mappingTorus_projection_isLocalDiffeomorph",
    "def fixedThroatQuotientChartedSpace",
    "def reflectedSphereQuotientChartedSpace",
    "theorem fixedThroatQuotient_isManifold",
    "theorem reflectedSphereQuotient_isManifold",
    "theorem fixedThroat_projection_isLocalDiffeomorph",
    "theorem reflectedSphere_projection_isLocalDiffeomorph",
    "theorem fixedThroatQuotientInclusion_contMDiff",
)

SMOOTH_QUOTIENT_MANIFOLD_STATUSES = (
    "effectiveMappingTorusSmoothQuotientManifoldProved",
    "effectiveThroatSmoothQuotientManifoldProved",
    "quotientProjectionLocalDiffeomorphProved",
    "fixedThroatQuotientInclusionContMDiffProved",
)

THROAT_COMPLEMENT_CONNECTED_STATUSES = (
    "positiveAndNegativeSphereSidesPathConnectedProved",
    "positiveCoverSidePathConnectedProved",
    "effectiveThroatComplementPathConnectedProved",
    "effectiveThroatComplementConnectedProved",
)


def assert_d8_topology_integrity(repo_root: Path = REPO_ROOT) -> None:
    gate = (repo_root / GATE).read_text(encoding="utf-8")
    normal_line_gate = (repo_root / NORMAL_LINE_GATE).read_text(encoding="utf-8")
    pt_gate = (repo_root / PT_GATE).read_text(encoding="utf-8")
    orientation_double_gate = (repo_root / ORIENTATION_DOUBLE_GATE).read_text(
        encoding="utf-8"
    )
    throat_complement_gate = (repo_root / THROAT_COMPLEMENT_GATE).read_text(
        encoding="utf-8"
    )
    throat_complement_connected_gate = (
        repo_root / THROAT_COMPLEMENT_CONNECTED_GATE
    ).read_text(encoding="utf-8")
    smooth_atlas_frontier_gate = (
        repo_root / SMOOTH_ATLAS_FRONTIER_GATE
    ).read_text(encoding="utf-8")
    smooth_deck_descent_gate = (
        repo_root / SMOOTH_DECK_DESCENT_GATE
    ).read_text(encoding="utf-8")
    smooth_quotient_manifold_gate = (
        repo_root / SMOOTH_QUOTIENT_MANIFOLD_GATE
    ).read_text(encoding="utf-8")
    facade = (repo_root / FACADE).read_text(encoding="utf-8")

    for declaration in DECLARATIONS:
        if declaration not in gate:
            raise AssertionError(f"missing D8 declaration: {declaration}")
    if re.search(r"\b(?:sorry|admit|axiom)\b", gate):
        raise AssertionError("proof placeholder found in D8 quotient gate")
    if "IsManifold" in gate:
        raise AssertionError("D8 quotient gate overclaims a manifold theorem")

    gate_import = "Gates.P0EFTJanusMappingTorusQuotient"
    if facade.count(gate_import) != 1:
        raise AssertionError("D8 facade omits the quotient gate")
    for status in STATUSES:
        if facade.count(f"{status} : Prop") != 1 or facade.count(f"s.{status}") != 1:
            raise AssertionError(f"D8 facade omits status: {status}")

    for declaration in NORMAL_LINE_DECLARATIONS:
        if declaration not in normal_line_gate:
            raise AssertionError(f"missing D8 associated-line declaration: {declaration}")
    if re.search(r"\b(?:sorry|admit|axiom)\b", normal_line_gate):
        raise AssertionError("proof placeholder found in D8 associated-line gate")
    for overclaim in ("IsManifold", "VectorBundle"):
        if overclaim in normal_line_gate:
            raise AssertionError(f"D8 associated-line gate overclaims {overclaim}")

    normal_line_import = "Gates.P0EFTJanusMappingTorusNormalLine"
    if facade.count(normal_line_import) != 1:
        raise AssertionError("D8 facade omits the associated-line gate")
    if facade.count("associatedNormalLineQuotientCoreClosed s") != 1:
        raise AssertionError("D8 smooth core omits the associated-line milestone")
    for status in NORMAL_LINE_STATUSES:
        if facade.count(f"{status} : Prop") != 1 or facade.count(f"s.{status}") != 1:
            raise AssertionError(f"D8 facade omits associated-line status: {status}")

    for declaration in PT_DECLARATIONS:
        if declaration not in pt_gate:
            raise AssertionError(f"missing D8 PT declaration: {declaration}")
    if re.search(r"\b(?:sorry|admit|axiom)\b", pt_gate):
        raise AssertionError("proof placeholder found in D8 PT gate")
    pt_import = "Gates.P0EFTJanusMappingTorusPTInvolution"
    if facade.count(pt_import) != 1:
        raise AssertionError("D8 facade omits the mapping-torus PT gate")
    if facade.count("effectiveMappingTorusPTCoreClosed s") != 1:
        raise AssertionError("D8 core omits the mapping-torus PT milestone")
    for status in PT_STATUSES:
        if facade.count(f"{status} : Prop") != 1 or facade.count(f"s.{status}") != 1:
            raise AssertionError(f"D8 facade omits PT status: {status}")

    for declaration in ORIENTATION_DOUBLE_DECLARATIONS:
        if declaration not in orientation_double_gate:
            raise AssertionError(
                f"missing D8 orientation-double-cover declaration: {declaration}"
            )
    if re.search(r"\b(?:sorry|admit|axiom)\b", orientation_double_gate):
        raise AssertionError("proof placeholder found in D8 orientation-double-cover gate")
    for overclaim in ("IsManifold", "VectorBundle"):
        if overclaim in orientation_double_gate:
            raise AssertionError(
                f"D8 orientation-double-cover gate overclaims {overclaim}"
            )
    orientation_double_import = "Gates.P0EFTJanusMappingTorusOrientationDoubleCover"
    if facade.count(orientation_double_import) != 1:
        raise AssertionError("D8 facade omits the orientation-double-cover gate")
    if facade.count("effectiveThroatOrientationDoubleCoverCoreClosed s") != 1:
        raise AssertionError("D8 smooth core omits the orientation-double-cover milestone")
    for status in ORIENTATION_DOUBLE_STATUSES:
        if facade.count(f"{status} : Prop") != 1 or facade.count(f"s.{status}") != 1:
            raise AssertionError(
                f"D8 facade omits orientation-double-cover status: {status}"
            )

    for declaration in THROAT_COMPLEMENT_DECLARATIONS:
        if declaration not in throat_complement_gate:
            raise AssertionError(
                f"missing D8 throat-complement declaration: {declaration}"
            )
    if re.search(r"\b(?:sorry|admit|axiom)\b", throat_complement_gate):
        raise AssertionError("proof placeholder found in D8 throat-complement gate")
    for overclaim in ("IsManifold", "VectorBundle", "IsConnected", "IsPreconnected"):
        if overclaim in throat_complement_gate:
            raise AssertionError(f"D8 throat-complement gate overclaims {overclaim}")
    complement_import = "Gates.P0EFTJanusMappingTorusThroatComplementSides"
    if facade.count(complement_import) != 1:
        raise AssertionError("D8 facade omits the throat-complement gate")
    if facade.count("effectiveThroatComplementSidesCoreClosed s") != 1:
        raise AssertionError("D8 smooth core omits the throat-complement milestone")
    for status in THROAT_COMPLEMENT_STATUSES:
        if facade.count(f"{status} : Prop") != 1 or facade.count(f"s.{status}") != 1:
            raise AssertionError(
                f"D8 facade omits throat-complement status: {status}"
            )

    for declaration in THROAT_COMPLEMENT_CONNECTED_DECLARATIONS:
        if declaration not in throat_complement_connected_gate:
            raise AssertionError(
                f"missing D8 connected-complement declaration: {declaration}"
            )
    if re.search(r"\b(?:sorry|admit|axiom)\b", throat_complement_connected_gate):
        raise AssertionError("proof placeholder found in D8 connected-complement gate")
    connected_import = "Gates.P0EFTJanusMappingTorusThroatComplementConnected"
    if facade.count(connected_import) != 1:
        raise AssertionError("D8 facade omits the connected-complement gate")
    if facade.count("effectiveThroatComplementConnectedCoreClosed s") != 1:
        raise AssertionError("D8 smooth core omits connected-complement milestone")
    for status in THROAT_COMPLEMENT_CONNECTED_STATUSES:
        if facade.count(f"{status} : Prop") != 1 or facade.count(f"s.{status}") != 1:
            raise AssertionError(
                f"D8 facade omits connected-complement status: {status}"
            )

    for declaration in SMOOTH_ATLAS_FRONTIER_DECLARATIONS:
        if declaration not in smooth_atlas_frontier_gate:
            raise AssertionError(
                f"missing D8 smooth-atlas-frontier declaration: {declaration}"
            )
    if re.search(r"\b(?:sorry|admit|axiom)\b", smooth_atlas_frontier_gate):
        raise AssertionError("proof placeholder found in D8 smooth-atlas frontier")
    smooth_frontier_import = "Gates.P0EFTJanusMappingTorusSmoothAtlasFrontier"
    if facade.count(smooth_frontier_import) != 1:
        raise AssertionError("D8 facade omits the smooth-atlas frontier gate")
    if facade.count("mappingTorusSmoothAtlasFrontierCoreClosed s") != 1:
        raise AssertionError("D8 smooth core omits smooth-atlas frontier milestone")
    for status in SMOOTH_ATLAS_FRONTIER_STATUSES:
        if facade.count(f"{status} : Prop") != 1 or facade.count(f"s.{status}") != 1:
            raise AssertionError(f"D8 facade omits smooth-atlas status: {status}")

    for declaration in SMOOTH_DECK_DESCENT_DECLARATIONS:
        if declaration not in smooth_deck_descent_gate:
            raise AssertionError(
                f"missing D8 smooth-deck descent declaration: {declaration}"
            )
    if re.search(r"\b(?:sorry|admit|axiom)\b", smooth_deck_descent_gate):
        raise AssertionError("proof placeholder found in D8 smooth-deck descent gate")
    smooth_descent_import = (
        "import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation."
        "Gates.P0EFTJanusMappingTorusSmoothQuotient\n"
    )
    if facade.count(smooth_descent_import) != 1:
        raise AssertionError("D8 facade omits the smooth-deck descent gate")
    if facade.count("mappingTorusSmoothDeckDescentFrontierClosed s") != 1:
        raise AssertionError("D8 smooth core omits smooth-deck descent milestone")
    status = "smoothDeckActionsAndAtlasTransitionsProved"
    if facade.count(f"{status} : Prop") != 1 or facade.count(f"s.{status}") != 1:
        raise AssertionError(f"D8 facade omits smooth-deck status: {status}")

    for declaration in SMOOTH_QUOTIENT_MANIFOLD_DECLARATIONS:
        if declaration not in smooth_quotient_manifold_gate:
            raise AssertionError(
                f"missing D8 smooth-quotient-manifold declaration: {declaration}"
            )
    if re.search(r"\b(?:sorry|admit|axiom)\b", smooth_quotient_manifold_gate):
        raise AssertionError("proof placeholder found in D8 smooth quotient manifold")
    smooth_quotient_import = (
        "import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation."
        "Gates.P0EFTJanusMappingTorusSmoothQuotientManifold\n"
    )
    if facade.count(smooth_quotient_import) != 1:
        raise AssertionError("D8 facade omits the smooth quotient manifold gate")
    if facade.count("mappingTorusSmoothQuotientManifoldCoreClosed s") != 1:
        raise AssertionError("D8 smooth core omits smooth quotient manifold milestone")
    for status in SMOOTH_QUOTIENT_MANIFOLD_STATUSES:
        if facade.count(f"{status} : Prop") != 1 or facade.count(f"s.{status}") != 1:
            raise AssertionError(
                f"D8 facade omits smooth quotient manifold status: {status}"
            )


def run_audit() -> None:
    assert_d8_topology_integrity()
    print("D8 topology integrity audit: all checks passed")


if __name__ == "__main__":
    run_audit()
