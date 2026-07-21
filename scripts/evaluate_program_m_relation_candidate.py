"""MF-GATE-002: raw relation -> reachability -> SCC quotient -> order-only report."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import numpy as np

try:
    from scripts.audit_program_m_blind_dimension import order_matrix_from_null_points
    from scripts.evaluate_program_m_order_candidate import (
        DEFAULT_DIMENSION_REFERENCE,
        DEFAULT_LOCALITY_REFERENCE,
        evaluate_order,
        load_order,
    )
except ModuleNotFoundError:  # Direct `python scripts/...py` execution.
    from audit_program_m_blind_dimension import order_matrix_from_null_points
    from evaluate_program_m_order_candidate import (
        DEFAULT_DIMENSION_REFERENCE,
        DEFAULT_LOCALITY_REFERENCE,
        evaluate_order,
        load_order,
    )


def _matrix_fingerprint(matrix: np.ndarray) -> str:
    packed = np.packbits(matrix.astype(np.uint8), bitorder="little")
    payload = matrix.shape[0].to_bytes(8, "little") + packed.tobytes()
    return hashlib.sha256(payload).hexdigest()


def reflexive_transitive_closure(relation: np.ndarray) -> np.ndarray:
    matrix = np.asarray(relation, dtype=bool)
    if matrix.ndim != 2 or matrix.shape[0] != matrix.shape[1]:
        raise ValueError("relation must be a square matrix")
    size = matrix.shape[0]
    rows = [
        sum(1 << int(index) for index in np.flatnonzero(matrix[source])) | (1 << source)
        for source in range(size)
    ]
    for middle in range(size):
        middle_bit = 1 << middle
        for source in range(size):
            if rows[source] & middle_bit:
                rows[source] |= rows[middle]
    closure = np.zeros((size, size), dtype=bool)
    for source, bits in enumerate(rows):
        closure[source] = [bool(bits & (1 << target)) for target in range(size)]
    return closure


def mutual_reachability_components(closure: np.ndarray) -> list[list[int]]:
    unseen = set(range(closure.shape[0]))
    components: list[list[int]] = []
    while unseen:
        root = min(unseen)
        component = sorted(
            vertex
            for vertex in unseen
            if closure[root, vertex] and closure[vertex, root]
        )
        components.append(component)
        unseen.difference_update(component)
    return components


def quotient_order(
    closure: np.ndarray, components: list[list[int]]
) -> tuple[np.ndarray, list[int]]:
    component_of = [0] * closure.shape[0]
    for component_index, component in enumerate(components):
        for vertex in component:
            component_of[vertex] = component_index
    quotient = np.zeros((len(components), len(components)), dtype=bool)
    for source_index, source_component in enumerate(components):
        source = source_component[0]
        for target_index, target_component in enumerate(components):
            quotient[source_index, target_index] = closure[source, target_component[0]]
    return quotient, component_of


def relation_to_skeleton(relation: np.ndarray) -> dict[str, object]:
    matrix = np.asarray(relation, dtype=bool)
    if matrix.ndim != 2 or matrix.shape[0] != matrix.shape[1]:
        raise ValueError("relation must be a square matrix")
    closure = reflexive_transitive_closure(matrix)
    components = mutual_reachability_components(closure)
    quotient, component_of = quotient_order(closure, components)
    primitive_edges = int(np.count_nonzero(matrix))
    closure_pairs = int(np.count_nonzero(closure))
    added_pairs = int(np.count_nonzero(closure & ~matrix))
    internal_edges = sum(
        bool(matrix[source, target])
        for source in range(matrix.shape[0])
        for target in range(matrix.shape[0])
        if component_of[source] == component_of[target]
    )
    bridge_edges = primitive_edges - internal_edges
    component_sizes = [len(component) for component in components]
    return {
        "closure": closure,
        "quotient": quotient,
        "components": components,
        "component_of": component_of,
        "audit": {
            "primitive_objects": int(matrix.shape[0]),
            "skeleton_objects": len(components),
            "collapsed_objects": int(matrix.shape[0]) - len(components),
            "primitive_relation_pairs": primitive_edges,
            "closure_pairs": closure_pairs,
            "pairs_added_by_reflexive_transitive_closure": added_pairs,
            "internal_primitive_edges": int(internal_edges),
            "bridge_primitive_edges": int(bridge_edges),
            "nontrivial_mutual_reachability_fibers": sum(size > 1 for size in component_sizes),
            "largest_fiber": max(component_sizes, default=0),
            "fiber_sizes": component_sizes,
            "primitive_relation_sha256": _matrix_fingerprint(matrix),
            "closure_sha256": _matrix_fingerprint(closure),
            "quotient_sha256": _matrix_fingerprint(quotient),
            "recoverability": (
                "the original relation remains recoverable only from the original input; "
                "the quotient report stores hashes/counts/fibers, not every primitive edge"
            ),
            "information_excluded_from_downstream_diagnostics": [
                "which primitive edges generated each reachability pair",
                "edge multiplicity patterns inside each mutual-reachability fiber",
                "endpoint incidence of primitive bridge edges",
                "self-loop choices erased by reflexive closure",
            ],
        },
    }


def evaluate_relation(
    relation: np.ndarray,
    *,
    locality_reference: dict[str, object],
    dimension_reference: dict[str, object],
    source_name: str,
) -> dict[str, object]:
    decomposition = relation_to_skeleton(relation)
    downstream = evaluate_order(
        decomposition["quotient"],
        locality_reference=locality_reference,
        dimension_reference=dimension_reference,
        source_name=f"{source_name}:scc_quotient",
    )
    return {
        "program": "MF-GATE-002",
        "source_name": source_name,
        "orientation_convention": (
            "input arrow direction is retained mathematically; no physical time orientation inferred"
        ),
        "reconstruction": decomposition["audit"],
        "fibers": decomposition["components"],
        "downstream_order_report": downstream,
        "status": downstream["status"],
        "claims_not_made": downstream["claims_not_made"],
    }


def transitive_reduction(order: np.ndarray) -> np.ndarray:
    """Cover relation of a finite partial order, used only to build examples."""
    matrix = np.asarray(order, dtype=bool)
    size = matrix.shape[0]
    reduction = np.zeros_like(matrix)
    future = [
        sum(1 << int(index) for index in np.flatnonzero(matrix[source]))
        for source in range(size)
    ]
    past = [
        sum(1 << int(index) for index in np.flatnonzero(matrix[:, target]))
        for target in range(size)
    ]
    for source in range(size):
        for target in np.flatnonzero(matrix[source]):
            target = int(target)
            if source != target and (future[source] & past[target]).bit_count() == 2:
                reduction[source, target] = True
    return reduction


def cyclic_refinement(reduced_relation: np.ndarray) -> np.ndarray:
    """Split object 0 into a two-cycle while preserving the same SCC quotient."""
    size = reduced_relation.shape[0]
    refined = np.zeros((size + 1, size + 1), dtype=bool)
    representatives = [0] + [index + 1 for index in range(1, size)]
    refined[0, 1] = True
    refined[1, 0] = True
    for source in range(size):
        for target in np.flatnonzero(reduced_relation[source]):
            refined[representatives[source], representatives[int(target)]] = True
    return refined


def example_reports(
    locality_reference: dict[str, object], dimension_reference: dict[str, object]
) -> dict[str, object]:
    rng = np.random.default_rng(2026091000)
    points = rng.random((256, 2))
    order = order_matrix_from_null_points(points)
    del points
    reduced = transitive_reduction(order)
    refined = cyclic_refinement(reduced)
    base_report = evaluate_relation(
        reduced,
        locality_reference=locality_reference,
        dimension_reference=dimension_reference,
        source_name="fresh_poisson_hasse_relation_256",
    )
    refined_report = evaluate_relation(
        refined,
        locality_reference=locality_reference,
        dimension_reference=dimension_reference,
        source_name="same_skeleton_with_two_cycle_257",
    )
    return {
        "program": "MF-GATE-002",
        "reports": [base_report, refined_report],
        "downstream_collision": {
            "same_quotient_sha256": (
                base_report["reconstruction"]["quotient_sha256"]
                == refined_report["reconstruction"]["quotient_sha256"]
            ),
            "same_diagnostics": (
                base_report["downstream_order_report"]["diagnostics"]
                == refined_report["downstream_order_report"]["diagnostics"]
            ),
            "primitive_relation_sha256_distinct": (
                base_report["reconstruction"]["primitive_relation_sha256"]
                != refined_report["reconstruction"]["primitive_relation_sha256"]
            ),
        },
    }


def _load_json(path: Path) -> dict[str, object]:
    return json.loads(path.read_text(encoding="utf-8"))


def main() -> None:
    parser = argparse.ArgumentParser()
    source = parser.add_mutually_exclusive_group(required=True)
    source.add_argument("--relation", type=Path)
    source.add_argument("--examples", action="store_true")
    parser.add_argument("--locality-reference", type=Path, default=DEFAULT_LOCALITY_REFERENCE)
    parser.add_argument("--dimension-reference", type=Path, default=DEFAULT_DIMENSION_REFERENCE)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    locality = _load_json(args.locality_reference)
    dimension = _load_json(args.dimension_reference)
    if args.examples:
        result = example_reports(locality, dimension)
    else:
        result = evaluate_relation(
            load_order(args.relation),
            locality_reference=locality,
            dimension_reference=dimension,
            source_name=str(args.relation),
        )
    payload = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(payload, encoding="utf-8")
    else:
        print(payload, end="")


if __name__ == "__main__":
    main()
