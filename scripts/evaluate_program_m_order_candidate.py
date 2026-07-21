"""MF-GATE-001: unified coordinate-free report for a finite order candidate."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import numpy as np

try:
    from scripts.audit_program_m_blind_dimension import (
        myrheim_meyer_dimension,
        order_matrix_from_null_points,
        ordering_fraction,
    )
    from scripts.audit_program_m_interval_abundance import interval_abundance_profile
    from scripts.audit_program_m_interval_multiscale import three_layer_order
except ModuleNotFoundError:  # Direct `python scripts/...py` execution.
    from audit_program_m_blind_dimension import (
        myrheim_meyer_dimension,
        order_matrix_from_null_points,
        ordering_fraction,
    )
    from audit_program_m_interval_abundance import interval_abundance_profile
    from audit_program_m_interval_multiscale import three_layer_order


REPOSITORY_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_LOCALITY_REFERENCE = (
    REPOSITORY_ROOT / "outputs" / "program_m" / "mf_loc_003_conformal.json"
)
DEFAULT_DIMENSION_REFERENCE = (
    REPOSITORY_ROOT / "outputs" / "program_m" / "mf_dim_001_blind.json"
)


def _fingerprint(order: np.ndarray) -> str:
    packed = np.packbits(order.astype(np.uint8), bitorder="little")
    payload = order.shape[0].to_bytes(8, "little") + packed.tobytes()
    return hashlib.sha256(payload).hexdigest()


def validate_partial_order(order: np.ndarray) -> dict[str, bool]:
    matrix = np.asarray(order, dtype=bool)
    square = matrix.ndim == 2 and matrix.shape[0] == matrix.shape[1]
    if not square:
        return {"square": False, "reflexive": False, "antisymmetric": False, "transitive": False}
    reflexive = bool(np.all(np.diag(matrix)))
    off_diagonal_symmetric = matrix & matrix.T
    np.fill_diagonal(off_diagonal_symmetric, False)
    antisymmetric = not bool(np.any(off_diagonal_symmetric))
    row_bits = [
        sum(1 << int(index) for index in np.flatnonzero(row))
        for row in matrix
    ]
    transitive = True
    for source in range(matrix.shape[0]):
        for middle in np.flatnonzero(matrix[source]):
            if row_bits[int(middle)] & ~row_bits[source]:
                transitive = False
                break
        if not transitive:
            break
    return {
        "square": square,
        "reflexive": reflexive,
        "antisymmetric": antisymmetric,
        "transitive": transitive,
    }


def _load_json(path: Path) -> dict[str, object]:
    return json.loads(path.read_text(encoding="utf-8"))


def _json_fingerprint(payload: dict[str, object]) -> str:
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(canonical).hexdigest()


def load_order(path: Path) -> np.ndarray:
    if path.suffix.lower() == ".npy":
        return np.asarray(np.load(path, allow_pickle=False), dtype=bool)
    payload = json.loads(path.read_text(encoding="utf-8"))
    if isinstance(payload, dict):
        payload = payload["order"]
    return np.asarray(payload, dtype=bool)


def evaluate_order(
    order: np.ndarray,
    *,
    locality_reference: dict[str, object],
    dimension_reference: dict[str, object],
    source_name: str,
) -> dict[str, object]:
    matrix = np.asarray(order, dtype=bool)
    validation = validate_partial_order(matrix)
    valid = all(validation.values())
    report: dict[str, object] = {
        "program": "MF-GATE-001",
        "source_name": source_name,
        "elements": int(matrix.shape[0]) if matrix.ndim == 2 else None,
        "order_sha256": _fingerprint(matrix) if matrix.ndim == 2 else None,
        "input_interpretation": (
            "mathematical partial order with supplied orientation; physical causality not inferred"
        ),
        "partial_order_validation": validation,
        "reference_provenance": {
            "dimension_program": dimension_reference["program"],
            "dimension_protocol": dimension_reference["protocol"]["protocol_id"],
            "dimension_reference_sha256": _json_fingerprint(dimension_reference),
            "locality_program": locality_reference["program"],
            "locality_protocol": locality_reference["protocol"]["protocol_id"],
            "locality_reference_sha256": _json_fingerprint(locality_reference),
        },
        "claims_not_made": [
            "physical causality",
            "continuum manifold",
            "metric reconstruction",
            "geometric uniqueness",
            "Janus structure",
            "throat",
        ],
    }
    if not valid:
        report["status"] = "rejected_invalid_partial_order"
        return report

    estimate = myrheim_meyer_dimension(matrix)
    dimension_interval = dimension_reference["protocol"]["thresholds"]["individual_interval"]
    dimension_pass = dimension_interval[0] <= estimate <= dimension_interval[1]
    size_reference = next(
        (
            row
            for row in locality_reference["results"]
            if int(row["elements"]) == matrix.shape[0]
        ),
        None,
    )
    locality: dict[str, object]
    if size_reference is None:
        locality = {
            "supported": False,
            "reason": "no frozen conformal reference for this cardinality",
        }
    else:
        profile = interval_abundance_profile(
            matrix,
            int(locality_reference["protocol"]["maximum_explicit_interior_size"]),
        )
        centroid = np.asarray(size_reference["reference_centroid"], dtype=float)
        score = float(np.sum(np.abs(profile - centroid)))
        threshold = float(size_reference["frozen_threshold"])
        locality = {
            "supported": True,
            "score": score,
            "threshold": threshold,
            "accepted": score <= threshold,
            "reference_program": locality_reference["program"],
            "coverage_scope": locality_reference["guarantee_scope"],
        }
    report["diagnostics"] = {
        "ordering_fraction": ordering_fraction(matrix),
        "myrheim_meyer_dimension": {
            "estimate": estimate,
            "reference_interval": dimension_interval,
            "accepted": dimension_pass,
            "meaning": "compatibility with one flat-interval order invariant only",
        },
        "interval_abundance": locality,
        "number_volume": "not_tested_without_target_embedding",
        "chain_time": "not_tested_without_target_embedding",
    }
    if not locality["supported"]:
        report["status"] = "indeterminate_unsupported_cardinality"
    elif dimension_pass and locality["accepted"]:
        report["status"] = "compatible_with_external_minkowski2_diagnostics"
    else:
        report["status"] = "incompatible_with_external_minkowski2_diagnostics"
    return report


def _reference_payloads(
    locality_path: Path, dimension_path: Path
) -> tuple[dict[str, object], dict[str, object]]:
    return _load_json(locality_path), _load_json(dimension_path)


def example_reports(
    locality_reference: dict[str, object], dimension_reference: dict[str, object]
) -> dict[str, object]:
    size = 256
    rng = np.random.default_rng(2026090000)
    points = rng.random((size, 2))
    poisson_order = order_matrix_from_null_points(points)
    del points
    grid_points = np.array([(u, v) for u in range(16) for v in range(16)])
    grid_order = order_matrix_from_null_points(grid_points)
    del grid_points
    layered_order = three_layer_order(size, 2026095000)
    return {
        "program": "MF-GATE-001",
        "examples_use_order_only_after_generation": True,
        "reports": [
            evaluate_order(
                poisson_order,
                locality_reference=locality_reference,
                dimension_reference=dimension_reference,
                source_name="fresh_poisson_256",
            ),
            evaluate_order(
                grid_order,
                locality_reference=locality_reference,
                dimension_reference=dimension_reference,
                source_name="regular_grid_16x16",
            ),
            evaluate_order(
                layered_order,
                locality_reference=locality_reference,
                dimension_reference=dimension_reference,
                source_name="kr_type_three_layer_256",
            ),
        ],
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    source = parser.add_mutually_exclusive_group(required=True)
    source.add_argument("--order", type=Path)
    source.add_argument("--examples", action="store_true")
    parser.add_argument("--locality-reference", type=Path, default=DEFAULT_LOCALITY_REFERENCE)
    parser.add_argument("--dimension-reference", type=Path, default=DEFAULT_DIMENSION_REFERENCE)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    locality, dimension = _reference_payloads(
        args.locality_reference, args.dimension_reference
    )
    if args.examples:
        result = example_reports(locality, dimension)
    else:
        result = evaluate_order(
            load_order(args.order),
            locality_reference=locality,
            dimension_reference=dimension,
            source_name=str(args.order),
        )
    payload = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(payload, encoding="utf-8")
    else:
        print(payload, end="")


if __name__ == "__main__":
    main()
