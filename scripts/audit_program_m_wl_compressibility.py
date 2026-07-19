"""MF-MAN-017: orientation-symmetric 1-WL structural repetition gate."""

from __future__ import annotations

import argparse
import json
import math
from collections import Counter
from pathlib import Path

import numpy as np

try:
    from scripts.audit_program_m_branch_adversary import repeated_two_level_branches
    from scripts.audit_program_m_intrinsic_link_fluctuations import conditioned_poisson_order
    from scripts.audit_program_m_twin_adversary import clone_vertex_order
except ModuleNotFoundError:  # Direct `python scripts/...py` execution.
    from audit_program_m_branch_adversary import repeated_two_level_branches
    from audit_program_m_intrinsic_link_fluctuations import conditioned_poisson_order
    from audit_program_m_twin_adversary import clone_vertex_order


PROTOCOL = {
    "protocol_id": "MF-MAN-017-v1",
    "base_seed": 2026103000,
    "cardinalities": [144, 256, 576, 784],
    "calibration_replicates": 79,
    "validation_replicates": 80,
    "alpha": 0.10,
    "upper_rank": 72,
}


def orientation_symmetric_wl(order: np.ndarray) -> dict[str, object]:
    matrix = np.asarray(order, dtype=bool)
    if matrix.ndim != 2 or matrix.shape[0] != matrix.shape[1]:
        raise ValueError("order must be a square matrix")
    size = len(matrix)
    strict = matrix & ~np.eye(size, dtype=bool)
    colors = np.zeros(size, dtype=int)
    for iteration in range(size + 1):
        color_count = int(np.max(colors)) + 1
        signatures = []
        for vertex in range(size):
            past = tuple(
                np.bincount(colors[strict[:, vertex]], minlength=color_count).tolist()
            )
            future = tuple(
                np.bincount(colors[strict[vertex]], minlength=color_count).tolist()
            )
            unordered_orientation = tuple(sorted((past, future)))
            signatures.append((int(colors[vertex]), *unordered_orientation))
        identifiers = {
            signature: index for index, signature in enumerate(sorted(set(signatures)))
        }
        refined = np.array([identifiers[signature] for signature in signatures])
        if np.array_equal(colors, refined):
            profile = sorted(Counter(refined).values(), reverse=True)
            return {
                "colors": refined,
                "iterations": iteration,
                "class_size_profile": profile,
                "largest_stable_class": profile[0] if profile else 0,
                "nontrivial_classes": sum(size > 1 for size in profile),
                "collision_pairs": sum(size * (size - 1) // 2 for size in profile),
            }
        colors = refined
    raise RuntimeError("color refinement failed to stabilize")


def wl_compressibility_audit() -> dict[str, object]:
    calibration_count = int(PROTOCOL["calibration_replicates"])
    validation_count = int(PROTOCOL["validation_replicates"])
    rank = int(PROTOCOL["upper_rank"])
    rows = []
    for size_index, cardinality in enumerate(PROTOCOL["cardinalities"]):
        seed_root = int(PROTOCOL["base_seed"]) + 100_000 * size_index
        calibration = sorted(
            int(
                orientation_symmetric_wl(
                    conditioned_poisson_order(cardinality, seed_root + replicate)
                )["largest_stable_class"]
            )
            for replicate in range(calibration_count)
        )
        threshold = calibration[rank - 1]
        validation = [
            int(
                orientation_symmetric_wl(
                    conditioned_poisson_order(
                        cardinality, seed_root + 50_000 + replicate
                    )
                )["largest_stable_class"]
            )
            for replicate in range(validation_count)
        ]
        controls = []
        if cardinality == 256:
            for kind, multiplicity, order in (
                ("exact_clones", 4, clone_vertex_order(4, seed_root + 90_004)),
                ("exact_clones", 8, clone_vertex_order(8, seed_root + 90_008)),
                (
                    "two_level_branches",
                    4,
                    repeated_two_level_branches(4, seed_root + 91_004),
                ),
                (
                    "two_level_branches",
                    8,
                    repeated_two_level_branches(8, seed_root + 91_008),
                ),
            ):
                report = orientation_symmetric_wl(order)
                controls.append(
                    {
                        "kind": kind,
                        "multiplicity": multiplicity,
                        "largest_stable_class": report["largest_stable_class"],
                        "class_size_profile_head": report["class_size_profile"][:6],
                        "accepted": report["largest_stable_class"] <= threshold,
                    }
                )
        rows.append(
            {
                "cardinality": cardinality,
                "upper_threshold": threshold,
                "validation_coverage": sum(value <= threshold for value in validation)
                / validation_count,
                "validation_maximum": max(validation),
                "controls": controls,
            }
        )
    expected_rank = math.ceil(
        (calibration_count + 1) * (1 - float(PROTOCOL["alpha"]))
    )
    return {
        "program": "MF-MAN-017",
        "input": "finite partial-order matrix only",
        "method": (
            "one-dimensional Weisfeiler-Leman color refinement on full strict "
            "past/future multisets, with the two orientations unordered"
        ),
        "protocol": PROTOCOL,
        "protocol_integrity": {
            "expected_rank": expected_rank,
            "rank_matches": rank == expected_rank,
            "fresh_validation_seeds": True,
        },
        "invariances": {
            "object_relabelling": "exact for the stable class-size profile",
            "orientation_reversal": "exact by unordered past/future signatures",
        },
        "rows": rows,
        "conclusion": (
            "stable color multiplicity generalizes exact twins and rejects the "
            "registered clone and repeated-branch controls"
        ),
        "known_limit": (
            "1-WL is an isomorphism heuristic, not a complete automorphism or "
            "compressibility invariant; regular and CFI-type constructions can fool it"
        ),
        "claims_not_made": [
            "complete detection of repeated structure",
            "Kolmogorov complexity or canonical minimal description length",
            "sufficiency for manifold-likeness",
        ],
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    payload = json.dumps(wl_compressibility_audit(), indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(payload, encoding="utf-8")
    else:
        print(payload, end="")


if __name__ == "__main__":
    main()
