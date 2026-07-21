"""MF-ADV-001: fresh adversarial search against the combined order-only gates."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import numpy as np

try:
    from scripts.audit_program_m_intrinsic_link_fluctuations import (
        intrinsic_link_fluctuation,
    )
    from scripts.evaluate_program_m_order_candidate import (
        DEFAULT_DIMENSION_REFERENCE,
        DEFAULT_LOCALITY_REFERENCE,
        evaluate_order,
    )
except ModuleNotFoundError:  # Direct `python scripts/...py` execution.
    from audit_program_m_intrinsic_link_fluctuations import intrinsic_link_fluctuation
    from evaluate_program_m_order_candidate import (
        DEFAULT_DIMENSION_REFERENCE,
        DEFAULT_LOCALITY_REFERENCE,
        evaluate_order,
    )


DEFAULT_LINK_REFERENCE = Path(
    "outputs/program_m/mf_man_015_intrinsic_link_fluctuations.json"
)

PROTOCOL = {
    "protocol_id": "MF-ADV-001-v1",
    "cardinality": 256,
    "base_seed": 2026102100,
    "replicates_per_parameter": 20,
    "forward_dag_probabilities": [
        0.0005,
        0.001,
        0.002,
        0.003,
        0.005,
        0.008,
        0.01,
        0.015,
        0.02,
        0.03,
        0.05,
        0.08,
    ],
    "three_layer_probabilities": [0.005, 0.01, 0.02, 0.05, 0.1, 0.2, 0.4, 0.8],
    "three_layer_sizes": [64, 128, 64],
    "pilot_seeds_excluded": True,
}


def reflexive_transitive_closure(forward_edges: np.ndarray) -> np.ndarray:
    edges = np.asarray(forward_edges, dtype=bool)
    size = edges.shape[0]
    rows = [1 << index for index in range(size)]
    for source in range(size - 1, -1, -1):
        for raw_target in np.flatnonzero(edges[source]):
            rows[source] |= rows[int(raw_target)]
    closure = np.zeros((size, size), dtype=bool)
    for source, bits in enumerate(rows):
        closure[source] = [bool(bits & (1 << target)) for target in range(size)]
    return closure


def random_forward_dag(cardinality: int, probability: float, seed: int) -> np.ndarray:
    rng = np.random.default_rng(seed)
    edges = np.triu(rng.random((cardinality, cardinality)) < probability, 1)
    return reflexive_transitive_closure(edges)


def random_three_layer_order(probability: float, seed: int) -> np.ndarray:
    lower, middle, upper = PROTOCOL["three_layer_sizes"]
    size = lower + middle + upper
    rng = np.random.default_rng(seed)
    edges = np.zeros((size, size), dtype=bool)
    edges[:lower, lower : lower + middle] = (
        rng.random((lower, middle)) < probability
    )
    edges[lower : lower + middle, lower + middle :] = (
        rng.random((middle, upper)) < probability
    )
    return reflexive_transitive_closure(edges)


def _load(path: Path) -> dict[str, object]:
    return json.loads(path.read_text(encoding="utf-8"))


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def adversarial_order_audit(
    *,
    link_reference_path: Path = DEFAULT_LINK_REFERENCE,
    locality_reference_path: Path = DEFAULT_LOCALITY_REFERENCE,
    dimension_reference_path: Path = DEFAULT_DIMENSION_REFERENCE,
) -> dict[str, object]:
    link_reference = _load(link_reference_path)
    locality_reference = _load(locality_reference_path)
    dimension_reference = _load(dimension_reference_path)
    cardinality = int(PROTOCOL["cardinality"])
    reference_row = next(
        row for row in link_reference["rows"] if row["cardinality"] == cardinality
    )
    link_lower, link_upper = reference_row["acceptance_interval"]
    families = [
        ("random_forward_dag", PROTOCOL["forward_dag_probabilities"]),
        ("random_three_layer", PROTOCOL["three_layer_probabilities"]),
    ]
    rows = []
    first_link_collision = None
    first_combined_collision = None
    for family_index, (family, probabilities) in enumerate(families):
        for parameter_index, probability in enumerate(probabilities):
            counts = {
                "generated": 0,
                "link_fluctuation_accepted": 0,
                "dimension_accepted": 0,
                "locality_accepted": 0,
                "dimension_and_locality_accepted": 0,
                "all_three_accepted": 0,
            }
            for replicate in range(int(PROTOCOL["replicates_per_parameter"])):
                seed = (
                    int(PROTOCOL["base_seed"])
                    + 1_000_000 * family_index
                    + 10_000 * parameter_index
                    + replicate
                )
                order = (
                    random_forward_dag(cardinality, probability, seed)
                    if family == "random_forward_dag"
                    else random_three_layer_order(probability, seed)
                )
                link_score = intrinsic_link_fluctuation(order)
                link_accepted = link_lower <= link_score <= link_upper
                report = evaluate_order(
                    order,
                    locality_reference=locality_reference,
                    dimension_reference=dimension_reference,
                    source_name=f"{family}:p={probability}:seed={seed}",
                )
                dimension_accepted = bool(
                    report["diagnostics"]["myrheim_meyer_dimension"]["accepted"]
                )
                locality_accepted = bool(
                    report["diagnostics"]["interval_abundance"]["accepted"]
                )
                combined = dimension_accepted and locality_accepted
                all_three = link_accepted and combined
                counts["generated"] += 1
                counts["link_fluctuation_accepted"] += int(link_accepted)
                counts["dimension_accepted"] += int(dimension_accepted)
                counts["locality_accepted"] += int(locality_accepted)
                counts["dimension_and_locality_accepted"] += int(combined)
                counts["all_three_accepted"] += int(all_three)
                witness = {
                    "family": family,
                    "probability": probability,
                    "seed": seed,
                    "order_sha256": report["order_sha256"],
                    "link_score": link_score,
                    "link_interval": [link_lower, link_upper],
                    "dimension": report["diagnostics"]["myrheim_meyer_dimension"],
                    "locality": report["diagnostics"]["interval_abundance"],
                }
                if link_accepted and first_link_collision is None:
                    first_link_collision = witness
                if all_three and first_combined_collision is None:
                    first_combined_collision = witness
            rows.append(
                {"family": family, "edge_probability": probability, **counts}
            )
    totals = {
        key: sum(row[key] for row in rows)
        for key in (
            "generated",
            "link_fluctuation_accepted",
            "dimension_accepted",
            "locality_accepted",
            "dimension_and_locality_accepted",
            "all_three_accepted",
        )
    }
    return {
        "program": "MF-ADV-001",
        "protocol": PROTOCOL,
        "references": {
            "link": {"path": str(link_reference_path), "sha256": _sha256(link_reference_path)},
            "locality": {
                "path": str(locality_reference_path),
                "sha256": _sha256(locality_reference_path),
            },
            "dimension": {
                "path": str(dimension_reference_path),
                "sha256": _sha256(dimension_reference_path),
            },
        },
        "construction_provenance": (
            "random forward DAGs and random three-layer orders; no target geometry "
            "or coordinates used in generation"
        ),
        "rows": rows,
        "totals": totals,
        "first_link_only_collision": first_link_collision,
        "first_combined_collision": first_combined_collision,
        "conclusion": (
            "MF-MAN-015 alone has many adversarial collisions; the frozen DIM/LOC "
            "intersection rejects every candidate in this finite search"
        ),
        "claims_not_made": [
            "exhaustiveness over all non-geometric orders",
            "proof that every generated order is non-manifoldlike",
            "sufficiency of the combined gates",
        ],
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    payload = json.dumps(adversarial_order_audit(), indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(payload, encoding="utf-8")
    else:
        print(payload, end="")


if __name__ == "__main__":
    main()
