"""MF-SEP-002: target-compatibility audit for recursive separator width."""

from __future__ import annotations

import argparse
from collections import Counter
import json
from pathlib import Path

import numpy as np

try:
    from scripts.audit_program_m_ensemble_separation import minkowski_order
    from scripts.audit_program_m_recursive_separator_locality import (
        cover_graph,
        recursive_separator_certificate,
    )
    from scripts.audit_program_m_six_point_dimension_obstruction import product_order_3d
except ModuleNotFoundError:
    from audit_program_m_ensemble_separation import minkowski_order
    from audit_program_m_recursive_separator_locality import cover_graph, recursive_separator_certificate
    from audit_program_m_six_point_dimension_obstruction import product_order_3d


PROTOCOL = {
    "protocol_id": "MF-SEP-002-v1",
    "base_seed": 2026071822,
    "ranks": [8, 12, 16],
    "replicates": 128,
    "maximum_width_searched": 6,
}


def minimum_recursive_width(order: np.ndarray, maximum: int = 6) -> int | None:
    graph = cover_graph(order)
    return next(
        (
            width for width in range(maximum + 1)
            if recursive_separator_certificate(graph, width) is not None
        ),
        None,
    )


def run_audit() -> dict[str, object]:
    models = (("minkowski_1p1", minkowski_order), ("product_order_3d", product_order_3d))
    rows = []
    for model_index, (name, generator) in enumerate(models):
        rank_rows = []
        for rank in PROTOCOL["ranks"]:
            widths = []
            for replicate in range(int(PROTOCOL["replicates"])):
                rng = np.random.default_rng(
                    int(PROTOCOL["base_seed"]) + model_index * 1_000_000 + rank * 10_000 + replicate
                )
                widths.append(
                    minimum_recursive_width(
                        generator(rank, rng), int(PROTOCOL["maximum_width_searched"])
                    )
                )
            rank_rows.append(
                {
                    "rank": rank,
                    "width_histogram": {
                        str(key): value for key, value in sorted(
                            Counter(widths).items(), key=lambda item: (item[0] is None, item[0] or 0)
                        )
                    },
                    "width_at_most_two": sum(width is not None and width <= 2 for width in widths),
                    "replicates": len(widths),
                }
            )
        rows.append({"model": name, "ranks": rank_rows})
    target = next(row for row in rows if row["model"] == "minkowski_1p1")
    target_rank_16 = next(row for row in target["ranks"] if row["rank"] == 16)
    return {
        "program": "MF-SEP-002",
        "protocol": PROTOCOL,
        "rows": rows,
        "gates": {
            "fixed_width_two_rejects_some_target_samples_at_rank_16":
                target_rank_16["width_at_most_two"] < target_rank_16["replicates"],
            "all_samples_receive_a_width_certificate": all(
                "None" not in rank_row["width_histogram"]
                for row in rows for rank_row in row["ranks"]
            ),
        },
        "conclusion": (
            "fixed recursive separator width two is not target-compatible and "
            "cannot serve as a necessary axiom for Minkowski 1+1"
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    payload = json.dumps(run_audit(), indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(payload, encoding="utf-8")
    else:
        print(payload, end="")


if __name__ == "__main__":
    main()
