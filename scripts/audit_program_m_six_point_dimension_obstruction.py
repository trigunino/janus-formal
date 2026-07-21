"""MF-REP-002: first intrinsic obstruction to a two-order representation."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import numpy as np

try:
    from scripts.audit_program_m_decorated_layer_adversary import decorated_layer_order
    from scripts.audit_program_m_ensemble_separation import minkowski_order
    from scripts.audit_program_m_three_symmetric_permuton import three_symmetric_permuton_order
except ModuleNotFoundError:
    from audit_program_m_decorated_layer_adversary import decorated_layer_order
    from audit_program_m_ensemble_separation import minkowski_order
    from audit_program_m_three_symmetric_permuton import three_symmetric_permuton_order


PROTOCOL = {
    "protocol_id": "MF-REP-002-v1",
    "rank": 6,
    "base_seed": 2026071812,
    "batches": 32,
    "samples_per_batch": 8192,
    "models_fixed_before_sampling": [
        "minkowski_1p1", "three_symmetric_permuton", "decorated_layer", "product_order_3d"
    ],
}


def product_order_3d(size: int, rng: np.random.Generator) -> np.ndarray:
    points = rng.random((size, 3))
    return np.all(points[:, None, :] <= points[None, :, :], axis=2)


def is_standard_s3(order: np.ndarray) -> bool:
    """Recognize S3 without labels: three minima, three maxima, missing matching."""
    strict = np.asarray(order, dtype=bool).copy()
    np.fill_diagonal(strict, False)
    return bool(
        np.count_nonzero(strict) == 6
        and sorted(np.count_nonzero(strict, axis=1).tolist()) == [0, 0, 0, 2, 2, 2]
        and sorted(np.count_nonzero(strict, axis=0).tolist()) == [0, 0, 0, 2, 2, 2]
    )


def run_audit() -> dict[str, object]:
    models = (
        ("minkowski_1p1", minkowski_order),
        ("three_symmetric_permuton", three_symmetric_permuton_order),
        ("decorated_layer", decorated_layer_order),
        ("product_order_3d", product_order_3d),
    )
    rows = []
    for model_index, (name, generator) in enumerate(models):
        counts = []
        for batch in range(int(PROTOCOL["batches"])):
            rng = np.random.default_rng(
                int(PROTOCOL["base_seed"]) + 1_000_000 * model_index + batch
            )
            counts.append(
                sum(
                    is_standard_s3(generator(int(PROTOCOL["rank"]), rng))
                    for _ in range(int(PROTOCOL["samples_per_batch"]))
                )
            )
        total = int(PROTOCOL["batches"]) * int(PROTOCOL["samples_per_batch"])
        rows.append(
            {
                "model": name,
                "samples": total,
                "s3_count": sum(counts),
                "s3_frequency": sum(counts) / total,
                "batches_with_s3": sum(count > 0 for count in counts),
            }
        )
    by_model = {row["model"]: row for row in rows}
    return {
        "program": "MF-REP-002",
        "protocol": PROTOCOL,
        "rows": rows,
        "gates": {
            "minkowski_has_no_s3": by_model["minkowski_1p1"]["s3_count"] == 0,
            "nonuniform_two_order_adversary_has_no_s3":
                by_model["three_symmetric_permuton"]["s3_count"] == 0,
            "three_coordinate_control_has_s3": by_model["product_order_3d"]["s3_count"] > 0,
        },
        "scope": (
            "S3 is a sufficient witness of dimension above two, not a complete "
            "finite forbidden-pattern characterization of two-dimensional posets"
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
