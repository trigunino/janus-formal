"""MF-GEO-002: test whether local metric uniqueness survives gluing."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

try:
    from scripts.audit_program_m_embedding_ambiguity import (
        interval_square_signature,
        product_order_realizers,
    )
except ModuleNotFoundError:
    from audit_program_m_embedding_ambiguity import (
        interval_square_signature,
        product_order_realizers,
    )


def induced_mask(mask: int, size: int, vertices: tuple[int, ...]) -> int:
    local_size = len(vertices)
    return sum(
        1 << (local_size * local_source + local_target)
        for local_source, source in enumerate(vertices)
        for local_target, target in enumerate(vertices)
        if mask & (1 << (size * source + target))
    )


def metric_class_count(mask: int, size: int) -> int:
    return len(
        {
            interval_square_signature(coordinates, mask, size)
            for coordinates in product_order_realizers(mask, size)
        }
    )


def run_audit() -> dict[str, object]:
    size = 4
    global_mask = sum(1 << (size * vertex + vertex) for vertex in range(size)) | (1 << 1)
    patches = ((0, 1, 2), (0, 1, 3))
    interface = (0, 1)
    patch_classes = [
        metric_class_count(induced_mask(global_mask, size, patch), len(patch))
        for patch in patches
    ]
    interface_classes = metric_class_count(
        induced_mask(global_mask, size, interface), len(interface)
    )
    global_classes = metric_class_count(global_mask, size)
    return {
        "program": "MF-GEO-002",
        "diagram": {
            "patches": [list(patch) for patch in patches],
            "shared_interface": list(interface),
            "every_primitive_pair_is_local": True,
            "unseen_pair": [2, 3],
        },
        "metric_class_counts": {
            "patches": patch_classes,
            "interface": interface_classes,
            "global": global_classes,
        },
        "gates": {
            "each_patch_is_locally_unique": all(count == 1 for count in patch_classes),
            "interface_is_unique": interface_classes == 1,
            "global_remains_ambiguous": global_classes > 1,
        },
        "conclusion": (
            "local metric uniqueness plus interface agreement does not select a "
            "unique global metric geometry"
        ),
        "missing_information": (
            "a rule controlling metric relations between points not jointly seen "
            "in any patch, or a refinement law that eventually observes every "
            "relevant pair"
        ),
        "scope": "exact finite no-go for the registered rank-metric reconstruction",
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
