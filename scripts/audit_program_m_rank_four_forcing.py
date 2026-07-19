"""MF-PAT-003: rank-four unlabelled product-posets force a uniform permuton."""

from __future__ import annotations

import argparse
import itertools
import json
from collections import defaultdict
from pathlib import Path

import numpy as np

try:
    from scripts.audit_program_m_induced_patterns import canonical_mask, relation_mask
except ModuleNotFoundError:
    from audit_program_m_induced_patterns import canonical_mask, relation_mask


# The second Sigma-forcing set in Chan et al., arXiv:1909.11027, Theorem 2.
FORCING_SET = {
    "1234", "1432", "2143", "2341", "3214", "3412", "4123", "4321"
}


def permutation_text(permutation: tuple[int, ...]) -> str:
    return "".join(str(value + 1) for value in permutation)


def rank_four_poset_classes() -> dict[int, list[str]]:
    classes: dict[int, list[str]] = defaultdict(list)
    for permutation in itertools.permutations(range(4)):
        points = np.column_stack((np.arange(4), permutation))
        order = np.all(points[:, None, :] <= points[None, :, :], axis=2)
        classes[canonical_mask(relation_mask(order))].append(
            permutation_text(permutation)
        )
    return {key: sorted(value) for key, value in classes.items()}


def run_audit() -> dict[str, object]:
    classes = rank_four_poset_classes()
    selected = {
        key: patterns
        for key, patterns in classes.items()
        if set(patterns) <= FORCING_SET
    }
    selected_union = set().union(*(set(patterns) for patterns in selected.values()))
    all_patterns = [pattern for patterns in classes.values() for pattern in patterns]
    gates = {
        "sixteen_unlabelled_product_posets": len(classes) == 16,
        "twenty_four_permutations_partitioned_once":
            len(all_patterns) == 24 and len(set(all_patterns)) == 24,
        "published_forcing_set_is_union_of_poset_classes": selected_union == FORCING_SET,
        "forcing_set_has_eight_patterns": len(FORCING_SET) == 8,
    }
    return {
        "program": "MF-PAT-003",
        "literature_certificate": {
            "source": "Chan et al. arXiv:1909.11027, Theorem 2",
            "forcing_set": sorted(FORCING_SET),
            "uniform_target_sum": len(FORCING_SET) / 24,
        },
        "selected_poset_classes": {
            str(key): patterns for key, patterns in sorted(selected.items())
        },
        "selected_class_count": len(selected),
        "all_poset_classes": {
            str(key): patterns for key, patterns in sorted(classes.items())
        },
        "gates": gates,
        "conclusion": (
            "within continuous two-coordinate product orders, equality of the full "
            "unlabelled rank-four poset law implies the published forcing pattern "
            "sum and therefore forces the uniform permuton"
        ),
        "scope": (
            "does not prove rank-four uniqueness among arbitrary exchangeable poset "
            "kernels or derive the two-coordinate representation from weaker axioms"
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
