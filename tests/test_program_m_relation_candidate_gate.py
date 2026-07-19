import json
from pathlib import Path

import numpy as np

from scripts.evaluate_program_m_order_candidate import (
    DEFAULT_DIMENSION_REFERENCE,
    DEFAULT_LOCALITY_REFERENCE,
)
from scripts.evaluate_program_m_relation_candidate import (
    cyclic_refinement,
    example_reports,
    reflexive_transitive_closure,
    relation_to_skeleton,
)


def _references() -> tuple[dict[str, object], dict[str, object]]:
    return (
        json.loads(Path(DEFAULT_LOCALITY_REFERENCE).read_text(encoding="utf-8")),
        json.loads(Path(DEFAULT_DIMENSION_REFERENCE).read_text(encoding="utf-8")),
    )


def test_closure_adds_reflexivity_and_transitivity() -> None:
    relation = np.zeros((3, 3), dtype=bool)
    relation[0, 1] = True
    relation[1, 2] = True
    closure = reflexive_transitive_closure(relation)
    assert np.all(np.diag(closure))
    assert closure[0, 2]


def test_cycle_collapses_to_one_skeleton_object() -> None:
    cycle = np.array([[0, 1, 0], [0, 0, 1], [1, 0, 0]], dtype=bool)
    decomposition = relation_to_skeleton(cycle)
    assert decomposition["audit"]["skeleton_objects"] == 1
    assert decomposition["audit"]["collapsed_objects"] == 2
    assert decomposition["quotient"].tolist() == [[True]]


def test_cyclic_refinement_preserves_quotient_but_not_primitive_relation() -> None:
    relation = np.zeros((4, 4), dtype=bool)
    relation[0, 1] = relation[1, 2] = relation[2, 3] = True
    refined = cyclic_refinement(relation)
    base = relation_to_skeleton(relation)
    lifted = relation_to_skeleton(refined)
    assert np.array_equal(base["quotient"], lifted["quotient"])
    assert base["audit"]["primitive_relation_sha256"] != (
        lifted["audit"]["primitive_relation_sha256"]
    )
    assert lifted["audit"]["nontrivial_mutual_reachability_fibers"] == 1


def test_end_to_end_examples_expose_downstream_collision() -> None:
    locality, dimension = _references()
    examples = example_reports(locality, dimension)
    assert all(examples["downstream_collision"].values())
    assert all(
        report["status"] == "compatible_with_external_minkowski2_diagnostics"
        for report in examples["reports"]
    )
