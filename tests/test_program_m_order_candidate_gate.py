import json
from pathlib import Path

import numpy as np

from scripts.evaluate_program_m_order_candidate import (
    DEFAULT_DIMENSION_REFERENCE,
    DEFAULT_LOCALITY_REFERENCE,
    evaluate_order,
    example_reports,
    validate_partial_order,
)


def _references() -> tuple[dict[str, object], dict[str, object]]:
    return (
        json.loads(Path(DEFAULT_LOCALITY_REFERENCE).read_text(encoding="utf-8")),
        json.loads(Path(DEFAULT_DIMENSION_REFERENCE).read_text(encoding="utf-8")),
    )


def test_invalid_relation_is_rejected_before_diagnostics() -> None:
    cycle = np.array([[1, 1, 0], [0, 1, 1], [1, 0, 1]], dtype=bool)
    locality, dimension = _references()
    report = evaluate_order(
        cycle,
        locality_reference=locality,
        dimension_reference=dimension,
        source_name="cycle",
    )
    assert validate_partial_order(cycle)["transitive"] is False
    assert report["status"] == "rejected_invalid_partial_order"
    assert "diagnostics" not in report


def test_report_is_relabelling_invariant_except_identity_metadata() -> None:
    chain = np.triu(np.ones((128, 128), dtype=bool))
    permutation = np.random.default_rng(1).permutation(128)
    relabelled = chain[np.ix_(permutation, permutation)]
    locality, dimension = _references()
    first = evaluate_order(
        chain, locality_reference=locality, dimension_reference=dimension, source_name="a"
    )
    second = evaluate_order(
        relabelled,
        locality_reference=locality,
        dimension_reference=dimension,
        source_name="b",
    )
    assert first["status"] == second["status"]
    assert first["diagnostics"] == second["diagnostics"]


def test_unsupported_cardinality_is_explicit() -> None:
    chain = np.triu(np.ones((8, 8), dtype=bool))
    locality, dimension = _references()
    report = evaluate_order(
        chain, locality_reference=locality, dimension_reference=dimension, source_name="small"
    )
    assert report["status"] == "indeterminate_unsupported_cardinality"


def test_fresh_examples_separate_poisson_from_controls() -> None:
    locality, dimension = _references()
    reports = {
        report["source_name"]: report
        for report in example_reports(locality, dimension)["reports"]
    }
    assert reports["fresh_poisson_256"]["status"] == (
        "compatible_with_external_minkowski2_diagnostics"
    )
    assert reports["regular_grid_16x16"]["status"] == (
        "incompatible_with_external_minkowski2_diagnostics"
    )
    assert reports["kr_type_three_layer_256"]["status"] == (
        "incompatible_with_external_minkowski2_diagnostics"
    )
