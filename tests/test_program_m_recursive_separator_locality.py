import numpy as np

from scripts.audit_program_m_no_finite_dimension_cutoff import crown_order
from scripts.audit_program_m_recursive_separator_locality import (
    cover_graph,
    recursive_separator_certificate,
    run_audit,
)


def test_cover_graph_of_crown_is_a_cycle() -> None:
    graph = cover_graph(crown_order(7))
    assert np.all(np.count_nonzero(graph, axis=1) == 2)


def test_crown_has_recursive_width_two_certificate() -> None:
    graph = cover_graph(crown_order(8))
    assert recursive_separator_certificate(graph, max_width=2) is not None


def test_separator_locality_countermodel_passes() -> None:
    assert all(run_audit()["gates"].values())
