from scripts.enumerate_program_m_relations import (
    canonical_mask,
    compression_audit,
    compressed_signature,
    dimension_invariant_audit,
    minkowski_two_order_audit,
    minkowski_two_scaling_audit,
    order_invariants,
    product_order_embedding,
    enumerate_size,
    reflexive_transitive_closure,
    run,
    strongly_connected_components,
    standard_example_order,
)


def test_unlabelled_relation_counts_through_four_objects() -> None:
    # Number of binary relations up to simultaneous row/column permutation.
    assert [enumerate_size(n)["isomorphism_classes"] for n in range(1, 5)] == [
        2,
        10,
        104,
        3044,
    ]


def test_canonical_form_is_relabelling_invariant() -> None:
    chain = (1 << (0 * 3 + 1)) | (1 << (1 * 3 + 2))
    reversed_chain = (1 << (2 * 3 + 1)) | (1 << (1 * 3 + 0))
    assert canonical_mask(chain, 3) == canonical_mask(reversed_chain, 3)


def test_three_cycle_has_one_strong_component() -> None:
    cycle = (1 << 1) | (1 << 5) | (1 << 6)
    closure = reflexive_transitive_closure(cycle, 3)
    assert strongly_connected_components(closure, 3) == ((0, 1, 2),)


def test_audit_range_is_explicit() -> None:
    assert len(run(2)["results"]) == 2


def test_compression_is_invariant_under_relabelling() -> None:
    chain = (1 << (0 * 3 + 1)) | (1 << (1 * 3 + 2))
    reversed_chain = (1 << (2 * 3 + 1)) | (1 << (1 * 3 + 0))
    for level in ("bare_skeleton", "fiber_sizes", "bridge_existence", "edge_counts"):
        assert compressed_signature(chain, 3, level) == compressed_signature(
            reversed_chain, 3, level
        )


def test_even_edge_count_compression_has_collisions() -> None:
    audit = compression_audit(4)
    assert audit["edge_counts"]["signatures"] < 3044
    assert audit["edge_counts"]["first_collision_masks"] is not None


def test_chain_and_antichain_exact_invariants() -> None:
    chain_order = 0
    antichain_order = 0
    for source in range(3):
        for target in range(3):
            if source <= target:
                chain_order |= 1 << (source * 3 + target)
            if source == target:
                antichain_order |= 1 << (source * 3 + target)
    assert order_invariants(chain_order, 3)["height"] == 3
    assert order_invariants(chain_order, 3)["width"] == 1
    assert order_invariants(antichain_order, 3)["height"] == 1
    assert order_invariants(antichain_order, 3)["width"] == 3


def test_ordering_fraction_does_not_identify_four_element_order() -> None:
    audit = dimension_invariant_audit(4)
    assert audit["ordering_fraction_first_collision"] is not None


def test_three_chain_embeds_exactly_in_minkowski_two_product_order() -> None:
    audit = minkowski_two_order_audit()
    assert audit["positive"]["null_rank_coordinates"] is not None
    gate = audit["positive"]["finite_gate"]
    assert all(
        row["count_volume_abs_error"] == [1, 1]
        for row in gate["all_endpoint_diamonds"]
    )
    assert all(
        row["chain_time_abs_error"] == [0, 1]
        for row in gate["all_endpoint_diamonds"]
    )


def test_standard_example_s3_does_not_embed_in_two_product_orders() -> None:
    s3 = standard_example_order(3)
    assert product_order_embedding(s3, 6) is None
    assert minkowski_two_order_audit()["negative"]["null_rank_coordinates"] is None


def test_minkowski_two_scaling_separates_volume_and_time_failures() -> None:
    rows = minkowski_two_scaling_audit()["rows"]
    grid_errors = [numerator / denominator for numerator, denominator in (
        row["square_grid_full_volume_relative_error"] for row in rows
    )]
    diagonal_errors = [numerator / denominator for numerator, denominator in (
        row["diagonal_chain_full_volume_relative_error"] for row in rows
    )]
    anisotropies = [row["square_grid_two_to_one_chain_time_relative_error"] for row in rows]
    assert all(later < earlier for earlier, later in zip(grid_errors, grid_errors[1:]))
    assert diagonal_errors[-1] > 0.9
    assert all(abs(error - anisotropies[0]) < 1e-12 for error in anisotropies)
    assert anisotropies[0] > 0
