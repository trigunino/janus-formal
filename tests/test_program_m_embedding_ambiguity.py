from scripts.audit_program_m_embedding_ambiguity import (
    ambiguity_audit,
    interval_square_signature,
    product_order_realizers,
)


def test_two_chain_plus_isolates_has_two_metric_classes() -> None:
    size = 4
    mask = sum(1 << (i * size + i) for i in range(size)) | (1 << 1)
    realizers = product_order_realizers(mask, size)
    signatures = {
        interval_square_signature(coordinates, mask, size)
        for coordinates in realizers
    }
    assert len(realizers) == 6
    assert len(signatures) == 2


def test_exhaustive_audit_finds_first_witness_at_four_objects() -> None:
    audit = ambiguity_audit(4)
    witness = audit["first_nonunique_witness"]
    assert witness["size"] == 4
    assert witness["strict_pairs"] == [[0, 1]]
    assert witness["metric_signature_count"] == 2
    assert audit["rows"][-1]["metric_ambiguous_classes"] > 0


def test_coordinate_exchange_does_not_change_signature() -> None:
    size = 4
    mask = sum(1 << (i * size + i) for i in range(size)) | (1 << 1)
    coordinates = product_order_realizers(mask, size)[0]
    exchanged = tuple((v, u) for u, v in coordinates)
    assert interval_square_signature(coordinates, mask, size) == (
        interval_square_signature(exchanged, mask, size)
    )
