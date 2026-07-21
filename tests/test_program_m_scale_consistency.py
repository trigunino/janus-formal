from fractions import Fraction

from scripts.audit_program_m_scale_consistency import scale_consistency_audit


def test_dimensionless_consistency_does_not_select_small_ambiguities() -> None:
    audit = scale_consistency_audit(5)
    row4, row5 = audit["rows"][3:]
    assert row4["metric_ambiguous_classes"] == 1
    assert row4["same_consistency_within_class"] == 1
    assert row5["metric_ambiguous_classes"] == 10
    assert row5["same_consistency_within_class"] == 10
    assert row5["uniquely_closest_classes"] == 0


def test_no_small_ambiguous_class_exactly_passes_asymptotic_identity() -> None:
    rows = scale_consistency_audit(5)["rows"]
    assert all(row["classes_with_exact_asymptotic_identity"] == 0 for row in rows)


def test_first_witness_candidates_have_equal_exact_consistency() -> None:
    candidates = scale_consistency_audit(5)["first_ambiguous_witness"]["candidates"]
    values = {
        Fraction(*candidate["two_density_chain_scale_squared"])
        for candidate in candidates
    }
    assert values == {Fraction(8)}
