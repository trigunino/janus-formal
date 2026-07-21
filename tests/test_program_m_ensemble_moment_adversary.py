from fractions import Fraction

from scripts.audit_program_m_ensemble_moment_adversary import PROTOCOL, run_audit


def test_mixture_matches_pair_and_three_chain_moments_exactly() -> None:
    weights = PROTOCOL["mixture_weights"]
    total_weight = Fraction(weights["total_order"]).limit_denominator()
    two_level_weight = Fraction(weights["two_level"]).limit_denominator()
    assert total_weight + two_level_weight / 2 == Fraction(1, 2)
    assert total_weight == Fraction(1, 6)


def test_stratification_realizes_declared_weights() -> None:
    counts = PROTOCOL["stratified_replicates"]
    total = sum(counts.values())
    for name, weight in PROTOCOL["mixture_weights"].items():
        assert Fraction(counts[name], total) == Fraction(weight).limit_denominator()


def test_frozen_gate_rejects_moment_matched_adversary() -> None:
    audit = run_audit()
    assert all(audit["gates"].values())
