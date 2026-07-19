from scripts.audit_program_m_interval_conformal import (
    PROTOCOL,
    conformal_threshold,
    run_audit,
)


def test_conformal_rank_for_preregistered_calibration_size() -> None:
    scores = [float(index) for index in range(39)]
    threshold, rank = conformal_threshold(scores, 0.10)
    assert rank == 36
    assert threshold == 35.0
    assert rank / 40 == 0.90


def test_fresh_seed_partitions_are_pairwise_disjoint() -> None:
    for index, _ in enumerate(PROTOCOL["sizes"]):
        base = int(PROTOCOL["base_seed"]) + index * int(PROTOCOL["scale_seed_stride"])
        reference = set(range(base, base + int(PROTOCOL["reference_replicates_per_size"])))
        calibration_base = base + int(PROTOCOL["calibration_seed_offset"])
        calibration = set(
            range(calibration_base, calibration_base + int(PROTOCOL["calibration_replicates_per_size"]))
        )
        validation_base = base + int(PROTOCOL["validation_seed_offset"])
        validation = set(
            range(validation_base, validation_base + int(PROTOCOL["validation_replicates_per_size"]))
        )
        assert reference.isdisjoint(calibration)
        assert reference.isdisjoint(validation)
        assert calibration.isdisjoint(validation)


def test_conformal_multiscale_gates_are_recorded() -> None:
    audit = run_audit()
    assert audit["protocol"] == PROTOCOL
    assert audit["gates"]["all_preregistered_gates"] is True
