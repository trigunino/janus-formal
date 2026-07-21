from scripts.audit_program_m_pairwise_refinement import run_audit


def test_pairwise_refinement_is_exact_uniqueness_criterion() -> None:
    audit = run_audit()
    assert audit["protocol"]["atlas_families"] == 256
    assert audit["failures"] == 0
    assert all(audit["gates"].values())
    assert audit["mf_geo_002_witness"] == {
        "original_pair_covered": False,
        "after_adding_2_3_patch": True,
    }
