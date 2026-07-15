from scripts.derive_bimetric_minisuperspace_dirac_constraints import build_payload


def test_secondary_candidate_is_nontrivial_and_primary_preservation_closes_on_it():
    payload = build_payload()

    assert payload["secondary_is_nonzero_polynomial"]
    assert payload["sample_secondary"] != "0"
    assert payload["preservation"]["dot_C_plus_matches_Nminus_secondary"]
    assert payload["preservation"]["dot_C_minus_matches_minus_Nplus_secondary"]
    assert payload["local_constraint_rank_at_exact_sample"] == 3
    assert payload["local_secondary_independence_witnessed"]
    assert payload["constrained_sample_residuals"] == ["0", "0", "0"]


def test_full_bd_removal_is_not_overclaimed():
    closure = build_payload()["closure"]

    assert closure["primary_lapse_constraints_derived"]
    assert closure["primary_poisson_bracket_computed"]
    assert closure["secondary_candidate_derived"]
    assert not closure["secondary_independence_global_rank_proved"]
    assert closure["secondary_independence_local_rank_witnessed"]
    assert not closure["full_adm_shift_redefinition_included"]
    assert not closure["boulware_deser_mode_removed_in_full_field_theory"]
