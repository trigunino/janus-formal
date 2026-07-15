from scripts.audit_bimetric_adm_bd_constraint import build_payload


def test_candidate_matches_hr_bulk_class_and_removes_bd_pair():
    payload = build_payload()
    assert all(payload["candidate_match"].values())
    assert payload["closure"]["bd_scalar_pair_removed"]
    assert payload["count"]["physical_phase_dimension"] == 14
    assert payload["count"]["configuration_degrees_of_freedom"] == 7


def test_domain_and_mechanization_limits_are_not_hidden():
    closure = build_payload()["closure"]
    assert not closure["full_functional_bracket_mechanized_in_repo"]
    assert not closure["global_square_root_domain_proved"]
    assert not closure["shift_map_global_invertibility_proved"]
