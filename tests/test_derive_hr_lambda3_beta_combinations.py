from scripts.derive_hr_lambda3_beta_combinations import build_payload


def test_beta_to_x_tensor_map_is_exact_in_all_components():
    payload = build_payload()
    assert payload["all_four_diagonal_component_identities"] == [True] * 4
    assert payload["closure"]["beta_to_X_mixing_map"]


def test_pt_branch_has_nonzero_cubic_mixing_and_fixed_ratio():
    pt = build_payload()["pt_branch"]
    assert pt["alpha1"] == "2*(b1 + b2)"
    assert pt["alpha2"] == "b1 + b2"
    assert pt["alpha2_over_alpha1"] == "1/2"
    assert pt["cubic_mixing_nonzero_on_positive_cone"]
