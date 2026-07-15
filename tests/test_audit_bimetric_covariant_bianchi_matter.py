from scripts.audit_bimetric_covariant_bianchi_matter import build_payload


def test_native_conservation_and_interaction_identity_close():
    payload = build_payload()
    assert payload["closure"]["inhomogeneous_covariant_identity"]
    assert payload["closure"]["native_matter_conservation"]
    assert not payload["matter_shell"]["direct_cross_transport_required"]


def test_janus_cross_source_is_not_claimed_from_minimal_candidate():
    payload = build_payload()
    assert not payload["closure"]["janus_signed_cross_source_from_candidate_A"]
    assert len(payload["forbidden_extensions"]) == 3
