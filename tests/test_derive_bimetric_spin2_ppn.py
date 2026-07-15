import sympy as sp

from scripts.derive_bimetric_spin2_ppn import C, S, build_payload, gamma_ppn, vainshtein_screening


def test_vdvz_and_equal_kinetic_limit():
    payload = build_payload()
    assert sp.simplify(gamma_ppn(1, 1) - sp.Rational(5, 7)) == 0
    assert payload["vdvz"]["pure_massive_gamma"] == "1/2"
    assert not payload["vdvz"]["linear_GR_limit_as_m_to_zero"]


def test_cross_scalar_cancellation_fails_with_full_spin2_projector():
    cross = build_payload()["cross_short_distance"]
    assert cross["Phi_factor"] == "-1/3"
    assert cross["Psi_factor"] == "1/3"
    assert not cross["scalar_kernel_cancellation_survives_spin2"]


def test_open_nonlinear_and_preferred_frame_work_is_explicit():
    closure = build_payload()["closure"]
    assert closure["linear_ppn_gamma"]
    assert closure["reduced_vainshtein_profile"]
    assert not closure["full_candidate_vainshtein_profile"]
    assert not closure["preferred_frame_ppn"]


def test_reduced_vainshtein_profile_solves_quadratic_branch():
    screening = vainshtein_screening()
    u = sp.factor(S * screening)
    assert sp.simplify(u + C * u**2 - S) == 0
    assert sp.limit(screening, S, 0, dir="+") == 1
    assert sp.limit(screening, S, sp.oo) == 0
