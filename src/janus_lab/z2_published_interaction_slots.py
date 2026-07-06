"""Published Janus bimetric interaction-slot reduction."""

from __future__ import annotations


def published_interaction_slots_payload() -> dict:
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "The_Janus_Cosmological_Model_published_bimetric_action",
        "reference_pages": {
            "action_variation": "73-81",
            "epjc_action": "223-226",
            "bianchi": "226-232",
        },
        "published_slots": {
            "S_plus": "same-sector plus matter action",
            "S_minus": "same-sector minus matter action",
            "S_cross_plus_from_minus": "interaction action inducing minus source in plus equation",
            "S_cross_minus_from_plus": "interaction action inducing plus source in minus equation",
        },
        "active_projection": {
            "T_plus": "delta S_plus / delta g_plus",
            "T_minus": "delta S_minus / delta g_minus",
            "T_minus_to_plus": "delta S_cross_plus_from_minus / delta g_plus",
            "T_plus_to_minus": "delta S_cross_minus_from_plus / delta g_minus",
            "B_minus_to_plus": "sqrt(abs(g_minus)/abs(g_plus))",
            "B_plus_to_minus": "sqrt(abs(g_plus)/abs(g_minus))",
        },
        "equation_skeleton": {
            "plus": "G_plus = kappa_J * (T_plus - B_minus_to_plus*T_minus_to_plus) + J_Sigma_plus",
            "minus": "G_minus = kappa_J * (T_minus - B_plus_to_minus*T_plus_to_minus) + J_Sigma_minus",
        },
        "bianchi_obligations": {
            "plus": "D_plus RHS_plus = 0",
            "minus": "D_minus RHS_minus = 0",
            "published_status": "checked in FLRW/Newtonian/TOV sectors, not full nonlinear tensor",
        },
        "interaction_tensor_complete_nonlinear_form_available": False,
        "sigma_source_available": False,
        "reduced_bianchi_closure_ready": False,
        "can_transport_to_sigma": False,
        "full_no_fit_prediction_ready": False,
        "forbidden_shortcuts": [
            "rho_eff collapse",
            "negative thermodynamic density postulate",
            "free interaction tensor without Bianchi",
            "local Sigma counterterm before reduced source closure",
        ],
    }
