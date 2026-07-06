"""Published Janus SO(3)/TOV/Newtonian reduced Bianchi status."""

from __future__ import annotations


def published_so3_bianchi_reduction_payload() -> dict:
    interaction_terms = {
        "positive_source_positive_test": {
            "sector": "plus",
            "test_body": "plus",
            "force_sign": "attractive",
            "status": "Newtonian/TOV reduced",
        },
        "negative_source_negative_test": {
            "sector": "minus",
            "test_body": "minus",
            "force_sign": "attractive",
            "status": "Newtonian/TOV reduced",
        },
        "positive_source_negative_test": {
            "sector": "cross",
            "test_body": "minus",
            "force_sign": "repulsive",
            "status": "Newtonian/TOV reduced",
        },
        "negative_source_positive_test": {
            "sector": "cross",
            "test_body": "plus",
            "force_sign": "repulsive",
            "status": "Newtonian/TOV reduced",
        },
    }
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "The_Janus_Cosmological_Model_stationary_SO3_TOV_Newtonian_reduction",
        "reference_pages": {
            "weak_field_stationary": "96-121",
            "EPJC_Bianchi_status": "226-232",
        },
        "reduction_type": "stationary_SO3_Newtonian_TOV_asymptotic",
        "interaction_terms": interaction_terms,
        "same_sector_attraction_ready": True,
        "opposite_sector_repulsion_ready": True,
        "determinant_ratio_weak_field_unity": True,
        "tov_newtonian_bianchi_asymptotic_ready": True,
        "stationary_so3_reduced_bianchi_ready": True,
        "generic_tensor_bianchi_ready": False,
        "sigma_transport_ready": False,
        "sigma_source_available": False,
        "active_embedding_ready": False,
        "full_no_fit_prediction_ready": False,
        "allowed_use": [
            "compact-object sign dynamics diagnostic",
            "stationary SO(3) source-slot sanity check",
            "input target for future active throat embedding comparison",
        ],
        "non_claims": [
            "not exact nonlinear interaction tensor",
            "not generic Bianchi closure",
            "not Sigma junction source",
            "not R_Sigma solution certificate",
            "not surface counterterm closure",
            "not observational prediction",
        ],
        "next_required": [
            "derive active SO(3) throat embedding X_plus/X_minus(R)",
            "pull back determinant bridges on Sigma",
            "derive DeltaK_s(R) and DeltaK_tau(R) from embedding",
            "compare reduced source force with Sigma radial balance",
        ],
    }
