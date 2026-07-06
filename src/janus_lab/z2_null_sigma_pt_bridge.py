"""Source-aligned null Sigma / PT bridge branch."""

from __future__ import annotations


def null_sigma_pt_bridge_source_alignment_payload() -> dict:
    return {
        "branch": "Z2_null_Sigma_PT_bridge",
        "active_core": "Z2_tunnel_Sigma",
        "source": "The_Janus_Cosmological_Model_chapters_6_7_and_EPJC_summary",
        "source_anchors": {
            "cross_term_not_staticity": "chapter 6, pages 177-181",
            "einstein_rosen_bridge_degenerate_throat": "chapter 6, pages 179-180, eqs 6.1.5-6.1.6",
            "eddington_cross_term_finite_infall": "chapter 6, page 181, eqs 6.3.2-6.3.3",
            "PT_sheets_orientation": "chapter 6, pages 182-184",
            "rho_fold_metrics": "chapter 6, page 185, eqs 6.4.1-6.4.4",
            "souriau_mass_energy_inversion": "chapter 6, page 186",
            "outgoing_second_sheet": "chapter 6, pages 188-189, eqs 6.7.1-6.7.4",
            "projective_topology": "chapter 7, pages 190-195",
            "published_wormhole_summary": "EPJC page 2 and conclusion, extracted pages 211 and 232",
        },
        "branch_claims": {
            "drdt_cross_term_retained": True,
            "one_way_membrane_interpretation": True,
            "two_PT_symmetric_sheets": True,
            "time_reversal_at_crossing": True,
            "orientation_reversal_at_crossing": True,
            "souriau_energy_mass_inversion_relevant": True,
            "projective_P4_tubular_context_relevant": True,
            "degenerate_or_null_throat_allowed": True,
        },
        "hard_separation_from_regular_sigma": {
            "regular_h_ab_K_ab_pipeline_allowed": False,
            "standard_GHY_Israel_Cartan_pipeline_allowed": False,
            "regular_counterterm_Lct_hK_allowed": False,
            "reason": "PDF branch permits degenerate/null throat data; regular Sigma requires invertible h_ab and unit normal.",
        },
        "required_null_formalism": {
            "null_generator_l_required": True,
            "auxiliary_null_normal_n_required": True,
            "screen_metric_q_AB_required": True,
            "expansion_theta_required": True,
            "shear_sigma_AB_required": True,
            "inaffinity_kappa_required": True,
            "null_corner_or_junction_terms_required": True,
            "null_Bianchi_transport_required": True,
        },
        "current_status": {
            "source_alignment_ready": True,
            "null_boundary_variables_declared": False,
            "null_action_variation_ready": False,
            "null_junction_balance_ready": False,
            "R_Sigma_certificate_ready": False,
            "observational_prediction_ready": False,
        },
        "next_required": [
            "declare null Sigma variables l,n,q_AB,theta,sigma_AB,kappa",
            "derive the null boundary/junction action replacing regular GHY",
            "transport the PT bridge orientation and time reversal into the null variables",
            "derive the null Bianchi balance across the Z2/PT bridge",
        ],
    }
