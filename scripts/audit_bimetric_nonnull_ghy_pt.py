from __future__ import annotations


def paired_ghy_factor(scale_ratio: float, orientation_parity: int,
                      curvature_parity: int) -> float:
    """Total density divided by the plus density for equal induced measures."""
    if orientation_parity not in (-1, 1) or curvature_parity not in (-1, 1):
        raise ValueError("PT parities must be signs")
    return 1 + scale_ratio * orientation_parity * curvature_parity


def pt_fixed_extrinsic_entry(value: float, transformed_value: float) -> dict:
    """At a PT-fixed throat, covariance plus normal reversal requires K=-K."""
    odd_covariant = transformed_value == -value
    fixed = transformed_value == value
    return {"pt_odd": odd_covariant, "pt_fixed": fixed,
            "forced_zero": odd_covariant and fixed and value == 0}


def build_payload() -> dict:
    return {
        "artifact": "bimetric_nonnull_ghy_pt",
        "density": "M^2 epsilon sqrt(abs(det h)) tr(h^{-1} K)",
        "program_p_inputs": {
            "canonical_throat_normal": "spacelike unit normal, n^2=+1",
            "local_second_fundamental_form": "K_ab=orientation_sign*(1/2)*partial_n h_ab",
            "dirichlet_variation": "delta(EH)+delta(GHY)=0 sector by sector",
        },
        "pt_law": {
            "paired_factor": "1+(M_minus^2/M_plus^2)*p_epsilon*p_K",
            "cancellation": "requires weighted parity product -1",
            "double_sign_reversal": "p_epsilon=p_K=-1 makes GHY PT-even, hence it adds",
            "fixed_throat_criterion": "if PT fixes the induced geometry and reverses the normal covariantly, K_ab=-K_ab and therefore K_ab=0",
        },
        "closure": {
            "nonnull_functional_selected_for_canonical_throat": True,
            "pt_parity_obstruction_classified": True,
            "cross_sheet_ghy_cancellation_generic": False,
            "sectorwise_eh_ghy_cancellation_available": True,
            "pt_fixed_total_geodesy_criterion_proved": True,
            "canonical_pt_covariance_of_extrinsic_curvature_proved": False,
            "canonical_throat_extrinsic_curvature_instantiated": False,
            "global_integrated_ghy_instantiated": False,
        },
    }
