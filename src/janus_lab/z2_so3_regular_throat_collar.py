"""Regular SO(3) throat collar requirements for the active Z2/Sigma branch."""

from __future__ import annotations

from src.janus_lab.z2_so3_throat_embedding import so3_throat_embedding_manifest


def regular_throat_collar_frontier_payload() -> dict:
    manifest = so3_throat_embedding_manifest()
    return {
        "active_core": "Z2_tunnel_Sigma",
        "collar_family": "regular_stationary_SO3_throat_collar",
        "reference_pages": {
            "MPLA_bridge": "177-188",
            "MPLA_minimal_area_throat": "183-185",
            "published_EPJC_wormhole_summary": "211, 232",
        },
        "radius_law_ready": manifest["throat_certificate"]["minimal_throat"],
        "regular_collar_metric_ansatz": (
            "ds^2 = A(rho)dT^2 + 2C(rho)dTdrho - B(rho)drho^2 - R(rho)^2 dOmega^2"
        ),
        "required_regular_conditions_at_sigma": {
            "R_prime_zero": True,
            "R_second_positive": True,
            "two_by_two_TRho_block_non_degenerate": "A(0)*B(0)+C(0)^2 != 0 up to signature convention",
            "Z2_parity": "R even; A,B even; C odd or fixed by orientation convention",
            "no_exterior_schwarzschild_coordinate_horizon": True,
        },
        "mpla_degenerate_bridge_branch": {
            "status": "diagnostic_only",
            "reason": "reported bridge picture may leave only angular components at the throat / zero determinant",
            "active_sigma_regular_branch_compatible": False,
        },
        "regular_collar_ready": False,
        "reason_not_ready": "A(rho), B(rho), C(rho) are not yet derived from the Janus bimetric action",
        "DeltaK_derivable_from_collar": False,
        "next_required": [
            "derive A(rho), B(rho), C(rho) from the active Z2 bimetric field equations",
            "prove the T-rho block is non-degenerate at Sigma",
            "compute Christoffels in the regular collar",
            "compute unit normal and K_ab on Sigma",
        ],
    }
