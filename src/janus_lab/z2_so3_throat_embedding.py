"""SO(3) throat embedding manifest from the MPLA local radius law."""

from __future__ import annotations

from src.janus_lab.mpla_schwarzschild_throat import (
    mpla_areal_radius,
    mpla_areal_radius_prime,
    mpla_areal_radius_second,
    mpla_throat_certificate,
)
from src.janus_lab.z2_published_so3_bianchi_reduction import (
    published_so3_bianchi_reduction_payload,
)


def so3_throat_stencil(rs: float = 1.0, step: float = 0.1) -> list[dict]:
    return [
        {
            "rho": rho,
            "R": mpla_areal_radius(rho, rs),
            "partial_rho_R": mpla_areal_radius_prime(rho, rs),
            "partial2_rho_R": mpla_areal_radius_second(rho, rs),
        }
        for rho in (-step, 0.0, step)
    ]


def so3_throat_embedding_manifest(rs: float = 1.0) -> dict:
    throat = mpla_throat_certificate(rs)
    so3 = published_so3_bianchi_reduction_payload()
    return {
        "active_core": "Z2_tunnel_Sigma",
        "embedding_family": "stationary_SO3_projective_throat",
        "source_radius_law": "MPLA_schwarzschild_throat_R(rho)=R_s*(1+log(cosh(rho)))",
        "published_reduction_source": so3["source"],
        "coordinate": {
            "normal_coordinate": "rho",
            "Sigma_location": 0.0,
            "Z2_action": "rho -> -rho with plus/minus sheet exchange",
        },
        "embedding_skeleton": {
            "X_plus": "(t_plus, rho, theta, phi) with R=R(rho)",
            "X_minus": "(t_minus, -rho, projective angular image(theta,phi)) with R=R(rho)",
            "Sigma": "rho=0, R=R_s",
        },
        "throat_certificate": throat,
        "radius_stencil": so3_throat_stencil(rs),
        "SO3_reduced_bianchi_ready": so3["stationary_so3_reduced_bianchi_ready"],
        "same_sector_attraction_ready": so3["same_sector_attraction_ready"],
        "opposite_sector_repulsion_ready": so3["opposite_sector_repulsion_ready"],
        "active_embedding_skeleton_ready": True,
        "metric_functions_ready": False,
        "christoffels_ready": False,
        "unit_normals_ready": False,
        "K_ab_plus_minus_ready": False,
        "DeltaK_s_tau_ready": False,
        "R_Sigma_solution_certificate_ready": False,
        "allowed_use": [
            "SO(3) throat coordinate and radius stencil",
            "Z2 even-radius/minimal-throat check",
            "input skeleton for future extrinsic-curvature calculation",
        ],
        "non_claims": [
            "not a complete active embedding",
            "not DeltaK_s or DeltaK_tau",
            "not Sigma radial balance",
            "not counterterm closure",
        ],
        "next_required": [
            "supply or derive metric functions f_plus(R), f_minus(R) or equivalent lapse/radial blocks",
            "compute Christoffels on both sheets",
            "compute unit normals and K_ab plus/minus",
            "derive DeltaK_s(R_s) and DeltaK_tau(R_s)",
        ],
    }
