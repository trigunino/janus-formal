from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.janus_lab.mpla_schwarzschild_throat import mpla_throat_certificate


OUTPUT_PATH = Path("outputs/active_z2_sigma/mpla_schwarzschild_throat_local_model.json")
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_mpla_schwarzschild_throat_local_model.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_mpla_schwarzschild_throat_local_model.json"
)


def build_payload(rs_over_ell: float = 1.0) -> dict:
    cert = mpla_throat_certificate(rs=rs_over_ell)
    payload = {
        "status": "janus-z2-sigma-mpla-schwarzschild-throat-local-model",
        "active_core": "Z2_tunnel_Sigma",
        "source": "MPLA_singularity_elimination_local_model",
        "coordinate": "rho",
        "areal_radius_formula": "R(rho) = R_s * (1 + log(cosh(rho)))",
        "rho_reflection": "rho -> -rho",
        "fold_transition": "F_plus <-> F_minus",
        "throat_topology": "S2 in the Schwarzschild local model",
        "local_certificate": cert,
        "R_Sigma_over_R_s": 1.0,
        "R_prime_at_Sigma_over_R_s": 0.0,
        "R_second_at_Sigma_over_R_s": 1.0,
        "minimal_throat_ready": cert["minimal_throat"],
        "Z2_orientation_reversal_ready": True,
        "mass_inversion_supported_by_reference": True,
        "negative_thermodynamic_density_postulated": False,
        "counterterm_coefficients_derived": False,
        "E_counterterm_derived": False,
        "absolute_R_Sigma_solution_ready": False,
        "primary_blocker": "R_s_scale_not_fixed_by_local_MPLA_throat_model",
        "allowed_use": [
            "local regular throat geometry diagnostic",
            "Z2 rho-reflection/orientation support",
            "dimensionless R_Sigma/R_s certificate",
        ],
        "forbidden_use": [
            "absolute BAO scale closure",
            "counterterm coefficient closure",
            "surface_hk density derivation",
        ],
    }
    return payload


def write_reports() -> dict:
    payload = build_payload()
    OUTPUT_PATH.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# Janus Z2/Sigma MPLA Schwarzschild Throat Local Model",
                "",
                f"Formula: `{payload['areal_radius_formula']}`",
                f"Minimal throat ready: `{payload['minimal_throat_ready']}`",
                f"R_Sigma/R_s: `{payload['R_Sigma_over_R_s']}`",
                f"Absolute R_Sigma ready: `{payload['absolute_R_Sigma_solution_ready']}`",
                f"E_counterterm derived: `{payload['E_counterterm_derived']}`",
                f"Primary blocker: `{payload['primary_blocker']}`",
            ]
        ),
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
