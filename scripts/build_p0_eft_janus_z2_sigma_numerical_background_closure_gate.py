from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_active_embedding_readiness_gate import (
    build_payload as build_active_embedding_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_effective_fluid_closure_gate import (
    build_payload as build_effective_fluid_payload,
)
from janus_lab.z2_sigma_background_manifest import load_active_z2sigma_background_scalar_manifest


BACKGROUND_SCALAR_MANIFEST_PATH = Path("outputs/active_z2_sigma/background_scalars.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_numerical_background_closure_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_numerical_background_closure_gate.json")


def build_payload() -> dict:
    effective_fluid = build_effective_fluid_payload()
    active_embedding = build_active_embedding_payload()
    numeric_fluid = effective_fluid["numeric"]
    active_embedding_readiness = active_embedding["readiness"]
    background_scalar_exists = BACKGROUND_SCALAR_MANIFEST_PATH.exists()
    background_scalar_valid = False
    background_scalar_error = None
    if background_scalar_exists:
        try:
            load_active_z2sigma_background_scalar_manifest(BACKGROUND_SCALAR_MANIFEST_PATH)
            background_scalar_valid = True
        except Exception as exc:
            background_scalar_error = str(exc)
    prerequisites = {
        "background_equations_derived": True,
        "effective_fluid_structural_projection_ready": effective_fluid[
            "effective_fluid_structural_projection_ready"
        ],
        "effective_fluid_numeric_closure_ready": effective_fluid[
            "effective_fluid_numeric_closure_ready"
        ],
        "active_tunnel_embedding_of_a_closure_ready": active_embedding[
            "active_embedding_readiness_ready"
        ],
        "rho_eff_Z2Sigma_of_a_ready": numeric_fluid["rho_eff_Z2Sigma_of_a_ready"],
        "p_eff_Z2Sigma_of_a_ready": numeric_fluid["p_eff_Z2Sigma_of_a_ready"],
        "H_Z2Sigma_callable_builder_ready": True,
        "E_Z2Sigma_dimensionless_callable_builder_ready": True,
        "active_H0_Z2Sigma_ready": background_scalar_valid,
        "active_omega_k_Z2Sigma_ready": background_scalar_valid,
        "active_G_Z2Sigma_ready": background_scalar_valid,
        "curvature_k_declared": True,
        "kappa_normalization_declared": True,
        "integration_domain_declared": True,
        "observational_parameter_fit_forbidden": True,
        "legacy_lcdm_background_reuse_forbidden": True,
        "archived_z4_background_reuse_forbidden": True,
    }
    return {
        "status": "janus-z2-sigma-numerical-background-closure-gate",
        "active_core": "Z2_tunnel_Sigma",
        "bibliography_checked": True,
        "structural_background_equation": "H_Z2Sigma(a)^2 + k/a^2 = kappa * rho_eff_Z2Sigma(a) / 3",
        "acceleration_equation": "a_ddot/a = -kappa * (rho_eff_Z2Sigma(a) + 3 p_eff_Z2Sigma(a)) / 6",
        "prerequisites": prerequisites,
        "upstream_frontiers": {
            "background_scalar_manifest": {
                "path": str(BACKGROUND_SCALAR_MANIFEST_PATH),
                "exists": background_scalar_exists,
                "valid": background_scalar_valid,
                "validation_error": background_scalar_error,
            },
            "effective_fluid": {
                "effective_fluid_structural_projection_ready": effective_fluid[
                    "effective_fluid_structural_projection_ready"
                ],
                "effective_fluid_numeric_closure_ready": effective_fluid[
                    "effective_fluid_numeric_closure_ready"
                ],
                "numeric": numeric_fluid,
            },
            "active_embedding": {
                "active_embedding_readiness_ready": active_embedding[
                    "active_embedding_readiness_ready"
                ],
                "readiness": active_embedding_readiness,
            },
        },
        "numerical_background_prerequisites_ready": all(prerequisites.values()),
        "numerical_H_Z2Sigma_ready": (
            background_scalar_valid and effective_fluid["effective_fluid_numeric_closure_ready"]
        ),
        "numerical_E_Z2Sigma_ready": effective_fluid["effective_fluid_numeric_closure_ready"],
        "H_Z2Sigma_callable_builder_ready": True,
        "E_Z2Sigma_dimensionless_callable_builder_ready": True,
        "numerical_Omega_m_Z2Sigma_ready": False,
        "full_cosmology_prediction_ready_no_fit": False,
        "missing_functions": [
            "X_plus_Z2Sigma(a)",
            "X_minus_Z2Sigma(a)",
            "DeltaK_s_Z2Sigma(a)",
            "DeltaK_tau_Z2Sigma(a)",
            "rho_eff_Z2Sigma(a)",
            "p_eff_Z2Sigma(a)",
        ],
        "next_required": [
            "close_active_tunnel_embedding_of_a_gate",
            "close_z2_sigma_effective_fluid_numeric_closure",
            "feed_active_H0_omega_k_and_rho_eff_into_existing_H_builder",
            "derive_Omega_m_Z2Sigma_callable_from_active_density_split",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Numerical Background Closure Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Bibliography checked: `{payload['bibliography_checked']}`",
        f"Background scalar manifest valid: `{payload['upstream_frontiers']['background_scalar_manifest']['valid']}`",
        f"Numerical H_Z2Sigma ready: `{payload['numerical_H_Z2Sigma_ready']}`",
        f"Numerical Omega_m_Z2Sigma ready: `{payload['numerical_Omega_m_Z2Sigma_ready']}`",
        "",
        "## Missing Functions",
    ]
    lines.extend(f"- `{item}`" for item in payload["missing_functions"])
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
