from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_projective_gluing_normal_orientation_sign_gate import (
    build_payload as build_orientation,
)
from scripts.build_p0_eft_janus_z2_sigma_counterterm_tetrad_metric_variation_transport_gate import (
    build_payload as build_metric_variation,
)
from scripts.build_p0_eft_janus_z2_sigma_counterterm_tetrad_extrinsic_curvature_variation_transport_gate import (
    build_payload as build_extrinsic_variation,
)


REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_surface_hk_variation_convention_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_surface_hk_variation_convention_gate.json"
)


def build_payload() -> dict:
    orientation = build_orientation()
    metric_variation = build_metric_variation()
    extrinsic_variation = build_extrinsic_variation()
    conventions = {
        "bulk_signature": "mostly_plus",
        "metric_variation_index_position": "delta_h_ab",
        "extrinsic_curvature_convention": (
            "K_ab = -n_mu(partial_a partial_b X^mu + "
            "Gamma^mu_alpha_beta e_a^alpha e_b^beta)"
        ),
        "z2_orientation": orientation["formulae"]["orientation_coefficient"],
        "minus_normal": orientation["formulae"]["normal_sign"],
        "surface_variation_template": (
            "delta S_Sigma = integral sqrt_abs_h "
            "[-1/2 T_surface^ab delta h_ab + D^ab delta K_ab + ...]"
        ),
    }
    guards = {
        "K_ab_sign_convention_declared": True,
        "normal_orientation_declared": orientation[
            "projective_gluing_normal_orientation_sign_ready"
        ],
        "metric_variation_index_position_declared": metric_variation[
            "tetrad_metric_variation_transport_ready"
        ],
        "signature_convention_declared": True,
        "delta_K_structural_variation_declared": extrinsic_variation["closure"][
            "delta_K_structural_formula_ready"
        ],
    }
    return {
        "status": "janus-z2-sigma-surface-hk-variation-convention-gate",
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_convention_ledger",
        "conventions": conventions,
        "guards": guards,
        "conventions_ready": all(guards.values()),
        "active_delta_K_value_transport_ready": extrinsic_variation["closure"][
            "extrinsic_curvature_variation_transport_ready"
        ],
        "gate_passed": all(guards.values()),
        "primary_blocker": "none" if all(guards.values()) else "surface_hk_convention_guard",
        "next_required": [
            "derive_active_Janus_Sigma_density_coefficients",
            "compute_T_surface_ab_and_D_ab_with_declared_conventions",
        ],
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# Janus Z2/Sigma Surface h/K Variation Convention Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Conventions ready: `{payload['conventions_ready']}`",
        "",
        "## Conventions",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["conventions"].items())
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    return "\n".join(lines)


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(render_markdown(payload), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
