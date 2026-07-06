from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_counterterm_tetrad_extrinsic_curvature_variation_transport_gate import (
    build_payload as build_delta_k_transport,
)
from scripts.build_p0_eft_janus_z2_sigma_counterterm_tetrad_metric_variation_transport_gate import (
    build_payload as build_delta_h_transport,
)
from scripts.build_p0_eft_janus_z2_sigma_projective_gluing_normal_orientation_sign_gate import (
    build_payload as build_orientation,
)


REPORT_PATH = Path(
    "outputs/reports/"
    "p0_eft_janus_z2_sigma_counterterm_tetrad_component_parity_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/"
    "p0_eft_janus_z2_sigma_counterterm_tetrad_component_parity_gate.json"
)


def build_payload() -> dict:
    delta_h = build_delta_h_transport()
    delta_k = build_delta_k_transport()
    orientation = build_orientation()

    metric_variation_parity_ready = delta_h["tetrad_metric_variation_transport_ready"]
    extrinsic_variation_parity_ready = (
        delta_k["deltaK_transport_ready"]
        and orientation["projective_gluing_normal_orientation_sign_ready"]
    )

    component_tests = {
        "metric_tetrad_component": {
            "component": "alpha_h = sqrt|h| R_h_ab delta h^ab",
            "variation_parity": "even",
            "coefficient_parity_required": "odd",
            "variation_parity_ready": metric_variation_parity_ready,
            "coefficient_parity_ready": False,
            "component_odd_proved": False,
            "blocker": "R_h_ab_Z2_odd_coefficient_parity",
            "reason": (
                "h_ab and delta h_ab are Z2-even. The component is odd only if "
                "the residual coefficient R_h_ab is Z2-odd."
            ),
        },
        "extrinsic_tetrad_component": {
            "component": "alpha_K = sqrt|h| R_K_ab delta K^ab",
            "variation_parity": "odd",
            "coefficient_parity_required": "even",
            "variation_parity_ready": extrinsic_variation_parity_ready,
            "coefficient_parity_ready": False,
            "component_odd_proved": False,
            "blocker": "R_K_ab_Z2_even_coefficient_parity",
            "reason": (
                "K_ab and delta K_ab inherit the normal-orientation sign. The "
                "component is odd only if R_K_ab is Z2-even."
            ),
        },
    }
    all_component_parities_ready = all(
        item["component_odd_proved"] for item in component_tests.values()
    )
    return {
        "status": "janus-z2-sigma-counterterm-tetrad-component-parity-gate",
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "declared": {
            "metric_tetrad_component_parity_declared": True,
            "extrinsic_tetrad_component_parity_declared": True,
            "coefficient_parity_required_not_assumed": True,
            "density_ansatz_forbidden": True,
            "fitted_coefficient_forbidden": True,
            "legacy_z4_reuse_forbidden": True,
        },
        "upstream": {
            "delta_h_transport": {
                "gate": delta_h["status"],
                "ready": delta_h["tetrad_metric_variation_transport_ready"],
            },
            "delta_k_transport": {
                "gate": delta_k["status"],
                "ready": delta_k["deltaK_transport_ready"],
            },
            "normal_orientation": {
                "gate": orientation["status"],
                "ready": orientation["projective_gluing_normal_orientation_sign_ready"],
                "formula": orientation["formulae"]["normal_sign"],
            },
        },
        "component_tests": component_tests,
        "closure": {
            "metric_variation_parity_ready": metric_variation_parity_ready,
            "extrinsic_variation_parity_ready": extrinsic_variation_parity_ready,
            "R_h_ab_Z2_odd_coefficient_parity_proved": False,
            "R_K_ab_Z2_even_coefficient_parity_proved": False,
            "metric_tetrad_component_Z2_odd_proved": False,
            "extrinsic_tetrad_component_Z2_odd_proved": False,
            "tetrad_component_parity_gate_passed": all_component_parities_ready,
        },
        "gate_passed": all_component_parities_ready,
        "primary_blocker": "R_h_ab_Z2_odd_coefficient_parity",
        "interpretation": (
            "The Janus/Z2 geometry fixes the parity of the variations: delta h is "
            "even, delta K is odd. This is not enough to close alpha_h/alpha_K. "
            "The residual coefficients must also have the required opposite/even "
            "parity, and those coefficient parities are not yet derived."
        ),
        "next_required": [
            "derive_R_h_ab_from_explicit_alpha_res_component_values",
            "prove_tau_Z2_pullback_R_h_ab_equals_minus_R_h_ab",
            "derive_R_K_ab_from_explicit_alpha_res_component_values",
            "prove_tau_Z2_pullback_R_K_ab_equals_plus_R_K_ab",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Counterterm Tetrad Component Parity Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
        "",
        payload["interpretation"],
        "",
        "## Component Tests",
    ]
    for name, item in payload["component_tests"].items():
        lines.append(
            f"- `{name}`: variation=`{item['variation_parity']}`, "
            f"coefficient_required=`{item['coefficient_parity_required']}`, "
            f"odd_proved=`{item['component_odd_proved']}`"
        )
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
