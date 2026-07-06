from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_counterterm_alpha_res_z2_anti_invariance_obligation_gate import (
    build_payload as build_alpha_anti_invariance,
)
from scripts.build_p0_eft_janus_z2_sigma_counterterm_boundary_action_functional_gate import (
    build_payload as build_boundary_action,
)
from scripts.build_p0_eft_janus_z2_sigma_counterterm_symbolic_local_primitive_gate import (
    build_payload as build_symbolic_primitive,
)


REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_counterterm_lct_z2_odd_density_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_counterterm_lct_z2_odd_density_gate.json"
)


def build_payload() -> dict:
    action = build_boundary_action()
    primitive = build_symbolic_primitive()
    alpha = build_alpha_anti_invariance()

    primitive_ready = bool(primitive["symbolic_local_primitive_ready"])
    integration_constant_odd_compatible = bool(
        action["closure"]["integration_constant_fixed_symbolically"]
    )
    alpha_odd = bool(alpha["closure"]["alpha_res_Z2_anti_invariance_proved"])
    lct_odd = primitive_ready and integration_constant_odd_compatible and alpha_odd
    return {
        "status": "janus-z2-sigma-counterterm-lct-z2-odd-density-gate",
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "declared": {
            "symbolic_primitive_imported": primitive_ready,
            "integration_constant_policy_imported": integration_constant_odd_compatible,
            "alpha_res_anti_invariance_route_imported": True,
            "density_ansatz_forbidden": True,
            "fitted_counterterm_coefficient_forbidden": True,
            "legacy_z4_reuse_forbidden": True,
        },
        "formulae": {
            "primitive": "L_ct = - integral_gamma alpha_res",
            "target": "tau_Z2^* L_ct = - L_ct",
            "sufficient_condition": (
                "tau_Z2^* alpha_res = - alpha_res and "
                "L_ct(reference_residual_zero_throat)=0"
            ),
            "cohomology_warning": (
                "If alpha_res is not exact globally or the integration constant is "
                "not fixed at a Z2-invariant zero throat, oddness of the primitive "
                "does not follow."
            ),
        },
        "closure": {
            "symbolic_primitive_ready": primitive_ready,
            "integration_constant_odd_compatible": integration_constant_odd_compatible,
            "alpha_res_Z2_anti_invariance_proved": alpha_odd,
            "field_space_exactness_proved": primitive["closure"].get(
                "coefficient_expansion_explicit", False
            ),
            "L_ct_Z2_odd_density_proved": lct_odd,
            "circular_route_detected": not alpha_odd,
        },
        "upstream_frontiers": {
            "alpha_res_anti_invariance": {
                "gate": alpha["status"],
                "ready": alpha["closure"]["alpha_res_Z2_anti_invariance_proved"],
                "primary_blocker": alpha["primary_blocker"],
                "component_parity_tests": alpha["component_parity_tests"],
            },
            "symbolic_primitive": {
                "gate": primitive["status"],
                "ready": primitive_ready,
                "radial_profile_ready": primitive["closure"]["radial_profile_ready"],
            },
            "boundary_action": {
                "gate": action["status"],
                "ready": action["boundary_action_functional_closed"],
                "integration_constant_policy": action["boundary_action"][
                    "integration_constant_policy"
                ],
            },
        },
        "gate_passed": lct_odd,
        "primary_blocker": "alpha_res_Z2_anti_invariance"
        if not alpha_odd
        else ("field_space_exactness_or_integration_constant" if not lct_odd else "none"),
        "interpretation": (
            "L_ct oddness is not independent. It follows from the symbolic primitive "
            "only if alpha_res is Z2-odd and the additive constant is fixed at the "
            "Z2-invariant zero-residual throat. Since alpha_res anti-invariance is "
            "still open, tau_Z2^* L_ct = -L_ct remains blocked. Using L_ct oddness "
            "to prove the tetrad pieces of alpha_res would be circular."
        ),
        "next_required": []
        if lct_odd
        else [
            "close_alpha_res_Z2_anti_invariance_componentwise",
            "verify_field_space_exactness_has_no_Z2_even_cohomology_constant",
            "or_emit_alpha_res_component_values_then_integrate_L_ct_primitive_and_check_Z2_parity",
            "or_return_to_nonzero_E_counterterm_radial_route",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Counterterm L_ct Z2-Odd Density Gate",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
        "",
        payload["interpretation"],
        "",
        "## Formulae",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["formulae"].items())
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
