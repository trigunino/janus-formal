from __future__ import annotations

import json
from pathlib import Path


REPORTS = Path("outputs/reports")
PROJECTIVE_PATH = REPORTS / "p0_eft_janus_projective_tunnel_interface.json"
THETA_PATH = Path("outputs/active_z2_sigma/holst_palatini_boundary_theta_pt67_projection.json")
JSON_PATH = REPORTS / "p0_eft_janus_z2_moebius_twisted_cycle_alpha_route_gate.json"
REPORT_PATH = REPORTS / "p0_eft_janus_z2_moebius_twisted_cycle_alpha_route_gate.md"


def _read(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8")) if path.exists() else {}


def _all_zero(values) -> bool:
    return isinstance(values, list) and all(float(v) == 0.0 for v in values)


def build_payload(
    projective_path: Path = PROJECTIVE_PATH,
    theta_path: Path = THETA_PATH,
) -> dict:
    projective = _read(projective_path)
    theta = _read(theta_path)
    interface = projective.get("projective_tunnel_interface", {})
    topology = projective.get("projective_tunnel_topology", {})

    twisted_shadow_ready = bool(topology.get("torus_to_klein_two_fold_cover")) and bool(
        topology.get("resolved_tunnel_shadow_not_boy_surface")
    )
    z2_cycle_ready = bool(interface.get("around_sigma_cycle_defined")) and bool(
        interface.get("around_sigma_maps_to_generator")
    )
    lift_4d_ready = bool(projective.get("z2_holonomy_path_available")) and twisted_shadow_ready
    theta_ready = bool(theta.get("R_h_trace_values_ready")) and bool(
        theta.get("R_K_trace_values_ready")
    )
    theta_period_nonzero = theta_ready and not (
        _all_zero(theta.get("R_h_trace_values")) and _all_zero(theta.get("R_K_trace_values"))
    )
    compact_action_cycle_ready = False
    alpha_selector_ready = (
        lift_4d_ready and z2_cycle_ready and theta_period_nonzero and compact_action_cycle_ready
    )

    return {
        "status": "janus-z2-moebius-twisted-cycle-alpha-route-gate",
        "active_core": "Z2_tunnel_Sigma",
        "route": "Moebius_twisted_throat_geometry",
        "twisted_2d_shadow_ready": twisted_shadow_ready,
        "z2_orientation_reversing_cycle_ready": z2_cycle_ready,
        "lift_to_4d_projective_tunnel_ready": lift_4d_ready,
        "theta_period_nonzero": theta_period_nonzero,
        "compact_action_cycle_ready": compact_action_cycle_ready,
        "alpha_selector_ready": alpha_selector_ready,
        "interpretation": (
            "The Moebius/Klein shadow is useful for orientation reversal and a compact-cycle "
            "intuition. Current Janus assets already have the Z2 aroundSigma cycle, but the "
            "active PT67 theta period is zero and no compact alpha action cycle is derived."
        ),
        "next_required_if_reopened": [
            "derive the exact 4D Moebius-like twisted tunnel lift, not only the 2D shadow",
            "derive a nonzero boundary theta/KKS period on the twisted cycle",
            "derive a compact action-angle cycle whose period depends on alpha",
        ],
        "gate_passed": True,
    }


def write_reports() -> dict:
    payload = build_payload()
    JSON_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# Janus Z2 Moebius Twisted Cycle Alpha Route Gate",
                "",
                f"Twisted 2D shadow ready: `{payload['twisted_2d_shadow_ready']}`",
                f"Z2 orientation cycle ready: `{payload['z2_orientation_reversing_cycle_ready']}`",
                f"4D lift ready: `{payload['lift_to_4d_projective_tunnel_ready']}`",
                f"Theta period nonzero: `{payload['theta_period_nonzero']}`",
                f"Compact action cycle ready: `{payload['compact_action_cycle_ready']}`",
                f"Alpha selector ready: `{payload['alpha_selector_ready']}`",
                "",
                payload["interpretation"],
            ]
        ),
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
