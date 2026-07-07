from __future__ import annotations

import json
from pathlib import Path


REPORTS = Path("outputs/reports")
RATIO_PATH = REPORTS / "p0_eft_janus_z2_published_bimetric_sector_ratio_gate.json"
RHO_PATH = REPORTS / "p0_eft_janus_z2_rho_plus0_abs_symbolic_closure_gate.json"
GLOBAL_STATE_PATH = REPORTS / "p0_eft_janus_z2_global_bimetric_state_to_flrw_sector_normalization_gate.json"
JSON_PATH = REPORTS / "p0_eft_janus_z2_bimetric_vacuum_alpha_selector_gate.json"
REPORT_PATH = REPORTS / "p0_eft_janus_z2_bimetric_vacuum_alpha_selector_gate.md"


def _read(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8")) if path.exists() else {}


def build_payload(
    ratio_path: Path = RATIO_PATH,
    rho_path: Path = RHO_PATH,
    global_state_path: Path = GLOBAL_STATE_PATH,
) -> dict:
    ratio = _read(ratio_path)
    rho = _read(rho_path)
    global_state = _read(global_state_path)

    relative_ratio_ready = bool(ratio.get("relative_sector_ratio_ready"))
    absolute_density_ready = bool(ratio.get("absolute_density_scale_ready")) or bool(
        global_state.get("sector_normalizations_ready")
    )
    rho_plus0_ready = bool(rho.get("rho_plus0_abs_ready"))
    noether_occupation_ready = not bool("N_occ_Z2Sigma" in rho.get("remaining_independent_inputs", []))
    curvature_radius_ready = not bool("R_curv_Z2Sigma" in rho.get("remaining_independent_inputs", []))
    state_law_ready = absolute_density_ready and rho_plus0_ready
    alpha_selector_ready = relative_ratio_ready and state_law_ready

    return {
        "status": "janus-z2-bimetric-vacuum-alpha-selector-gate",
        "active_core": "Z2_tunnel_Sigma",
        "route": "bimetric_vacuum_equation_of_state",
        "published_relative_sector_ratio_ready": relative_ratio_ready,
        "absolute_density_scale_ready": absolute_density_ready,
        "rho_plus0_abs_ready": rho_plus0_ready,
        "N_occ_Z2Sigma_ready": noether_occupation_ready,
        "R_curv_Z2Sigma_ready": curvature_radius_ready,
        "global_bimetric_state_law_ready": state_law_ready,
        "alpha_selector_ready": alpha_selector_ready,
        "blocked_by": [
            name
            for name, ready in {
                "absolute_density_scale_ready": absolute_density_ready,
                "rho_plus0_abs_ready": rho_plus0_ready,
                "N_occ_Z2Sigma_ready": noether_occupation_ready,
                "R_curv_Z2Sigma_ready": curvature_radius_ready,
            }.items()
            if not ready
        ],
        "interpretation": (
            "The published bimetric material supplies a relative plus/minus sector "
            "ratio, but not the absolute FLRW density scale. Therefore it cannot "
            "select alpha without a global state law for rho_plus0 or equivalent "
            "N_occ and R_curv inputs."
        ),
        "gate_passed": True,
    }


def write_reports() -> dict:
    payload = build_payload()
    JSON_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# Janus Z2 Bimetric Vacuum Alpha Selector Gate",
                "",
                f"Relative sector ratio ready: `{payload['published_relative_sector_ratio_ready']}`",
                f"Absolute density scale ready: `{payload['absolute_density_scale_ready']}`",
                f"rho_plus0 ready: `{payload['rho_plus0_abs_ready']}`",
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
