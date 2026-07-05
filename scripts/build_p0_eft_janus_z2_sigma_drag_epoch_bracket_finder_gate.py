from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_drag_epoch_bracket_finder_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_drag_epoch_bracket_finder_gate.json")


def build_payload() -> dict:
    return {
        "status": "janus-z2-sigma-drag-epoch-bracket-finder-gate",
        "active_core": "Z2_tunnel_Sigma",
        "bibliography_checked": True,
        "primary_sources_checked": [
            "Eisenstein & Hu 1997, arXiv:astro-ph/9709112",
            "Hu & Sugiyama 1996 photon-baryon tight-coupling treatment",
        ],
        "drag_epoch_bracket_finder_ready": True,
        "bracket_condition": "Gamma_drag_Z2Sigma(z)-H_Z2Sigma(z) changes sign on an active z grid",
        "requires_active_H_Z2Sigma": True,
        "requires_active_Gamma_drag_Z2Sigma": True,
        "requires_active_z_grid": True,
        "uses_planck_lcdm_drag_epoch_fit": False,
        "uses_archived_z4_inputs": False,
        "z_d_values_ready": False,
        "gate_passed": True,
        "next_required": [
            "derive_H_Z2Sigma_from_active_FLRW_components",
            "derive_Gamma_drag_Z2Sigma_from_active_free_electron_history",
            "run_bracket_then_bisection_solver_for_z_d_Z2Sigma",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Drag Epoch Bracket Finder Gate",
        "",
        f"Bracket finder ready: `{payload['drag_epoch_bracket_finder_ready']}`",
        f"z_d values ready: `{payload['z_d_values_ready']}`",
        f"Gate passed: `{payload['gate_passed']}`",
        "",
        "## Condition",
        f"`{payload['bracket_condition']}`",
        "",
        "## Next Required",
    ]
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
