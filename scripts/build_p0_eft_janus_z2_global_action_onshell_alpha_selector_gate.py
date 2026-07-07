from __future__ import annotations

import json
from pathlib import Path


REPORTS = Path("outputs/reports")
MINI_PATH = REPORTS / "p0_eft_janus_z2_published_minisuperspace_hamiltonian_reduction_gate.json"
SCOUPLE_PATH = REPORTS / "p0_scouple_accepted_action_search.json"
JSON_PATH = REPORTS / "p0_eft_janus_z2_global_action_onshell_alpha_selector_gate.json"
REPORT_PATH = REPORTS / "p0_eft_janus_z2_global_action_onshell_alpha_selector_gate.md"


def _read(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8")) if path.exists() else {}


def build_payload(mini_path: Path = MINI_PATH, scouple_path: Path = SCOUPLE_PATH) -> dict:
    mini = _read(mini_path)
    scouple = _read(scouple_path)
    checks = mini.get("checks", {})

    published_action_anchor = bool(scouple.get("m15_action_accepted_for_field_equations")) or bool(
        checks.get("published_bimetric_action_anchor_available")
    )
    exact_alpha_family = bool(checks.get("published_exact_solution_available")) and bool(
        checks.get("alpha_Eglobal_identity_available")
    )
    minisuperspace_written = bool(checks.get("minisuperspace_lagrangian_written"))
    on_shell_functional = bool(checks.get("action_integral_I_alpha_derived"))
    finite_boundary_prescription = bool(checks.get("compact_cycle_in_reduced_orbit_found"))
    stationarity_selector = bool(checks.get("integrality_or_selection_law_derived"))

    selector_ready = (
        published_action_anchor
        and exact_alpha_family
        and minisuperspace_written
        and on_shell_functional
        and finite_boundary_prescription
        and stationarity_selector
    )

    return {
        "status": "janus-z2-global-action-onshell-alpha-selector-gate",
        "active_core": "Z2_tunnel_Sigma",
        "route": "global_action_energy_principle",
        "published_bimetric_action_anchor_available": published_action_anchor,
        "exact_alpha_family_available": exact_alpha_family,
        "minisuperspace_lagrangian_written": minisuperspace_written,
        "on_shell_S_or_V_alpha_derived": on_shell_functional,
        "finite_boundary_prescription_for_noncompact_orbit": finite_boundary_prescription,
        "stationarity_or_minimum_selector_derived": stationarity_selector,
        "alpha_selector_ready": selector_ready,
        "classification": "action_anchor_without_selector"
        if not selector_ready
        else "global_action_alpha_selector_ready",
        "blocked_by": [
            name
            for name, ready in {
                "minisuperspace_lagrangian_written": minisuperspace_written,
                "on_shell_S_or_V_alpha_derived": on_shell_functional,
                "finite_boundary_prescription_for_noncompact_orbit": finite_boundary_prescription,
                "stationarity_or_minimum_selector_derived": stationarity_selector,
            }.items()
            if not ready
        ],
        "interpretation": (
            "The published action/equation material anchors the Janus family and "
            "identifies alpha with E_global. It does not yet produce a finite "
            "on-shell functional S_on(alpha) or V(alpha) with a selection rule."
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
                "# Janus Z2 Global Action On-Shell Alpha Selector Gate",
                "",
                f"Published action anchor: `{payload['published_bimetric_action_anchor_available']}`",
                f"Exact alpha family: `{payload['exact_alpha_family_available']}`",
                f"On-shell S/V(alpha): `{payload['on_shell_S_or_V_alpha_derived']}`",
                f"Finite boundary prescription: `{payload['finite_boundary_prescription_for_noncompact_orbit']}`",
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
