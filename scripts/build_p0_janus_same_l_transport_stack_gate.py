from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_janus_same_l_transport_stack_gate.md")
JSON_PATH = Path("outputs/reports/p0_janus_same_l_transport_stack_gate.json")


def build_payload() -> dict:
    same_l_uses = [
        "transport dust/perfect-fluid/kinetic stress tensors",
        "define K_plus and mirror K_minus consistently",
        "define Q_cross optical contraction",
        "map minus momenta into plus-observer moments",
        "compute DL residuals and mirror inverse residuals",
    ]
    required_identities = [
        "L^T eta L=eta",
        "e_plus L = mapped e_minus on the accepted tetrad branch",
        "same L is used for K, Q_cross, and kinetic moment projection",
        "D L comes from spin connections or source-derived transport, not a fitted boost",
        "R_plus=R_minus=0 after substituting the same L and D L",
    ]
    rejection_rules = [
        "reject L_geom if Lorentz condition is unproved",
        "reject any separate L for Q_cross versus K",
        "reject fitted or observer-normalized L",
    ]
    return {
        "description": "P0 gate requiring one admissible same-L transport stack.",
        "status": "same-l-transport-stack-gate-open",
        "depends_on": [
            "p0_bianchi_minimal_same_l_qcross_gate",
            "p0_janus_weakfield_lorentz_projection_derivation",
            "p0_janus_metric_tetrad_source_branch_gate",
        ],
        "same_l_uses": same_l_uses,
        "required_identities": required_identities,
        "rejection_rules": rejection_rules,
        "same_l_stack_written": True,
        "lorentz_condition_required": True,
        "same_l_for_k_qcross_kinetics_required": True,
        "same_l_1p1_lorentz_probe_available": True,
        "lgeom_tetrad_map_residual_probe_available": True,
        "lgeom_dl_lie_residual_probe_available": True,
        "dl_source_derived": False,
        "same_l_stack_closed": False,
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The same-L problem is a stack identity, not a scalar factor. One L must pass "
            "Lorentz/tetrad compatibility and be reused for K, Q_cross, kinetic moments, and DL."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Janus Same-L Transport Stack Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Same-L stack written: {payload['same_l_stack_written']}",
        f"Lorentz condition required: {payload['lorentz_condition_required']}",
        f"Same L for K/Qcross/kinetics required: {payload['same_l_for_k_qcross_kinetics_required']}",
        f"Same-L 1+1 Lorentz probe available: {payload['same_l_1p1_lorentz_probe_available']}",
        "Lgeom tetrad map residual probe available: "
        f"{payload['lgeom_tetrad_map_residual_probe_available']}",
        "Lgeom DL Lie residual probe available: "
        f"{payload['lgeom_dl_lie_residual_probe_available']}",
        f"D L source-derived: {payload['dl_source_derived']}",
        f"Same-L stack closed: {payload['same_l_stack_closed']}",
        f"Uses observational fit: {payload['uses_observational_fit']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Same-L Uses",
        "",
    ]
    lines.extend(f"- {item}" for item in payload["same_l_uses"])
    lines.extend(["", "## Required Identities", ""])
    lines.extend(f"- `{item}`" for item in payload["required_identities"])
    lines.extend(["", "## Rejection Rules", ""])
    lines.extend(f"- {item}" for item in payload["rejection_rules"])
    lines.extend(["", f"Verdict: {payload['verdict']}", ""])
    return "\n".join(lines)


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH) -> dict:
    report_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.parent.mkdir(parents=True, exist_ok=True)
    payload = build_payload()
    json_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    report_path.write_text(render_markdown(payload), encoding="utf-8")
    return payload


def main() -> None:
    write_reports()
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()
