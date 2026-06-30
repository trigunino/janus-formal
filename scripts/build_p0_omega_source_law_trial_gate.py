from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_omega_source_law_trial_gate.md")
JSON_PATH = Path("outputs/reports/p0_omega_source_law_trial_gate.json")


def build_payload() -> dict:
    trial_rows = [
        {
            "trial": "fermi_walker_comoving",
            "condition": "derive D_u tetrad law with e0=u and Omega_u u=0",
            "closed": False,
        },
        {
            "trial": "source_congruence_force",
            "condition": "derive geodesic/cross-force law that fixes transported dust frame",
            "closed": False,
        },
        {
            "trial": "shared_transport",
            "condition": "same source law fixes L/Omega for K, Q_cross, and mirror",
            "closed": False,
        },
        {
            "trial": "no_gauge_fit",
            "condition": "do not choose comoving frame or Omega after residual evaluation",
            "closed": True,
        },
    ]
    return {
        "description": "Trial gate for source laws that could derive Omega_u u=0.",
        "status": "omega-source-law-trial-open",
        "trial_rows": trial_rows,
        "fermi_walker_trial_available": True,
        "fermi_walker_omega_u_zero_trial_available": True,
        "source_congruence_trial_available": True,
        "source_congruence_omega_gate_available": True,
        "shared_transport_required": True,
        "no_gauge_fit_rule_closed": True,
        "source_law_closed": False,
        "omega_source_or_axiom_decision_available": True,
        "omega_u_zero_source_closed": False,
        "omega_residual_closed": False,
        "prediction_ready": False,
        "physics_closed": False,
        "verdict": (
            "The next closure attempt must source-derive Omega_u u=0 from transport "
            "or congruence dynamics; a gauge choice after seeing the residual is rejected."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Omega Source Law Trial Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Fermi-Walker trial available: {payload['fermi_walker_trial_available']}",
        f"Fermi-Walker Omega u=0 trial available: {payload['fermi_walker_omega_u_zero_trial_available']}",
        f"Source congruence trial available: {payload['source_congruence_trial_available']}",
        f"Source congruence Omega gate available: {payload['source_congruence_omega_gate_available']}",
        f"Shared transport required: {payload['shared_transport_required']}",
        f"No gauge fit rule closed: {payload['no_gauge_fit_rule_closed']}",
        f"Source law closed: {payload['source_law_closed']}",
        f"Omega source or axiom decision available: {payload['omega_source_or_axiom_decision_available']}",
        f"Omega_u u=0 source closed: {payload['omega_u_zero_source_closed']}",
        f"Omega residual closed: {payload['omega_residual_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Trial Rows",
        "",
    ]
    for row in payload["trial_rows"]:
        lines.append(f"- {row['trial']}: {row['condition']} (closed: {row['closed']})")
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
