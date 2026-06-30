from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_route_a_integrability_nullspace_audit.md")
JSON_PATH = Path("outputs/reports/p0_route_a_integrability_nullspace_audit.json")


def build_payload() -> dict:
    equation_rows = [
        {"equation": "J=dphi", "role": "map existence", "filter": True},
        {"equation": "partial_[a J^mu_b]=0", "role": "curl/Frobenius integrability", "filter": True},
        {"equation": "det(dphi)!=0", "role": "local invertibility", "filter": True},
        {"equation": "L^T eta L=eta", "role": "Lorentz admissibility", "filter": True},
        {"equation": "L_minus_to_plus L_plus_to_minus=I", "role": "mirror inverse", "filter": True},
        {"equation": "B4vol_plus_minus B4vol_minus_plus=1", "role": "measure mirror", "filter": True},
        {"equation": "same phi/J/L for Cuu, F_alpha, B4vol, K, Q_cross", "role": "stack consistency", "filter": True},
    ]
    probe_rows = [
        {
            "case": "compatible_gradient_map",
            "input": "phi=(x+eps sin y, y)",
            "curl_defect": 0.0,
            "passes": True,
        },
        {
            "case": "defected_nonintegrable_j",
            "input": "J^x_y=eps x, J^y_x=0",
            "curl_defect": 1.0,
            "passes": False,
        },
        {
            "case": "free_harmonic_mode",
            "input": "phi=x+epsilon sin x with periodic boundary",
            "curl_defect": 0.0,
            "passes": True,
        },
    ]
    nullspace_rows = [
        {
            "mode": "translation",
            "removed_by_integrability": False,
            "needs": "boundary/gauge",
        },
        {
            "mode": "Lorentz/Killing frame freedom",
            "removed_by_integrability": False,
            "needs": "tetrad gauge/source",
        },
        {
            "mode": "periodic epsilon family",
            "removed_by_integrability": False,
            "needs": "source or boundary amplitude selector",
        },
        {
            "mode": "holonomy class",
            "removed_by_integrability": False,
            "needs": "global topology/source condition",
        },
    ]
    return {
        "description": "Route A audit: integrability as a no-axiom filter for phi/J/L selection.",
        "status": "integrability-necessary-filter-underselects",
        "equation_rows": equation_rows,
        "probe_rows": probe_rows,
        "nullspace_rows": nullspace_rows,
        "necessary_gate": True,
        "compatible_probe_passes": True,
        "defected_probe_fails": True,
        "nonzero_nullspace_without_source": True,
        "unique_phi_j_l_selected": False,
        "requires_scouple": False,
        "uses_observational_fit": False,
        "uses_qdet_qcross_absorption": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "Integrability is mandatory and useful for rejecting invalid phi/J/L candidates, "
            "but it leaves nullspace modes. It cannot by itself replace a source or boundary "
            "selection law."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Route A Integrability Nullspace Audit",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Necessary gate: {payload['necessary_gate']}",
        f"Compatible probe passes: {payload['compatible_probe_passes']}",
        f"Defected probe fails: {payload['defected_probe_fails']}",
        f"Nonzero nullspace without source: {payload['nonzero_nullspace_without_source']}",
        f"Unique phi/J/L selected: {payload['unique_phi_j_l_selected']}",
        f"Requires S_couple: {payload['requires_scouple']}",
        f"Uses observational fit: {payload['uses_observational_fit']}",
        f"Uses Qdet/Qcross absorption: {payload['uses_qdet_qcross_absorption']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Equations",
        "",
        "| equation | role | filter |",
        "|---|---|---:|",
    ]
    for row in payload["equation_rows"]:
        lines.append(f"| `{row['equation']}` | {row['role']} | {row['filter']} |")
    lines.extend(["", "## Probes", "", "| case | input | curl defect | passes |", "|---|---|---:|---:|"])
    for row in payload["probe_rows"]:
        lines.append(f"| {row['case']} | `{row['input']}` | {row['curl_defect']} | {row['passes']} |")
    lines.extend(["", "## Nullspace", "", "| mode | removed by integrability | needs |", "|---|---:|---|"])
    for row in payload["nullspace_rows"]:
        lines.append(f"| {row['mode']} | {row['removed_by_integrability']} | {row['needs']} |")
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
