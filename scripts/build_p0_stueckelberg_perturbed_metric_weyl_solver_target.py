from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_stueckelberg_perturbed_metric_weyl_solver_target.md")
JSON_PATH = Path("outputs/reports/p0_stueckelberg_perturbed_metric_weyl_solver_target.json")


def build_payload() -> dict:
    inputs = [
        "background g_plus from M18 positive optical branch",
        "transported stress source T_to or kinetic f_to",
        "s_cross weak-field sign for reduced Ricci diagnostic",
        "phi/L convention used for stress transport",
    ]
    equations = [
        {
            "name": "metric_perturbation_target",
            "equation": "delta G_plus[h_plus] = chi delta S_plus[T_plus,T_minus_to_plus,phi,L]",
            "status": "target-not-solved",
        },
        {
            "name": "weyl_output",
            "equation": "C_plus[k,m,k,m] = Weyl[g_plus+h_plus] screen contraction",
            "status": "target-output",
        },
        {
            "name": "ricci_output",
            "equation": "R_plus[k,k] = Ricci[g_plus+h_plus] null contraction",
            "status": "compare-to-reduced-sachs",
        },
    ]
    required_outputs = [
        "h_plus gauge declaration",
        "C_plus_kmkm grid/ray samples",
        "R_plus_kk grid/ray samples",
        "Bianchi residual for delta S_plus",
        "comparison to PM reduced Ricci diagnostic",
    ]
    decision = {
        "weyl_solver_target_defined": True,
        "perturbed_metric_solved": False,
        "pm_proxy_replacement_path_defined": True,
        "prediction_ready": False,
        "reason": (
            "The missing Weyl term is now reduced to a concrete perturbed-metric solve. "
            "PM shear proxies remain diagnostics until h_plus is solved and Weyl/Ricci "
            "ray contractions are emitted explicitly."
        ),
    }
    return {
        "artifact": "p0_stueckelberg_perturbed_metric_weyl_solver_target",
        "status": "perturbed-metric-weyl-solver-target-open",
        "fit_used": False,
        "free_parameters": [],
        "physics_closed": False,
        "prediction_ready": False,
        "inputs": inputs,
        "equations": equations,
        "required_outputs": required_outputs,
        "decision": decision,
    }


def render_markdown(payload: dict) -> str:
    decision = payload["decision"]
    lines = [
        "# P0 Stueckelberg Perturbed Metric Weyl Solver Target",
        "",
        f"Status: {payload['status']}",
        f"Fit used: {payload['fit_used']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Inputs",
    ]
    lines.extend(f"- {item}" for item in payload["inputs"])
    lines.extend(["", "## Equations"])
    for row in payload["equations"]:
        lines.append(f"- {row['name']}: `{row['equation']}` (status={row['status']})")
    lines.extend(["", "## Required Outputs"])
    lines.extend(f"- {item}" for item in payload["required_outputs"])
    lines.extend(
        [
            "",
            "## Decision",
            f"Weyl solver target defined: {decision['weyl_solver_target_defined']}",
            f"Perturbed metric solved: {decision['perturbed_metric_solved']}",
            f"PM proxy replacement path defined: {decision['pm_proxy_replacement_path_defined']}",
            f"Prediction ready: {decision['prediction_ready']}",
            f"Reason: {decision['reason']}",
            "",
        ]
    )
    return "\n".join(lines)


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH) -> dict:
    payload = build_payload()
    report_path.parent.mkdir(parents=True, exist_ok=True)
    report_path.write_text(render_markdown(payload), encoding="utf-8")
    json_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    return payload


if __name__ == "__main__":
    write_reports()
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")
