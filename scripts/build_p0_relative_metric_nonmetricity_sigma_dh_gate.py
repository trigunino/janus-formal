from __future__ import annotations

from pathlib import Path
import json
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_relative_strain_q_derivative_omega_gate import (
    build_payload as build_dq_gate,
)
from scripts.build_p0_sigma_dh_equivalence_gate import build_payload as build_sigma_gate


REPORT_PATH = Path("outputs/reports/p0_relative_metric_nonmetricity_sigma_dh_gate.md")
JSON_PATH = Path("outputs/reports/p0_relative_metric_nonmetricity_sigma_dh_gate.json")


def build_payload() -> dict:
    sigma = build_sigma_gate()
    dq = build_dq_gate()
    return {
        "description": "Gate for treating N_alpha=D_alpha H as relative-metric nonmetricity, not as a free selector.",
        "status": "relative-metric-nonmetricity-selector-open",
        "depends_on": [
            "p0_sigma_dh_equivalence_gate",
            "p0_relative_strain_q_derivative_omega_gate",
            "p0_sigma_trace_only_no_go_gate",
            "p0_nonmetricity_integrability_curl_gate",
            "p0_nonmetricity_mirror_inverse_gate",
        ],
        "definition": "N_alpha := D_alpha H, with H=eta^{-1} L_geom^T eta L_geom",
        "sigma_equivalence": sigma["inverse_identity"],
        "dq_rule": dq["matrix_log_derivative"],
        "decomposition": {
            "trace": "Tr(H^{-1} N_alpha) = D_alpha log det(H)",
            "trace_free": "N_alpha_TF = N_alpha - (Tr(H^{-1}N_alpha)/n) H",
            "meaning": "B4vol/determinant can constrain only the trace; Q_TF needs trace-free nonmetricity",
        },
        "source_selector_tests": [
            "published Janus equation explicitly gives N_alpha or D_alpha H",
            "relative curvature/nonmetricity identity fixes N_alpha before residual substitution",
            "Stueckelberg or BF action varies H/L_geom and returns N_alpha as an EL equation",
            "boundary/gauge data for N_alpha are declared before observations",
        ],
        "rejection_rules": [
            "do not define N_alpha and call it selected",
            "do not use determinant/B4vol trace to close Q_TF",
            "do not use pure Lorentz Omega_alpha because it gives N_alpha=0",
            "do not fit N_alpha/DQ to lensing or power residuals",
        ],
        "n_definition_closed": True,
        "trace_tracefree_split_closed": True,
        "trace_only_no_go": "p0_sigma_trace_only_no_go_gate",
        "integrability_gate": "p0_nonmetricity_integrability_curl_gate",
        "mirror_inverse_gate": "p0_nonmetricity_mirror_inverse_gate",
        "source_selector_found": False,
        "trace_only_closure_sufficient": False,
        "prediction_ready": False,
        "notable_improvement": (
            "The nonmetricity route is now a precise target: source-select N_alpha, "
            "especially its trace-free part, before using DQ."
        ),
        "remaining_lock": (
            "Find a Janus source/action/relative-curvature identity that fixes N_alpha, "
            "not only its determinant trace."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Relative-Metric Nonmetricity Sigma/DH Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Definition: `{payload['definition']}`",
        f"N definition closed: {payload['n_definition_closed']}",
        f"Trace/trace-free split closed: {payload['trace_tracefree_split_closed']}",
        f"Trace-only no-go: `{payload['trace_only_no_go']}`",
        f"Integrability gate: `{payload['integrability_gate']}`",
        f"Mirror inverse gate: `{payload['mirror_inverse_gate']}`",
        f"Source selector found: {payload['source_selector_found']}",
        f"Trace-only closure sufficient: {payload['trace_only_closure_sufficient']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Identities",
        "",
        f"- Sigma equivalence: `{payload['sigma_equivalence']}`",
        f"- DQ rule: `{payload['dq_rule']}`",
        "",
        "## Decomposition",
        "",
    ]
    for key, value in payload["decomposition"].items():
        lines.append(f"- {key}: `{value}`")
    lines.extend(["", "## Source Selector Tests", ""])
    lines.extend(f"- {item}" for item in payload["source_selector_tests"])
    lines.extend(["", "## Rejection Rules", ""])
    lines.extend(f"- {item}" for item in payload["rejection_rules"])
    lines.extend(["", "## Result", "", payload["notable_improvement"], ""])
    lines.extend([f"Remaining lock: {payload['remaining_lock']}", ""])
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
