from __future__ import annotations

from pathlib import Path
import json

import sympy as sp


REPORT_PATH = Path("outputs/reports/p0_nonmetricity_integrability_curl_gate.md")
JSON_PATH = Path("outputs/reports/p0_nonmetricity_integrability_curl_gate.json")


def build_payload() -> dict:
    x, y = sp.symbols("x y")
    h = sp.Function("h")(x, y)
    nx_from_h = sp.diff(h, x)
    ny_from_h = sp.diff(h, y)
    compatible_curl = sp.simplify(sp.diff(ny_from_h, x) - sp.diff(nx_from_h, y))
    nx_bad = x * y
    ny_bad = sp.Integer(0)
    curl_defect = sp.simplify(sp.diff(ny_bad, x) - sp.diff(nx_bad, y))
    return {
        "description": "Integrability curl gate for N_alpha=D_alpha H relative nonmetricity.",
        "status": "nonmetricity-integrability-curl-gate-open",
        "numeric_probe": "p0_nonmetricity_curl_numeric_probe",
        "definition": "N_alpha := D_alpha H",
        "flat_patch_identity": "partial_[alpha N_beta]=0 componentwise when N=dH",
        "covariant_identity": "D_[alpha N_beta] = [D_alpha,D_beta]H, fixed by the same connection/curvature branch",
        "compatible_toy": {
            "N_x": str(nx_from_h),
            "N_y": str(ny_from_h),
            "curl": str(compatible_curl),
            "passes": bool(compatible_curl == 0),
        },
        "curl_defect_toy": {
            "N_x": str(nx_bad),
            "N_y": str(ny_bad),
            "curl": str(curl_defect),
            "passes": bool(curl_defect == 0),
        },
        "acceptance_tests": [
            "one same H integrates the proposed N_alpha on the evaluated patch",
            "covariant curl equals the curvature commutator fixed by the same Gamma/Omega branch",
            "mirror branch integrates to H^{-1} with Q -> -Q",
            "no curl defect is inserted to cancel R_plus/R_minus",
        ],
        "n_definition_closed": True,
        "flat_integrability_toy_closed": True,
        "curl_defect_rejected": True,
        "source_n_integrability_proved": False,
        "numeric_probe_available": True,
        "mirror_integrability_proved": False,
        "prediction_ready": False,
        "verdict": (
            "A candidate N_alpha is admissible only if it integrates to the same H "
            "with the correct covariant curl. Arbitrary source one-forms are rejected."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Nonmetricity Integrability Curl Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Definition: `{payload['definition']}`",
        f"Flat patch identity: `{payload['flat_patch_identity']}`",
        f"Covariant identity: `{payload['covariant_identity']}`",
        f"N definition closed: {payload['n_definition_closed']}",
        f"Flat integrability toy closed: {payload['flat_integrability_toy_closed']}",
        f"Curl defect rejected: {payload['curl_defect_rejected']}",
        f"Source N integrability proved: {payload['source_n_integrability_proved']}",
        f"Numeric probe: `{payload['numeric_probe']}`",
        f"Mirror integrability proved: {payload['mirror_integrability_proved']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Toy Checks",
        "",
    ]
    for name in ("compatible_toy", "curl_defect_toy"):
        row = payload[name]
        lines.append(f"- {name}: `N_x={row['N_x']}`, `N_y={row['N_y']}`, `curl={row['curl']}`, passes={row['passes']}")
    lines.extend(["", "## Acceptance Tests", ""])
    lines.extend(f"- {item}" for item in payload["acceptance_tests"])
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
