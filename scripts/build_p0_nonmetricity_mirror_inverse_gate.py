from __future__ import annotations

from pathlib import Path
import json

import sympy as sp


REPORT_PATH = Path("outputs/reports/p0_nonmetricity_mirror_inverse_gate.md")
JSON_PATH = Path("outputs/reports/p0_nonmetricity_mirror_inverse_gate.json")


def build_payload() -> dict:
    h, dh = sp.symbols("h dh", positive=True)
    mirror_h = 1 / h
    mirror_dh = sp.diff(mirror_h, h) * dh
    q = sp.log(h) / 2
    mirror_q = sp.log(mirror_h) / 2
    return {
        "description": "Mirror inverse gate for relative nonmetricity N_alpha=D_alpha H.",
        "status": "nonmetricity-mirror-inverse-identity-closed-source-open",
        "definition": "H_mirror=H^{-1}",
        "matrix_identity": "N_mirror_alpha = D_alpha(H^{-1}) = -H^{-1} N_alpha H^{-1}",
        "scalar_check": {
            "H_mirror": str(mirror_h),
            "N_mirror": str(mirror_dh),
            "Q_plus_Q_mirror": str(sp.simplify(q + mirror_q)),
        },
        "requirements": [
            "minus branch must use the inverse of the same H, not an independent H_mirror",
            "N_mirror is induced by N_alpha; it is not a second fitted source one-form",
            "mirror curl/integrability follows from the same H^{-1} branch and connection convention",
            "Q_mirror=-Q must feed the same A_Janus odd branch",
        ],
        "mirror_identity_closed": True,
        "independent_mirror_n_allowed": False,
        "mirror_source_selected": False,
        "prediction_ready": False,
        "verdict": (
            "The mirror nonmetricity row is algebraically fixed once H and N_alpha "
            "are fixed. The remaining source problem is the original N_alpha branch."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Nonmetricity Mirror Inverse Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Definition: `{payload['definition']}`",
        f"Matrix identity: `{payload['matrix_identity']}`",
        f"Mirror identity closed: {payload['mirror_identity_closed']}",
        f"Independent mirror N allowed: {payload['independent_mirror_n_allowed']}",
        f"Mirror source selected: {payload['mirror_source_selected']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Scalar Check",
        "",
    ]
    for key, value in payload["scalar_check"].items():
        lines.append(f"- {key}: `{value}`")
    lines.extend(["", "## Requirements", ""])
    lines.extend(f"- {item}" for item in payload["requirements"])
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
