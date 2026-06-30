from __future__ import annotations

from pathlib import Path
import json
import sys

import sympy as sp


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_lorentz_polar_projection_regular_branch import (
    build_payload as build_polar_regular,
)
from scripts.build_p0_polar_projection_derivative_obstruction import (
    build_payload as build_polar_derivative,
)


REPORT_PATH = Path("outputs/reports/p0_relative_strain_q_regular_branch_gate.md")
JSON_PATH = Path("outputs/reports/p0_relative_strain_q_regular_branch_gate.json")


def build_payload() -> dict:
    polar = build_polar_regular()
    derivative = build_polar_derivative()
    h = sp.symbols("h", positive=True)
    q_eigen = sp.log(h) / 2
    mirror_q_eigen = sp.log(1 / h) / 2
    mirror_residual = sp.simplify(q_eigen + mirror_q_eigen)

    return {
        "description": "Regular-branch definition gate for the covariant relative strain tensor Q.",
        "status": "relative-strain-q-regular-branch-defined-not-source-closed",
        "definition": "H=eta^{-1} L_geom^T eta L_geom; Q=1/2 log(H) on a real smooth regular branch",
        "mirror_definition": "mirror inverse uses H^{-1}, hence Q_mirror=-Q",
        "scalar_eigen_check": {
            "q_eigen": str(q_eigen),
            "mirror_q_eigen": str(mirror_q_eigen),
            "mirror_odd_residual": str(mirror_residual),
        },
        "trace_relation": "Tr(Q)=1/2 log det(H); determinant/log-volume is only the trace of Q",
        "anisotropic_part": "trace-free Q_TF = Q - (Tr(Q)/n) I carries non-volume solder strain",
        "regularity_from_polar_gate": polar["regularity_conditions"],
        "derivative_obligations": [
            row["obligation"] for row in derivative["square_root_obligations"]
        ],
        "derivative_gate": "p0_relative_strain_q_derivative_omega_gate",
        "dh_source_gate": "p0_relative_strain_dh_lgeom_vs_lorentz_gate",
        "derivative_rule": "D_alpha Q=1/2 FrechetLog_H[D_alpha H], not scalar H^{-1}D_alpha H unless [H,D_alpha H]=0",
        "q_regular_branch_defined": True,
        "q_source_selected": False,
        "q_derivative_closed": False,
        "same_l_omega_closed": False,
        "prediction_ready": False,
        "notable_improvement": (
            "Q now has a concrete regular-branch definition. Its trace reproduces "
            "log-determinant information, while its trace-free part keeps the "
            "anisotropic same-L solder data needed by K/Q_cross/Vlasov."
        ),
        "remaining_lock": (
            "Derive that this polar/log branch is selected by Janus source/action "
            "and close DQ through the same Omega_alpha used by L transport."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Relative Strain Q Regular Branch Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Definition: `{payload['definition']}`",
        f"Mirror definition: `{payload['mirror_definition']}`",
        f"Q regular branch defined: {payload['q_regular_branch_defined']}",
        f"Q source selected: {payload['q_source_selected']}",
        f"Q derivative closed: {payload['q_derivative_closed']}",
        f"Same L/Omega closed: {payload['same_l_omega_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Scalar Eigen Check",
        "",
    ]
    for key, value in payload["scalar_eigen_check"].items():
        lines.append(f"- {key}: `{value}`")
    lines.extend(
        [
            "",
            "## Trace And Anisotropy",
            "",
            f"- trace relation: `{payload['trace_relation']}`",
            f"- anisotropic part: `{payload['anisotropic_part']}`",
            "",
            "## Regularity Conditions",
            "",
        ]
    )
    lines.extend(f"- {item}" for item in payload["regularity_from_polar_gate"])
    lines.extend(["", "## Derivative Obligations", ""])
    lines.extend(f"- `{item}`" for item in payload["derivative_obligations"])
    lines.append(f"- D H source gate: `{payload['dh_source_gate']}`")
    lines.append(f"- derivative gate: `{payload['derivative_gate']}`")
    lines.append(f"- derivative rule: `{payload['derivative_rule']}`")
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
