from __future__ import annotations

from pathlib import Path
import json
import sys

import sympy as sp


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_relative_strain_q_regular_branch_gate import (
    build_payload as build_q_regular,
)


REPORT_PATH = Path("outputs/reports/p0_covariant_q_field_candidate_gate.md")
JSON_PATH = Path("outputs/reports/p0_covariant_q_field_candidate_gate.json")


def build_payload() -> dict:
    q_regular = build_q_regular()
    q, r1, r3 = sp.symbols("q r1 r3")
    odd_transport = r1 * q + r3 * q**3
    mirror_odd_residual = sp.expand(odd_transport.subs(q, -q) + odd_transport)
    candidates = [
        {
            "name": "log_b4vol_or_logdet",
            "covariant": True,
            "mirror_odd": True,
            "keeps_anisotropic_strain": False,
            "selects_l": False,
            "verdict": "reject as sole q: repeats determinant/B4vol underselection",
        },
        {
            "name": "trace_relative_strain",
            "covariant": True,
            "mirror_odd": True,
            "keeps_anisotropic_strain": False,
            "selects_l": "partial",
            "verdict": "diagnostic scalar only; loses shear/anisotropic solder data",
        },
        {
            "name": "relative_strain_tensor_Q",
            "covariant": True,
            "mirror_odd": True,
            "keeps_anisotropic_strain": True,
            "selects_l": "candidate",
            "verdict": "minimal viable q/Q object if polar/log branch is regular and source-selected",
        },
        {
            "name": "raw_L_geom",
            "covariant": False,
            "mirror_odd": "not guaranteed",
            "keeps_anisotropic_strain": True,
            "selects_l": False,
            "verdict": "reject until Lorentz/polar regularity and derivative law are proved",
        },
    ]
    return {
        "description": "Gate for choosing the covariant q/Q object used by the A_Janus lift.",
        "status": "q-field-candidate-selected-conditionally",
        "symbolic_odd_transport": str(odd_transport),
        "mirror_odd_residual": str(mirror_odd_residual),
        "candidate_rows": candidates,
        "selected_candidate": "relative_strain_tensor_Q",
        "selected_candidate_definition": q_regular["definition"],
        "selected_candidate_regular_gate": "p0_relative_strain_q_regular_branch_gate",
        "selected_candidate_derivative_gate": q_regular["derivative_gate"],
        "selected_candidate_trace_relation": q_regular["trace_relation"],
        "covariant_transport_target": "A_Janus(Q)=r1 Q + r3 Q^3 + higher odd source-derived terms",
        "regularity_requirements": [
            "same phi/L used by B4vol, K, Q_cross and Vlasov",
            "Lorentz/polar branch regularity and time orientation fixed before use",
            "DQ uses FrechetLog_H[D_alpha H] from the same Omega_alpha branch",
            "mirror inverse maps Q_plus_to_minus=-Q_minus_to_plus",
            "determinant trace is only Tr(Q), not the whole transport field",
        ],
        "source_fixed": False,
        "prediction_ready": False,
        "notable_improvement": (
            "The lift no longer depends on an arbitrary scalar q. The minimal viable "
            "object is the odd relative strain tensor Q; determinant/log-volume is only "
            "a trace diagnostic and cannot carry the full same-L transport."
        ),
        "remaining_lock": (
            "Derive the regular polar/log branch and the coefficients r1/r3 from "
            "Janus source/action or relative-curvature equations."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Covariant q/Q Field Candidate Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Selected candidate: {payload['selected_candidate']}",
        f"Source fixed: {payload['source_fixed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Odd Transport Check",
        "",
        f"- symbolic transport: `{payload['symbolic_odd_transport']}`",
        f"- mirror odd residual: `{payload['mirror_odd_residual']}`",
        "",
        "## Candidates",
        "",
        "| name | covariant | mirror odd | keeps anisotropic strain | selects L | verdict |",
        "|---|---|---|---|---|---|",
    ]
    for row in payload["candidate_rows"]:
        lines.append(
            f"| {row['name']} | {row['covariant']} | {row['mirror_odd']} | "
            f"{row['keeps_anisotropic_strain']} | {row['selects_l']} | {row['verdict']} |"
        )
    lines.extend(
        [
            "",
            "## Selected Candidate",
            "",
        f"- definition: `{payload['selected_candidate_definition']}`",
        f"- regular gate: `{payload['selected_candidate_regular_gate']}`",
        f"- derivative gate: `{payload['selected_candidate_derivative_gate']}`",
        f"- trace relation: `{payload['selected_candidate_trace_relation']}`",
        f"- transport target: `{payload['covariant_transport_target']}`",
            "",
            "## Regularity Requirements",
            "",
        ]
    )
    lines.extend(f"- {item}" for item in payload["regularity_requirements"])
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
