from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_tracefree_h_frechet_log_adjoint_gate.md")
JSON_PATH = Path("outputs/reports/p0_tracefree_h_frechet_log_adjoint_gate.json")


def build_payload() -> dict:
    spectral_rules = [
        {
            "rule": "frechet_log_kernel",
            "formula": "L_log,H[A]_ij = f^[1](lambda_i,lambda_j) A_ij",
            "condition": "H diagonalizable on the selected regular log branch",
        },
        {
            "rule": "divided_difference",
            "formula": "f^[1](li,lj)=(log(li)-log(lj))/(li-lj), f^[1](li,li)=1/li",
            "condition": "positive/nonzero spectrum with continuous diagonal limit",
        },
        {
            "rule": "self_adjoint_spd_branch",
            "formula": "<B,L_log,H[A]> = <L_log,H[B],A>",
            "condition": "H self-adjoint positive branch and same trace/Frobenius pairing",
        },
        {
            "rule": "qtf_to_h_gradient",
            "formula": "G_H = 1/2 L_log,H^*[P_STF(G_Q)] + deltaP_STF terms",
            "condition": "only after projector dependency and source-action provenance are handled",
        },
    ]
    requirements = [
        "regular spectral/log branch for H",
        "same inner product used for adjoint and source variation",
        "same L/Omega/tetrad branch as Q_TF and Q_cross",
        "projector variation terms carried separately",
        "boundary terms fixed before integrating derivative actions by parts",
        "Janus source/action provenance before prediction use",
    ]
    forbidden_routes = [
        "replace L_log,H^* by scalar H^{-1} outside a commuting/eigen branch",
        "drop off-diagonal divided-difference coefficients",
        "use determinant trace as the trace-free adjoint source",
        "claim source closure from adjoint algebra alone",
    ]
    return {
        "description": "Bounded P0 gate for the FrechetLog_H adjoint in the Q_TF-to-H variation.",
        "status": "tracefree-h-frechet-log-adjoint-gate-open",
        "target_channel": "H_TF/Q_TF",
        "spectral_adjoint_recorded": True,
        "self_adjoint_only_on_spd_branch": True,
        "commuting_shortcut_allowed": False,
        "offdiagonal_kernel_required": True,
        "projector_dependency_required": True,
        "source_provenance_closed": False,
        "accepted_as_closure": False,
        "spectral_rules": spectral_rules,
        "requirements": requirements,
        "forbidden_routes": forbidden_routes,
        "prediction": False,
        "prediction_ready": False,
        "verdict": (
            "The FrechetLog adjoint is now explicit. It is a valid algebraic "
            "transport rule on a regular self-adjoint log branch, but it is not "
            "a Janus source law and cannot replace source/action provenance."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Trace-Free H FrechetLog Adjoint Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Target channel: {payload['target_channel']}",
        f"Spectral adjoint recorded: {payload['spectral_adjoint_recorded']}",
        f"Self-adjoint only on SPD branch: {payload['self_adjoint_only_on_spd_branch']}",
        f"Commuting shortcut allowed: {payload['commuting_shortcut_allowed']}",
        f"Offdiagonal kernel required: {payload['offdiagonal_kernel_required']}",
        f"Projector dependency required: {payload['projector_dependency_required']}",
        f"Source provenance closed: {payload['source_provenance_closed']}",
        f"Accepted as closure: {payload['accepted_as_closure']}",
        f"Prediction: {payload['prediction']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Spectral Rules",
        "",
        "| rule | formula | condition |",
        "|---|---|---|",
    ]
    for row in payload["spectral_rules"]:
        lines.append(f"| {row['rule']} | `{row['formula']}` | {row['condition']} |")
    lines.extend(["", "## Requirements", ""])
    lines.extend(f"- {item}" for item in payload["requirements"])
    lines.extend(["", "## Forbidden Routes", ""])
    lines.extend(f"- {item}" for item in payload["forbidden_routes"])
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
