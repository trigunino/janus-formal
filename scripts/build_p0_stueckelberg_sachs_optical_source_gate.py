from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_stueckelberg_sachs_optical_source_gate.md")
JSON_PATH = Path("outputs/reports/p0_stueckelberg_sachs_optical_source_gate.json")


def build_payload() -> dict:
    sachs_chain = [
        {
            "step": "null_focusing",
            "formula": "d theta/dlambda = -1/2 theta^2 - sigma^2 + omega^2 - R_{mu nu} k^mu k^nu",
            "role": "optical equation source is Ricci contraction along null ray",
        },
        {
            "step": "field_equation_substitution",
            "formula": "R_{mu nu} k^mu k^nu <- K_cross/matter source contraction",
            "role": "requires Janus field equations, not optical normalization",
        },
        {
            "step": "stress_projection",
            "formula": "candidate source ~ k_mu k_nu T_to^{mu nu}",
            "role": "matches part of P_opt candidate",
        },
        {
            "step": "screen_projection",
            "formula": "m_mu mbar_nu T_to^{mu nu} contributes only if field equation/optical scalar derivation requires it",
            "role": "screen term cannot be inserted as fit",
        },
    ]
    blockers = [
        "Janus Ricci/source substitution must supply the positive/negative mass sign",
        "screen projection term must be derived from optical tidal/shear equations",
        "Q_det volume factors remain outside Sachs source normalization",
        "same transported T_to/f_to must feed both stress and optical source",
    ]
    decision = {
        "sachs_gate_defined": True,
        "popt_partially_matches_sachs_source": True,
        "janus_sign_derived": False,
        "screen_term_derived": False,
        "prediction_ready": False,
        "reason": (
            "The null-null stress contraction is the Sachs-compatible part of P_opt. "
            "The Janus sign and any screen/tidal terms still need derivation from the "
            "field equations and optical scalar system."
        ),
    }
    return {
        "artifact": "p0_stueckelberg_sachs_optical_source_gate",
        "status": "sachs-source-gate-open",
        "fit_used": False,
        "free_parameters": [],
        "physics_closed": False,
        "prediction_ready": False,
        "sachs_chain": sachs_chain,
        "blockers": blockers,
        "decision": decision,
    }


def render_markdown(payload: dict) -> str:
    decision = payload["decision"]
    lines = [
        "# P0 Stueckelberg Sachs Optical Source Gate",
        "",
        f"Status: {payload['status']}",
        f"Fit used: {payload['fit_used']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Sachs Chain",
    ]
    for row in payload["sachs_chain"]:
        lines.append(f"- {row['step']}: `{row['formula']}`")
        lines.append(f"  - role: {row['role']}")
    lines.extend(["", "## Blockers"])
    lines.extend(f"- {item}" for item in payload["blockers"])
    lines.extend(
        [
            "",
            "## Decision",
            f"Sachs gate defined: {decision['sachs_gate_defined']}",
            f"P_opt partially matches Sachs source: {decision['popt_partially_matches_sachs_source']}",
            f"Janus sign derived: {decision['janus_sign_derived']}",
            f"Screen term derived: {decision['screen_term_derived']}",
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
