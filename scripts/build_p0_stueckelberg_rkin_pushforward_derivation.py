from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_stueckelberg_rkin_pushforward_derivation.md")
JSON_PATH = Path("outputs/reports/p0_stueckelberg_rkin_pushforward_derivation.json")


def build_payload() -> dict:
    derivation = [
        {
            "step": "source_liouville",
            "formula": "L_minus[f_minus]=p^a partial_a f_minus-Gamma_minus^i_{bc}p^b p^c partial_{p^i}f_minus=0",
            "status": "source-sector-assumption",
        },
        {
            "step": "pushforward",
            "formula": "f_-to+(x,p)=Phi_* f_minus with p^mu=L^mu_a p^a",
            "status": "definition",
        },
        {
            "step": "receiver_liouville",
            "formula": "L_plus[f_-to+]=R_kin,+",
            "status": "derived-shape",
        },
        {
            "step": "residual",
            "formula": "R_kin,+=(L_plus Phi_* - Phi_* L_minus)[f_minus]",
            "status": "no-fit-commutator",
        },
        {
            "step": "cold_limit",
            "formula": "first moment of R_kin,+ -> rho_-to+ h C_plus-minus u u",
            "status": "conditional",
        },
    ]
    mirror = {
        "formula": "R_kin,-=(L_minus Phi^{-1}_* - Phi^{-1}_* L_plus)[f_plus]",
        "required": "must be inverse-supported mirror of plus residual",
        "closed": False,
    }
    decision = {
        "rkin_shape_derived": True,
        "fit_used": False,
        "source_derived_transport_closed": False,
        "cold_moment_matches_prior_gate": True,
        "prediction_ready": False,
        "reason": (
            "R_kin has a clean no-fit definition as the commutator between receiver "
            "Liouville flow and pushed source Liouville flow. Closure still requires "
            "proving this commutator vanishes or has the required mirror/source form "
            "for the chosen Janus phi/L."
        ),
    }
    return {
        "artifact": "p0_stueckelberg_rkin_pushforward_derivation",
        "status": "rkin-commutator-derived-closure-open",
        "physics_closed": False,
        "prediction_ready": False,
        "derivation": derivation,
        "mirror": mirror,
        "decision": decision,
    }


def render_markdown(payload: dict) -> str:
    decision = payload["decision"]
    lines = [
        "# P0 Stueckelberg R_kin Pushforward Derivation",
        "",
        f"Status: {payload['status']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Derivation",
    ]
    for row in payload["derivation"]:
        lines.append(f"- {row['step']}: `{row['formula']}` (status={row['status']})")
    mirror = payload["mirror"]
    lines.extend(
        [
            "",
            "## Mirror",
            f"Formula: `{mirror['formula']}`",
            f"Required: {mirror['required']}",
            f"Closed: {mirror['closed']}",
            "",
            "## Decision",
            f"R_kin shape derived: {decision['rkin_shape_derived']}",
            f"Fit used: {decision['fit_used']}",
            f"Source-derived transport closed: {decision['source_derived_transport_closed']}",
            f"Cold moment matches prior gate: {decision['cold_moment_matches_prior_gate']}",
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
