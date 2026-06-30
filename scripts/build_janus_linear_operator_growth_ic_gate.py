from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/janus_linear_operator_growth_ic_gate.md")
JSON_PATH = Path("outputs/reports/janus_linear_operator_growth_ic_gate.json")


def build_payload() -> dict:
    chain = [
        {"step": "Omega_s(a)", "requires": "source-derived sector backgrounds", "closed": False},
        {"step": "M(a)", "requires": "Omega_plus/Omega_minus_eff in one density convention", "closed": False},
        {"step": "G_J(a,a_i)", "requires": "growth propagator from M(a) and E_J(a)", "closed": False},
        {"step": "T_J(k,a_i)", "requires": "Janus transfer source, not imported scaffold", "closed": False},
        {"step": "A_J", "requires": "source-backed or declared no-fit amplitude", "closed": False},
        {"step": "IC equations", "requires": "same branch for density, theta, beta", "closed": False},
    ]
    forbidden_substitutes = [
        "Lambda-CDM transfer function",
        "Gaussian/lognormal/bounded toy IC",
        "sigma8/S8/survey normalization",
        "negative-proper density before Q_det branch is fixed",
        "physical beta before L_minus_to_plus closes",
    ]
    return {
        "description": "Bounded gate from Janus linear operator to growth, transfer, amplitude and IC readiness.",
        "status": "bounded-derivation-open",
        "chain": chain,
        "forbidden_substitutes": forbidden_substitutes,
        "operator_growth_ic_chain_written": True,
        "source_derived_operator_closed": False,
        "transfer_closed": False,
        "amplitude_closed": False,
        "ic_ready": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The linear prediction chain is explicit. It remains blocked until Omega_s(a), "
            "T_J(k), A_J, Q_det and L transport are source-derived without fit."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# Janus Linear Operator Growth IC Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Operator/growth/IC chain written: {payload['operator_growth_ic_chain_written']}",
        f"IC ready: {payload['ic_ready']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Chain",
        "",
        "| step | requires | closed |",
        "|---|---|---|",
    ]
    for row in payload["chain"]:
        lines.append(f"| {row['step']} | {row['requires']} | {row['closed']} |")
    lines.extend(["", "## Forbidden Substitutes", ""])
    lines.extend(f"- {item}" for item in payload["forbidden_substitutes"])
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
