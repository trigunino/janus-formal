from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_stueckelberg_kinetic_transport_candidate.md")
JSON_PATH = Path("outputs/reports/p0_stueckelberg_kinetic_transport_candidate.json")


def build_payload() -> dict:
    equations = [
        {
            "sector": "plus",
            "equation": "p^mu partial_mu f_-to+ - Gamma_plus^i_{alpha beta} p^alpha p^beta partial_{p^i} f_-to+ = R_kin,+[phi,L,f_-]",
            "residual": "R_kin,+ must equal transported source-flow defect; zero only if phi/L maps source geodesics to plus geodesics",
        },
        {
            "sector": "minus",
            "equation": "p^a partial_a f_+to- - Gamma_minus^i_{bc} p^b p^c partial_{p^i} f_+to- = R_kin,-[phi^{-1},L^{-1},f_+]",
            "residual": "mirror residual must be inverse-supported, not fitted independently",
        },
    ]
    moment_tests = [
        {
            "name": "zeroth_moment",
            "target": "transported mass continuity",
            "closed": "conditional",
        },
        {
            "name": "first_moment",
            "target": "momentum/geodesic residual equals rho h Cuu in cold limit",
            "closed": "conditional",
        },
        {
            "name": "second_moment",
            "target": "stress tensor includes pressure/velocity-dispersion when not cold",
            "closed": False,
        },
    ]
    decision = {
        "kinetic_equation_shape_defined": True,
        "source_derived": False,
        "cold_limit_matches_sheet_sum": True,
        "full_kinetic_closure": False,
        "prediction_ready": False,
        "reason": (
            "The kinetic transport candidate cleanly generalizes sheet-sum diagnostics. "
            "It is still not Janus-derived closure until R_kin is obtained from phi/L "
            "transport identities and its moments close without fitting."
        ),
    }
    return {
        "artifact": "p0_stueckelberg_kinetic_transport_candidate",
        "status": "kinetic-transport-candidate-open",
        "fit_used": False,
        "free_parameters": [],
        "physics_closed": False,
        "prediction_ready": False,
        "equations": equations,
        "moment_tests": moment_tests,
        "decision": decision,
    }


def render_markdown(payload: dict) -> str:
    decision = payload["decision"]
    lines = [
        "# P0 Stueckelberg Kinetic Transport Candidate",
        "",
        f"Status: {payload['status']}",
        f"Fit used: {payload['fit_used']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Equations",
    ]
    for row in payload["equations"]:
        lines.append(f"- {row['sector']}: `{row['equation']}`")
        lines.append(f"  - residual: {row['residual']}")
    lines.extend(["", "## Moment Tests"])
    for row in payload["moment_tests"]:
        lines.append(f"- {row['name']}: {row['target']} (closed={row['closed']})")
    lines.extend(
        [
            "",
            "## Decision",
            f"Kinetic equation shape defined: {decision['kinetic_equation_shape_defined']}",
            f"Source derived: {decision['source_derived']}",
            f"Cold limit matches sheet sum: {decision['cold_limit_matches_sheet_sum']}",
            f"Full kinetic closure: {decision['full_kinetic_closure']}",
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
