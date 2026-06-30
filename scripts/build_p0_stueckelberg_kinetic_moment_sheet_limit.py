from __future__ import annotations

import json
from pathlib import Path


REPORT_PATH = Path("outputs/reports/p0_stueckelberg_kinetic_moment_sheet_limit.md")
JSON_PATH = Path("outputs/reports/p0_stueckelberg_kinetic_moment_sheet_limit.json")


def build_payload() -> dict:
    moment_chain = [
        {
            "step": "phase_space_stress",
            "formula": "T_to^{mu nu}(x)=int p^mu p^nu f_to(x,p) dP_to",
            "role": "kinetic definition replaces single-stream dust after caustic",
        },
        {
            "step": "cold_sheet_decomposition",
            "formula": "f_to(x,p)=sum_s w_s(x) delta(p-p_s(x))",
            "role": "finite sheets are a cold kinetic approximation",
        },
        {
            "step": "sheet_stress",
            "formula": "T_to^{mu nu}=sum_s rho_s_to u_s^mu u_s^nu",
            "role": "recovers sheet-sum stress without arbitrary weights",
        },
        {
            "step": "moment_conservation",
            "formula": "nabla_mu T_to^{mu}_{nu}=int p_nu C[f_to] dP_to",
            "role": "collisionless/transport equation controls conservation defects",
        },
    ]
    closure_obligations = [
        "derive f_to transport from Janus phi/L or sector geodesic flow",
        "show cold-sheet weights w_s are transported phase-space measure",
        "prove mirror kinetic distribution is inverse-supported",
        "derive optical Q_cross as a moment/projection of the same f_to",
    ]
    decision = {
        "sheet_sum_derived_as_cold_kinetic_limit": True,
        "arbitrary_sheet_weights_removed": True,
        "kinetic_transport_derived_from_janus": False,
        "physics_closed": False,
        "prediction_ready": False,
        "reason": (
            "The sheet-sum model is not arbitrary if treated as the cold-sheet limit of "
            "a kinetic distribution. This removes free sheet weights, but full closure "
            "requires deriving the kinetic transport and optical projection from Janus "
            "phi/L data."
        ),
    }
    return {
        "artifact": "p0_stueckelberg_kinetic_moment_sheet_limit",
        "status": "cold-kinetic-sheet-limit-conditional",
        "fit_used": False,
        "free_parameters": [],
        "physics_closed": False,
        "prediction_ready": False,
        "moment_chain": moment_chain,
        "closure_obligations": closure_obligations,
        "decision": decision,
    }


def render_markdown(payload: dict) -> str:
    decision = payload["decision"]
    lines = [
        "# P0 Stueckelberg Kinetic Moment Sheet Limit",
        "",
        f"Status: {payload['status']}",
        f"Fit used: {payload['fit_used']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Moment Chain",
    ]
    for row in payload["moment_chain"]:
        lines.append(f"- {row['step']}: `{row['formula']}`")
        lines.append(f"  - role: {row['role']}")
    lines.extend(["", "## Closure Obligations"])
    lines.extend(f"- {item}" for item in payload["closure_obligations"])
    lines.extend(
        [
            "",
            "## Decision",
            f"Sheet sum derived as cold kinetic limit: {decision['sheet_sum_derived_as_cold_kinetic_limit']}",
            f"Arbitrary sheet weights removed: {decision['arbitrary_sheet_weights_removed']}",
            f"Kinetic transport derived from Janus: {decision['kinetic_transport_derived_from_janus']}",
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
