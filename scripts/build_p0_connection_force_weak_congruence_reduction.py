from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_connection_force_weak_congruence_reduction.md")
JSON_PATH = Path("outputs/reports/p0_connection_force_weak_congruence_reduction.json")


def build_payload() -> dict:
    reduction = [
        {
            "sector": "positive",
            "connection_force": "C_plus-minus^mu_{alpha beta} u_-to+^alpha u_-to+^beta",
            "weak_congruence_target": "u_-to+^nu D_plus_nu u_-to+^mu = 0",
            "interpretation": "transported negative dust follows plus receiver geodesics",
            "closed": False,
        },
        {
            "sector": "negative",
            "connection_force": "C_minus-plus^a_{mu nu} u_+to-^mu u_+to-^nu",
            "weak_congruence_target": "u_+to-^b D_minus_b u_+to-^a = 0",
            "interpretation": "transported positive dust follows minus receiver geodesics",
            "closed": False,
        },
    ]
    proof_obligations = [
        "derive weak congruence from Stueckelberg E_phi/E_L or S_couple",
        "prove plus and minus weak equations are inverse-map mirrors",
        "prove curl/integrability obstruction cancels on the dust image",
        "prove same L is used by dust K transport and optical Q_cross",
        "reinsert pressure/Pi before claiming tensor-matter closure",
    ]
    rejection_rules = [
        "do not upgrade weak congruence to full metric isometry",
        "do not set C=0 for transverse directions",
        "do not tune boundary conditions from observations",
        "do not mark R_plus/R_minus closed while any proof obligation is open",
    ]
    return {
        "description": "Reduction of relative-connection force cancellation to weak congruence targets.",
        "status": "weak-congruence-reduction-open",
        "reduction": reduction,
        "proof_obligations": proof_obligations,
        "rejection_rules": rejection_rules,
        "connection_force_reduced_to_weak_congruence": True,
        "weak_congruence_selector_artifact": "p0_janus_weak_congruence_selector_derivation_gate",
        "weak_congruence_source_derived": False,
        "r_plus_closed": False,
        "r_minus_closed": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The Cuu blocker reduces to projected receiver-geodesic conditions. "
            "This is narrower than isometry, but remains unproved until derived from the map equations."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Connection Force Weak Congruence Reduction",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Connection force reduced: {payload['connection_force_reduced_to_weak_congruence']}",
        f"Weak congruence selector artifact: `{payload['weak_congruence_selector_artifact']}`",
        f"Weak congruence source derived: {payload['weak_congruence_source_derived']}",
        f"R plus closed: {payload['r_plus_closed']}",
        f"R minus closed: {payload['r_minus_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Reduction",
        "",
    ]
    for row in payload["reduction"]:
        lines.append(f"- {row['sector']}: `{row['connection_force']}`")
        lines.append(f"  - target: `{row['weak_congruence_target']}`")
        lines.append(f"  - interpretation: {row['interpretation']}")
        lines.append(f"  - closed: {row['closed']}")
    lines.extend(["", "## Proof Obligations", ""])
    lines.extend(f"- {item}" for item in payload["proof_obligations"])
    lines.extend(["", "## Rejection Rules", ""])
    lines.extend(f"- {item}" for item in payload["rejection_rules"])
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
