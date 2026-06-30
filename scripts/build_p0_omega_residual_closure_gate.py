from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_omega_residual_closure_gate.md")
JSON_PATH = Path("outputs/reports/p0_omega_residual_closure_gate.json")


def build_payload() -> dict:
    gate_rows = [
        {
            "gate": "residual_isolated",
            "requirement": "delta_g M[Omega]=L(Omega^T T_minus + T_minus Omega)L^T",
            "closed": True,
        },
        {
            "gate": "dust_rank_one_condition",
            "requirement": "Omega residual must vanish or be proved harmless for T_minus=rho u u",
            "closed": False,
        },
        {
            "gate": "k_qcross_same_omega",
            "requirement": "same Omega must be used for K transport and Q_cross projection",
            "closed": False,
        },
        {
            "gate": "mirror_inverse",
            "requirement": "plus-to-minus Omega must be inverse/mirror compatible",
            "closed": False,
        },
        {
            "gate": "no_fit_selection",
            "requirement": "Omega cannot be chosen only to cancel one residual",
            "closed": True,
        },
    ]
    return {
        "description": "Closure gate for the Lorentz-gauge Omega residual in pulled M metric response.",
        "status": "omega-residual-gate-open",
        "gate_rows": gate_rows,
        "omega_residual_isolated": True,
        "omega_dust_rank_one_condition_available": True,
        "dust_rank_one_condition_closed": False,
        "k_qcross_same_omega_closed": False,
        "omega_k_qcross_consistency_gate_available": True,
        "omega_closure_routes_gate_available": True,
        "mirror_inverse_closed": False,
        "no_fit_selection_rule_closed": True,
        "omega_residual_closed": False,
        "pulled_m_metric_response_closed": False,
        "full_k_plus_closed": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "Omega is now the explicit remaining Lorentz-gauge blocker. It needs a "
            "dust-rank-one condition, K/Q_cross consistency, and mirror compatibility."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Omega Residual Closure Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Omega residual isolated: {payload['omega_residual_isolated']}",
        f"Omega dust rank-one condition available: {payload['omega_dust_rank_one_condition_available']}",
        f"Dust rank-one condition closed: {payload['dust_rank_one_condition_closed']}",
        f"K/Qcross same Omega closed: {payload['k_qcross_same_omega_closed']}",
        f"Omega K/Qcross consistency gate available: {payload['omega_k_qcross_consistency_gate_available']}",
        f"Omega closure routes gate available: {payload['omega_closure_routes_gate_available']}",
        f"Mirror inverse closed: {payload['mirror_inverse_closed']}",
        f"No-fit selection rule closed: {payload['no_fit_selection_rule_closed']}",
        f"Omega residual closed: {payload['omega_residual_closed']}",
        f"Pulled M metric response closed: {payload['pulled_m_metric_response_closed']}",
        f"Full K_plus closed: {payload['full_k_plus_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Gate Rows",
        "",
    ]
    for row in payload["gate_rows"]:
        lines.append(f"- {row['gate']}: {row['requirement']} (closed: {row['closed']})")
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
