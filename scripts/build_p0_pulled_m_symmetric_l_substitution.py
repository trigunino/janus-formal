from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_pulled_m_symmetric_l_substitution.md")
JSON_PATH = Path("outputs/reports/p0_pulled_m_symmetric_l_substitution.json")


def build_payload() -> dict:
    substitution_rows = [
        {
            "row": "l_response_split",
            "formula": "L^{-1}delta L = S_g + Omega, Sym(S_g)=S_g, Omega_ab=-Omega_ba",
            "status": "defined",
        },
        {
            "row": "symmetric_metric_piece",
            "formula": "S_g fixed by delta_g(L^T g_plus^{-1} L)=0",
            "status": "closed-up-to-index-convention",
        },
        {
            "row": "m_variation_split",
            "formula": "delta_g M = delta_g M[S_g] + delta_g M[Omega] + L(delta_g T_minus)L^T",
            "status": "closed-algebraic",
        },
        {
            "row": "omega_residual",
            "formula": "delta_g M[Omega] = L(Omega^T T_minus + T_minus Omega)L^T",
            "status": "open-lorentz-gauge-residual",
        },
        {
            "row": "dust_rank_one_test",
            "formula": "for T_minus=rho uu, Omega residual vanishes only if projected Omega leaves u direction fixed",
            "status": "condition-required",
        },
        {
            "row": "k_qcross_guard",
            "formula": "Omega choice must be identical for K transport and Q_cross; it cannot be chosen to cancel K only",
            "status": "required",
        },
    ]
    return {
        "description": "Substitution of the metric-fixed symmetric L response into delta_g M.",
        "status": "symmetric-l-substitution-closed-omega-open",
        "substitution_rows": substitution_rows,
        "symmetric_l_piece_substituted": True,
        "m_variation_split_closed": True,
        "omega_residual_isolated": True,
        "omega_residual_closed": False,
        "dust_rank_one_omega_condition_available": True,
        "same_omega_for_k_qcross_required": True,
        "omega_residual_closure_gate_available": True,
        "pulled_m_metric_response_closed": False,
        "full_k_plus_closed": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The metric-fixed symmetric L contribution can be substituted into delta_g M. "
            "Closure now reduces to the Lorentz-gauge residual Omega and mirror consistency."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Pulled M Symmetric L Substitution",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Symmetric L piece substituted: {payload['symmetric_l_piece_substituted']}",
        f"M variation split closed: {payload['m_variation_split_closed']}",
        f"Omega residual isolated: {payload['omega_residual_isolated']}",
        f"Omega residual closed: {payload['omega_residual_closed']}",
        f"Dust rank-one Omega condition available: {payload['dust_rank_one_omega_condition_available']}",
        f"Same Omega for K/Qcross required: {payload['same_omega_for_k_qcross_required']}",
        f"Omega residual closure gate available: {payload['omega_residual_closure_gate_available']}",
        f"Pulled M metric response closed: {payload['pulled_m_metric_response_closed']}",
        f"Full K_plus closed: {payload['full_k_plus_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Substitution Rows",
        "",
    ]
    for row in payload["substitution_rows"]:
        lines.append(f"- {row['row']}: `{row['formula']}` ({row['status']})")
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
