from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_bianchi_minimal_mirror_inverse_attempt.md")
JSON_PATH = Path("outputs/reports/p0_bianchi_minimal_mirror_inverse_attempt.json")


def build_payload() -> dict:
    inverse_map_equations = [
        {
            "name": "lorentz_inverse",
            "formula": "L_pm=L_mp^{-1}, equivalently L_mp=L_pm^{-1}",
            "role": "plus-to-minus and minus-to-plus maps are not independent fit knobs",
        },
        {
            "name": "omega_inverse_transport",
            "formula": "Omega_alpha_mp=-L_pm^{-1} Omega_alpha_pm L_pm plus sector-connection conversion terms",
            "role": "inverse branch transports the same Lorentz connection data after changing receiver derivative",
        },
        {
            "name": "reciprocal_b4vol",
            "formula": "B_4vol_pm B_4vol_mp=1, so log B_4vol_pm=-log B_4vol_mp after inverse pullback",
            "role": "determinant weights are reciprocal rather than separately calibratable scalars",
        },
    ]
    local_flow_implications = [
        {
            "row": "plus_receives_minus",
            "implied_by_joint_branch": True,
            "longitudinal_condition": "u_pm.D_plus log B_4vol_pm is selected by the product-rule residual",
            "transverse_condition": "h_pm Omega_u_pm u_pm cancels the projected C_pm(u_pm,u_pm) force",
            "full_connection_selected": False,
        },
        {
            "row": "minus_receives_plus",
            "implied_by_inverse_transport_only": True,
            "longitudinal_condition": "u_mp.D_minus log B_4vol_mp must be the reciprocal transported condition",
            "transverse_condition": "h_mp Omega_u_mp u_mp must cancel the mirrored projected C_mp(u_mp,u_mp) force",
            "full_connection_selected": False,
        },
    ]
    residual_rows = [
        {
            "row": "plus_receives_minus",
            "required_residual": "R_pm_parallel=0 and h_pm R_pm=0",
            "closed": False,
            "reason": "local flow branch closes only the selected contraction, not full mirror/integrability",
        },
        {
            "row": "minus_receives_plus",
            "required_residual": "R_mp_parallel=0 and h_mp R_mp=0",
            "closed": False,
            "reason": "inverse transport is a candidate law until the mirrored Bianchi row is checked",
        },
    ]
    consistency_requirements = [
        {
            "requirement": "same_l_for_qcross",
            "detail": "Q_cross must use the same inverse-paired L_pm/L_mp as K transport",
            "closed": False,
        },
        {
            "requirement": "no_fit",
            "detail": "do not tune L_pm, L_mp, Omega, or B_4vol after inspecting residuals",
            "closed": True,
        },
        {
            "requirement": "no_scalar_absorption",
            "detail": "do not absorb residual rows into Q_det, Q_cross, rho_to, or B_4vol scalars",
            "closed": True,
        },
    ]
    return {
        "description": (
            "Bounded P0 mirror-inverse consistency attempt for the Bianchi-minimal joint branch. "
            "It records what the local flow solution implies under inverse transport and keeps "
            "both mirrored Bianchi residual rows open."
        ),
        "status": "mirror-inverse-consistency-attempt-open",
        "starts_from": [
            "p0_bianchi_minimal_joint_dl_dlogb_solution",
            "p0_bianchi_minimal_integrability_mirror_gate",
        ],
        "inverse_map_equations": inverse_map_equations,
        "local_flow_implications": local_flow_implications,
        "residual_rows": residual_rows,
        "consistency_requirements": consistency_requirements,
        "inverse_map_written": True,
        "omega_inverse_transport_written": True,
        "b4vol_reciprocity_written": True,
        "local_flow_branch_implications_written": True,
        "both_residual_rows_required": True,
        "both_residual_rows_closed": False,
        "mirror_inverse_closed": False,
        "same_l_for_qcross_required": True,
        "fitting_allowed": False,
        "scalar_absorption_allowed": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The local branch gives a candidate inverse-paired mirror law, but mirror consistency "
            "is not closed unless both plus-receives-minus and minus-receives-plus residual rows "
            "vanish using the same L for K and Q_cross. No fitting or scalar absorption is allowed."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Bianchi-Minimal Mirror-Inverse Consistency Attempt",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Starts from: {', '.join(payload['starts_from'])}",
        f"Inverse map written: {payload['inverse_map_written']}",
        f"Omega inverse transport written: {payload['omega_inverse_transport_written']}",
        f"B_4vol reciprocity written: {payload['b4vol_reciprocity_written']}",
        f"Local flow branch implications written: {payload['local_flow_branch_implications_written']}",
        f"Both residual rows required: {payload['both_residual_rows_required']}",
        f"Both residual rows closed: {payload['both_residual_rows_closed']}",
        f"Mirror inverse closed: {payload['mirror_inverse_closed']}",
        f"Same L for Q_cross required: {payload['same_l_for_qcross_required']}",
        f"Fitting allowed: {payload['fitting_allowed']}",
        f"Scalar absorption allowed: {payload['scalar_absorption_allowed']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Inverse Map Equations",
        "",
        "| name | formula | role |",
        "|---|---|---|",
    ]
    for row in payload["inverse_map_equations"]:
        lines.append(f"| {row['name']} | `{row['formula']}` | {row['role']} |")
    lines.extend(["", "## Local Flow Implications", ""])
    for row in payload["local_flow_implications"]:
        lines.append(f"- {row['row']}:")
        lines.append(f"  - longitudinal condition: `{row['longitudinal_condition']}`")
        lines.append(f"  - transverse condition: `{row['transverse_condition']}`")
        lines.append(f"  - full connection selected: {row['full_connection_selected']}")
    lines.extend(["", "## Residual Rows", "", "| row | required residual | closed | reason |", "|---|---|---|---|"])
    for row in payload["residual_rows"]:
        lines.append(f"| {row['row']} | `{row['required_residual']}` | {row['closed']} | {row['reason']} |")
    lines.extend(["", "## Consistency Requirements", "", "| requirement | detail | closed |", "|---|---|---|"])
    for row in payload["consistency_requirements"]:
        lines.append(f"| {row['requirement']} | {row['detail']} | {row['closed']} |")
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
