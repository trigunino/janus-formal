from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_bianchi_minimal_joint_dl_dlogb_solution.md")
JSON_PATH = Path("outputs/reports/p0_bianchi_minimal_joint_dl_dlogb_solution.json")


def build_payload() -> dict:
    equations = [
        {
            "name": "rank_one_cross_source",
            "formula": "K_to^{mu nu}=rho_to u_to^mu u_to^nu",
            "role": "dust-only cross stress in the receiver sector",
        },
        {
            "name": "bianchi_product_rule",
            "formula": (
                "D_mu(B rho u^mu u^nu)=B[(D_mu(rho u^mu)+rho u^mu D_mu log B)u^nu "
                "+ rho u^mu D_mu u^nu]"
            ),
            "role": "splits determinant continuity from transverse acceleration",
        },
        {
            "name": "longitudinal_measure_condition",
            "formula": "D_mu(rho u^mu)+rho u^mu D_mu log B=0",
            "role": "selects the flow contraction u.D log B, not the full gradient",
        },
        {
            "name": "transverse_transport_condition",
            "formula": "h^nu_alpha[(Omega_u u)^alpha + C^alpha_{beta gamma}u^beta u^gamma]=0",
            "role": "selects only the projected action of Omega_u on u",
        },
        {
            "name": "minimal_lorentz_generator",
            "formula": "Omega_u_min=-a_req tensor u_flat + u tensor a_req_flat, a_req=-h C(u,u)",
            "role": "unique boost-only generator mapping u to the required transverse acceleration",
        },
    ]
    solved_components = {
        "u_dot_dlogb_selected": True,
        "full_dlogb_gradient_selected": False,
        "omega_u_u_projected_selected": True,
        "full_omega_alpha_selected": False,
        "minimal_boost_generator_written": True,
        "spatial_rotation_gauge_selected": False,
    }
    closure_obligations = [
        "derive C^alpha_{beta gamma} from the plus/minus Janus connection difference in the chosen tetrads",
        "prove mirror reciprocity for the minus-to-plus and plus-to-minus branches",
        "prove integrability D_alpha L=Omega_alpha L, not only the flow contraction Omega_u",
        "show Q_cross uses the same L and same minimal branch without fitting",
        "extend beyond rank-one dust before pressure/Pi or multistream claims",
        "verify no B_4vol, V3_dust, rho_to, Q_det, or Q_cross double counting",
    ]
    no_rustine_rules = [
        "Omega is fixed by the transverse Bianchi residual, not by lensing data",
        "D log B is fixed by the longitudinal product rule, not by scalar calibration",
        "unselected transverse D log B and spatial Omega rotations remain open, not hidden",
        "Q_det and Q_cross cannot absorb remaining tensor terms",
    ]
    return {
        "description": (
            "Bianchi-minimal joint branch for the two current P0 blockers: D_u L/Omega "
            "and D log B_4vol. It separates the rank-one dust residual into longitudinal "
            "measure continuity and transverse transport equations."
        ),
        "status": "conditional-joint-branch-open",
        "janus_starting_point": "coupled Janus field equations plus Bianchi identity for determinant-weighted cross sources",
        "equations": equations,
        "solved_components": solved_components,
        "closure_obligations": closure_obligations,
        "no_rustine_rules": no_rustine_rules,
        "starts_from_janus_bianchi": True,
        "joint_system_written": True,
        "u_dot_dlogb_selected": True,
        "omega_u_u_projected_selected": True,
        "full_dlogb_gradient_selected": False,
        "full_omega_alpha_selected": False,
        "same_l_for_k_qcross_required": True,
        "rank_one_dust_only": True,
        "pressure_pi_closed": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "This is the strongest non-rustine progress: Bianchi does not select a full "
            "L/Omega connection or full D log B gradient, but it does select the dust-flow "
            "contraction u.D log B and the projected action Omega_u u needed to cancel the "
            "transverse connection force. Full closure still requires mirror, integrability, "
            "same-L Q_cross, and non-dust extensions."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Bianchi-Minimal Joint DL/DlogB Solution",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Janus starting point: {payload['janus_starting_point']}",
        f"Starts from Janus Bianchi: {payload['starts_from_janus_bianchi']}",
        f"Joint system written: {payload['joint_system_written']}",
        f"u.D log B selected: {payload['u_dot_dlogb_selected']}",
        f"Projected Omega_u u selected: {payload['omega_u_u_projected_selected']}",
        f"Full D log B gradient selected: {payload['full_dlogb_gradient_selected']}",
        f"Full Omega_alpha selected: {payload['full_omega_alpha_selected']}",
        f"Same L for K/Q_cross required: {payload['same_l_for_k_qcross_required']}",
        f"Rank-one dust only: {payload['rank_one_dust_only']}",
        f"Pressure/Pi closed: {payload['pressure_pi_closed']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Equations",
        "",
        "| name | formula | role |",
        "|---|---|---|",
    ]
    for row in payload["equations"]:
        lines.append(f"| {row['name']} | `{row['formula']}` | {row['role']} |")
    lines.extend(["", "## Solved Components", ""])
    lines.extend(f"- {key}: {value}" for key, value in payload["solved_components"].items())
    lines.extend(["", "## Closure Obligations", ""])
    lines.extend(f"- {item}" for item in payload["closure_obligations"])
    lines.extend(["", "## No-Rustine Rules", ""])
    lines.extend(f"- {item}" for item in payload["no_rustine_rules"])
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
