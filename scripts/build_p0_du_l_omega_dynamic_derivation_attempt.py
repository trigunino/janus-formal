from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_du_l_omega_dynamic_derivation_attempt.md")
JSON_PATH = Path("outputs/reports/p0_du_l_omega_dynamic_derivation_attempt.json")


def build_payload() -> dict:
    derivation_steps = [
        {
            "step": "lorentz_tetrad_bridge",
            "statement": "L maps source-sector tetrad components into receiver-sector tetrad components",
            "formula": "v_to^A=L^A_B v_from^B, with L^T eta L=eta",
            "proved": "algebraic",
        },
        {
            "step": "connection_from_dynamic_l",
            "statement": "a dynamic L defines the Lorentz connection one-form used by the residual",
            "formula": "Omega_alpha=(D_alpha L)L^{-1}, Omega_{alpha AB}=-Omega_{alpha BA}",
            "proved": "algebraic-if-L-is-Lorentz",
        },
        {
            "step": "dust_congruence_condition",
            "statement": "rank-one dust cancellation requires the transported frame to keep u parallel along the dust flow",
            "formula": "Omega_u u=0, where Omega_u=u^alpha Omega_alpha",
            "proved": "necessary-algebraic-target",
        },
        {
            "step": "projected_cuu_cancellation_target",
            "statement": "projected dust force cancellation targets the transverse connection force",
            "formula": "h E_dust = rho h C(u,u), then require the dynamic DL/Omega terms to cancel projected Cuu",
            "proved": "target-not-source-derived",
        },
    ]
    algebraic_results = [
        "If L is Lorentz, Omega_alpha=(D_alpha L)L^{-1} is eta-antisymmetric.",
        "For T=rho u u, Omega^T T+T Omega reduces to rho[(Omega_u u)_flat u_flat+u_flat (Omega_u u)_flat].",
        "For rho != 0 and normalized timelike u, Omega_u u=0 cancels the rank-one dust Omega residual.",
        "The projected Cuu row can be stated as a cancellation target against h E_dust.",
    ]
    source_dependent_gaps = [
        "Janus source/action equations have not selected the dynamic L.",
        "The dust congruence law that forces Omega_u u=0 is not derived.",
        "The projected Cuu cancellation is not proved from the action for dynamic L.",
        "Mirror consistency and pressure/Pi extensions remain open.",
    ]
    consistency_requirements = [
        {
            "requirement": "same_l_for_k",
            "detail": "the L used in Omega_alpha must also enter K_plus/K_minus transport",
            "closed": False,
        },
        {
            "requirement": "same_l_for_qcross",
            "detail": "the same L must induce Q_cross optical contractions",
            "closed": False,
        },
        {
            "requirement": "no_scalar_absorption",
            "detail": "do not absorb the residual into Q_det, Q_cross, density, or a fitted scalar",
            "closed": True,
        },
        {
            "requirement": "no_posthoc_fit",
            "detail": "do not fit L/Omega after inspecting the Cuu or lensing residual",
            "closed": True,
        },
    ]
    return {
        "description": "Bounded P0 dynamic D_u L / Omega_u u=0 derivation attempt.",
        "status": "dynamic-du-l-omega-derivation-attempt-open",
        "derivation_steps": derivation_steps,
        "algebraic_results": algebraic_results,
        "source_dependent_gaps": source_dependent_gaps,
        "consistency_requirements": consistency_requirements,
        "l_as_lorentz_tetrad_bridge": True,
        "omega_defined_from_l": True,
        "omega_u_u_zero_cancellation_proved_algebraically": True,
        "projected_cuu_cancellation_target_defined": True,
        "projected_cuu_cancellation_source_derived": False,
        "same_l_for_k_qcross_required": True,
        "fitting_allowed": False,
        "scalar_absorption_allowed": False,
        "source_action_law_closed": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The strongest bounded result is algebraic: a Lorentz L gives "
            "Omega=(D L)L^{-1}, and Omega_u u=0 cancels the rank-one dust Omega "
            "residual while defining the projected Cuu cancellation target. The "
            "missing step is source/action selection of the same L for K and Q_cross; "
            "no fitting or scalar absorption is allowed."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Dynamic D_u L / Omega_u u=0 Derivation Attempt",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"L as Lorentz tetrad bridge: {payload['l_as_lorentz_tetrad_bridge']}",
        f"Omega defined from L: {payload['omega_defined_from_l']}",
        f"Omega_u u=0 cancellation proved algebraically: {payload['omega_u_u_zero_cancellation_proved_algebraically']}",
        f"Projected Cuu cancellation target defined: {payload['projected_cuu_cancellation_target_defined']}",
        f"Projected Cuu cancellation source-derived: {payload['projected_cuu_cancellation_source_derived']}",
        f"Same L for K/Q_cross required: {payload['same_l_for_k_qcross_required']}",
        f"Fitting allowed: {payload['fitting_allowed']}",
        f"Scalar absorption allowed: {payload['scalar_absorption_allowed']}",
        f"Source/action law closed: {payload['source_action_law_closed']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Derivation Steps",
        "",
        "| step | statement | formula | proved |",
        "|---|---|---|---|",
    ]
    for row in payload["derivation_steps"]:
        lines.append(
            f"| {row['step']} | {row['statement']} | `{row['formula']}` | {row['proved']} |"
        )
    lines.extend(["", "## Algebraic Results", ""])
    lines.extend(f"- {item}" for item in payload["algebraic_results"])
    lines.extend(["", "## Source-Dependent Gaps", ""])
    lines.extend(f"- {item}" for item in payload["source_dependent_gaps"])
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
