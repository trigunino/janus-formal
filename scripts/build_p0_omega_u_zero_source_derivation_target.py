from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_omega_u_zero_source_derivation_target.md")
JSON_PATH = Path("outputs/reports/p0_omega_u_zero_source_derivation_target.json")


def build_payload() -> dict:
    algebra = {
        "dust_stress": "T=rho u u",
        "omega_residual": "Delta_Omega M=L(Omega^T T+T Omega)L^T",
        "rank_one_substitution": "Omega^T T+T Omega=rho[(Omega u)_flat u_flat+u_flat (Omega u)_flat]",
        "closure_condition": "For rho != 0 and timelike normalized u, rank-one dust closure requires Omega_u u=0 along the dust congruence.",
        "bounded_result": "Omega_u u=0 would close this residual, but only as a condition derived from the transport/source law.",
    }
    required_equations = [
        {
            "equation": "Lorentz connection definition",
            "form": "Omega_alpha=(D_alpha L)L^{-1}, Omega_{alpha AB}=-Omega_{alpha BA}",
            "status": "written",
        },
        {
            "equation": "Dust-flow restriction",
            "form": "Omega_u=u^alpha Omega_alpha along u",
            "status": "written",
        },
        {
            "equation": "Fermi-Walker/comoving tetrad law",
            "form": "D_u e_A=(u_A a^B-a_A u^B)e_B, with comoving e_0=u",
            "status": "source-law-needed",
        },
        {
            "equation": "Source congruence equation",
            "form": "u^beta D_beta u^alpha=0 or a source-derived cross-force replacement",
            "status": "source-law-needed",
        },
        {
            "equation": "Residual substitution",
            "form": "Omega_u u=0 => Omega^T T+T Omega=0 along dust flow",
            "status": "conditional",
        },
        {
            "equation": "K/Q_cross compatibility",
            "form": "same source-derived L/Omega enters K transport and Q_cross optical contractions",
            "status": "open",
        },
    ]
    blockers = [
        "derive Fermi-Walker or comoving tetrad transport from Janus source equations, not gauge preference",
        "derive the relevant dust/source congruence and acceleration law",
        "prove Omega_u u=0 follows along the whole congruence, not only at one fitted event",
        "prove the same L/Omega closes K transport and Q_cross contractions",
        "extend or explicitly bound the result away from rank-one dust",
    ]
    forbidden_shortcuts = [
        "setting Omega_u u=0 by hand after seeing the residual",
        "choosing Omega components from lensing or survey fit",
        "using a comoving tetrad convention without a source transport law",
        "using one Omega for the residual and another for K/Q_cross",
    ]
    return {
        "description": (
            "Bounded P0 target for source-deriving Omega_u u=0 along a dust congruence."
        ),
        "status": "source-derivation-target-open",
        "rank_one_dust_scope": True,
        "omega_u_zero_would_close_residual": True,
        "closure_is_algebraic_only": True,
        "must_be_source_derived": True,
        "fermi_walker_or_comoving_tetrad_required": True,
        "source_congruence_required": True,
        "omega_source_law_trial_gate_available": True,
        "fit_choice_allowed": False,
        "k_qcross_compatibility_closed": False,
        "source_derivation_closed": False,
        "physics_closed": False,
        "prediction_ready": False,
        "prediction_claim": False,
        "algebra": algebra,
        "required_equations": required_equations,
        "blockers": blockers,
        "forbidden_shortcuts": forbidden_shortcuts,
        "verdict": (
            "Omega_u u=0 is the right dust-rank-one closure condition for the Omega "
            "residual, but it is not a prediction input until a source-derived "
            "Fermi-Walker/comoving tetrad or source-congruence law produces it. "
            "Post-hoc fitting is disallowed, so the prediction claim remains false."
        ),
    }


def render_markdown(payload: dict) -> str:
    a = payload["algebra"]
    lines = [
        "# P0 Omega u=0 Source-Derivation Target",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Rank-one dust scope: {payload['rank_one_dust_scope']}",
        f"Omega_u u=0 would close residual: {payload['omega_u_zero_would_close_residual']}",
        f"Closure is algebraic only: {payload['closure_is_algebraic_only']}",
        f"Must be source-derived: {payload['must_be_source_derived']}",
        f"Fermi-Walker/comoving tetrad required: {payload['fermi_walker_or_comoving_tetrad_required']}",
        f"Source congruence required: {payload['source_congruence_required']}",
        f"Omega source law trial gate available: {payload['omega_source_law_trial_gate_available']}",
        f"Fit choice allowed: {payload['fit_choice_allowed']}",
        f"K/Q_cross compatibility closed: {payload['k_qcross_compatibility_closed']}",
        f"Source derivation closed: {payload['source_derivation_closed']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        f"Prediction claim: {payload['prediction_claim']}",
        "",
        "## Algebra",
        "",
        f"- dust stress: `{a['dust_stress']}`",
        f"- omega residual: `{a['omega_residual']}`",
        f"- rank-one substitution: `{a['rank_one_substitution']}`",
        f"- closure condition: {a['closure_condition']}",
        f"- bounded result: {a['bounded_result']}",
        "",
        "## Required Equations",
        "",
        "| equation | form | status |",
        "|---|---|---|",
    ]
    for row in payload["required_equations"]:
        lines.append(f"| {row['equation']} | `{row['form']}` | {row['status']} |")
    lines.extend(["", "## Blockers", ""])
    lines.extend(f"- {item}" for item in payload["blockers"])
    lines.extend(["", "## Forbidden Shortcuts", ""])
    lines.extend(f"- {item}" for item in payload["forbidden_shortcuts"])
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
