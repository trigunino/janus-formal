from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_fermi_walker_omega_u_zero_trial.md")
JSON_PATH = Path("outputs/reports/p0_fermi_walker_omega_u_zero_trial.json")


def build_payload() -> dict:
    equations = [
        {
            "name": "Lorentz connection",
            "form": "Omega_alpha=(D_alpha L)L^{-1}, Omega_{alpha AB}=-Omega_{alpha BA}",
            "role": "defines the tetrad transport connection",
        },
        {
            "name": "Flow contraction",
            "form": "Omega_u=u^alpha Omega_alpha",
            "role": "isolates the connection seen along the source flow",
        },
        {
            "name": "Comoving tetrad condition",
            "form": "e_0=u",
            "role": "identifies the time leg with the source four-velocity",
        },
        {
            "name": "Fermi-Walker law",
            "form": "D_u e_A=(u_A a^B-a_A u^B)e_B, a=D_u u",
            "role": "fixes no intrinsic spatial rotation along u",
        },
        {
            "name": "Time-leg consequence",
            "form": "D_u e_0=a, and Omega_u e_0=0 when e_0=u is FW-transported as the comoving leg",
            "role": "candidate route to Omega_u u=0",
        },
        {
            "name": "Dust residual closure",
            "form": "T=rho u u, Omega_u u=0 => Omega_u^T T+T Omega_u=0",
            "role": "conditional algebraic closure only",
        },
    ]
    conditional_closure = [
        "If the Janus source law selects a comoving tetrad with e_0=u, the tetrad time leg is not a fitted gauge choice.",
        "If that same source law enforces Fermi-Walker transport along u, the flow contraction gives Omega_u u=0.",
        "Then the rank-one dust Omega residual closes algebraically along the same congruence.",
    ]
    open_requirements = [
        "derive the comoving e_0=u selection from Janus source equations",
        "derive the Fermi-Walker law from the same source law, not from a frame convention",
        "share the resulting L/Omega with K transport and Q_cross optical contractions",
        "prove the statement along the source congruence, not at one event",
        "bound or extend the claim beyond rank-one dust",
    ]
    forbidden_shortcuts = [
        "postulating Omega_u u=0 after residual inspection",
        "choosing a separate Omega for K or Q_cross",
        "using Fermi-Walker transport as a prediction without Janus-source provenance",
    ]
    return {
        "description": (
            "Bounded P0 trial testing whether a Fermi-Walker/comoving tetrad law can "
            "source-derive Omega_u u=0."
        ),
        "status": "trial-open",
        "bounded_p0_artifact": True,
        "equations_written": True,
        "comoving_e0_equals_u_required": True,
        "fermi_walker_source_law_required": True,
        "conditional_closure_if_source_law_enforces_fw": True,
        "omega_u_zero_source_derived": False,
        "janus_source_derivation_open": True,
        "k_qcross_sharing_required": True,
        "k_qcross_sharing_closed": False,
        "prediction_ready": False,
        "prediction_claim": False,
        "equations": equations,
        "conditional_closure": conditional_closure,
        "open_requirements": open_requirements,
        "forbidden_shortcuts": forbidden_shortcuts,
        "verdict": (
            "The Fermi-Walker/comoving route conditionally yields Omega_u u=0 if "
            "Janus source dynamics derive both e_0=u and the FW transport law. "
            "That source derivation is still open, and the same L/Omega must be "
            "shared with K and Q_cross before any prediction claim is allowed."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Fermi-Walker Omega_u u=0 Trial",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Bounded P0 artifact: {payload['bounded_p0_artifact']}",
        f"Equations written: {payload['equations_written']}",
        f"Comoving e0=u required: {payload['comoving_e0_equals_u_required']}",
        f"Fermi-Walker source law required: {payload['fermi_walker_source_law_required']}",
        f"Conditional closure if source law enforces FW: {payload['conditional_closure_if_source_law_enforces_fw']}",
        f"Omega_u u=0 source-derived: {payload['omega_u_zero_source_derived']}",
        f"Janus source derivation open: {payload['janus_source_derivation_open']}",
        f"K/Q_cross sharing required: {payload['k_qcross_sharing_required']}",
        f"K/Q_cross sharing closed: {payload['k_qcross_sharing_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        f"Prediction claim: {payload['prediction_claim']}",
        "",
        "## Equations",
        "",
        "| name | form | role |",
        "|---|---|---|",
    ]
    for row in payload["equations"]:
        lines.append(f"| {row['name']} | `{row['form']}` | {row['role']} |")
    lines.extend(["", "## Conditional Closure", ""])
    lines.extend(f"- {item}" for item in payload["conditional_closure"])
    lines.extend(["", "## Open Requirements", ""])
    lines.extend(f"- {item}" for item in payload["open_requirements"])
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
