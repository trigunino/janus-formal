from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_janus_pi_zero_preservation_gate.md")
JSON_PATH = Path("outputs/reports/p0_janus_pi_zero_preservation_gate.json")


def build_payload() -> dict:
    sufficient_conditions = [
        "initial Pi_ij=0 on the chosen slice",
        "trace-free flow shear sigma_ij vanishes or is source-cancelled",
        "trace-free heat-flux divergence TF(D_k Q_ijk) vanishes or is source-cancelled",
        "trace-free Janus force/source term TF(S_ij[A_Janus,L,B_4vol]) vanishes",
        "same-L tensor transport preserves spatial isotropy",
    ]
    generation_channels = [
        "mean-flow shear creates anisotropic stress from isotropic pressure",
        "trace-free force/connection terms create Pi even if Pi starts at zero",
        "heat-flux divergence D_k Q_ijk sources the stress trace-free part",
        "mismatched L/K/Q_cross transport can create nonphysical Pi terms",
    ]
    forbidden_shortcuts = [
        "do not set Pi_ij=0 globally from initial isotropy alone",
        "do not absorb trace-free tensor terms into Q_det or Q_cross",
        "do not set Q_ijk=0 without a source or collision argument",
    ]
    return {
        "description": "P0 gate for when Pi=0 can be preserved rather than imposed.",
        "status": "pi-zero-preservation-gate-open",
        "depends_on": [
            "p0_janus_full_vlasov_moment_closure_contract",
            "p0_janus_kinetic_moment_hierarchy_equations",
        ],
        "preservation_identity_target": (
            "D_t Pi_ij = TF[-2 p sigma_ij - D_k Q_ijk + S_ij[A_Janus,L,B_4vol] + connection terms]"
        ),
        "sufficient_conditions": sufficient_conditions,
        "generation_channels": generation_channels,
        "forbidden_shortcuts": forbidden_shortcuts,
        "pi_zero_initial_condition_is_not_proof": True,
        "pi_zero_preservation_conditions_written": True,
        "pi_zero_source_proved": False,
        "isotropic_dispersion_closed": False,
        "anisotropic_stress_evolution_closed": False,
        "uses_observational_fit": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "Pi=0 is admissible only as a conditional preserved branch. It becomes a Janus "
            "proof only if the trace-free shear, heat-flux and source terms vanish or cancel "
            "from source-derived equations."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Janus Pi Zero Preservation Gate",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Preservation identity target: `{payload['preservation_identity_target']}`",
        f"Pi zero initial condition is not proof: {payload['pi_zero_initial_condition_is_not_proof']}",
        f"Pi zero preservation conditions written: {payload['pi_zero_preservation_conditions_written']}",
        f"Pi zero source proved: {payload['pi_zero_source_proved']}",
        f"Isotropic dispersion closed: {payload['isotropic_dispersion_closed']}",
        f"Anisotropic stress evolution closed: {payload['anisotropic_stress_evolution_closed']}",
        f"Uses observational fit: {payload['uses_observational_fit']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Sufficient Conditions",
        "",
    ]
    lines.extend(f"- {item}" for item in payload["sufficient_conditions"])
    lines.extend(["", "## Generation Channels", ""])
    lines.extend(f"- {item}" for item in payload["generation_channels"])
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
