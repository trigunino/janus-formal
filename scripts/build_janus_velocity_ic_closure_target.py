from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/janus_velocity_ic_closure_target.md")
JSON_PATH = Path("outputs/reports/janus_velocity_ic_closure_target.json")


def build_payload() -> dict:
    no_fit_inputs = [
        "T_plus(k,a_i) and T_minus(k,a_i) from the Janus two-sector linear operator",
        "D_plus(a) and D_minus(a) from the Janus growth propagator",
        "A_J amplitude from source physics or declared no-fit comparison, not sigma8",
        "theta_s(k,a_i) from continuity/euler, not arbitrary velocity scaling",
        "Q_det branch fixed before deciding whether delta_minus is proper or plus-effective",
        "Q_cross/L_minus_to_plus branch fixed before using velocities for lensing",
    ]
    conditional_velocity_relation = [
        "theta_s(k,a) = -a H_J(a) d(delta_s)/d ln a",
        "v_s(k,a) = i k theta_s(k,a) / k^2 for irrotational scalar modes",
        "valid only after the same delta_s branch is used by PM density and Q_cross transport",
    ]
    forbidden_claims = [
        "no sigma8 normalization from the current grid",
        "no survey-fit amplitude for A_J",
        "no reuse of analytic-multimode convergence control as physical transfer evidence",
        "no Q_cross velocity bridge claim before L_minus_to_plus/K_plus closure",
    ]
    simulation_gate_requirements = [
        "derive two-sector transfer functions",
        "derive initial velocity field from the same transfer/growth solution",
        "verify sign conventions against the signed PM kernel",
        "run controlled convergence after IC physics is explicit",
    ]
    return {
        "description": "Closure target for Janus-derived initial conditions and velocity fields.",
        "status": "derivation-target",
        "source_derived_ic_ready": False,
        "velocity_scaffold_closed": False,
        "sigma8_claim_allowed": False,
        "prediction_ready": False,
        "no_fit_inputs": no_fit_inputs,
        "conditional_velocity_relation": conditional_velocity_relation,
        "forbidden_claims": forbidden_claims,
        "simulation_gate_requirements": simulation_gate_requirements,
        "verdict": (
            "The velocity relation is usable only as a conditional target. Production "
            "ICs remain blocked until transfer, growth, amplitude and Q_cross transport "
            "come from the same Janus source equations."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# Janus Velocity IC Closure Target",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Source-derived IC ready: {payload['source_derived_ic_ready']}",
        f"Velocity scaffold closed: {payload['velocity_scaffold_closed']}",
        f"Sigma8 claim allowed: {payload['sigma8_claim_allowed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## No-fit Inputs",
        "",
    ]
    lines.extend(f"- {item}" for item in payload["no_fit_inputs"])
    lines.extend(["", "## Conditional Velocity Relation", ""])
    lines.extend(f"- `{item}`" for item in payload["conditional_velocity_relation"])
    lines.extend(["", "## Forbidden Claims", ""])
    lines.extend(f"- {item}" for item in payload["forbidden_claims"])
    lines.extend(["", "## Simulation Gate Requirements", ""])
    lines.extend(f"- {item}" for item in payload["simulation_gate_requirements"])
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
