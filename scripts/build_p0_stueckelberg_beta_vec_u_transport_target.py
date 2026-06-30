from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_stueckelberg_beta_vec_u_transport_target.md")
JSON_PATH = Path("outputs/reports/p0_stueckelberg_beta_vec_u_transport_target.json")


def build_payload() -> dict:
    derivation_chain = [
        "derive T_plus(k,a_i), T_minus(k,a_i) from Janus two-sector source equations",
        "derive D_plus(a), D_minus(a) and theta_s from the same growth/continuity/euler branch",
        "compute beta_minus_to_plus=v_minus_to_plus/c with provenance source_derived_janus_dynamics",
        "form u_minus=gamma(1,beta) using the checked local Lorentz helper",
        "map u_minus_to_plus=L_minus_to_plus u_minus with the same admissible L used by K and Q_cross",
    ]
    admissibility_gates = [
        "beta provenance must be source_derived_janus_dynamics",
        "L_minus_to_plus must satisfy L^T eta L=eta and preserve time orientation",
        "the same L must induce K_plus/K_minus transport and optical Q_cross",
        "R_plus=0 and R_minus=0 must hold after substituting beta, u, L, K and Q_cross",
        "PM/H0-calibrated beta is diagnostic only",
    ]
    blockers = [
        "source-derived transfer/growth/velocity solution not yet available",
        "derived L_minus_to_plus and D L law not yet available",
        "same-map K/Q_cross compatibility not yet closed",
        "two-sector Bianchi residual cancellation not yet closed",
    ]
    code_surfaces = [
        "janus_lab.lensing.lorentz_gamma_from_beta_vectors",
        "janus_lab.lensing.transported_four_velocity_from_beta_vectors",
        "janus_lab.lensing.beta_field_is_prediction_ready",
        "scripts/build_janus_velocity_ic_closure_target.py",
        "scripts/build_p0_l_k_qcross_consistency_target.py",
        "scripts/build_p0_stueckelberg_beta_field_provenance_gate.py",
    ]
    decision = {
        "beta_vec_u_transport_target_defined": True,
        "local_beta_u_code_available": True,
        "pm_calibrated_beta_diagnostic_available": True,
        "source_derived_beta_available": False,
        "admissible_l_transport_available": False,
        "same_l_for_k_and_qcross_closed": False,
        "r_plus_closed": False,
        "r_minus_closed": False,
    }
    return {
        "description": "P0 target for deriving beta_vec and u_minus_to_plus from Janus source dynamics.",
        "status": "derivation-target-open",
        "decision": decision,
        "derivation_chain": derivation_chain,
        "admissibility_gates": admissibility_gates,
        "blockers": blockers,
        "code_surfaces": code_surfaces,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "This locks the required route: beta and u_minus_to_plus must come from "
            "Janus transfer/growth/velocity plus one Lorentz-admissible L shared by "
            "K and Q_cross. No prediction is unlocked."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Stueckelberg Beta/u Transport Target",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
    ]
    lines.extend(f"{key}: {value}" for key, value in payload["decision"].items())
    lines.extend(["", "## Derivation Chain", ""])
    lines.extend(f"- {item}" for item in payload["derivation_chain"])
    lines.extend(["", "## Admissibility Gates", ""])
    lines.extend(f"- {item}" for item in payload["admissibility_gates"])
    lines.extend(["", "## Blockers", ""])
    lines.extend(f"- {item}" for item in payload["blockers"])
    lines.extend(["", "## Code Surfaces", ""])
    lines.extend(f"- `{item}`" for item in payload["code_surfaces"])
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
