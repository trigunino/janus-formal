from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_source_derived_beta_reconstruction_target.md")
JSON_PATH = Path("outputs/reports/p0_source_derived_beta_reconstruction_target.json")


def build_payload() -> dict:
    reconstruction_steps = [
        "solve Janus linear two-sector operator for delta_plus(k,a), delta_minus(k,a)",
        "derive theta_s(k,a) from continuity and verify with Euler/geodesic sign",
        "recover irrotational v_s(k,a)=i k theta_s/k^2 with k=0 excluded",
        "map v_minus through admissible L_minus_to_plus before optical use",
        "convert beta_minus_to_plus=v_minus_to_plus/c and mark provenance source_derived_janus_dynamics",
    ]
    acceptance_checks = [
        "same transfer/growth/amplitude branch feeds density and velocity",
        "A_J is source-backed or declared no-fit, never sigma8/S8 fitted",
        "Q_det convention fixed before comparing plus-effective and minus-proper density",
        "L_minus_to_plus is Lorentz-compatible and shared by K/Q_cross",
        "PM velocity calibration may validate units only, not physical provenance",
    ]
    blockers = {
        "linear_operator_derived": False,
        "theta_from_continuity_euler_closed": False,
        "admissible_l_for_velocity_map": False,
        "source_derived_beta_available": False,
        "prediction_ready": False,
    }
    return {
        "description": "Target for reconstructing beta_vec from Janus source-derived linear velocity modes.",
        "status": "reconstruction-target-open",
        "reconstruction_steps": reconstruction_steps,
        "acceptance_checks": acceptance_checks,
        "blockers": blockers,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "This narrows beta closure to a concrete chain from Janus linear modes. "
            "Until theta_s and L_minus_to_plus are derived, beta remains diagnostic."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 Source-derived Beta Reconstruction Target",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Reconstruction Steps",
        "",
    ]
    lines.extend(f"- {item}" for item in payload["reconstruction_steps"])
    lines.extend(["", "## Acceptance Checks", ""])
    lines.extend(f"- {item}" for item in payload["acceptance_checks"])
    lines.extend(["", "## Blockers", ""])
    lines.extend(f"- {key}: {value}" for key, value in payload["blockers"].items())
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
