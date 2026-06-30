from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/janus_linear_theta_mode_reduction_derivation.md")
JSON_PATH = Path("outputs/reports/janus_linear_theta_mode_reduction_derivation.json")


def build_payload() -> dict:
    modal_reduction = {
        "delta_sum": "Omega_minus delta_plus + Omega_plus delta_minus_eff",
        "delta_source": "delta_plus - delta_minus_eff",
        "theta_sum": "-a H d(delta_sum)/d ln a",
        "theta_source": "-a H d(delta_source)/d ln a",
        "theta_plus_minus": "recover theta_plus/theta_minus only after Omega_s(a) branch is fixed",
    }
    closure_flags = {
        "modal_theta_reduction_written": True,
        "omega_branch_source_derived": False,
        "amplitude_source_derived": False,
        "qdet_branch_fixed": False,
        "physical_beta_ready": False,
    }
    blockers = [
        "Omega_plus(a) and Omega_minus_eff(a) must be source-derived before inverting modes",
        "A_J and T_J(k) remain open",
        "delta_minus_eff versus negative-proper branch depends on Q_det",
        "L_minus_to_plus still blocks physical Q_cross/beta use",
    ]
    return {
        "description": "Algebraic modal reduction of Janus linear theta variables.",
        "status": "algebraic-derivation-open",
        "modal_reduction": modal_reduction,
        "closure_flags": closure_flags,
        "blockers": blockers,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The modal theta reduction is written, but theta_plus/theta_minus become "
            "physical only after the same Janus operator fixes Omega_s(a), Q_det and amplitude."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# Janus Linear Theta Mode Reduction Derivation",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Physics closed: {payload['physics_closed']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Modal Reduction",
        "",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["modal_reduction"].items())
    lines.extend(["", "## Closure Flags", ""])
    lines.extend(f"- {key}: {value}" for key, value in payload["closure_flags"].items())
    lines.extend(["", "## Blockers", ""])
    lines.extend(f"- {item}" for item in payload["blockers"])
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
