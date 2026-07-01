from __future__ import annotations

from pathlib import Path
import json

try:
    from scripts.build_kids1000_janus_holst_kink_lensing_target import build_payload as build_kink_target
except ModuleNotFoundError:
    from build_kids1000_janus_holst_kink_lensing_target import build_payload as build_kink_target

from janus_lab.kink_growth import growth_prediction_ready, integrate_kink_growth


REPORT_PATH = Path("outputs/reports/kids1000_janus_holst_kink_solver_scaffold.md")
JSON_PATH = Path("outputs/reports/kids1000_janus_holst_kink_solver_scaffold.json")


def build_payload() -> dict:
    target = build_kink_target()
    disabled = integrate_kink_growth(
        k=1.0,
        a_initial=0.2,
        a_final=1.0,
        a_sigma=2.0 / 3.0,
        s_kink=lambda _k, _a: 0.05,
        skink_coefficient_derived=False,
        samples=96,
    )
    enabled_mechanics = integrate_kink_growth(
        k=1.0,
        a_initial=0.2,
        a_final=1.0,
        a_sigma=2.0 / 3.0,
        s_kink=lambda _k, _a: 0.05,
        skink_coefficient_derived=True,
        samples=96,
    )
    ready = growth_prediction_ready(
        skink_coefficient_derived=target["open_inputs"]["skink_coefficient_derived"],
        alpha_janus_derived=target["open_inputs"]["alpha_Janus_derived"],
    )
    return {
        "description": "No-fit kink growth ODE scaffold for the KiDS-1000 Janus-Holst branch.",
        "status": "kink-growth-solver-scaffold-not-predictive",
        "a_sigma": 2.0 / 3.0,
        "target_status": target["status"],
        "mechanics_check": {
            "disabled_final_delta": disabled[-1]["delta"],
            "disabled_final_ddelta": disabled[-1]["ddelta_dln_a"],
            "enabled_mechanics_final_delta": enabled_mechanics[-1]["delta"],
            "enabled_mechanics_final_ddelta": enabled_mechanics[-1]["ddelta_dln_a"],
            "delta_continuity_encoded": True,
            "growth_velocity_jump_encoded": True,
        },
        "skink_coefficient_derived": target["open_inputs"]["skink_coefficient_derived"],
        "alpha_Janus_derived": target["open_inputs"]["alpha_Janus_derived"],
        "uses_kids_residuals": False,
        "uses_bin_shift": False,
        "uses_bin_factors": False,
        "prediction_ready": ready,
        "blocked_reason": "S_kink coefficient and alpha_Janus(a) are not source-derived.",
    }


def render_markdown(payload: dict) -> str:
    check = payload["mechanics_check"]
    lines = [
        "# KiDS-1000 Janus-Holst Kink Solver Scaffold",
        "",
        payload["description"],
        "",
        f"Status: `{payload['status']}`",
        f"a_sigma: `{payload['a_sigma']:.6g}`",
        f"Target status: `{payload['target_status']}`",
        f"S_kink coefficient derived: `{payload['skink_coefficient_derived']}`",
        f"alpha_Janus derived: `{payload['alpha_Janus_derived']}`",
        f"Uses KiDS residuals: `{payload['uses_kids_residuals']}`",
        f"Uses bin shift: `{payload['uses_bin_shift']}`",
        f"Uses bin factors: `{payload['uses_bin_factors']}`",
        f"Prediction ready: `{payload['prediction_ready']}`",
        "",
        "## Mechanics Check",
        "",
        f"- disabled final delta: `{check['disabled_final_delta']:.6g}`",
        f"- disabled final ddelta/dln a: `{check['disabled_final_ddelta']:.6g}`",
        f"- enabled mechanics final delta: `{check['enabled_mechanics_final_delta']:.6g}`",
        f"- enabled mechanics final ddelta/dln a: `{check['enabled_mechanics_final_ddelta']:.6g}`",
        f"- delta continuity encoded: `{check['delta_continuity_encoded']}`",
        f"- growth velocity jump encoded: `{check['growth_velocity_jump_encoded']}`",
        "",
        payload["blocked_reason"],
        "",
    ]
    return "\n".join(lines)


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH) -> dict:
    report_path.parent.mkdir(parents=True, exist_ok=True)
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
