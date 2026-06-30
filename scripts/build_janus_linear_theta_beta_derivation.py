from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/janus_linear_theta_beta_derivation.md")
JSON_PATH = Path("outputs/reports/janus_linear_theta_beta_derivation.json")


def theta_from_growth_derivative(
    scale_factor: float,
    h_of_a: float,
    d_delta_dln_a: float,
) -> float:
    if scale_factor <= 0.0:
        raise ValueError("scale_factor must be positive.")
    if h_of_a <= 0.0:
        raise ValueError("h_of_a must be positive.")
    return -scale_factor * h_of_a * d_delta_dln_a


def beta_mode_from_theta(
    theta: float,
    wavenumber: float,
    speed_of_light: float = 299792.458,
) -> float:
    if wavenumber <= 0.0:
        raise ValueError("wavenumber must be positive; k=0 has no velocity inversion.")
    if speed_of_light <= 0.0:
        raise ValueError("speed_of_light must be positive.")
    return theta / (wavenumber * speed_of_light)


def build_payload() -> dict:
    derivation = {
        "continuity": "theta_s(k,a) = -a H(a) d delta_s(k,a)/d ln a",
        "irrotational_velocity": "v_s(k,a) = i k theta_s(k,a)/k^2 for k>0",
        "beta_mode": "beta_s_parallel = theta_s/(k c) up to Fourier phase/sign convention",
        "hubble_branch": "H(a)=H0 E_J(a)",
    }
    worked_check = {
        "a": 0.5,
        "H_over_H0": 2.0,
        "d_delta_dln_a": 0.25,
        "theta_over_H0": theta_from_growth_derivative(0.5, 2.0, 0.25),
    }
    blockers = [
        "delta_s(k,a) and d delta_s/d ln a remain diagnostic until sourced by Janus operator",
        "Fourier sign convention must match the PM/survey pipeline",
        "k=0 velocity inversion is forbidden",
        "beta is physical only after L_minus_to_plus and provenance gates close",
        "A_J remains no-fit/source-backed only",
    ]
    return {
        "description": "Local derivation from linear growth derivative to theta_s and beta mode.",
        "status": "conditional-derivation-open",
        "derivation": derivation,
        "worked_check": worked_check,
        "blockers": blockers,
        "theta_relation_checked": True,
        "source_operator_closed": False,
        "source_derived_beta_ready": False,
        "physics_closed": False,
        "prediction_ready": False,
        "verdict": (
            "The theta/beta algebra is explicit and testable. It remains conditional "
            "until delta_s, its growth derivative, amplitude and L transport are source-derived."
        ),
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# Janus Linear Theta/Beta Derivation",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Theta relation checked: {payload['theta_relation_checked']}",
        f"Source operator closed: {payload['source_operator_closed']}",
        f"Source-derived beta ready: {payload['source_derived_beta_ready']}",
        f"Prediction ready: {payload['prediction_ready']}",
        "",
        "## Derivation",
        "",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["derivation"].items())
    lines.extend(["", "## Worked Check", ""])
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["worked_check"].items())
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
