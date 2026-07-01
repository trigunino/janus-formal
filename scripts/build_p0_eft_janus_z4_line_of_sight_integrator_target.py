from __future__ import annotations

from pathlib import Path
import json
import math


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_line_of_sight_integrator_target.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_line_of_sight_integrator_target.json")


def _visibility(eta: float, eta_star: float = 7.0, sigma: float = 0.8) -> float:
    return math.exp(-((eta - eta_star) ** 2) / (2.0 * sigma * sigma)) / (math.sqrt(2.0 * math.pi) * sigma)


def _source(eta: float) -> float:
    theta0 = 1.0e-5 * math.cos(0.15 * eta)
    psi = 0.8e-5 * math.exp(-0.05 * eta)
    doppler = 0.2e-5 * math.sin(0.12 * eta)
    isw = -0.05e-5 * math.exp(-0.05 * eta)
    return _visibility(eta) * (theta0 + psi + doppler) + isw * math.exp(-eta / 20.0)


def build_payload() -> dict:
    eta0, eta1, steps = 0.0, 20.0, 800
    h = (eta1 - eta0) / steps
    integral = 0.0
    visibility_integral = 0.0
    max_abs_source = 0.0
    for idx in range(steps + 1):
        eta = eta0 + idx * h
        weight = 0.5 if idx in (0, steps) else 1.0
        source = _source(eta)
        vis = _visibility(eta)
        integral += weight * source * h
        visibility_integral += weight * vis * h
        max_abs_source = max(max_abs_source, abs(source))

    finite = math.isfinite(integral) and math.isfinite(visibility_integral)
    return {
        "status": "janus-z4-line-of-sight-integrator-target",
        "eta_initial": eta0,
        "eta_final": eta1,
        "steps": steps,
        "los_integral": integral,
        "visibility_integral": visibility_integral,
        "visibility_normalization_error": abs(visibility_integral - 1.0),
        "max_abs_source": max_abs_source,
        "source_function_declared": True,
        "visibility_source_inserted": True,
        "isw_source_inserted": True,
        "finite_integral_produced": finite,
        "spectrum_proxy_exported": True,
        "physical_boltzmann_transfer_executed": False,
        "planck_likelihood_adapter_ready": False,
        "next_required": "Replace this proxy integral with k/ell-resolved Z4 transfer functions before Planck likelihood.",
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Line-of-Sight Integrator Target",
        "",
        f"Status: `{payload['status']}`",
        f"LOS integral: `{payload['los_integral']}`",
        f"Visibility normalization error: `{payload['visibility_normalization_error']}`",
        f"Finite integral: `{payload['finite_integral_produced']}`",
        f"Physical transfer executed: `{payload['physical_boltzmann_transfer_executed']}`",
        "",
        f"Next required: {payload['next_required']}",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
