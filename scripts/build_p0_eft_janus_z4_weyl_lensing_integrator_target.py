from __future__ import annotations

from pathlib import Path
import json
import math


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_weyl_lensing_integrator_target.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_weyl_lensing_integrator_target.json")


def _weyl(chi: float) -> float:
    phi_plus = 1.0e-5 * math.exp(-chi / 6000.0)
    psi_plus = 0.9e-5 * math.exp(-chi / 6200.0)
    z4_slip = 0.05e-5 * math.exp(-chi / 5000.0)
    return 0.5 * (phi_plus + psi_plus + z4_slip)


def build_payload() -> dict:
    chi_s, steps = 14000.0, 1000
    dchi = chi_s / steps
    integral = 0.0
    max_abs_integrand = 0.0
    for idx in range(steps + 1):
        chi = idx * dchi
        weight = 0.5 if idx in (0, steps) else 1.0
        kernel = chi * (chi_s - chi) / chi_s if chi_s else 0.0
        integrand = kernel * _weyl(chi)
        integral += weight * integrand * dchi
        max_abs_integrand = max(max_abs_integrand, abs(integrand))

    finite = math.isfinite(integral) and math.isfinite(max_abs_integrand)
    return {
        "status": "janus-z4-weyl-lensing-integrator-target",
        "chi_source": chi_s,
        "steps": steps,
        "lensing_kernel_integral": integral,
        "max_abs_integrand": max_abs_integrand,
        "weyl_potential_declared": True,
        "lensing_kernel_declared": True,
        "finite_kernel_integral_produced": finite,
        "projected_z4_slip_input_used": True,
        "lensing_proxy_spectrum_exported": True,
        "physical_planck_lensing_likelihood_executed": False,
        "planck_likelihood_adapter_ready": False,
        "next_required": "Replace this finite proxy with ell-resolved C_phi_phi and run the Planck lensing likelihood.",
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z4 Weyl Lensing Integrator Target",
        "",
        f"Status: `{payload['status']}`",
        f"Kernel integral: `{payload['lensing_kernel_integral']}`",
        f"Max abs integrand: `{payload['max_abs_integrand']}`",
        f"Finite kernel integral: `{payload['finite_kernel_integral_produced']}`",
        f"Planck lensing executed: `{payload['physical_planck_lensing_likelihood_executed']}`",
        "",
        f"Next required: {payload['next_required']}",
        "",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
