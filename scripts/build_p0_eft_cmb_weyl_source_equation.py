from __future__ import annotations

from pathlib import Path
import json

try:
    from scripts.build_p0_eft_janus_holst_distance_ruler_map import master_branch_background
except ModuleNotFoundError:
    from build_p0_eft_janus_holst_distance_ruler_map import master_branch_background


REPORT_PATH = Path("outputs/reports/p0_eft_cmb_weyl_source_equation.md")
JSON_PATH = Path("outputs/reports/p0_eft_cmb_weyl_source_equation.json")


def build_payload() -> dict:
    constants, _ = master_branch_background()
    return {
        "description": "Janus-Holst Weyl source equation target for replacing the CMB proxy kernel.",
        "status": "cmb-weyl-source-equation-derived-as-linear-response-target",
        "weyl_source_formula": (
            "W(k,a) = 0.5*(Phi+Psi) = -3/4 * Omega_m(a) * Sigma_JH(k,a) * delta_m(k,a) / k^2"
        ),
        "sigma_formula": (
            "Sigma_JH(k,a) = mu_JH(k,a) * (1 + eta_slip_JH(k,a))/2"
        ),
        "mu_formula": (
            "mu_JH(k,a) = 1 + (161/36)*Omega_T(a)*k^2/(k^2 + 3*H(a)^2/2)"
        ),
        "slip_status": "kink/derivative-slip encoded; value-slip Green kernel remains a controlled target",
        "closed_inputs": {
            "alpha_iso": "161/36",
            "Omega_m0": constants["Omega_m0"],
            "Omega_T0": constants["Omega_T0"],
            "spin_background_screened": True,
        },
        "weyl_source_equation_ready": True,
        "weyl_transfer_function_integrated": False,
        "proxy_replaced": False,
        "next_required": "integrate this Weyl source in the CMB transfer hierarchy with a physical visibility function.",
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT CMB Weyl Source Equation",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Weyl source equation ready: {payload['weyl_source_equation_ready']}",
        f"Weyl transfer integrated: {payload['weyl_transfer_function_integrated']}",
        f"Proxy replaced: {payload['proxy_replaced']}",
        "",
        "## Formulae",
        "",
        f"- `{payload['weyl_source_formula']}`",
        f"- `{payload['sigma_formula']}`",
        f"- `{payload['mu_formula']}`",
        f"- slip: {payload['slip_status']}",
        "",
        "## Next",
        "",
        payload["next_required"],
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
