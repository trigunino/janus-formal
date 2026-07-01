from __future__ import annotations

from pathlib import Path
import json

try:
    from scripts.build_kids1000_janus_holst_no_fit_boundary import build_payload as build_no_fit_payload
    from scripts.build_p0_eft_cmb_weyl_source_equation import build_payload as build_weyl_source_payload
    from scripts.build_p0_eft_slip_green_neumann_bridge import build_payload as build_neumann_payload
    from scripts.build_p0_eft_slip_jump_derivation_check import build_payload as build_jump_payload
    from scripts.build_p0_janus_weakfield_dust_slip_green_kernel_target import build_payload as build_dust_green_payload
except ModuleNotFoundError:
    from build_kids1000_janus_holst_no_fit_boundary import build_payload as build_no_fit_payload
    from build_p0_eft_cmb_weyl_source_equation import build_payload as build_weyl_source_payload
    from build_p0_eft_slip_green_neumann_bridge import build_payload as build_neumann_payload
    from build_p0_eft_slip_jump_derivation_check import build_payload as build_jump_payload
    from build_p0_janus_weakfield_dust_slip_green_kernel_target import build_payload as build_dust_green_payload


REPORT_PATH = Path("outputs/reports/kids1000_janus_holst_value_slip_kernel_target.md")
JSON_PATH = Path("outputs/reports/kids1000_janus_holst_value_slip_kernel_target.json")


def build_payload() -> dict:
    boundary = build_no_fit_payload()
    jump = build_jump_payload()
    neumann = build_neumann_payload()
    weyl = build_weyl_source_payload()
    dust_green = build_dust_green_payload()
    failure = boundary["dominant_failure"]
    return {
        "description": "KiDS-1000 target contract for deriving the Janus-Holst value-slip kernel.",
        "status": "value-slip-kernel-target-open",
        "kids_symptom": {
            "dominant_pair": failure["pair"],
            "bin_factor_highest": failure["bin_factor_highest"],
            "posthoc_delta_z_indicator": failure["best_posthoc_delta_z"],
            "posthoc_shifted_bin": failure["best_posthoc_shifted_bin"],
            "posthoc_chi2_per_dof": failure["best_posthoc_chi2_per_dof"],
        },
        "closed_inputs": {
            "derivative_jump_slip_source_closed": jump["theorem_status"]["derivative_jump_slip_source_closed"],
            "weyl_source_equation_ready": weyl["weyl_source_equation_ready"],
            "mu_formula": weyl["mu_formula"],
            "sigma_formula_target": weyl["sigma_formula"],
        },
        "open_inputs": {
            "algebraic_value_slip_derived": jump["theorem_status"]["algebraic_value_slip_derived"],
            "green_kernel_computed": neumann["theorem_status"]["green_kernel_computed"],
            "dust_green_physics_closed": dust_green["physics_closed"],
            "boundary_conditions_source_derived": dust_green["boundary_conditions_source_derived"],
        },
        "target_operator": {
            "input_fields": ["Omega_T(a)", "chi_x(a)", "mu_JH(k,a)", "derivative slip source"],
            "output_field": "eta_slip_JH(k,a) or an equivalent positive-photon optical projection factor",
            "must_feed": "Sigma_JH(k,a) = mu_JH(k,a) * (1 + eta_slip_JH(k,a))/2",
            "must_not_feed": "Z_MID_BIN2, per-bin amplitude factors, or any KiDS residual-derived scalar",
        },
        "acceptance_tests": [
            "derive a value-slip Green kernel before reading KiDS residuals",
            "recover finite non-fit eta_slip_JH(k,a) on the KiDS lens redshift range",
            "run KiDS COSEBIs with no Z_MID_BIN2 or bin-factor correction",
            "report whether the bin-2 diagnostic improves without using bin-2 data as an input",
        ],
        "forbidden_shortcuts": boundary["forbidden_uses"]
        + [
            "choose Green-kernel coefficient to reproduce delta_z=+0.15",
            "tune eta_slip_JH(k,a) on the pair 2-3 residual",
        ],
        "gate_closed": False,
        "prediction_ready": False,
        "boundary": (
            "The KiDS bin-2 shift is only a target symptom. The value-slip kernel must be "
            "derived from the Janus-Holst boundary/Green problem before it can enter lensing."
        ),
    }


def render_markdown(payload: dict) -> str:
    symptom = payload["kids_symptom"]
    lines = [
        "# KiDS-1000 Janus-Holst Value-Slip Kernel Target",
        "",
        payload["description"],
        "",
        f"Status: `{payload['status']}`",
        f"Gate closed: `{payload['gate_closed']}`",
        f"Prediction ready: `{payload['prediction_ready']}`",
        "",
        "## KiDS Symptom",
        "",
        f"- dominant pair: `{symptom['dominant_pair']}`",
        f"- highest bin factor: `{symptom['bin_factor_highest']}`",
        f"- posthoc shifted bin: `{symptom['posthoc_shifted_bin']}`",
        f"- posthoc delta_z indicator: `{symptom['posthoc_delta_z_indicator']}`",
        f"- posthoc chi2/dof: `{symptom['posthoc_chi2_per_dof']:.6g}`",
        "",
        "## Target Operator",
        "",
    ]
    lines.extend(f"- {key}: `{value}`" for key, value in payload["target_operator"].items())
    lines.extend(["", "## Closed Inputs", ""])
    lines.extend(f"- {key}: `{value}`" for key, value in payload["closed_inputs"].items())
    lines.extend(["", "## Open Inputs", ""])
    lines.extend(f"- {key}: `{value}`" for key, value in payload["open_inputs"].items())
    lines.extend(["", "## Acceptance Tests", ""])
    lines.extend(f"- {item}" for item in payload["acceptance_tests"])
    lines.extend(["", "## Forbidden Shortcuts", ""])
    lines.extend(f"- {item}" for item in payload["forbidden_shortcuts"])
    lines.extend(["", payload["boundary"], ""])
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
