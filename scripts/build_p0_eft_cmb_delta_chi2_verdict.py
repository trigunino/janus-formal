from __future__ import annotations

from pathlib import Path
import json


REPORT_PATH = Path("outputs/reports/p0_eft_cmb_delta_chi2_verdict.md")
JSON_PATH = Path("outputs/reports/p0_eft_cmb_delta_chi2_verdict.json")
CALIBRATION_PATH = Path("outputs/reports/p0_eft_planck_likelihood_baseline_calibration.json")
VISIBILITY_PATH = Path("outputs/reports/p0_eft_nonlocal_visibility_scan.json")
POLARIZATION_PATH = Path("outputs/reports/p0_eft_polarization_source_shape_scan.json")


def read_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def build_payload() -> dict:
    calibration = read_json(CALIBRATION_PATH)
    visibility = read_json(VISIBILITY_PATH)
    polarization = read_json(POLARIZATION_PATH)
    deltas = calibration["deltas_janus_minus_reference"]
    lowe_ok = abs(deltas["chi2_lowl_EE"]) < 2.0
    highl_ok = deltas["chi2_highl"] < 0.0
    lensing_blocker = deltas["chi2_lensing"] > 2.0
    cmb_delta_ok_at_working_point = deltas["chi2_CMB"] < 0.0

    return {
        "description": "Delta-chi2 CMB verdict using raw Planck likelihood with LCDM only as numerical offset calibration.",
        "status": "cmb-delta-chi2-verdict-recorded",
        "uses_lcdm_compressed_parameters_as_data": False,
        "raw_planck_likelihood_used": True,
        "deltas_janus_minus_reference": deltas,
        "working_point_improves_total_delta_chi2": cmb_delta_ok_at_working_point,
        "lowE_reclassified_as_not_blocking": lowe_ok,
        "highl_reclassified_as_not_blocking_at_working_point": highl_ok,
        "lensing_is_residual_blocker": lensing_blocker,
        "nonlocal_visibility_best_chi2_CMB": visibility["best"]["chi2_CMB"],
        "polarization_source_best_chi2_CMB": polarization["best"]["chi2_CMB"],
        "full_cosmology_prediction_ready_no_fit": False,
        "next_required": (
            "Stop targeting lowE absolute chi2. Focus on calibrated high-l transfer and lensing/Weyl "
            "consistency using direct raw-likelihood delta-chi2 gates."
        ),
    }


def render_markdown(payload: dict) -> str:
    return "\n".join(
        [
            "# P0 EFT CMB Delta-Chi2 Verdict",
            "",
            payload["description"],
            "",
            f"Status: {payload['status']}",
            f"Uses LCDM compressed parameters as data: {payload['uses_lcdm_compressed_parameters_as_data']}",
            f"Raw Planck likelihood used: {payload['raw_planck_likelihood_used']}",
            f"Working point improves total delta chi2: {payload['working_point_improves_total_delta_chi2']}",
            f"lowE not blocking: {payload['lowE_reclassified_as_not_blocking']}",
            f"high-l not blocking at working point: {payload['highl_reclassified_as_not_blocking_at_working_point']}",
            f"lensing residual blocker: {payload['lensing_is_residual_blocker']}",
            f"Full no-fit ready: {payload['full_cosmology_prediction_ready_no_fit']}",
            "",
            "## Delta chi2 Janus - Reference",
            "",
            *[f"- `{key}`: `{value}`" for key, value in payload["deltas_janus_minus_reference"].items()],
            "",
            "## Next",
            "",
            payload["next_required"],
            "",
        ]
    )


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
