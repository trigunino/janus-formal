from __future__ import annotations

import json
from pathlib import Path


OUTPUT_PATH = Path("outputs/active_z2_sigma/published_bimetric_sector_ratio_inputs.json")
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_published_bimetric_sector_ratio_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_published_bimetric_sector_ratio_gate.json"
)


def build_payload(*, write_output: bool = False) -> dict:
    visible_fraction = 0.05
    negative_fraction_abs = 0.95
    ratio = -negative_fraction_abs / visible_fraction
    ratio_payload = {
        "active_core": "Z2_tunnel_Sigma",
        "source": "published_janus_M30_conclusion",
        "published_visible_fraction": visible_fraction,
        "published_negative_mass_fraction_abs": negative_fraction_abs,
        "PT_energy_sign_reversal": True,
        "rho_minus0_over_rho_plus0": ratio,
        "relative_sector_ratio_ready": True,
        "absolute_density_scale_ready": False,
        "observational_fit_used": False,
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
        "source_anchor": (
            "M30 / The Janus Cosmological Model conclusion: approximately "
            "5% visible matter and 95% negative mass."
        ),
    }
    if write_output:
        OUTPUT_PATH.parent.mkdir(parents=True, exist_ok=True)
        OUTPUT_PATH.write_text(json.dumps(ratio_payload, indent=2), encoding="utf-8")
    return {
        "status": "janus-z2-published-bimetric-sector-ratio-gate",
        "active_core": "Z2_tunnel_Sigma",
        "ratio_payload": ratio_payload,
        "relative_sector_ratio_ready": True,
        "absolute_density_scale_ready": False,
        "primary_blocker": "absolute_density_or_global_state_scale",
        "output_path": str(OUTPUT_PATH),
        "output_written": write_output,
        "forbidden_shortcuts": [
            "do_not_turn_5_95_ratio_into_absolute_density",
            "do_not_import_LCDM_omega_values",
            "do_not_fit_ratio_to_observations",
        ],
        "next_required": [
            "derive_rho_plus0_absolute_scale_from_global_bimetric_state",
            "then_set_rho_minus0_equal_ratio_times_rho_plus0",
        ],
        "gate_passed": True,
    }


def write_reports() -> dict:
    payload = build_payload(write_output=True)
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    ratio = payload["ratio_payload"]["rho_minus0_over_rho_plus0"]
    lines = [
        "# Janus Z2 Published Bimetric Sector Ratio Gate",
        "",
        f"Relative sector ratio ready: `{payload['relative_sector_ratio_ready']}`",
        f"rho_minus0/rho_plus0: `{ratio}`",
        f"Absolute density scale ready: `{payload['absolute_density_scale_ready']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
    ]
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
