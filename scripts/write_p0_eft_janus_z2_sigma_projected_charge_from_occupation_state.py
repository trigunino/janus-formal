from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_projected_baryon_noether_charge_input_gate import (
    build_payload as build_charge_gate_payload,
)
from src.janus_lab.z2_sigma_projected_occupation_state import (
    load_projected_occupation_state_payload,
)


OCCUPATION_PATH = Path("outputs/active_z2_sigma/projected_occupation_state_inputs.json")
SOURCE_PATH = Path("outputs/active_z2_sigma/projected_baryon_noether_charge_source_inputs.json")
CHARGE_PATH = Path("outputs/active_z2_sigma/projected_baryon_noether_charge_inputs.json")
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_projected_charge_from_occupation_state.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_projected_charge_from_occupation_state.json"
)


def _source_from_occupation(occupation: dict) -> dict:
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_rd_used": False,
        "archived_z4_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "observational_baryon_fit_used": False,
        "projected_Dirac_current_ready": True,
        "charge_boundary_projection_ready": True,
        "projection_weights_free": False,
        "formula": "N_b,Z2Sigma = N_occ,Z2Sigma",
        "normalizations": {
            "projected_baryon_number_charge_Z2Sigma": occupation["N_occ_Z2Sigma"],
        },
        "normalization_provenance": {
            "projected_baryon_number_charge_Z2Sigma": (
                "derived_from_explicit_projected_occupation_state_initial_data"
            ),
        },
        "occupation_state": occupation,
    }


def build_payload(
    *,
    occupation_path: Path = OCCUPATION_PATH,
    source_path: Path = SOURCE_PATH,
    charge_path: Path = CHARGE_PATH,
    write_output: bool = True,
) -> dict:
    occupation_exists = occupation_path.exists()
    source_written = False
    validation_error = None
    charge_gate = None
    if occupation_exists:
        try:
            occupation = load_projected_occupation_state_payload(occupation_path)
            source = _source_from_occupation(occupation)
            if write_output:
                source_path.parent.mkdir(parents=True, exist_ok=True)
                source_path.write_text(json.dumps(source, indent=2), encoding="utf-8")
            source_written = True
            charge_gate = build_charge_gate_payload(
                input_path=source_path,
                output_path=charge_path,
            )
        except Exception as exc:
            validation_error = str(exc)
    primary_blocker = (
        "none"
        if charge_gate and charge_gate["gate_passed"]
        else "projected_occupation_state_inputs_json"
        if not occupation_exists
        else validation_error
        or "projected_baryon_noether_charge_input_gate"
    )
    return {
        "status": "janus-z2-sigma-projected-charge-from-occupation-state",
        "active_core": "Z2_tunnel_Sigma",
        "occupation_manifest": str(occupation_path),
        "source_manifest": str(source_path),
        "charge_manifest": str(charge_path),
        "occupation_manifest_exists": occupation_exists,
        "source_manifest_written": source_written,
        "charge_manifest_written": bool(charge_gate and charge_gate["gate_passed"]),
        "full_no_fit_prediction_ready": False,
        "observational_fit_used": False,
        "gate_passed": bool(charge_gate and charge_gate["gate_passed"]),
        "primary_blocker": primary_blocker,
        "validation_error": validation_error,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# Janus Z2/Sigma Projected Charge From Occupation State",
                "",
                f"Occupation manifest exists: `{payload['occupation_manifest_exists']}`",
                f"Source manifest written: `{payload['source_manifest_written']}`",
                f"Charge manifest written: `{payload['charge_manifest_written']}`",
                f"Full no-fit prediction ready: `{payload['full_no_fit_prediction_ready']}`",
                f"Gate passed: `{payload['gate_passed']}`",
                f"Primary blocker: `{payload['primary_blocker']}`",
            ]
        ),
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
