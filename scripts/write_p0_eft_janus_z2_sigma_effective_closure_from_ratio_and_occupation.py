from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.janus_lab.z2_sigma_effective_closure import validate_effective_closure_payload
from src.janus_lab.z2_sigma_projected_occupation_state import (
    load_projected_occupation_state_payload,
)


PARTIAL_PATH = Path(
    "outputs/active_z2_sigma/effective_partial_closure_from_projective_ratio.json"
)
OCCUPATION_PATH = Path("outputs/active_z2_sigma/projected_occupation_state_inputs.json")
OUTPUT_PATH = Path("outputs/active_z2_sigma/effective_closure_inputs.json")
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_effective_closure_from_ratio_and_occupation.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_effective_closure_from_ratio_and_occupation.json"
)


def _load_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def _load_ratio(partial_path: Path) -> float:
    payload = _load_json(partial_path)
    return float(
        payload["derived_effective_initial_data"][
            "R_Sigma_over_ell_collar_Z2Sigma"
        ]
    )


def _load_occupation(occupation_path: Path) -> tuple[float, str]:
    payload = load_projected_occupation_state_payload(occupation_path)
    return float(payload["N_occ_Z2Sigma"]), str(payload["N_occ_provenance"])


def build_payload(
    *,
    partial_path: Path = PARTIAL_PATH,
    occupation_path: Path = OCCUPATION_PATH,
    output_path: Path = OUTPUT_PATH,
) -> dict:
    partial_exists = partial_path.exists()
    occupation_exists = occupation_path.exists()
    validation_error = None
    output_written = False
    effective = None
    if partial_exists and occupation_exists:
        try:
            ratio = _load_ratio(partial_path)
            occupation, occupation_provenance = _load_occupation(occupation_path)
            effective = validate_effective_closure_payload(
                {
                    "active_core": "Z2_tunnel_Sigma",
                    "source": "effective_initial_data",
                    "compressed_planck_lcdm_used": False,
                    "archived_z4_reuse_used": False,
                    "observational_fit_used": False,
                    "full_no_fit_prediction_ready": False,
                    "effective_initial_data": {
                        "R_Sigma_over_ell_collar_Z2Sigma": ratio,
                        "projected_baryon_number_charge_Z2Sigma": occupation,
                    },
                    "effective_initial_data_provenance": {
                        "R_Sigma_over_ell_collar_Z2Sigma": "projective_stereographic_Z2_ratio_derivation",
                        "projected_baryon_number_charge_Z2Sigma": occupation_provenance,
                    },
                }
            )
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(json.dumps(effective, indent=2), encoding="utf-8")
            output_written = True
        except Exception as exc:
            validation_error = str(exc)
    elif not partial_exists:
        validation_error = "partial projective ratio manifest is missing"
    elif not occupation_exists:
        validation_error = "projected occupation state input is missing"
    return {
        "status": "janus-z2-sigma-effective-closure-from-ratio-and-occupation",
        "active_core": "Z2_tunnel_Sigma",
        "partial_manifest": str(partial_path),
        "occupation_manifest": str(occupation_path),
        "output_manifest": str(output_path),
        "partial_exists": partial_exists,
        "occupation_exists": occupation_exists,
        "effective_closure_written": output_written,
        "effective_closure_ready": output_written,
        "full_no_fit_prediction_ready": False,
        "effective_initial_data": effective["effective_initial_data"] if effective else None,
        "primary_blocker": "none" if output_written else "projected_occupation_state_inputs_json",
        "validation_error": validation_error,
        "next_required": []
        if output_written
        else [
            "write outputs/active_z2_sigma/projected_occupation_state_inputs.json",
            "source must be explicit_state_initial_data",
            "do not use Planck/LCDM/Z4/fit provenance",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Effective Closure From Ratio And Occupation",
        "",
        f"Partial exists: `{payload['partial_exists']}`",
        f"Occupation exists: `{payload['occupation_exists']}`",
        f"Effective closure ready: `{payload['effective_closure_ready']}`",
        f"Full no-fit prediction ready: `{payload['full_no_fit_prediction_ready']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
    ]
    if payload["validation_error"]:
        lines.extend(["", "## Validation Error", payload["validation_error"]])
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
