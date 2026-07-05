from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.z2_sigma_early_plasma import (
    make_conserved_baryon_density_z2sigma,
    make_blackbody_photon_energy_density_z2sigma,
    make_conserved_photon_temperature_z2sigma,
    make_free_electron_density_z2sigma,
    make_thomson_drag_rate_z2sigma,
)
from janus_lab.z2_sigma_early_plasma_inputs import load_active_z2sigma_early_plasma_input_manifest
from janus_lab.z2_sigma_early_plasma_manifest import (
    Z2SigmaEarlyPlasmaComponentFunctions,
    write_active_z2sigma_early_plasma_manifest,
)


INPUT_PATH = Path("outputs/active_z2_sigma/early_plasma_inputs.json")
MANIFEST_PATH = Path("outputs/active_z2_sigma/early_plasma.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_early_plasma_manifest_writer_from_inputs_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_early_plasma_manifest_writer_from_inputs_gate.json")


def _build_components(payload: dict) -> Z2SigmaEarlyPlasmaComponentFunctions:
    n = payload["normalizations"]
    photon_temperature = make_conserved_photon_temperature_z2sigma(
        float(n["photon_temperature0_Z2Sigma"])
    )
    rho_photon = make_blackbody_photon_energy_density_z2sigma(
        photon_temperature,
        radiation_constant_j_m3_k4=float(n["radiation_constant_J_m3_K4"]),
    )
    baryon_number = lambda z: float(n["baryon_number_density0_m3_Z2Sigma"]) * (1.0 + z) ** 3
    rho_baryon = make_conserved_baryon_density_z2sigma(float(n["rho_baryon0_Z2Sigma"]))
    if "ionization_history" in payload:
        history_z = np.asarray(payload["ionization_history"]["z_grid"], dtype=float)
        history_xe = np.asarray(
            payload["ionization_history"]["ionization_fraction_Z2Sigma"],
            dtype=float,
        )

        def ionization(z):
            z_arr = np.asarray(z, dtype=float)
            return np.interp(z_arr, history_z, history_xe)

    else:
        ionization = lambda z: float(n["ionization_fraction_Z2Sigma"]) * (1.0 + 0.0 * z)
    free_electron = make_free_electron_density_z2sigma(
        baryon_number,
        ionization,
        electrons_per_baryon=float(n["electrons_per_baryon"]),
    )
    gamma_drag = make_thomson_drag_rate_z2sigma(
        free_electron,
        rho_baryon,
        rho_photon,
        sigma_thomson_m2=float(n["sigma_thomson_m2"]),
    )
    return Z2SigmaEarlyPlasmaComponentFunctions(
        rho_baryon_z2sigma=rho_baryon,
        rho_photon_z2sigma=rho_photon,
        gamma_drag_z2sigma=gamma_drag,
    )


def build_payload(
    *,
    input_path: Path = INPUT_PATH,
    manifest_path: Path = MANIFEST_PATH,
) -> dict:
    input_exists = input_path.exists()
    input_valid = False
    manifest_written = False
    validation_error = None
    if input_exists:
        try:
            payload = load_active_z2sigma_early_plasma_input_manifest(input_path)
            input_valid = True
            write_active_z2sigma_early_plasma_manifest(
                manifest_path,
                payload["z_grid"],
                _build_components(payload),
                {
                    "rho_baryon_Z2Sigma": payload["normalization_provenance"][
                        "rho_baryon0_Z2Sigma"
                    ],
                    "rho_photon_Z2Sigma": payload["normalization_provenance"][
                        "photon_temperature0_Z2Sigma"
                    ],
                    "Gamma_drag_Z2Sigma": payload["normalization_provenance"][
                        "sigma_thomson_m2"
                    ]
                    + (
                        "_with_"
                        + payload["ionization_history"]["provenance"]
                        if "ionization_history" in payload
                        else ""
                    ),
                },
            )
            manifest_written = True
        except Exception as exc:
            validation_error = str(exc)
    return {
        "status": "janus-z2-sigma-early-plasma-manifest-writer-from-inputs-gate",
        "active_core": "Z2_tunnel_Sigma",
        "input_manifest": str(input_path),
        "output_manifest": str(manifest_path),
        "input_exists": input_exists,
        "input_valid": input_valid,
        "manifest_written": manifest_written,
        "uses_compressed_planck_lcdm_rd": False,
        "uses_archived_z4_inputs": False,
        "uses_phenomenological_holst_bao_scan": False,
        "gate_passed": manifest_written,
        "validation_error": validation_error,
        "next_required": [
            "supply_outputs_active_z2_sigma_early_plasma_inputs_json",
            "run_early_plasma_component_manifest_gate",
            "run_bao_component_manifest_writer_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Early-Plasma Manifest Writer From Inputs Gate",
        "",
        f"Input exists: `{payload['input_exists']}`",
        f"Input valid: `{payload['input_valid']}`",
        f"Manifest written: `{payload['manifest_written']}`",
        f"Gate passed: `{payload['gate_passed']}`",
    ]
    if payload["validation_error"]:
        lines.extend(["", "## Validation Error", payload["validation_error"]])
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
