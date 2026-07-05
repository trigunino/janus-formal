from __future__ import annotations

import json
from pathlib import Path


INPUT_PATH = Path("outputs/active_z2_sigma/early_plasma_photon_density_firas_codata_inputs.json")
OUTPUT_PATH = Path("outputs/active_z2_sigma/early_plasma_photon_density_history_firas_codata.json")
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_early_plasma_photon_density_history_firas_codata_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_early_plasma_photon_density_history_firas_codata_gate.json"
)
DEFAULT_Z_GRID = [0.0, 10.0, 100.0, 1000.0, 2000.0]


def _load(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def _history_payload(input_payload: dict, z_grid: list[float]) -> dict:
    rho0 = float(input_payload["normalizations"]["rho_photon0_Z2Sigma_J_m3"])
    if rho0 <= 0.0:
        raise ValueError("rho_photon0_Z2Sigma_J_m3 must be positive")
    if any(z < 0.0 for z in z_grid) or any(b <= a for a, b in zip(z_grid, z_grid[1:])):
        raise ValueError("z_grid must be non-negative and strictly increasing")
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "direct_noncompressed_observation_plus_codata",
        "compressed_planck_lcdm_rd_used": False,
        "archived_z4_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "observational_fit_used": False,
        "formula": "rho_photon_Z2Sigma(z)=rho_photon0_Z2Sigma*(1+z)^4",
        "z_grid": z_grid,
        "rho_photon_Z2Sigma_J_m3": [rho0 * (1.0 + z) ** 4 for z in z_grid],
        "normalizations": {
            "rho_photon0_Z2Sigma_J_m3": rho0,
        },
        "input_manifest": str(INPUT_PATH),
    }


def build_payload(
    *,
    input_path: Path = INPUT_PATH,
    output_path: Path = OUTPUT_PATH,
    z_grid: list[float] | None = None,
    write_output: bool = True,
) -> dict:
    input_exists = input_path.exists()
    output_written = False
    output_valid = False
    validation_error = None
    if z_grid is None:
        z_grid = DEFAULT_Z_GRID
    if input_exists and write_output:
        try:
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(
                json.dumps(_history_payload(_load(input_path), z_grid), indent=2),
                encoding="utf-8",
            )
            output_written = True
        except Exception as exc:
            validation_error = str(exc)
    if output_path.exists():
        try:
            payload = _load(output_path)
            values = payload["rho_photon_Z2Sigma_J_m3"]
            output_valid = (
                payload.get("active_core") == "Z2_tunnel_Sigma"
                and payload.get("source") == "direct_noncompressed_observation_plus_codata"
                and payload.get("compressed_planck_lcdm_rd_used") is False
                and payload.get("archived_z4_reuse_used") is False
                and len(values) == len(payload["z_grid"])
                and all(float(value) > 0.0 for value in values)
            )
        except Exception as exc:
            validation_error = str(exc)
    return {
        "status": "janus-z2-sigma-early-plasma-photon-density-history-firas-codata-gate",
        "active_core": "Z2_tunnel_Sigma",
        "input_manifest": str(input_path),
        "output_manifest": str(output_path),
        "input_exists": input_exists,
        "output_written": output_written,
        "output_exists": output_path.exists(),
        "output_valid": output_valid,
        "validation_error": validation_error,
        "rho_photon_history_available": output_valid,
        "uses_compressed_planck_lcdm_rd": False,
        "uses_archived_z4_inputs": False,
        "uses_phenomenological_holst_bao_scan": False,
        "uses_observational_fit": False,
        "gate_passed": output_valid,
        "does_not_fix_baryon_or_ionization_normalizations": True,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# Janus Z2/Sigma Photon Density History FIRAS+CODATA Gate",
                "",
                f"Photon history available: `{payload['rho_photon_history_available']}`",
                f"Gate passed: `{payload['gate_passed']}`",
            ]
        ),
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
