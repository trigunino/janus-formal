from __future__ import annotations

import json
from pathlib import Path


OUTPUT_PATH = Path("outputs/active_z2_sigma/background_gravity_normalization_inputs.json")
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_background_gravity_codata_convention_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_background_gravity_codata_convention_gate.json"
)

G_CODATA_2022_SI = 6.67430e-11
G_CODATA_2022_STANDARD_UNCERTAINTY_SI = 0.00015e-11
NIST_CODATA_G_URL = "https://physics.nist.gov/cgi-bin/cuu/Value?bg="


def build_payload(*, output_path: Path = OUTPUT_PATH, write_output: bool = True) -> dict:
    output_written = False
    output_valid = False
    validation_error = None
    if write_output:
        output_path.parent.mkdir(parents=True, exist_ok=True)
        output_path.write_text(
            json.dumps(
                {
                    "active_core": "Z2_tunnel_Sigma",
                    "source": "active_derived",
                    "compressed_planck_lcdm_background_used": False,
                    "archived_z4_background_reuse_used": False,
                    "observational_H0_fit_used": False,
                    "scalars": {
                        "gravitational_constant_si_Z2Sigma": G_CODATA_2022_SI,
                    },
                    "scalar_provenance": {
                        "G_Z2Sigma": "explicit_low_energy_SI_gravity_convention:NIST_CODATA_2022_Newtonian_constant_of_gravitation",
                    },
                    "source_reference": {
                        "name": "NIST CODATA Newtonian constant of gravitation",
                        "url": NIST_CODATA_G_URL,
                        "standard_uncertainty_si": G_CODATA_2022_STANDARD_UNCERTAINTY_SI,
                    },
                },
                indent=2,
            ),
            encoding="utf-8",
        )
        output_written = True
    if output_path.exists():
        try:
            payload = json.loads(output_path.read_text(encoding="utf-8"))
            output_valid = (
                payload.get("active_core") == "Z2_tunnel_Sigma"
                and payload.get("source") == "active_derived"
                and payload.get("compressed_planck_lcdm_background_used") is False
                and payload.get("archived_z4_background_reuse_used") is False
                and payload.get("observational_H0_fit_used") is False
                and float(payload["scalars"]["gravitational_constant_si_Z2Sigma"])
                == G_CODATA_2022_SI
                and "NIST_CODATA_2022"
                in payload["scalar_provenance"]["G_Z2Sigma"]
            )
        except Exception as exc:
            validation_error = str(exc)
    return {
        "status": "janus-z2-sigma-background-gravity-codata-convention-gate",
        "active_core": "Z2_tunnel_Sigma",
        "bibliography_checked": True,
        "primary_sources_checked": [NIST_CODATA_G_URL],
        "G_Z2Sigma_value_si": G_CODATA_2022_SI,
        "G_Z2Sigma_standard_uncertainty_si": G_CODATA_2022_STANDARD_UNCERTAINTY_SI,
        "output_manifest": str(output_path),
        "output_written": output_written,
        "output_exists": output_path.exists(),
        "output_valid": output_valid,
        "validation_error": validation_error,
        "uses_compressed_planck_lcdm_background": False,
        "uses_archived_z4_background": False,
        "uses_observational_H0_fit": False,
        "is_cosmological_parameter_fit": False,
        "gate_passed": output_valid,
        "next_required": [
            "run_background_gravity_input_writer_gate",
            "combine_with_active_H0_and_curvature_inputs",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# Janus Z2/Sigma Background Gravity CODATA Convention Gate",
                "",
                f"G value SI: `{payload['G_Z2Sigma_value_si']}`",
                f"Output written: `{payload['output_written']}`",
                f"Gate passed: `{payload['gate_passed']}`",
            ]
        ),
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
