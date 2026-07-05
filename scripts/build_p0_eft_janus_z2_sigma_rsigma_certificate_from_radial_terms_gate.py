from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.z2_sigma_rsigma_certificate import (
    write_active_z2sigma_rsigma_solution_certificate,
)
from janus_lab.z2_sigma_rsigma_equation import (
    assemble_rsigma_residual_payload,
    build_rsigma_certificate_from_residual_payload,
)


INPUT_PATH = Path("outputs/active_z2_sigma/rsigma_radial_terms_inputs.json")
OUTPUT_PATH = Path("outputs/active_z2_sigma/rsigma_solution_certificate.json")
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_rsigma_certificate_from_radial_terms_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_rsigma_certificate_from_radial_terms_gate.json"
)


def _load_input(path: Path) -> dict:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("Input active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_derived":
        raise ValueError("Input source must be active_derived")
    for key in [
        "compressed_planck_lcdm_background_used",
        "archived_z4_background_reuse_used",
        "observational_H0_fit_used",
        "observational_curvature_fit_used",
        "phenomenological_holst_bao_scan_used",
    ]:
        if payload.get(key) is not False:
            raise ValueError(f"Forbidden provenance flag must be false: {key}")
    return payload


def build_payload(*, input_path: Path = INPUT_PATH, output_path: Path = OUTPUT_PATH) -> dict:
    input_exists = input_path.exists()
    certificate_written = False
    validation_error = None
    residual_max_abs = None
    if input_exists:
        try:
            source = _load_input(input_path)
            residual_payload = assemble_rsigma_residual_payload(
                a_grid=source["a_grid"],
                E_CartanGHY=source["E_CartanGHY"],
                E_HolstNiehYan=source["E_HolstNiehYan"],
                E_matterFlux=source["E_matterFlux"],
                E_counterterm=source["E_counterterm"],
                term_provenance=source["term_provenance"],
            )
            residual_max_abs = residual_payload["R_Sigma_solution_residual_max_abs"]
            certificate = build_rsigma_certificate_from_residual_payload(
                residual_payload=residual_payload,
                certificate_payload=source["certificate_payload"],
            )
            write_active_z2sigma_rsigma_solution_certificate(output_path, certificate)
            certificate_written = True
        except Exception as exc:
            validation_error = str(exc)
    return {
        "status": "janus-z2-sigma-rsigma-certificate-from-radial-terms-gate",
        "active_core": "Z2_tunnel_Sigma",
        "input_manifest": str(input_path),
        "output_certificate": str(output_path),
        "input_exists": input_exists,
        "effective_RSigma_equation_extracted": input_exists and validation_error is None,
        "R_Sigma_solution_residual_max_abs": residual_max_abs,
        "requires_term_provenance": True,
        "R_Sigma_solution_certificate_written": certificate_written,
        "gate_passed": certificate_written,
        "primary_blocker": "none" if certificate_written else "R_Sigma_solution_certificate",
        "validation_error": validation_error,
        "next_required": []
        if certificate_written
        else [
            "supply_outputs_active_z2_sigma_rsigma_radial_terms_inputs_json",
            "ensure_E_CartanGHY_E_HolstNiehYan_E_matterFlux_E_counterterm_sum_to_zero",
            "provide_matching_embedding_curvature_H0_payload_without_fit",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma R_Sigma Certificate From Radial Terms Gate",
        "",
        f"Input exists: `{payload['input_exists']}`",
        f"Residual max abs: `{payload['R_Sigma_solution_residual_max_abs']}`",
        f"Certificate written: `{payload['R_Sigma_solution_certificate_written']}`",
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
