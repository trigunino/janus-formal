from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.z2_sigma_rsigma_certificate import (
    load_active_z2sigma_rsigma_solution_certificate,
)


CERTIFICATE_PATH = Path("outputs/active_z2_sigma/rsigma_solution_certificate.json")
Q_INPUT_PATH = Path("outputs/active_z2_sigma/unit_intrinsic_metric_q_ab_inputs.json")
OUTPUT_PATH = Path("outputs/active_z2_sigma/cartan_ghy_rsigma_isotropic_radius_collar_inputs.json")
REPORT_PATH = Path(
    "outputs/reports/"
    "p0_eft_janus_z2_sigma_cartan_ghy_rsigma_certificate_to_isotropic_radius_collar_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/"
    "p0_eft_janus_z2_sigma_cartan_ghy_rsigma_certificate_to_isotropic_radius_collar_gate.json"
)


def _load_q(path: Path) -> dict:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("q_ab active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_derived":
        raise ValueError("q_ab source must be active_derived")
    for key in [
        "compressed_planck_lcdm_background_used",
        "archived_z4_background_reuse_used",
        "observational_H0_fit_used",
        "observational_curvature_fit_used",
        "phenomenological_holst_bao_scan_used",
    ]:
        if payload.get(key) is not False:
            raise ValueError(f"Forbidden provenance flag must be false: {key}")
    q = np.asarray(payload.get("unit_intrinsic_metric_q_ab"), dtype=float)
    if q.ndim != 2 or q.shape[0] != q.shape[1]:
        raise ValueError("unit_intrinsic_metric_q_ab must be square")
    if not np.all(np.isfinite(q)):
        raise ValueError("unit_intrinsic_metric_q_ab must be finite")
    if not np.allclose(q, q.T):
        raise ValueError("unit_intrinsic_metric_q_ab must be symmetric")
    if np.linalg.det(q) == 0.0:
        raise ValueError("unit_intrinsic_metric_q_ab must be nondegenerate")
    provenance = str(payload.get("unit_intrinsic_metric_q_ab_provenance", "")).strip()
    if not provenance:
        raise ValueError("unit_intrinsic_metric_q_ab_provenance must be nonempty")
    lowered = provenance.lower()
    if any(token in lowered for token in ["planck", "lcdm", "z4", "fit", "bao_scan"]):
        raise ValueError(f"Forbidden provenance for unit_intrinsic_metric_q_ab: {provenance}")
    return payload


def build_payload(
    *,
    certificate_path: Path = CERTIFICATE_PATH,
    q_input_path: Path = Q_INPUT_PATH,
    output_path: Path = OUTPUT_PATH,
) -> dict:
    certificate_exists = certificate_path.exists()
    q_exists = q_input_path.exists()
    output_written = False
    validation_error = None
    if certificate_exists and q_exists:
        try:
            certificate = load_active_z2sigma_rsigma_solution_certificate(certificate_path)
            q_payload = _load_q(q_input_path)
            built = {
                "active_core": "Z2_tunnel_Sigma",
                "source": "active_derived",
                "compressed_planck_lcdm_background_used": False,
                "archived_z4_background_reuse_used": False,
                "observational_H0_fit_used": False,
                "observational_curvature_fit_used": False,
                "phenomenological_holst_bao_scan_used": False,
                "a_grid": certificate["a_grid"],
                "R_Sigma_of_a": certificate["R_Sigma_of_a"],
                "unit_intrinsic_metric_q_ab": q_payload["unit_intrinsic_metric_q_ab"],
                "radial_offsets": q_payload["radial_offsets"],
                "ambient_coordinate_offsets": q_payload["ambient_coordinate_offsets"],
                "intrinsic_coordinate_offsets": q_payload["intrinsic_coordinate_offsets"],
                "z2_orientation_sign": certificate["z2_orientation_sign"],
                "kappa_Z2Sigma": q_payload["kappa_Z2Sigma"],
                "E_CartanGHY_provenance": (
                    certificate["rsigma_solution_provenance"]
                    + " + "
                    + q_payload["unit_intrinsic_metric_q_ab_provenance"]
                ),
            }
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(json.dumps(built, indent=2), encoding="utf-8")
            output_written = True
        except Exception as exc:
            validation_error = str(exc)
    return {
        "status": "janus-z2-sigma-cartan-ghy-rsigma-certificate-to-isotropic-radius-collar-gate",
        "active_core": "Z2_tunnel_Sigma",
        "certificate_path": str(certificate_path),
        "q_input_path": str(q_input_path),
        "output_manifest": str(output_path),
        "certificate_exists": certificate_exists,
        "q_input_exists": q_exists,
        "isotropic_radius_collar_input_written": output_written,
        "gate_passed": output_written,
        "primary_blocker": "none" if output_written else "R_Sigma_solution_certificate_and_unit_q_ab",
        "validation_error": validation_error,
        "next_required": []
        if output_written
        else [
            "provide_outputs_active_z2_sigma_rsigma_solution_certificate_json",
            "provide_outputs_active_z2_sigma_unit_intrinsic_metric_q_ab_inputs_json",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma R_Sigma Certificate To Isotropic Radius Collar Gate",
        "",
        f"Certificate exists: `{payload['certificate_exists']}`",
        f"q_ab input exists: `{payload['q_input_exists']}`",
        f"Output written: `{payload['isotropic_radius_collar_input_written']}`",
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
