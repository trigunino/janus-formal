from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))


HOLST_PATH = Path("outputs/active_z2_sigma/holst_nieh_yan_radial_inputs.json")
OUTPUT_PATH = Path("outputs/active_z2_sigma/counterterm_immirzi_residual_scalar_inputs.json")
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_counterterm_immirzi_scalar_contraction_torsionless.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_counterterm_immirzi_scalar_contraction_torsionless.json"
)


def _reject_forbidden(payload: dict) -> None:
    for key in [
        "compressed_planck_lcdm_background_used",
        "archived_z4_reuse_used",
        "archived_z4_background_reuse_used",
        "phenomenological_holst_bao_scan_used",
        "observational_H0_fit_used",
        "observational_curvature_fit_used",
        "fitted_counterterm_coefficient_used",
    ]:
        if payload.get(key, False) is not False:
            raise ValueError(f"Forbidden provenance flag must be false: {key}")


def _build_output(holst: dict) -> dict:
    if holst.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("Holst payload active_core must be Z2_tunnel_Sigma")
    if holst.get("source") != "active_derived":
        raise ValueError("Holst payload source must be active_derived")
    _reject_forbidden(holst)
    if holst.get("torsionless_Nieh_Yan_zero_identity_ready") is not True:
        raise ValueError("torsionless_Nieh_Yan_zero_identity_ready must be true")
    if holst.get("holst_nieh_yan_radial_reduction_ready") is not True:
        raise ValueError("holst_nieh_yan_radial_reduction_ready must be true")
    values = [float(v) for v in holst["E_HolstNiehYan_values"]]
    if any(v != 0.0 for v in values):
        raise ValueError("E_HolstNiehYan_values must vanish on this branch")
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
        "archived_z4_background_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "observational_H0_fit_used": False,
        "observational_curvature_fit_used": False,
        "fitted_counterterm_coefficient_used": False,
        "a_grid": holst["a_grid"],
        "R_chi_partial_R_chi_values": [0.0 for _ in values],
        "R_chi_profile_solved": False,
        "partial_R_chi_profile_solved": False,
        "scalar_contraction_ready": True,
        "L_ct_integration_constant_fixed": False,
        "provenance": (
            "active torsionless Sigma branch: NY pullback and E_HolstNiehYan vanish "
            "for any Immirzi profile; only the radial contraction R_chi partial_R chi "
            "is zero, not a solved Immirzi profile"
        ),
    }


def build_payload(
    *,
    holst_path: Path = HOLST_PATH,
    output_path: Path = OUTPUT_PATH,
) -> dict:
    input_exists = holst_path.exists()
    output_written = False
    validation_error = None
    output = None
    if input_exists:
        try:
            output = _build_output(json.loads(holst_path.read_text(encoding="utf-8")))
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(json.dumps(output, indent=2), encoding="utf-8")
            output_written = True
        except Exception as exc:
            validation_error = str(exc)
    return {
        "status": "janus-z2-sigma-counterterm-immirzi-scalar-contraction-torsionless",
        "active_core": "Z2_tunnel_Sigma",
        "input_manifest": str(holst_path),
        "output_manifest": str(output_path),
        "input_exists": input_exists,
        "immirzi_scalar_contraction_written": output_written,
        "gate_passed": output_written,
        "validation_error": validation_error,
        "output": output,
        "primary_blocker": "none" if output_written else "holst_nieh_yan_radial_inputs",
        "next_required": [] if output_written else ["derive_torsionless_Nieh_Yan_zero_identity"],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Counterterm Immirzi Scalar Contraction",
        "",
        f"Output written: `{payload['immirzi_scalar_contraction_written']}`",
        f"Gate passed: `{payload['gate_passed']}`",
    ]
    if payload["validation_error"]:
        lines.extend(["", "## Validation Error", payload["validation_error"]])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
