from __future__ import annotations

import json
from pathlib import Path


SCALE_PATH = Path(
    "outputs/active_z2_sigma/background_dimensionless_curvature_scale_normalization_inputs.json"
)
H0_PATH = Path("outputs/active_z2_sigma/background_H0_normalization_inputs.json")
RADIUS_PATH = Path("outputs/active_z2_sigma/background_curvature_radius_inputs.json")
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_dimensionful_scale_separation_obligation_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_dimensionful_scale_separation_obligation_gate.json"
)


def _read_scale(path: Path) -> float | None:
    if not path.exists():
        return None
    payload = json.loads(path.read_text(encoding="utf-8"))
    return float(payload["scalars"]["h0_R_curv_over_c_Z2Sigma"])


def build_payload(
    *,
    scale_path: Path = SCALE_PATH,
    h0_path: Path = H0_PATH,
    radius_path: Path = RADIUS_PATH,
) -> dict:
    scale_value = _read_scale(scale_path)
    scale_exists = scale_value is not None
    h0_exists = h0_path.exists()
    radius_exists = radius_path.exists()
    dimensionful_inputs_ready = h0_exists and radius_exists
    return {
        "status": "janus-z2-sigma-dimensionful-scale-separation-obligation-gate",
        "active_core": "Z2_tunnel_Sigma",
        "dimensionless_scale_manifest": str(scale_path),
        "h0_normalization_manifest": str(h0_path),
        "curvature_radius_manifest": str(radius_path),
        "dimensionless_scale_exists": scale_exists,
        "h0_normalization_exists": h0_exists,
        "curvature_radius_exists": radius_exists,
        "h0_R_curv_over_c_Z2Sigma": scale_value,
        "can_compute_scale_free_omega_k_from_product": scale_exists,
        "can_invert_product_to_H0_or_R_curv": False,
        "dimensionless_product_insufficient_for_physical_volume": True,
        "dimensionless_product_insufficient_for_Gamma_drag_over_H0": True,
        "dimensionful_scale_inputs_ready": dimensionful_inputs_ready,
        "uses_compressed_planck_lcdm_background": False,
        "uses_archived_z4_background": False,
        "uses_observational_H0_fit": False,
        "uses_observational_curvature_fit": False,
        "gate_passed": dimensionful_inputs_ready,
        "blocker": None
        if dimensionful_inputs_ready
        else "derive active H0_Z2Sigma and active R_curv_Z2Sigma separately; do not invert H0*R_curv/c",
        "next_required": [
            "derive_active_H0_Z2Sigma_scale_normalization",
            "derive_active_R_curv_Z2Sigma_from_embedding_or_throat_scale",
            "rerun_background_H0_and_curvature_radius_input_writers",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Dimensionful Scale Separation Obligation Gate",
        "",
        f"Dimensionless scale exists: `{payload['dimensionless_scale_exists']}`",
        f"H0 normalization exists: `{payload['h0_normalization_exists']}`",
        f"Curvature radius exists: `{payload['curvature_radius_exists']}`",
        f"Can invert product: `{payload['can_invert_product_to_H0_or_R_curv']}`",
        f"Gate passed: `{payload['gate_passed']}`",
    ]
    if payload["blocker"]:
        lines.extend(["", "## Blocker", payload["blocker"]])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
