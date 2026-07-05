from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_projected_baryon_noether_charge_input_gate import (
    build_payload as build_projected_baryon_charge_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_spatial_volume_projective_slice_gate import (
    build_payload as build_spatial_volume_payload,
)
from src.janus_lab.z2_sigma_projected_baryon_charge import (
    validate_active_projected_baryon_charge_payload,
)


CHARGE_PATH = Path("outputs/active_z2_sigma/projected_baryon_noether_charge_inputs.json")
VOLUME_PATH = Path("outputs/active_z2_sigma/spatial_volume_normalization_inputs.json")
OUTPUT_PATH = Path(
    "outputs/active_z2_sigma/early_plasma_baryon_number_density_noether_volume_inputs.json"
)
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_baryon_number_density_noether_volume_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_baryon_number_density_noether_volume_gate.json"
)


FORBIDDEN_FLAGS = [
    "compressed_planck_lcdm_rd_used",
    "archived_z4_reuse_used",
    "phenomenological_holst_bao_scan_used",
]


def _load(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def _validate_common(payload: dict, label: str) -> None:
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError(f"{label} active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_derived":
        raise ValueError(f"{label} source must be active_derived")
    for key in FORBIDDEN_FLAGS:
        if payload.get(key) is not False:
            raise ValueError(f"{label} forbidden provenance flag must be false: {key}")


def _assemble(charge: dict, volume: dict) -> dict:
    charge = validate_active_projected_baryon_charge_payload(charge)
    _validate_common(volume, "Volume")
    charge_values = charge.get("normalizations", {})
    volume_values = volume.get("normalizations", {})
    charge_provenance = charge.get("normalization_provenance", {})
    volume_provenance = volume.get("normalization_provenance", {})
    n_projected = float(charge_values["projected_baryon_number_charge_Z2Sigma"])
    volume0 = float(volume_values["spatial_volume0_m3_Z2Sigma"])
    if volume0 <= 0.0:
        raise ValueError("spatial_volume0_m3_Z2Sigma must be positive")
    volume_policy = volume.get("volume_policy", {})
    if volume_policy.get("z2_cover_factor_applied_once") is not True:
        raise ValueError("Z2 cover factor must be applied exactly once in volume policy")
    if "volume_convention" not in volume_policy:
        raise ValueError("volume_policy.volume_convention is required")
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "compressed_planck_lcdm_rd_used": False,
        "archived_z4_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "formula": "n_b0_Z2Sigma = N_b,Z2Sigma / V0,Z2Sigma",
        "normalizations": {
            "baryon_number_density0_m3_Z2Sigma": n_projected / volume0,
            "projected_baryon_number_charge_Z2Sigma": n_projected,
            "spatial_volume0_m3_Z2Sigma": volume0,
        },
        "normalization_provenance": {
            "baryon_number_density0_m3_Z2Sigma": (
                "derived_from_projected_Noether_baryon_charge_and_active_spatial_volume"
            ),
            "projected_baryon_number_charge_Z2Sigma": charge_provenance[
                "projected_baryon_number_charge_Z2Sigma"
            ],
            "spatial_volume0_m3_Z2Sigma": volume_provenance["spatial_volume0_m3_Z2Sigma"],
        },
        "volume_policy": volume_policy,
    }


def build_payload(
    *,
    charge_path: Path = CHARGE_PATH,
    volume_path: Path = VOLUME_PATH,
    output_path: Path = OUTPUT_PATH,
) -> dict:
    charge_exists = charge_path.exists()
    volume_exists = volume_path.exists()
    charge_gate = build_projected_baryon_charge_payload()
    volume_gate = build_spatial_volume_payload()
    validation_error = None
    output_written = False
    active_charge_valid = False
    active_volume_valid = False
    if charge_exists and volume_exists:
        try:
            density = _assemble(_load(charge_path), _load(volume_path))
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(json.dumps(density, indent=2), encoding="utf-8")
            output_written = True
            active_charge_valid = True
            active_volume_valid = True
        except Exception as exc:
            validation_error = str(exc)
    elif not charge_gate["gate_passed"]:
        validation_error = "Projected baryon charge manifest missing or gate is not derived"
    elif not volume_gate["gate_passed"]:
        validation_error = "Spatial volume manifest missing or projective slice gate is not derived"
    upstream_frontiers = {
        "projected_baryon_charge": {
            "gate": charge_gate["status"],
            "passed": charge_gate["gate_passed"],
            "manifest_exists": charge_exists,
            "nearest_frontier": charge_gate.get("nearest_projected_baryon_charge_frontier"),
            "upstream_frontiers": charge_gate.get("upstream_frontiers", {}),
            "primary_blocker": charge_gate.get("primary_blocker", "projected_baryon_charge"),
        },
        "spatial_volume": {
            "gate": volume_gate["status"],
            "passed": volume_gate["gate_passed"],
            "manifest_exists": volume_exists,
            "input_exists": volume_gate.get("input_exists"),
            "requires_active_R_curv_Z2Sigma": volume_gate.get(
                "requires_active_R_curv_Z2Sigma"
            ),
            "requires_k_Z2Sigma_plus_one": volume_gate.get("requires_k_Z2Sigma_plus_one"),
            "validation_error": volume_gate.get("validation_error"),
            "primary_blocker": volume_gate.get("primary_blocker", "spatial_volume"),
        },
    }
    missing = [
        name
        for name, frontier in upstream_frontiers.items()
        if not frontier["passed"] and not frontier["manifest_exists"]
    ]
    if output_written:
        primary_blocker = "none"
    elif not charge_exists and charge_gate.get("primary_blocker") != "none":
        primary_blocker = charge_gate.get("primary_blocker", "projected_baryon_charge")
    elif not volume_exists and volume_gate.get("primary_blocker") != "none":
        primary_blocker = volume_gate.get("primary_blocker", "spatial_volume")
    else:
        primary_blocker = "projected_baryon_charge_and_spatial_volume"
    return {
        "status": "janus-z2-sigma-baryon-number-density-noether-volume-gate",
        "active_core": "Z2_tunnel_Sigma",
        "projected_charge_manifest": str(charge_path),
        "spatial_volume_manifest": str(volume_path),
        "output_manifest": str(output_path),
        "projected_charge_manifest_exists": charge_exists,
        "spatial_volume_manifest_exists": volume_exists,
        "projected_baryon_charge_gate_passed": charge_gate["gate_passed"],
        "spatial_volume_projective_slice_gate_passed": volume_gate["gate_passed"],
        "accepts_explicit_active_manifests": True,
        "active_projected_baryon_charge_valid": active_charge_valid,
        "active_spatial_volume_valid": active_volume_valid,
        "upstream_frontiers": upstream_frontiers,
        "nearest_baryon_density_frontier": {
            "blocks": missing
            or [
                "validated_projected_baryon_charge_manifest",
                "validated_spatial_volume_manifest",
            ],
            "diagnostic_only": True,
        },
        "baryon_number_density0_ready": output_written,
        "formula": "n_b0_Z2Sigma = N_b,Z2Sigma / V0,Z2Sigma",
        "observational_fit_forbidden": True,
        "compressed_planck_lcdm_rd_forbidden": True,
        "archived_z4_reuse_forbidden": True,
        "gate_passed": output_written,
        "primary_blocker": primary_blocker,
        "validation_error": validation_error,
        "next_required": [
            "derive_projected_Noether_baryon_charge_Z2Sigma",
            "derive_active_spatial_volume0_Z2Sigma",
            "apply_Z2_cover_factor_exactly_once",
            "feed_baryon_number_density0_to_early_plasma_model_normalizations",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Baryon Number Density Noether/Volume Gate",
        "",
        f"Projected charge manifest exists: `{payload['projected_charge_manifest_exists']}`",
        f"Spatial volume manifest exists: `{payload['spatial_volume_manifest_exists']}`",
        f"Baryon number density ready: `{payload['baryon_number_density0_ready']}`",
        f"Gate passed: `{payload['gate_passed']}`",
        "",
        f"Formula: `{payload['formula']}`",
    ]
    if payload["validation_error"]:
        lines.extend(["", "## Validation Error", payload["validation_error"]])
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
