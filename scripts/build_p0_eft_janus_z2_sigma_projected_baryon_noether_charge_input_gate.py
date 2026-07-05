from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_dirac_charge_boundary_projection_gate import (
    build_payload as build_dirac_charge_boundary_projection_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_dirac_number_normalization_gate import (
    build_payload as build_dirac_number_normalization_payload,
)
from src.janus_lab.z2_sigma_projected_baryon_charge import (
    validate_active_projected_baryon_charge_payload,
)


INPUT_PATH = Path("outputs/active_z2_sigma/projected_baryon_noether_charge_source_inputs.json")
OUTPUT_PATH = Path("outputs/active_z2_sigma/projected_baryon_noether_charge_inputs.json")
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_projected_baryon_noether_charge_input_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_projected_baryon_noether_charge_input_gate.json"
)


def _load(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def _build_charge(payload: dict) -> dict:
    if payload.get("projected_Dirac_current_ready") is not True:
        raise ValueError("projected_Dirac_current_ready must be true")
    if payload.get("charge_boundary_projection_ready") is not True:
        raise ValueError("charge_boundary_projection_ready must be true")
    if payload.get("projection_weights_free") is not False:
        raise ValueError("projection weights must not be free")
    output = validate_active_projected_baryon_charge_payload(payload)
    output.update({
        "projection_policy": {
            "formula": "N_b,Z2Sigma = P_Z2Sigma(N_+, N_-; psi_Sigma)",
            "projected_Dirac_current_ready": True,
            "charge_boundary_projection_ready": True,
            "projection_weights_free": False,
            "observational_baryon_fit_used": False,
        },
    })
    return output


def build_payload(*, input_path: Path = INPUT_PATH, output_path: Path = OUTPUT_PATH) -> dict:
    input_exists = input_path.exists()
    boundary_projection = build_dirac_charge_boundary_projection_payload()
    number_normalization = build_dirac_number_normalization_payload()
    output_written = False
    validation_error = None
    charge_value = None
    if input_exists:
        try:
            output = _build_charge(_load(input_path))
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(json.dumps(output, indent=2), encoding="utf-8")
            charge_value = output["normalizations"]["projected_baryon_number_charge_Z2Sigma"]
            output_written = True
        except Exception as exc:
            validation_error = str(exc)
    elif not boundary_projection["dirac_charge_boundary_projection_ready"]:
        validation_error = "Dirac charge boundary projection is not derived"
    elif not number_normalization["dirac_number_normalization_ready"]:
        validation_error = "Dirac number normalization is not derived"
    if output_written:
        primary_blocker = "none"
    elif boundary_projection.get("primary_blocker") and boundary_projection.get("primary_blocker") != "none":
        primary_blocker = boundary_projection["primary_blocker"]
    elif number_normalization.get("primary_blocker") and number_normalization.get("primary_blocker") != "none":
        primary_blocker = number_normalization["primary_blocker"]
    else:
        primary_blocker = "active_Dirac_charge_boundary_projection"
    return {
        "status": "janus-z2-sigma-projected-baryon-noether-charge-input-gate",
        "active_core": "Z2_tunnel_Sigma",
        "input_manifest": str(input_path),
        "output_manifest": str(output_path),
        "input_exists": input_exists,
        "projected_baryon_charge_manifest_written": output_written,
        "dirac_charge_boundary_projection_ready": boundary_projection[
            "dirac_charge_boundary_projection_ready"
        ],
        "dirac_charge_boundary_projection_closure": boundary_projection["closure"],
        "input_active_derived_manifest_is_authoritative": True,
        "upstream_frontiers": {
            "dirac_charge_boundary_projection": {
                "gate": boundary_projection["status"],
                "ready": boundary_projection["dirac_charge_boundary_projection_ready"],
                "closure": boundary_projection["closure"],
                "upstream_frontiers": boundary_projection["upstream_frontiers"],
                "nearest_required": boundary_projection["next_required"],
                "primary_blocker": boundary_projection.get(
                    "primary_blocker", "active_Dirac_charge_boundary_projection"
                ),
            },
            "dirac_number_normalization": {
                "gate": number_normalization["status"],
                "ready": number_normalization["dirac_number_normalization_ready"],
                "closure": number_normalization["closure"],
                "formulas": number_normalization["formulas"],
                "nearest_required": number_normalization["next_required"],
                "primary_blocker": number_normalization.get(
                    "primary_blocker", "active_Dirac_number_normalization"
                ),
            }
        },
        "nearest_projected_baryon_charge_frontier": {
            "blocks": [] if output_written else [
                "active_Dirac_charge_boundary_projection",
                "active_Dirac_number_normalization",
            ],
            "gates": [
                "P0EFTJanusZ2SigmaDiracChargeBoundaryProjectionGate",
                "P0EFTJanusZ2SigmaDiracNumberNormalizationGate",
            ],
            "diagnostic_only": True,
        },
        "projected_charge_formula_declared": True,
        "requires_projected_Dirac_current": True,
        "requires_charge_boundary_projection": True,
        "free_projection_weights_forbidden": True,
        "observational_baryon_fit_forbidden": True,
        "compressed_planck_lcdm_rd_forbidden": True,
        "archived_z4_reuse_forbidden": True,
        "projected_baryon_number_charge_value": charge_value,
        "primary_blocker": primary_blocker,
        "gate_passed": output_written,
        "validation_error": validation_error,
        "next_required": [
            "pass_projected_Dirac_matter_current_gate",
            "pass_Dirac_charge_boundary_projection_gate",
            "derive_projected_baryon_number_charge_Z2Sigma",
            "write_projected_baryon_noether_charge_source_inputs_json",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Projected Baryon Noether Charge Input Gate",
        "",
        f"Input exists: `{payload['input_exists']}`",
        f"Dirac charge boundary projection ready: `{payload['dirac_charge_boundary_projection_ready']}`",
        f"Projected charge manifest written: `{payload['projected_baryon_charge_manifest_written']}`",
        f"Gate passed: `{payload['gate_passed']}`",
        "",
        "## Next Required",
    ]
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    if payload["validation_error"]:
        lines.extend(["", "## Validation Error", payload["validation_error"]])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
