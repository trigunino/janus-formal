from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.derive_p0_eft_janus_z2_sigma_remaining_non_ghy_counterterm_channel_audit import (
    build_payload as build_non_ghy_audit,
)


AUDIT_PATH = Path("outputs/active_z2_sigma/remaining_non_ghy_counterterm_channel_audit.json")
GRID_SOURCE_PATH = Path("outputs/active_z2_sigma/cartan_ghy_components.json")
OUTPUT_PATH = Path("outputs/active_z2_sigma/counterterm_component_inputs.json")
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_counterterm_zero_component_inputs_from_no_extension.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_counterterm_zero_component_inputs_from_no_extension.json"
)


def _read_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def _load_or_build_audit(path: Path) -> dict:
    if path.exists():
        return _read_json(path)
    return build_non_ghy_audit(output_path=path)


def build_payload(
    *,
    audit_path: Path = AUDIT_PATH,
    grid_source_path: Path = GRID_SOURCE_PATH,
    output_path: Path = OUTPUT_PATH,
) -> dict:
    audit = _load_or_build_audit(audit_path)
    grid_source_exists = grid_source_path.exists()
    output_written = False
    validation_error = None

    can_write_zero = bool(
        audit.get("E_counterterm_zero_under_no_extension_policy")
        and audit.get("remaining_non_GHY_channel_absence_proved")
        and not any(audit.get("open_non_GHY_channels", {}).values())
    )
    if can_write_zero and grid_source_exists:
        try:
            grid_source = _read_json(grid_source_path)
            a_grid = grid_source["a_grid"]
            zeros = [0.0 for _ in a_grid]
            payload = {
                "active_core": "Z2_tunnel_Sigma",
                "source": "active_derived",
                "compressed_planck_lcdm_background_used": False,
                "archived_z4_reuse_used": False,
                "phenomenological_holst_bao_scan_used": False,
                "fitted_counterterm_coefficient_used": False,
                "counterterm_FLRW_stress_reduced": True,
                "counterterm_radial_reduction_ready": True,
                "counterterm_no_extension_zero_derived": True,
                "a_grid": a_grid,
                "counterterm_rho": zeros,
                "counterterm_p": zeros,
                "counterterm_provenance": (
                    "no-extension Z2/Sigma audit: Cartan-GHY/junction partition, "
                    "Holst/Palatini/Nieh-Yan exact boundary channel, PT67 smooth "
                    "joint/corner channel, spinor, connection, torsion and matter-flux "
                    "non-GHY sources eliminated; no published/adopted cross-action"
                ),
            }
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
            output_written = True
        except Exception as exc:
            validation_error = str(exc)

    return {
        "status": "janus-z2-sigma-counterterm-zero-component-inputs-from-no-extension",
        "active_core": "Z2_tunnel_Sigma",
        "audit_manifest": str(audit_path),
        "grid_source_manifest": str(grid_source_path),
        "output_manifest": str(output_path),
        "grid_source_exists": grid_source_exists,
        "remaining_non_GHY_absence_proved": bool(
            audit.get("remaining_non_GHY_channel_absence_proved")
        ),
        "no_extension_policy_forbids_cross_action": bool(
            audit.get("cross_action_audit", {}).get("no_extension_policy_forbids_cross_action")
        ),
        "E_counterterm_zero_under_no_extension_policy": bool(
            audit.get("E_counterterm_zero_under_no_extension_policy")
        ),
        "counterterm_component_inputs_written": output_written,
        "gate_passed": output_written,
        "validation_error": validation_error,
        "next_required": [] if output_written else [
            "prove_remaining_non_GHY_absence",
            "provide_active_component_a_grid",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Counterterm Zero Component Inputs From No-Extension",
        "",
        f"Remaining non-GHY absence proved: `{payload['remaining_non_GHY_absence_proved']}`",
        f"No-extension forbids cross-action: `{payload['no_extension_policy_forbids_cross_action']}`",
        f"E_counterterm zero under no-extension: `{payload['E_counterterm_zero_under_no_extension_policy']}`",
        f"Inputs written: `{payload['counterterm_component_inputs_written']}`",
    ]
    if payload["validation_error"]:
        lines.extend(["", "## Validation Error", payload["validation_error"]])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
