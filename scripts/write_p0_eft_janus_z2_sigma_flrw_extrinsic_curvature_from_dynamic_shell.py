from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "src"
if str(SRC) not in sys.path:
    sys.path.insert(0, str(SRC))

from janus_lab.z2_sigma_extrinsic_curvature import (
    build_flrw_extrinsic_curvature_grid_payload,
    dynamic_spherical_shell_extrinsic_curvature_components,
)


INPUT_PATH = Path("outputs/active_z2_sigma/dynamic_shell_extrinsic_curvature_inputs.json")
OUTPUT_PATH = Path("outputs/active_z2_sigma/flrw_extrinsic_curvature_grid_inputs.json")
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_flrw_extrinsic_curvature_from_dynamic_shell.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_flrw_extrinsic_curvature_from_dynamic_shell.json"
)


def _load(path: Path) -> dict:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("dynamic shell payload active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_derived":
        raise ValueError("dynamic shell payload source must be active_derived")
    for key in [
        "compressed_planck_lcdm_background_used",
        "archived_z4_reuse_used",
        "phenomenological_holst_bao_scan_used",
        "observational_fit_used",
    ]:
        if payload.get(key) is not False:
            raise ValueError(f"Forbidden provenance flag must be false: {key}")
    return payload


def build_payload(*, input_path: Path = INPUT_PATH, output_path: Path = OUTPUT_PATH) -> dict:
    if not input_path.exists():
        return {
            "status": "janus-z2-sigma-flrw-extrinsic-curvature-from-dynamic-shell",
            "active_core": "Z2_tunnel_Sigma",
            "input_manifest": str(input_path),
            "output_manifest": str(output_path),
            "flrw_extrinsic_curvature_grid_inputs_written": False,
            "gate_passed": False,
            "primary_blocker": "dynamic_shell_extrinsic_curvature_inputs_missing",
        }

    validation_error = None
    try:
        source = _load(input_path)
        components = dynamic_spherical_shell_extrinsic_curvature_components(
            R=source["R_Sigma_of_a"],
            R_dot=source["R_dot_of_a"],
            R_ddot=source["R_ddot_of_a"],
            f_plus=source["f_plus_of_R"],
            f_minus=source["f_minus_of_R"],
            df_plus_dR=source["df_plus_dR"],
            df_minus_dR=source["df_minus_dR"],
            epsilon_plus=float(source["epsilon_plus"]),
            epsilon_minus=float(source["epsilon_minus"]),
        )
        built = build_flrw_extrinsic_curvature_grid_payload(
            a_grid=source["a_grid"],
            k_s_plus=components["K_s_plus"],
            k_s_minus=components["K_s_minus"],
            k_tau_plus=components["K_tau_plus"],
            k_tau_minus=components["K_tau_minus"],
            z2_orientation_sign=float(source["z2_orientation_sign"]),
            k_provenance=source["dynamic_shell_provenance"],
        )
        built["K_reduction_route"] = "dynamic_spherical_shell"
        output_path.parent.mkdir(parents=True, exist_ok=True)
        output_path.write_text(json.dumps(built, indent=2), encoding="utf-8")
        written = True
    except Exception as exc:
        validation_error = str(exc)
        written = False

    return {
        "status": "janus-z2-sigma-flrw-extrinsic-curvature-from-dynamic-shell",
        "active_core": "Z2_tunnel_Sigma",
        "input_manifest": str(input_path),
        "output_manifest": str(output_path),
        "flrw_extrinsic_curvature_grid_inputs_written": written,
        "gate_passed": written,
        "primary_blocker": "none" if written else "invalid_dynamic_shell_inputs",
        "validation_error": validation_error,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# Janus Z2/Sigma FLRW Extrinsic Curvature From Dynamic Shell",
                "",
                f"Written: `{payload['flrw_extrinsic_curvature_grid_inputs_written']}`",
                f"Primary blocker: `{payload['primary_blocker']}`",
            ]
        ),
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
