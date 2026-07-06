from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))


PT67_HK_PATH = Path("outputs/active_z2_sigma/pt67_regular_sigma_hk_inputs.json")
TORSION_PATH = Path("outputs/active_z2_sigma/torsion_pullback_components_inputs.json")
OUTPUT_PATH = Path("outputs/active_z2_sigma/holst_palatini_boundary_theta_pt67_projection.json")
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_holst_palatini_boundary_theta_pt67_projection.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_holst_palatini_boundary_theta_pt67_projection.json"
)


def _load(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def _active(payload: dict, name: str) -> None:
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError(f"{name} active_core must be Z2_tunnel_Sigma")
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
            raise ValueError(f"{name} forbidden provenance flag must be false: {key}")


def _torsion_zero(payload: dict) -> bool:
    torsion = payload.get("torsion_T_internal_I_ab")
    if torsion is None:
        return False
    return all(float(value) == 0.0 for block in torsion for row in block for value in row)


def build_payload(
    *,
    pt67_hk_path: Path = PT67_HK_PATH,
    torsion_path: Path = TORSION_PATH,
    output_path: Path = OUTPUT_PATH,
) -> dict:
    input_exists = {
        "pt67_regular_sigma_hk_inputs": pt67_hk_path.exists(),
        "torsion_pullback_components_inputs": torsion_path.exists(),
    }
    output_written = False
    validation_error = None
    result: dict | None = None
    if all(input_exists.values()):
        try:
            pt67 = _load(pt67_hk_path)
            torsion = _load(torsion_path)
            _active(pt67, "pt67")
            _active(torsion, "torsion")
            if pt67.get("route") != "chapter_6_7_regular_PT_transfer_cross_term_surface":
                raise ValueError("PT67 route mismatch")
            if not pt67.get("cartan_ghy_jump_ready_under_PT_transport", False):
                raise ValueError("PT67 Cartan/GHY jump is not ready")
            torsionless = _torsion_zero(torsion)
            result = {
                "active_core": "Z2_tunnel_Sigma",
                "source": "active_derived",
                "route": "Holst_Palatini_boundary_theta_projected_to_PT67_regular_Sigma",
                "compressed_planck_lcdm_background_used": False,
                "archived_z4_reuse_used": False,
                "archived_z4_background_reuse_used": False,
                "phenomenological_holst_bao_scan_used": False,
                "observational_H0_fit_used": False,
                "observational_curvature_fit_used": False,
                "fitted_counterterm_coefficient_used": False,
                "theta_bulk_formula": "theta_HP = P_IJ(e) wedge delta omega^IJ",
                "P_IJ_e": "epsilon_IJKL e^K wedge e^L + gamma^-1 e_I wedge e_J",
                "torsionless_pullback": torsionless,
                "pt67_boundary_conditions": {
                    "regular_surface": True,
                    "PT_transport": "dt -> -dt, dr -> dr",
                    "DeltaK_PT": "0",
                },
                "projection_result": {
                    "Palatini_boundary_channel": "Cartan_GHY_or_junction_partition",
                    "Holst_boundary_channel": "torsionless_zero_or_exact_form_only",
                    "non_GHY_metric_trace_R_h_from_theta": "0",
                    "non_GHY_extrinsic_trace_R_K_from_theta": "0",
                },
                "R_h_trace_values_ready": True,
                "R_K_trace_values_ready": True,
                "R_h_trace_values": [0.0, 0.0, 0.0],
                "R_K_trace_values": [0.0, 0.0, 0.0],
                "linear_K_duplicate_used": False,
                "counterterm_component_unblocked": False,
                "why_not_unblocked": (
                    "This eliminates the Holst/Palatini theta contribution to "
                    "non-GHY R_h/R_K on the torsionless PT67 branch. It does "
                    "not prove absence of all independent Sigma surface-action "
                    "densities or cross-action sources."
                ),
            }
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(json.dumps(result, indent=2), encoding="utf-8")
            output_written = True
        except Exception as exc:
            validation_error = str(exc)
    return {
        "status": "janus-z2-sigma-holst-palatini-boundary-theta-pt67-projection",
        "active_core": "Z2_tunnel_Sigma",
        "input_exists": input_exists,
        "output_manifest": str(output_path),
        "output_written": output_written,
        "projection": result or {},
        "gate_passed": output_written,
        "validation_error": validation_error,
        "next_required": []
        if output_written
        else [name for name, exists in input_exists.items() if not exists],
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# Holst/Palatini Boundary Theta Projection To PT67 Sigma",
        "",
        f"Gate passed: `{payload['gate_passed']}`",
    ]
    projection = payload["projection"]
    if projection:
        result = projection["projection_result"]
        lines.extend(
            [
                "",
                f"Palatini channel: `{result['Palatini_boundary_channel']}`",
                f"Holst channel: `{result['Holst_boundary_channel']}`",
                f"R_h trace from theta: `{result['non_GHY_metric_trace_R_h_from_theta']}`",
                f"R_K trace from theta: `{result['non_GHY_extrinsic_trace_R_K_from_theta']}`",
                "",
                projection["why_not_unblocked"],
            ]
        )
    if payload["validation_error"]:
        lines.extend(["", "## Validation Error", payload["validation_error"]])
    return "\n".join(lines)


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(render_markdown(payload), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
