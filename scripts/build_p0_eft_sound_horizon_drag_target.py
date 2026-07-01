from __future__ import annotations

from pathlib import Path
import json

try:
    from scripts.build_p0_eft_bao_friction_ruler_derivation import fine_scan
except ModuleNotFoundError:
    from build_p0_eft_bao_friction_ruler_derivation import fine_scan


REPORT_PATH = Path("outputs/reports/p0_eft_sound_horizon_drag_target.md")
JSON_PATH = Path("outputs/reports/p0_eft_sound_horizon_drag_target.json")


def build_payload() -> dict:
    friction = fine_scan()
    dv_factor = float(friction["best"]["dv_factor"])
    rd_ratio = float(friction["effective_sound_horizon_ratio"])
    hubble_boost = 1.0 / rd_ratio
    delta_hubble_squared = hubble_boost * hubble_boost - 1.0
    return {
        "description": "Sound-horizon target implied by the Janus-Holst BAO D_V residual.",
        "status": "sound-horizon-drag-target-encoded",
        "input_dv_factor": dv_factor,
        "required_rd_ratio": rd_ratio,
        "required_rd_shrink": float(friction["effective_sound_horizon_shrink"]),
        "uniform_drag_epoch_hubble_boost": hubble_boost,
        "required_fractional_E2_excess": delta_hubble_squared,
        "chi2_after_target": friction["best"]["chi2"],
        "passes_bao_shape_gate": friction["passes_shape_gate"],
        "is_derived_geometry": False,
        "next_required": "derive the ~9.4% drag-epoch E^2 excess from Janus-Holst torsion/radion plasma dynamics.",
    }


def render_markdown(payload: dict) -> str:
    lines = [
        "# P0 EFT Sound Horizon Drag Target",
        "",
        payload["description"],
        "",
        f"Status: {payload['status']}",
        f"Passes BAO shape gate: {payload['passes_bao_shape_gate']}",
        f"Derived geometry: {payload['is_derived_geometry']}",
        "",
        "## Target",
        "",
        f"- D_V factor: {payload['input_dv_factor']:.6g}",
        f"- required r_d Janus / r_d ref: {payload['required_rd_ratio']:.6g}",
        f"- required r_d shrink: {payload['required_rd_shrink']:.6g}",
        f"- uniform drag-epoch H boost: {payload['uniform_drag_epoch_hubble_boost']:.6g}",
        f"- required fractional E^2 excess: {payload['required_fractional_E2_excess']:.6g}",
        "",
        "## Next",
        "",
        payload["next_required"],
        "",
    ]
    return "\n".join(lines)


def write_reports(report_path: Path = REPORT_PATH, json_path: Path = JSON_PATH) -> dict:
    report_path.parent.mkdir(parents=True, exist_ok=True)
    payload = build_payload()
    json_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    report_path.write_text(render_markdown(payload), encoding="utf-8")
    return payload


def main() -> None:
    write_reports()
    print(f"Wrote {REPORT_PATH}")
    print(f"Wrote {JSON_PATH}")


if __name__ == "__main__":
    main()
