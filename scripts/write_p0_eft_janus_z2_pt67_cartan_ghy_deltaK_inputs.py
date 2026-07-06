from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.write_p0_eft_janus_z2_pt67_regular_sigma_hk_inputs import (
    JSON_PATH as PT67_HK_PATH,
)


OUTPUT_PATH = Path("outputs/active_z2_sigma/cartan_ghy_deltaK_inputs.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_pt67_cartan_ghy_deltaK_inputs.json")
DEFAULT_A_GRID = [0.25, 0.5, 1.0]


def _load_pt67_hk(path: Path) -> dict:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError("PT67 h/K active_core must be Z2_tunnel_Sigma")
    if payload.get("route") != "chapter_6_7_regular_PT_transfer_cross_term_surface":
        raise ValueError("PT67 h/K route mismatch")
    provenance = payload.get("provenance", {})
    if provenance.get("uses_observational_fit") is not False:
        raise ValueError("PT67 h/K input must not use observational fit")
    if provenance.get("uses_free_orientation_sign") is not False:
        raise ValueError("PT67 h/K input must not use a free orientation sign")
    delta = payload.get("DeltaK_PT_transport", {})
    if delta.get("DeltaK_ready") is not True:
        raise ValueError("PT67 DeltaK transport is not ready")
    if float(delta.get("DeltaK_TT", 1.0)) != 0.0:
        raise ValueError("PT67 DeltaK_TT must vanish")
    if float(delta.get("DeltaK_thetatheta", 1.0)) != 0.0:
        raise ValueError("PT67 DeltaK_thetatheta must vanish")
    if float(delta.get("DeltaK_screen_trace", 1.0)) != 0.0:
        raise ValueError("PT67 DeltaK_screen_trace must vanish")
    return payload


def build_payload(
    *,
    pt67_hk_path: Path = PT67_HK_PATH,
    a_grid: list[float] | None = None,
) -> dict:
    grid = list(DEFAULT_A_GRID if a_grid is None else a_grid)
    if len(grid) < 2 or any(value <= 0.0 for value in grid):
        raise ValueError("a_grid must contain positive values")
    if any(left >= right for left, right in zip(grid, grid[1:])):
        raise ValueError("a_grid must be strictly increasing")

    _load_pt67_hk(pt67_hk_path)
    zeros = [0.0 for _ in grid]
    return {
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_derived",
        "route": "chapter_6_7_regular_PT_transfer_cross_term_surface",
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "a_grid": grid,
        "DeltaK_s_Z2Sigma": zeros,
        "DeltaK_tau_Z2Sigma": zeros,
        "z2_orientation_sign": -1.0,
        "DeltaK_provenance": (
            "PT67 regular Sigma h/K transport: dt -> -dt, dr -> dr; "
            "DeltaK_TT and DeltaK_screen_trace vanish under PT pullback"
        ),
        "jump_convention": "PT_transport_pullback_not_outward_Israel_cut_and_paste",
        "uses_free_orientation_sign": False,
        "uses_observational_fit": False,
        "cartan_ghy_deltaK_inputs_ready": True,
    }


def write_outputs() -> dict:
    payload = build_payload()
    OUTPUT_PATH.parent.mkdir(parents=True, exist_ok=True)
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_outputs(), indent=2))
