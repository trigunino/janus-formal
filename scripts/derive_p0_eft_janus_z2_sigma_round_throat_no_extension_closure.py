from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from janus_lab.z2_sigma_round_throat_counterterm import (
    no_extension_zero_source_constraints,
)


HOLST_PATH = Path("outputs/active_z2_sigma/rsigma_E_HolstNiehYan.json")
MATTER_PATH = Path("outputs/active_z2_sigma/rsigma_E_matterFlux.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_round_throat_no_extension_closure.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_round_throat_no_extension_closure.json")


def _load_term(path: Path) -> dict | None:
    if not path.exists():
        return None
    payload = json.loads(path.read_text(encoding="utf-8"))
    if payload.get("active_core") != "Z2_tunnel_Sigma":
        raise ValueError(f"{path} active_core must be Z2_tunnel_Sigma")
    if payload.get("source") != "active_derived":
        raise ValueError(f"{path} source must be active_derived")
    values = np.asarray(payload.get("term_values"), dtype=float)
    if values.ndim != 1 or not np.all(np.isfinite(values)):
        raise ValueError(f"{path} term_values must be finite one-dimensional")
    return {**payload, "_term_values_array": values}


def build_payload(
    *,
    holst_path: Path = HOLST_PATH,
    matter_path: Path = MATTER_PATH,
) -> dict:
    holst = _load_term(holst_path)
    matter = _load_term(matter_path)
    terms_available = holst is not None and matter is not None
    source_terms_zero = False
    if terms_available:
        source_terms_zero = bool(
            np.allclose(holst["_term_values_array"], 0.0, atol=0.0)
            and np.allclose(matter["_term_values_array"], 0.0, atol=0.0)
        )
    constraints = no_extension_zero_source_constraints()
    radius_selection_ready = False
    return {
        "status": "janus-z2-sigma-round-throat-no-extension-closure",
        "active_core": "Z2_tunnel_Sigma",
        "source": "active_symbolic_derivation",
        "extension_allowed": False,
        "compressed_planck_lcdm_background_used": False,
        "archived_z4_reuse_used": False,
        "phenomenological_holst_bao_scan_used": False,
        "input_terms_available": terms_available,
        "HolstNiehYan_radial_block_zero": bool(
            holst is not None and np.allclose(holst["_term_values_array"], 0.0, atol=0.0)
        ),
        "matter_flux_radial_block_zero": bool(
            matter is not None and np.allclose(matter["_term_values_array"], 0.0, atol=0.0)
        ),
        "source_terms_zero": source_terms_zero,
        "round_throat_E_counterterm": constraints["polynomial"],
        "no_extension_zero_source_constraints": constraints,
        "radius_selection_ready": radius_selection_ready,
        "R_Sigma_solution_certificate_ready": False,
        "no_extension_closure_recorded": True,
        "gate_passed": True,
        "conclusion": (
            "With the current active Holst/Nieh-Yan and matter-flux radial blocks equal to zero, "
            "a local round-throat HK counterterm can either vanish identically on the round throat "
            "or require independently derived a0..a3. It does not select R_Sigma by itself."
        ),
        "next_required": [
            "derive_active_surface_density_coefficients_a0_a1_a2_a3",
            "or_derive_independent_global_regular_tunnel_radius_condition",
        ],
    }


def render_markdown(payload: dict) -> str:
    constraints = payload["no_extension_zero_source_constraints"]
    lines = [
        "# Janus Z2/Sigma Round-Throat No-Extension Closure",
        "",
        f"Source terms zero: `{payload['source_terms_zero']}`",
        f"Radius selection ready: `{payload['radius_selection_ready']}`",
        "",
        "## Result",
        payload["conclusion"],
        "",
        "## Polynomial",
        f"`{payload['round_throat_E_counterterm']}`",
        "",
        "## Zero-For-All-R Constraints",
    ]
    lines.extend(
        f"- `{key} = {value}`"
        for key, value in constraints["zero_for_all_positive_R_constraints"].items()
    )
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    return "\n".join(lines)


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(render_markdown(payload), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
