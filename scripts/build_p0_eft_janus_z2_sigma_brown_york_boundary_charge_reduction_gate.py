from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_brown_york_k_difference_symbolic_gate import (
    build_payload as build_k_difference,
)


Q_PATH = Path("outputs/active_z2_sigma/unit_intrinsic_metric_q_ab_inputs.json")
G_PATH = Path("outputs/active_z2_sigma/background_gravity_normalization_inputs.json")
REPORT_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_brown_york_boundary_charge_reduction_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/p0_eft_janus_z2_sigma_brown_york_boundary_charge_reduction_gate.json"
)


def _read_json(path: Path) -> dict | None:
    if not path.exists():
        return None
    return json.loads(path.read_text(encoding="utf-8"))


def build_payload(*, q_path: Path = Q_PATH, g_path: Path = G_PATH) -> dict:
    q_payload = _read_json(q_path)
    g_payload = _read_json(g_path)
    k_diff = build_k_difference()
    q_ready = bool(q_payload and q_payload.get("active_core") == "Z2_tunnel_Sigma")
    g_ready = bool(g_payload and g_payload.get("active_core") == "Z2_tunnel_Sigma")
    topology = (q_payload or {}).get("spatial_topology", {})
    closure = {
        "unit_intrinsic_metric_q_ab_available": q_ready,
        "surface_volume_factor_available": "volume_factor_pi2_R3" in topology,
        "G_Z2Sigma_available": g_ready,
        "boundary_reference_subtraction_available": True,
        "k_ref_minus_k_phys_symbolic_available": bool(
            k_diff["symbolic_boundary_charge_formula_ready"]
        ),
        "absolute_R_Sigma_or_surface_measure_available": False,
        "boundary_charge_above_reference_available": False,
    }
    return {
        "status": "janus-z2-sigma-brown-york-boundary-charge-reduction-gate",
        "active_core": "Z2_tunnel_Sigma",
        "charge_route": "BrownYork_quasilocal_boundary_reference_subtraction",
        "formula": (
            "E_BY[Sigma] = (1/kappa) integral_Sigma N sqrt(q) "
            "(k_ref - k_phys), with the reference branch subtracted to zero."
        ),
        "known_inputs": {
            "q_manifest": str(q_path),
            "G_manifest": str(g_path),
            "volume_factor_pi2_R3": topology.get("volume_factor_pi2_R3"),
            "symbolic_E_BY_for_eps_minus_one": k_diff["formulas"][
                "E_BY_for_eps_minus_one"
            ],
            "reference_prescription_conclusion": k_diff["reference_prescription"][
                "conclusion"
            ],
        },
        "closure": closure,
        "boundary_charge_reduction_ready": all(closure.values()),
        "H0_mapping_ready": False,
        "blocked_by": [
            item
            for item, ok in closure.items()
            if not ok
        ],
        "forbidden_shortcuts": [
            "do_not_replace_k_ref_minus_k_phys_by_fit",
            "do_not_use_dimensionless_RSigma_over_ell_as_absolute_measure",
            "do_not_identify_reference_zero_with_physical_charge",
        ],
        "next_required": [
            "derive_absolute_R_Sigma_or_active_surface_measure",
            "then_compute_boundary_charge_above_reference",
        ],
        "gate_passed": True,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Brown-York Boundary Charge Reduction Gate",
        "",
        f"Formula: `{payload['formula']}`",
        f"Charge reduction ready: `{payload['boundary_charge_reduction_ready']}`",
        f"H0 mapping ready: `{payload['H0_mapping_ready']}`",
        "",
        "## Blocked By",
    ]
    lines.extend(f"- `{item}`" for item in payload["blocked_by"])
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
