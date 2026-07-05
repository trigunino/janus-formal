from __future__ import annotations

import json
import sys
from pathlib import Path

import numpy as np

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from scripts.build_p0_eft_janus_z2_sigma_holst_nieh_yan_radial_inputs_from_torsionless_identity_gate import (
    build_payload as build_holst_nieh_yan_torsionless_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_stress_equivariance_gate import (
    build_payload as build_stress_equivariance_payload,
)


INPUT_PATH = Path("outputs/active_z2_sigma/holst_nieh_yan_radial_inputs.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_holst_torsion_flux_zero_or_equivariance_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_holst_torsion_flux_zero_or_equivariance_gate.json")


def _load_zero_holst_boundary_flux(path: Path) -> tuple[bool, str | None]:
    if not path.exists():
        return False, "holst_nieh_yan_radial_inputs_missing"
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
        if payload.get("active_core") != "Z2_tunnel_Sigma":
            return False, "active_core_mismatch"
        if payload.get("source") != "active_derived":
            return False, "source_not_active_derived"
        if payload.get("torsionless_Nieh_Yan_zero_identity_ready") is not True:
            return False, "torsionless_Nieh_Yan_zero_identity_not_ready"
        values = np.asarray(payload.get("E_HolstNiehYan_values"), dtype=float)
        if values.ndim != 1 or values.size == 0:
            return False, "E_HolstNiehYan_values_invalid"
        if not np.all(np.isfinite(values)):
            return False, "E_HolstNiehYan_values_not_finite"
        if float(np.max(np.abs(values))) > 1e-12:
            return False, "E_HolstNiehYan_values_nonzero"
        return True, None
    except Exception as exc:
        return False, str(exc)


def build_payload(*, input_path: Path = INPUT_PATH) -> dict:
    torsionless_writer = (
        {"status": "preexisting-holst-nieh-yan-radial-inputs"}
        if input_path.exists()
        else build_holst_nieh_yan_torsionless_payload(output_path=input_path)
    )
    stress_equivariance = build_stress_equivariance_payload()
    zero_boundary_flux_ready, validation_error = _load_zero_holst_boundary_flux(input_path)
    z2_equivariance_ready = bool(
        stress_equivariance["closure"].get("Holst_torsion_stress_Z2_equivariance_derived")
    )
    ready = zero_boundary_flux_ready or z2_equivariance_ready
    return {
        "status": "janus-z2-sigma-holst-torsion-flux-zero-or-equivariance-gate",
        "active_core": "Z2_tunnel_Sigma",
        "declared": {
            "Holst_Nieh_Yan_boundary_flux_slot_declared": True,
            "torsionless_Nieh_Yan_zero_identity_route_declared": True,
            "Z2_equivariant_Holst_stress_route_declared": True,
            "bulk_Holst_stress_not_claimed_from_boundary_identity": True,
            "observational_fit_forbidden": True,
        },
        "routes": {
            "torsionless_boundary_flux": {
                "ready": zero_boundary_flux_ready,
                "source_gate": torsionless_writer["status"],
                "validation_error": validation_error,
                "scope": "local_Sigma_Holst_Nieh_Yan_radial_flux_slot_only",
            },
            "z2_equivariant_holst_stress": {
                "ready": z2_equivariance_ready,
                "source_gate": stress_equivariance["status"],
                "scope": "full_Holst_stress_flux_cancellation_if_derived",
            },
        },
        "formulas": {
            "torsionless_identity": "T|_Sigma = 0 -> d(e^a wedge T_a)|_Sigma = 0 -> E_HolstNiehYan = 0",
            "equivariance_route": "F_Holst^Z2Sigma = F_Holst^+ + eps_Z2 F_Holst^- = 0 if T_Holst^- = tau_* T_Holst^+",
        },
        "holst_torsion_flux_zero_or_equivariance_ready": ready,
        "gate_passed": ready,
        "primary_blocker": "none" if ready else "Holst_boundary_flux_zero_or_Z2_equivariance",
        "scope": {
            "active_sigma_flux_slot": "closed_if_gate_passed",
            "off_sigma_bulk_Holst_stress": "not_claimed",
            "dynamic_Immirzi_bulk_profile": "not_required_for_torsionless_boundary_flux_identity",
        },
        "next_required": []
        if ready
        else [
            "derive_torsionless_Holst_Nieh_Yan_radial_inputs",
            "or_derive_Holst_torsion_stress_Z2_equivariance",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Holst Torsion Flux Zero Or Equivariance Gate",
        "",
        f"Ready: `{payload['holst_torsion_flux_zero_or_equivariance_ready']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
        "",
        "## Routes",
    ]
    for name, route in payload["routes"].items():
        lines.append(f"- `{name}`: ready=`{route['ready']}`, scope=`{route['scope']}`")
    lines.extend(["", "## Scope"])
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["scope"].items())
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
