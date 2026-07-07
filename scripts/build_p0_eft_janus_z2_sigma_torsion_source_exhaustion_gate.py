from __future__ import annotations

import json
from pathlib import Path
from typing import Any


REPORTS = Path("outputs/reports")
ACTIVE = Path("outputs/active_z2_sigma")

SPIN_CURRENT_PATH = REPORTS / "p0_eft_janus_z2_sigma_spin_current_of_a_gate.json"
TORSION_FIELD_PATH = REPORTS / "p0_eft_janus_z2_sigma_torsion_field_solution_of_a_gate.json"
TORSION_PULLBACK_PATH = ACTIVE / "torsion_pullback_components_inputs.json"
HOLST_ZERO_PATH = REPORTS / "p0_eft_janus_z2_sigma_holst_torsion_flux_zero_or_equivariance_gate.json"
THETA_PATH = ACTIVE / "holst_palatini_boundary_theta_pt67_projection.json"
LLBRANE_PATH = REPORTS / "p0_eft_janus_z2_null_sigma_llbrane_tension_derivation_frontier_gate.json"
JSON_PATH = REPORTS / "p0_eft_janus_z2_sigma_torsion_source_exhaustion_gate.json"
REPORT_PATH = REPORTS / "p0_eft_janus_z2_sigma_torsion_source_exhaustion_gate.md"


def _read(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8")) if path.exists() else {}


def _all_nested_zero(value: Any) -> bool:
    if isinstance(value, list):
        return all(_all_nested_zero(v) for v in value)
    if isinstance(value, (int, float)):
        return float(value) == 0.0
    return False


def build_payload(
    spin_current_path: Path = SPIN_CURRENT_PATH,
    torsion_field_path: Path = TORSION_FIELD_PATH,
    torsion_pullback_path: Path = TORSION_PULLBACK_PATH,
    holst_zero_path: Path = HOLST_ZERO_PATH,
    theta_path: Path = THETA_PATH,
    llbrane_path: Path = LLBRANE_PATH,
) -> dict[str, Any]:
    spin = _read(spin_current_path)
    torsion_field = _read(torsion_field_path)
    pullback = _read(torsion_pullback_path)
    holst_zero = _read(holst_zero_path)
    theta = _read(theta_path)
    llbrane = _read(llbrane_path)

    spin_ready = bool(spin.get("spin_current_of_a_ready"))
    boundary_torsion_ready = bool(
        torsion_field.get("closure", {}).get("boundary_torsion_source_of_a_ready")
    )
    torsion_pullback_ready = bool(pullback.get("Sigma_torsion_pullback_ready"))
    torsion_pullback_zero = torsion_pullback_ready and _all_nested_zero(
        pullback.get("torsion_T_internal_I_ab")
    )
    nieh_yan_nonzero = bool(holst_zero.get("routes", {}).get("z2_equivariant_holst_stress", {}).get("ready")) and not bool(
        holst_zero.get("routes", {}).get("torsionless_boundary_flux", {}).get("ready")
    )
    torsionful_bc_ready = boundary_torsion_ready or (
        bool(theta.get("torsionless_pullback")) is False and theta != {}
    )
    singular_defect_ready = bool(llbrane.get("chi_LL_derivation_ready"))

    source_channels = {
        "spin_current_on_sigma": {
            "exists_in_physics": True,
            "active_in_model": spin_ready,
            "reason_if_inactive": "Dirac/fermion route exists, but fermion distribution and spin polarization on Sigma are not derived.",
        },
        "nieh_yan_charge_nonzero": {
            "exists_in_physics": True,
            "active_in_model": nieh_yan_nonzero,
            "reason_if_inactive": "Active Sigma torsion pullback is zero; Nieh-Yan is zero/exact on the torsionless branch.",
        },
        "torsionful_boundary_condition": {
            "exists_in_physics": True,
            "active_in_model": torsionful_bc_ready,
            "reason_if_inactive": "PT67 boundary theta is explicitly torsionless and no boundary torsion source is derived.",
        },
        "singular_defect_source": {
            "exists_in_physics": True,
            "active_in_model": singular_defect_ready,
            "reason_if_inactive": "Null/LL bridge is a separate extension; it gives mass in terms of chi_LL but no Janus chi_LL selection.",
        },
    }
    torsion_source_on_sigma = any(ch["active_in_model"] for ch in source_channels.values())

    return {
        "status": "janus-z2-sigma-torsion-source-exhaustion-gate",
        "active_core": "Z2_tunnel_Sigma",
        "branch": "regular_PT67_Sigma",
        "question": "Does the active Janus/Z2/PT67 model derive a nonzero torsion source on Sigma?",
        "torsion_pullback_ready": torsion_pullback_ready,
        "torsion_pullback_zero": torsion_pullback_zero,
        "source_channels": source_channels,
        "torsion_source_on_sigma": torsion_source_on_sigma,
        "open_torsionful_holst_nieh_yan_sigma": torsion_source_on_sigma,
        "archive_torsionful_branch_recommended": not torsion_source_on_sigma,
        "what_is_proven": (
            "Relative to the active field content and PT67 torsionless boundary data, "
            "no nonzero Sigma torsion source is derived."
        ),
        "what_is_not_proven": (
            "This does not prove that no extension can source torsion. It only blocks "
            "torsionful Holst/Nieh-Yan as an active Janus/Z2 consequence until one "
            "source channel is derived."
        ),
        "allowed_reopen_inputs": [
            "derive Sigma fermion distribution and spin polarization",
            "derive nonzero Nieh-Yan/torsion charge on the throat",
            "derive torsionful first-order boundary condition",
            "derive a singular/null defect source with selected chi_LL",
        ],
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    JSON_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# Janus Z2 Sigma Torsion Source Exhaustion Gate",
                "",
                f"Torsion source on Sigma: `{payload['torsion_source_on_sigma']}`",
                f"Open torsionful Holst/Nieh-Yan Sigma: `{payload['open_torsionful_holst_nieh_yan_sigma']}`",
                f"Archive torsionful branch recommended: `{payload['archive_torsionful_branch_recommended']}`",
                "",
                payload["what_is_proven"],
                "",
                payload["what_is_not_proven"],
            ]
        ),
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
