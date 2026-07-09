from __future__ import annotations

import json
from pathlib import Path


JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_global_state_formal_asset_inventory.json")
REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_global_state_formal_asset_inventory.md")


def _exists(path: str) -> bool:
    return Path(path).exists()


def build_payload() -> dict:
    assets = {
        "projected_baryon_noether_charge": {
            "lean": "JanusFormal/Branches/Z2SigmaRegular/MatterPlasmaSpinor/Gates/P0EFTJanusZ2SigmaProjectedBaryonNoetherChargeInputGate.lean",
            "role": "projects Dirac/Noether baryon charge to Sigma",
            "closes_absolute_normalization": False,
            "remaining_blocker": "authoritative charge manifest or Dirac number normalization",
        },
        "baryon_noether_volume_density": {
            "lean": "JanusFormal/Branches/Z2SigmaRegular/MatterPlasmaSpinor/Gates/P0EFTJanusZ2SigmaBaryonNumberDensityNoetherVolumeGate.lean",
            "role": "turns projected charge plus active volume into density",
            "closes_absolute_normalization": False,
            "remaining_blocker": "projected charge and active spatial volume",
        },
        "souriau_boundary_hamiltonian": {
            "lean": "JanusFormal/Branches/Z2SigmaRegular/GlobalBimetricAlpha/Gates/P0EFTJanusZ2SigmaSouriauBoundaryHamiltonianAttemptGate.lean",
            "role": "global charge/Hamiltonian label and moment-map route",
            "closes_absolute_normalization": False,
            "remaining_blocker": "local density or metric/K variation from the charge",
        },
        "cosmological_charge_projection_exhaustion": {
            "script": "scripts/build_p0_eft_janus_z2_cosmological_charge_projection_exhaustion_gate.py",
            "role": "checks whether visible total charge becomes M_bridge",
            "closes_absolute_normalization": False,
            "remaining_blocker": "state/projection theorem plus absolute charge or volume",
        },
        "global_bimetric_state_to_sector_normalization": {
            "lean": "JanusFormal/Branches/Z2SigmaRegular/GlobalBimetricAlpha/Gates/P0EFTJanusZ2GlobalBimetricStateToFLRWSectorNormalizationGate.lean",
            "script": "scripts/build_p0_eft_janus_z2_global_bimetric_state_to_flrw_sector_normalization_gate.py",
            "role": "strict adapter from global stress-energy state to rho_+0/rho_-0",
            "closes_absolute_normalization": False,
            "remaining_blocker": "global_bimetric_stress_energy_state_inputs.json",
        },
    }
    for asset in assets.values():
        if "lean" in asset:
            asset["lean_exists"] = _exists(asset["lean"])
        if "script" in asset:
            asset["script_exists"] = _exists(asset["script"])
    return {
        "status": "janus-z2-global-state-formal-asset-inventory",
        "active_core": "Z2_tunnel_Sigma",
        "assets": assets,
        "conclusion": (
            "JanusFormal already contains Noether/Souriau/charge-density scaffolds. "
            "They identify the correct charge routes but do not select the absolute "
            "global bimetric stress-energy state needed for rho_+0/rho_-0."
        ),
        "next_required": [
            "derive or admit active global_bimetric_stress_energy_state_inputs.json",
            "then run global_bimetric_state_to_flrw_sector_normalization_gate",
        ],
        "gate_passed": True,
    }


def write_reports() -> dict:
    payload = build_payload()
    JSON_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2 Global State Formal Asset Inventory",
        "",
        payload["conclusion"],
        "",
        "## Assets",
    ]
    for name, asset in payload["assets"].items():
        lines.append(
            f"- `{name}`: closes_absolute_normalization=`{asset['closes_absolute_normalization']}`; "
            f"blocker=`{asset['remaining_blocker']}`"
        )
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
