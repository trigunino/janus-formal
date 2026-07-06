from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_saha_ionization_history_gate import (
    build_payload as build_saha_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_early_plasma_saha_inputs_assembler_gate import (
    build_payload as build_saha_inputs_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_early_plasma_manifest_writer_from_inputs_gate import (
    build_payload as build_early_plasma_manifest_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_thomson_drag_rate_builder_gate import (
    build_payload as build_thomson_drag_payload,
)
from scripts.run_p0_eft_janus_z2_sigma_effective_state_density_chain import (
    build_payload as build_density_chain_payload,
)
from scripts.write_p0_eft_janus_z2_sigma_baryon_density_si_from_dimensionless_invariants import (
    build_payload as build_si_density_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_plasma_unblock_chain.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_plasma_unblock_chain.json")


def build_payload() -> dict:
    density_chain = build_density_chain_payload()
    si_density = build_si_density_payload()
    saha = build_saha_payload()
    saha_inputs = build_saha_inputs_payload()
    early_manifest = build_early_plasma_manifest_payload()
    thomson = build_thomson_drag_payload()
    passed = (
        density_chain["chain_passed"]
        and si_density["gate_passed"]
        and saha["gate_passed"]
        and saha_inputs["gate_passed"]
        and early_manifest["gate_passed"]
        and thomson["gate_passed"]
    )
    if passed:
        primary_blocker = "none"
    elif not density_chain["chain_passed"]:
        primary_blocker = density_chain["primary_blocker"]
    elif not si_density["gate_passed"]:
        primary_blocker = si_density["primary_blocker"]
    else:
        primary_blocker = (
            saha["primary_blocker"]
            if not saha["gate_passed"]
            else "early_plasma_inputs"
            if not saha_inputs["gate_passed"]
            else "early_plasma_manifest"
            if not early_manifest["gate_passed"]
            else "active_H0_Z2Sigma"
        )
    return {
        "status": "janus-z2-sigma-plasma-unblock-chain",
        "active_core": "Z2_tunnel_Sigma",
        "density_chain": density_chain,
        "si_baryon_density": si_density,
        "saha_history": saha,
        "saha_inputs": saha_inputs,
        "early_plasma_manifest": early_manifest,
        "thomson_drag": thomson,
        "chain_passed": passed,
        "full_no_fit_prediction_ready": False,
        "primary_blocker": primary_blocker,
        "next_required": [
            "derive_or_supply_projected_occupation_state_inputs_json",
            "derive_H0_Z2Sigma_or_R_curv_Z2Sigma_m",
            "then_run_early_plasma_saha_inputs_assembler_gate",
            "then_run_early_plasma_manifest_writer_from_inputs_gate",
            "then_run_thomson_drag_rate_builder_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# Janus Z2/Sigma Plasma Unblock Chain",
                "",
                f"Density chain passed: `{payload['density_chain']['chain_passed']}`",
                f"SI baryon density passed: `{payload['si_baryon_density']['gate_passed']}`",
                f"Saha history passed: `{payload['saha_history']['gate_passed']}`",
                f"Saha inputs passed: `{payload['saha_inputs']['gate_passed']}`",
                f"Early-plasma manifest passed: `{payload['early_plasma_manifest']['gate_passed']}`",
                f"Thomson drag passed: `{payload['thomson_drag']['gate_passed']}`",
                f"Chain passed: `{payload['chain_passed']}`",
                f"Primary blocker: `{payload['primary_blocker']}`",
                f"Full no-fit prediction ready: `{payload['full_no_fit_prediction_ready']}`",
            ]
        ),
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
