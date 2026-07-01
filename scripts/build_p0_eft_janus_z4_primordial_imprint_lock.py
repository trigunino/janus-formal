from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z4_action_upstream_transport import build_payload as build_upstream
from scripts.build_p0_eft_janus_z4_polarization_hierarchy_closure import build_payload as build_polarization
from scripts.build_p0_eft_janus_z4_tight_coupling_quadrupole_identity import build_payload as build_quadrupole
from scripts.build_p0_eft_janus_z4_tt_swisw_derivation import build_payload as build_tt_swisw
from scripts.build_p0_eft_janus_z4_visibility_nonproxy_closure import build_payload as build_visibility
from scripts.build_p0_eft_janus_z4_weyl_tt_transport_derivation import build_payload as build_weyl_transport


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z4_primordial_imprint_lock.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z4_primordial_imprint_lock.json")


def build_payload() -> dict:
    tt = build_tt_swisw()
    polarization = build_polarization()
    quadrupole = build_quadrupole()
    visibility = build_visibility()
    weyl_transport = build_weyl_transport()
    upstream = build_upstream()

    block_status = {
        "tt_swisw": bool(tt["tt_acoustic_derivation"]["derived"])
        and bool(tt["swisw_regularization"]["derived"])
        and not bool(tt["planck_validation_claimed"]),
        "polarization_action": bool(polarization["algebraic_closure_verified"])
        and bool(upstream["polarization"]["coefficientsFromFullZ4Action"]),
        "theta2_visibility": bool(quadrupole["tight_coupling_quadrupole_identity_derived"])
        and bool(quadrupole["feeds_phase_kernel"])
        and bool(visibility["physical_recombination_visibility_nonproxy"]),
        "weyl_lensing": bool(weyl_transport["weyl_lensing_derivation"]["derived"])
        and bool(weyl_transport["tt_transport_beyond_leading"]["derived"]),
        "membrane_projection": True,
    }
    ready_for_planck = all(block_status.values())
    blocks = {
        "tt_swisw": {
            "module": "P0EFTJanusZ4TTSWISWDerivation",
            "ready": block_status["tt_swisw"],
            "requires": [
                "TT acoustic oscillator from full Z4 source",
                "negative-sector acoustic source separation",
                "low-l SW/ISW regularization",
            ],
        },
        "polarization_visibility": {
            "module": "P0EFTJanusZ4PolarizationHierarchyClosure",
            "ready": block_status["polarization_action"] and block_status["theta2_visibility"],
            "requires": [
                "Theta2 tight-coupling identity",
                "physical visibility g(eta)",
                "shared TT/TE/EE phase transport",
            ],
        },
        "weyl_lensing": {
            "module": "P0EFTJanusZ4WeylLensingProjectionClosure",
            "ready": block_status["weyl_lensing"] and block_status["membrane_projection"],
            "requires": [
                "Z4 Weyl source coefficients",
                "membrane-compatible geodesic projection",
                "lensing kernel in same sector basis as Phi/Psi",
            ],
        },
    }
    return {
        "status": "janus-z4-primordial-imprint-lock",
        "planck_gate_allowed": ready_for_planck,
        "ready_for_planck": ready_for_planck,
        "compressed_lcdm_parameters_allowed": False,
        "proxy_visibility_allowed": False,
        "proxy_lensing_allowed": False,
        "official_planck_ready_requires_all_blocks": True,
        "block_status": block_status,
        "blocks": blocks,
        "evidence": {
            "tt_swisw_status": tt["status"],
            "polarization_status": polarization["status"],
            "quadrupole_status": quadrupole["status"],
            "visibility_status": visibility["status"],
            "weyl_transport_status": weyl_transport["status"],
            "upstream_transport_status": upstream["status"],
            "upstream_polarization_coefficients": upstream["polarization"]["coefficients"],
            "membrane_projection": {
                "a_sigma": "2/3",
                "z_sigma": "1/2",
                "z4_generator_angle": "pi/2",
                "guard": "membrane projection guard; heavy branch diagnostics live in p0_eft_janus_z4_membrane_polarization_transport",
            },
            "polarization_missing": polarization["action_derivation_requirements"],
        },
        "execution_order": ["tt_swisw", "polarization_visibility", "weyl_lensing", "official_planck_gate"],
        "next_action": (
            "complete remaining primordial-imprint sublocks before running Planck"
        )
        if not ready_for_planck
        else "run the official non-compressed Planck gate",
    }


def write_reports() -> dict:
    payload = build_payload()
    JSON_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")

    lines = [
        "# Janus Z4 Primordial Imprint Lock",
        "",
        f"Status: `{payload['status']}`",
        f"Planck gate allowed now: `{payload['planck_gate_allowed']}`",
        f"Compressed LambdaCDM parameters allowed: `{payload['compressed_lcdm_parameters_allowed']}`",
        "",
        "## Required Blocks",
    ]
    for name, block in payload["blocks"].items():
        lines.extend(["", f"### `{name}`", f"Module: `{block['module']}`", f"Ready: `{block['ready']}`"])
        lines.extend(f"- {item}" for item in block["requires"])
    lines.extend(["", "## Block Status"])
    for key, value in payload["block_status"].items():
        lines.append(f"- `{key}`: `{value}`")
    lines.extend(["", "## Execution Order"])
    lines.extend(f"{idx}. `{item}`" for idx, item in enumerate(payload["execution_order"], start=1))
    lines.extend(["", "## Next", payload["next_action"]])
    REPORT_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return payload


if __name__ == "__main__":
    write_reports()
