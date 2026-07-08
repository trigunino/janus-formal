from __future__ import annotations

import json
from pathlib import Path
from typing import Any


REPORTS = Path("outputs/reports")
JSON_PATH = REPORTS / "p0_eft_janus_complex_reality_candidate_phase_space_matrix_gate.json"
REPORT_PATH = REPORTS / "p0_eft_janus_complex_reality_candidate_phase_space_matrix_gate.md"


def build_payload() -> dict[str, Any]:
    core = [
        {
            "id": "active_throat_S2",
            "base_object": "geometric S2 on Sigma",
            "status": "best_direct_route",
            "missing": [
                "active_Omega_Sigma_pullback",
                "nonzero_area_component",
            ],
        },
        {
            "id": "CP1_spinor_frame_orbit",
            "base_object": "SU(2)/U(1) ~= S2",
            "status": "best_quantum_candidate",
            "missing": [
                "Janus_PT_derives_CP1_orbit",
                "map_j_to_alpha_m",
            ],
        },
        {
            "id": "aroundSigma_cross_compact_phase",
            "base_object": "S1 x S1 action-angle torus",
            "status": "plausible_higher_risk",
            "missing": [
                "compact_phase_derived",
                "nonzero_KKS_cross_term",
            ],
        },
    ]
    extensions = [
        {
            "id": "moebius_twisted_throat",
            "base": "aroundSigma_cross_compact_phase",
            "useful_if": "twist derives compact phase or Pin/spin holonomy",
            "not_useful_if": "only changes topology picture",
        },
        {
            "id": "klein_twofold_shadow",
            "base": "aroundSigma_cross_compact_phase",
            "useful_if": "quotient/lift creates compact phase direction",
            "not_useful_if": "only restates Z2 cover",
        },
        {
            "id": "higher_CPn_flag_orbit",
            "base": "CP1_spinor_frame_orbit",
            "useful_if": "Janus_PT naturally has larger compact orbit",
            "not_useful_if": "primitive periods reduce to CP1 roots",
        },
        {
            "id": "spin_pin_lift",
            "base": "CP1_or_aroundSigma_phase",
            "useful_if": "lift fixes spinor orbit or quantized holonomy",
            "not_useful_if": "no boundary symplectic form is produced",
        },
        {
            "id": "TQFT_level_on_Sigma",
            "base": "CP1_or_torus",
            "useful_if": "level is derived from Janus boundary action",
            "not_useful_if": "level is inserted by hand",
        },
        {
            "id": "casimir_topological_vacuum",
            "base": "active_throat_S2",
            "useful_if": "produces source and symplectic state law tied to Sigma",
            "not_useful_if": "only gives energy scale",
        },
    ]
    return {
        "status": "janus-complex-reality-candidate-phase-space-matrix-gate",
        "core_candidate_count": len(core),
        "core_candidates": core,
        "extensions": extensions,
        "extension_policy": (
            "Open an extension only if it produces active Omega_Sigma on S2, "
            "a Janus-derived CP1 orbit, or a compact phase paired with aroundSigma."
        ),
        "matrix_ready": True,
        "alpha_generated_now": False,
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    REPORTS.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# Janus Complex Reality Candidate Phase-Space Matrix Gate",
                "",
                f"Core candidate count: `{payload['core_candidate_count']}`",
                f"Matrix ready: `{payload['matrix_ready']}`",
                f"Alpha generated now: `{payload['alpha_generated_now']}`",
                "",
                payload["extension_policy"],
            ]
        )
        + "\n",
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
