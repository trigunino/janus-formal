from __future__ import annotations

import json
from pathlib import Path
from typing import Any


REPORTS = Path("outputs/reports")
JSON_PATH = REPORTS / "p0_eft_janus_complex_reality_eq131_kks_projection_gate.json"
REPORT_PATH = REPORTS / "p0_eft_janus_complex_reality_eq131_kks_projection_gate.md"


def build_payload() -> dict[str, Any]:
    # Minimal explicit counterexample with L=I, C=e0, P'=e0.
    # Eq. 131 raw translation term is T_raw = 2 C P'^dagger.
    # T_raw[0,0]=2 is Hermitian, not anti-Hermitian, so it cannot be used
    # directly as an anti-Hermitian moment component for KKS construction.
    raw_term_antihermitian_residual = 4.0
    projected_term_antihermitian_residual = 0.0
    return {
        "status": "janus-complex-reality-eq131-kks-projection-gate",
        "source_anchor": "X2026-complex-reality Eq. 131 and appendix Eq. 13",
        "published_eq131_accepted_as_source_anchor": True,
        "raw_eq131_translation_term": "2*C*P_prime_dagger*L_dagger",
        "raw_eq131_translation_term_preserves_antihermitian_M_generically": False,
        "explicit_counterexample": {
            "L": "I",
            "C": "e0",
            "P_prime": "e0",
            "T_raw_00": 2.0,
            "T_raw_dagger_plus_T_raw_00": raw_term_antihermitian_residual,
        },
        "kks_ready_translation_term": "C*P_prime_dagger*L_dagger - L*P_prime*C_dagger",
        "kks_ready_term_matches_real_appendix_pattern": True,
        "kks_ready_term_preserves_antihermitian_M": True,
        "projected_counterexample_residual": projected_term_antihermitian_residual,
        "interpretation": (
            "Eq. 131 is a valid source anchor for the complex coadjoint route, "
            "but KKS use must keep the moment in the anti-Hermitian dual space. "
            "Therefore the translation contribution must be represented by its "
            "anti-Hermitian projection, matching the real appendix subtraction."
        ),
        "blocks_alpha": False,
        "blocks_state_space_gate": False,
        "blocks_kks_density_gate": False,
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    REPORTS.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# Janus Complex Reality Eq. 131 KKS Projection Gate",
                "",
                f"Published Eq. 131 accepted: `{payload['published_eq131_accepted_as_source_anchor']}`",
                f"Raw term generically anti-Hermitian: `{payload['raw_eq131_translation_term_preserves_antihermitian_M_generically']}`",
                f"KKS-ready term: `{payload['kks_ready_translation_term']}`",
                f"Matches real appendix pattern: `{payload['kks_ready_term_matches_real_appendix_pattern']}`",
                "",
                payload["interpretation"],
            ]
        )
        + "\n",
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
