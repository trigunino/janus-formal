from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_complex_reality_combined_kks_period_gate import (
    build_payload as build_kks_payload,
)
from scripts.build_p0_eft_janus_complex_reality_active_embedding_or_compact_phase_gate import (
    build_payload as build_active_payload,
)


REPORTS = Path("outputs/reports")
JSON_PATH = REPORTS / "p0_eft_janus_complex_reality_prequantization_integrality_gate.json"
REPORT_PATH = REPORTS / "p0_eft_janus_complex_reality_prequantization_integrality_gate.md"


def build_payload() -> dict[str, Any]:
    kks = build_kks_payload()
    active = build_active_payload()

    checks = {
        "combined_KKS_formula_ready": kks["symbolic_combined_KKS_period_nonzero"],
        "boundary_two_cycle_declared": False,
        "compact_phase_direction_derived": False,
        "kks_density_nonzero_on_quantizable_cycle": False,
        "prequantization_period_computable": False,
        "integral_over_2pi_hbar_is_integer": False,
        "mass_or_charge_lattice_derived": False,
        "alpha_map_to_boundary_charge_derived": False,
        "j_quantization_derived": False,
    }

    route_ready = active["nonzero_KKS_boundary_period_route_ready"]

    checks["boundary_two_cycle_declared"] = bool(
        kks.get("checks", {}).get("cp1_derived_from_Janus_PT")
    )
    checks["compact_phase_direction_derived"] = route_ready
    checks["kks_density_nonzero_on_quantizable_cycle"] = bool(
        kks.get("janus_derived_combined_KKS_period_nonzero")
    )

    prequantization_integrality_ready = all(checks.values())

    return {
        "status": "janus-complex-reality-prequantization-integrality-gate",
        "checks": checks,
        "prequantization_integrality_ready": prequantization_integrality_ready,
        "prequantization_formula": "integral_Sigma Omega / (2*pi*|hbar|) in Z for a closed quantization cycle",
        "active_route_informational": active,
        "route_ready": route_ready,
        "alpha_generated_now": False,
        "verdict": (
            "The symbolic KKS structure is in place, but no closed quantization cycle "
            "with nonzero Omega, normalized integral, or derived lattice law is currently "
            "available to fix alpha_m."
        ),
        "still_missing": [key for key, ok in checks.items() if not ok],
        "next_gate": "ComplexRealityAlphaStateLawVerdictGate",
        "gate_passed": True,
    }


def write_reports() -> dict[str, Any]:
    payload = build_payload()
    REPORTS.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    REPORT_PATH.write_text(
        "\n".join(
            [
                "# Janus Complex Reality Prequantization Integrality Gate",
                "",
                f"Prequantization integral-ready: `{payload['prequantization_integrality_ready']}`",
                f"Alpha generated now: `{payload['alpha_generated_now']}`",
                f"Next gate: `{payload['next_gate']}`",
                "",
                payload["verdict"],
                "",
                "## Still Missing",
                *[f"- `{item}`" for item in payload["still_missing"]],
            ]
        )
        + "\n",
        encoding="utf-8",
    )
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
