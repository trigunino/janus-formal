from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_projected_dirac_matter_current_gate import (
    build_payload as build_projected_dirac_current_payload,
)
from scripts.build_p0_eft_janus_z2_sigma_spinor_bundle_projection_gate import (
    build_payload as build_spinor_bundle_projection_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_dirac_charge_boundary_projection_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_dirac_charge_boundary_projection_gate.json")


def build_payload() -> dict:
    projected_current = build_projected_dirac_current_payload()
    spinor_projection = build_spinor_bundle_projection_payload()
    projected_current_ready = projected_current["projected_dirac_matter_current_ready"]
    spinor_projection_ready = spinor_projection["spinor_bundle_projection_ready"]
    declared = {
        "curved_Dirac_charge_bibliography_checked": True,
        "projected_Dirac_matter_current_gate_declared": True,
        "spinor_bundle_projection_gate_declared": True,
        "spinor_boundary_projection_map_gate_declared": True,
        "plus_charge_integral_declared": True,
        "minus_charge_integral_declared": True,
        "Z2Sigma_charge_projection_declared": True,
        "conservation_anomaly_guard_declared": True,
        "boundary_leak_guard_declared": True,
        "observational_fit_forbidden": True,
    }
    closure = {
        "projected_Dirac_current_ready": projected_current_ready,
        "spinor_projection_ready": spinor_projection_ready,
        "plus_charge_integral_ready": False,
        "minus_charge_integral_ready": False,
        "Z2Sigma_projected_charge_ready": False,
        "charge_boundary_projection_ready": False,
    }
    return {
        "status": "janus-z2-sigma-dirac-charge-boundary-projection-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "Parker/Toms QFT in curved spacetime: conserved particle-number/electric charge currents",
            "Dirac equation in curved spacetime and associated conserved current",
            "Hollands/Wald curved-spacetime QFT framework",
        ],
        "bibliography_result": (
            "The literature supplies conserved-current charge integrals on hypersurfaces. "
            "It does not fix active Janus Z2/Sigma plus/minus charges or the projected throat charge."
        ),
        "source_links": [
            "https://books.google.com/books/about/Quantum_Field_Theory_in_Curved_Spacetime.html?id=5nNuGMBBTjMC",
            "https://inspirehep.net/literature/857188",
            "https://arxiv.org/abs/1401.2026",
        ],
        "declared": declared,
        "closure": closure,
        "upstream_frontiers": {
            "projected_dirac_matter_current": {
                "gate": projected_current["status"],
                "ready": projected_current_ready,
                "primary_blocker": projected_current.get("primary_blocker", "unknown"),
                "closure": projected_current["closure"],
            },
            "spinor_bundle_projection": {
                "gate": spinor_projection["status"],
                "ready": spinor_projection_ready,
                "primary_blocker": spinor_projection.get("primary_blocker", "unknown"),
                "closure": spinor_projection["closure"],
            },
        },
        "formulas": {
            "plus_charge": "N_+ = integral_{C_+} J_+^mu dSigma_mu",
            "minus_charge": "N_- = integral_{C_-} J_-^mu dSigma_mu",
            "projected_charge": "N_Z2Sigma = P_Z2Sigma(N_+, N_-; psi_Sigma^Z2)",
            "leak_guard": "dN_Z2Sigma/dtau = 0 only if anomaly and boundary-leak terms vanish",
        },
        "dirac_charge_boundary_projection_ledger_declared": all(declared.values()),
        "dirac_charge_boundary_projection_ready": all(declared.values()) and all(closure.values()),
        "gate_passed": all(declared.values()) and all(closure.values()),
        "primary_blocker": (
            "none"
            if all(declared.values()) and all(closure.values())
            else (
                projected_current["primary_blocker"]
                if not projected_current["gate_passed"]
                else spinor_projection["primary_blocker"]
                if not spinor_projection["gate_passed"]
                else "Dirac_charge_integrals_and_Z2Sigma_projection"
            )
        ),
        "next_required": [
            "pass_projected_Dirac_matter_current_gate",
            "pass_spinor_bundle_projection_gate",
            "prove_no_charge_anomaly_or_boundary_leak",
            "derive_N_plus_N_minus_and_N_Z2Sigma",
            "feed_result_to_Dirac_number_normalization_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Dirac Charge Boundary Projection Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['dirac_charge_boundary_projection_ledger_declared']}`",
        f"Charge projection ready: `{payload['dirac_charge_boundary_projection_ready']}`",
        f"Primary blocker: `{payload['primary_blocker']}`",
        "",
        "## Formulas",
    ]
    lines.extend(f"- `{key}`: `{value}`" for key, value in payload["formulas"].items())
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
