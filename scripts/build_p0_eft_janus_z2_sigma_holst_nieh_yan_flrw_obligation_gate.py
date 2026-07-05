from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_torsion_pullback_on_sigma_gate import (
    build_payload as build_torsion_pullback_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_holst_nieh_yan_flrw_obligation_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_holst_nieh_yan_flrw_obligation_gate.json")


def build_payload() -> dict:
    torsion_pullback = build_torsion_pullback_payload()
    method = {
        "Holst_Nieh_Yan_bibliography_checked": True,
        "Holst_Nieh_Yan_torsion_relation_imported": True,
        "torsionless_Holst_vanishing_guard_declared": True,
        "Sigma_torsion_pullback_declared": True,
        "torsion_pullback_on_Sigma_gate_declared": True,
        "Immirzi_boundary_variation_declared": True,
    }
    closure = {
        "FLRW_torsion_irreducible_decomposition_ready": torsion_pullback[
            "closure"
        ]["FLRW_irreducible_torsion_pullback_ready"],
        "Holst_Nieh_Yan_FLRW_stress_reduced": False,
        "Holst_Nieh_Yan_rho_p_of_a_ready": False,
    }
    return {
        "status": "janus-z2-sigma-holst-nieh-yan-flrw-obligation-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "Banerjee 2010, arXiv:1002.0669",
            "Pollari 2023, arXiv:2302.00584",
            "Holst/Nieh-Yan scalar-Immirzi cosmology references",
        ],
        "bibliography_result": (
            "The generic Holst/Nieh-Yan torsion relation is available. No source gives the "
            "active Janus Z2/Sigma FLRW torsion pullback and rho/p reduction."
        ),
        "method": method,
        "closure": closure,
        "upstream_frontiers": {
            "torsion_pullback_on_sigma": {
                "gate": torsion_pullback["status"],
                "ready": torsion_pullback["torsion_pullback_on_sigma_ready"],
                "closure": torsion_pullback["closure"],
            },
        },
        "holst_nieh_yan_method_ready": all(method.values()),
        "holst_nieh_yan_FLRW_closure_ready": all(method.values()) and all(closure.values()),
        "guards": {
            "do_not_import_torsionless_Holst_as_nonzero": True,
            "do_not_reuse_archived_Z4_Immirzi_growth_coefficients": True,
            "dynamic_Immirzi_requires_boundary_variation": True,
        },
        "next_required": [
            "derive_FLRW_irreducible_torsion_pullback_on_Sigma",
            "pass_torsion_pullback_on_Sigma_gate",
            "vary_dynamic_Immirzi_Holst_Nieh_Yan_boundary_term_with_respect_to_h_ab",
            "reduce_Holst_Nieh_Yan_stress_to_rho_p_of_a",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Holst-Nieh-Yan FLRW Obligation Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Method ready: `{payload['holst_nieh_yan_method_ready']}`",
        f"FLRW closure ready: `{payload['holst_nieh_yan_FLRW_closure_ready']}`",
        "",
        "## Primary Sources Checked",
    ]
    lines.extend(f"- {item}" for item in payload["primary_sources_checked"])
    lines.extend(["", "## Next Required"])
    lines.extend(f"- `{item}`" for item in payload["next_required"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
