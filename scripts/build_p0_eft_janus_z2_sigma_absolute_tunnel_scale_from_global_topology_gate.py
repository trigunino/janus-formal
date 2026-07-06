from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.build_p0_eft_janus_z2_sigma_optimal_reference_embedding_scale_gate import (
    build_payload as build_reference_scale,
)
from scripts.write_p0_eft_janus_z2_sigma_rsigma_over_ell_collar_from_projective_stereographic import (
    build_payload as build_ratio,
)


REPORT_PATH = Path(
    "outputs/reports/"
    "p0_eft_janus_z2_sigma_absolute_tunnel_scale_from_global_topology_gate.md"
)
JSON_PATH = Path(
    "outputs/reports/"
    "p0_eft_janus_z2_sigma_absolute_tunnel_scale_from_global_topology_gate.json"
)


def build_payload() -> dict:
    ratio = build_ratio()
    reference = build_reference_scale()
    closure = {
        "global_projective_topology_declared": True,
        "Z2_antipodal_cover_declared": True,
        "resolved_tunnel_sigma_declared": True,
        "projective_ratio_RSigma_over_ell_collar_fixed": bool(
            ratio["ratio_solution_ready"]
        ),
        "reference_embedding_subtraction_declared": bool(
            reference["reference_prescription_ready"]
        ),
        "global_topology_has_dimensionful_scale": False,
        "homothety_degeneracy_removed": False,
        "absolute_RSigma_derived": False,
    }
    return {
        "status": "janus-z2-sigma-absolute-tunnel-scale-from-global-topology-gate",
        "active_core": "Z2_tunnel_Sigma",
        "question": "Can global Janus topology alone derive an absolute tunnel scale?",
        "result": (
            "No. The S4/RP4 projective topology plus tunnel regularity fixes the "
            "dimensionless ratio R_Sigma/ell_collar, currently 1, but remains "
            "invariant under a common homothety R_Sigma -> L R_Sigma and "
            "ell_collar -> L ell_collar. A dimensionful datum is required."
        ),
        "closure": closure,
        "ratio_result": {
            "R_Sigma_over_ell_collar": ratio["R_Sigma_over_ell_collar"],
            "absolute_RSigma_fixed": ratio["full_R_Sigma_solution_certificate_ready"],
            "primary_blocker": ratio["primary_blocker"],
        },
        "homothety_argument": {
            "transformation": "(R_Sigma, ell_collar) -> (L R_Sigma, L ell_collar)",
            "invariant": "R_Sigma/ell_collar",
            "brown_york_charge_scaling": "E_BY -> L^2 E_BY",
            "H0_mapping_scaling": "H0 cannot be fixed until L is fixed",
        },
        "absolute_scale_derivable_from_global_topology": False,
        "allowed_without_new_input": [
            "R_Sigma_over_ell_collar = 1",
            "symbolic_E_BY = 12*pi^2*R_Sigma^2/kappa_Z2Sigma",
            "scale_free_topological_statements",
        ],
        "needed_dimensionful_datum": [
            "absolute ell_collar from an action parameter or boundary metric",
            "absolute R_Sigma from a global metric normalization theorem",
            "boundary charge value from an independent state/Noether sector",
            "Planck/UV length only if derived as part of the Janus action, not inserted by hand",
        ],
        "forbidden_shortcuts": [
            "do_not_set_RSigma_equals_one_in_physical_units",
            "do_not_promote_stereographic_unit_radius_to_length",
            "do_not_extract_length_from_topology_without_dimensionful_structure",
        ],
        "gate_passed": True,
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Absolute Tunnel Scale From Global Topology Gate",
        "",
        payload["result"],
        "",
        f"Absolute scale derivable: `{payload['absolute_scale_derivable_from_global_topology']}`",
        "",
        "## Homothety Argument",
    ]
    lines.extend(
        f"- `{key}`: `{value}`" for key, value in payload["homothety_argument"].items()
    )
    lines.extend(["", "## Needed Dimensionful Datum"])
    lines.extend(f"- `{item}`" for item in payload["needed_dimensionful_datum"])
    REPORT_PATH.write_text("\n".join(lines), encoding="utf-8")
    return payload


if __name__ == "__main__":
    print(json.dumps(write_reports(), indent=2))
