from __future__ import annotations

import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from scripts.build_p0_eft_janus_z2_sigma_smooth_embedded_throat_gate import (
    build_payload as build_smooth_embedded_throat_payload,
)


REPORT_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_collar_tubular_neighborhood_gate.md")
JSON_PATH = Path("outputs/reports/p0_eft_janus_z2_sigma_collar_tubular_neighborhood_gate.json")


def build_payload() -> dict:
    throat = build_smooth_embedded_throat_payload()
    declared = {
        "collar_neighborhood_bibliography_checked": True,
        "tubular_neighborhood_bibliography_checked": True,
        "smooth_gluing_bibliography_checked": True,
        "projective_tunnel_interface_declared": True,
        "sigma_smooth_embedded_throat_gate_declared": True,
        "polar_neighborhood_removal_declared": True,
        "sigma_throat_declared": True,
        "normal_bundle_declared": True,
        "boundary_collars_declared": True,
        "observational_fit_forbidden": True,
    }
    closure = {
        "sigma_smooth_embedded_derived": throat["sigma_smooth_embedded_throat_ready"],
        "normal_bundle_derived": False,
        "plus_boundary_collar_derived": False,
        "minus_boundary_collar_derived": False,
        "tubular_neighborhood_derived": False,
        "collar_compatibility_derived": False,
        "collar_tubular_neighborhood_ready": False,
    }
    return {
        "status": "janus-z2-sigma-collar-tubular-neighborhood-gate",
        "active_core": "Z2_tunnel_Sigma",
        "primary_sources_checked": [
            "collar neighborhood theorem",
            "tubular neighborhood theorem",
            "smooth gluing/collaring for manifolds with boundary",
            "active Sigma smooth embedded throat gate",
        ],
        "source_links": [
            "https://ncatlab.org/nlab/show/collar+neighbourhood+theorem",
            "https://ncatlab.org/nlab/show/tubular+neighbourhood",
            "https://msp.org/agt/2007/7-1/agt-v7-n1-p01-p.pdf",
            "https://jfdavis.pages.iu.edu/teaching/m623/smooth_structures_and_handles.pdf",
        ],
        "bibliography_result": (
            "Standard sources provide collar and tubular neighborhoods once the "
            "boundary/submanifold hypotheses are met. The Janus-specific work is "
            "to prove Sigma is a smooth embedded throat with a derived normal "
            "bundle and compatible plus/minus collars."
        ),
        "declared": declared,
        "closure": closure,
        "upstream_frontiers": {
            "sigma_smooth_embedded_throat": {
                "gate": throat["status"],
                "ready": throat["sigma_smooth_embedded_throat_ready"],
                "closure": throat["closure"],
                "primary_blocker": throat.get("primary_blocker"),
            },
        },
        "formulas": {
            "plus_collar": "c_+ : Sigma x [0, eps) -> M_+",
            "minus_collar": "c_- : Sigma x [0, eps) -> M_-",
            "normal_tube": "nu(Sigma)_{<eps} -> U_Sigma",
            "compatibility": "c_+|Sigma = c_-|Sigma = id_Sigma",
        },
        "collar_tubular_neighborhood_ledger_declared": all(declared.values()),
        "collar_tubular_neighborhood_ready": all(declared.values()) and all(closure.values()),
        "standard_collar_tubular_theorems_available": True,
        "gate_passed": all(declared.values()) and all(closure.values()),
        "primary_blocker": (
            "none"
            if all(declared.values()) and all(closure.values())
            else throat.get("primary_blocker", "sigma_smooth_embedded_throat")
        ),
        "next_required": [
            "pass_sigma_smooth_embedded_throat_gate",
            "prove_sigma_is_smooth_embedded_throat",
            "derive_normal_bundle_of_sigma",
            "derive_plus_boundary_collar",
            "derive_minus_boundary_collar",
            "prove_collar_compatibility",
            "feed_result_to_resolved_tunnel_smooth_atlas_gate",
        ],
    }


def write_reports() -> dict:
    payload = build_payload()
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    lines = [
        "# Janus Z2/Sigma Collar Tubular Neighborhood Gate",
        "",
        f"Active core: `{payload['active_core']}`",
        f"Ledger declared: `{payload['collar_tubular_neighborhood_ledger_declared']}`",
        f"Ready: `{payload['collar_tubular_neighborhood_ready']}`",
        "",
        "## Bibliography",
        payload["bibliography_result"],
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
